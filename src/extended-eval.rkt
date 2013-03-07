#lang racket

(require compiler/compiler
         compiler/zo-parse
         compiler/zo-marshal
         "priminfo.rkt")

(define (compile-bytecode expr)
  (let ([tmp (make-temporary-file)])
    (call-with-output-file tmp #:exists 'truncate
      (λ (p) 
        (parameterize ([current-namespace (make-base-namespace)])
          (write (compile expr) p))))
    (begin0
      (call-with-input-file tmp zo-parse)
      (delete-file tmp))))

(define ip->bytecode
  (lambda (ip)
    (zo-parse ip)))

(define zo-file->bytecode
  (lambda (fn)
    (call-with-input-file fn ip->bytecode)))

(define source-file->bytecode
  (let ([compile-file (let ([compile-files (compile-zos #f)])
                        (lambda (fn dir)
                          (compile-files (list fn) dir)))])
    (lambda (fn)
      (let ([dir (make-temporary-file "rkt-compile-tmp-~a" 'directory)])
        (parameterize ([current-namespace (make-base-namespace)]
                       [compile-context-preservation-enabled #t])
          (compile-file fn dir))
        (zo-file->bytecode
          (path-replace-suffix (path->complete-path fn dir) "_rkt.zo"))))))

(define source->bytecode
  (lambda (expr)
    (ip->bytecode
      (let ([out (open-output-bytes)])
        (parameterize ([current-namespace (make-base-namespace)]
                       [compile-context-preservation-enabled #t])
          (write (compile expr) out))
        (close-output-port out)
        (open-input-bytes (get-output-bytes out))))))

;;
;; output grammar:
;;  Prog --> `(,<Expr> ,<TextSegPart> ...)
;;  Expr --> (loc <offset>)
;;        |  (loc-clr <offset>)
;;        |  (loc-noclr <offset>)
;;        |  (loc-box <offset>)
;;        |  (loc-box-clr <offset>)
;;        |  (loc-box-noclr <offset>)
;;        |  (let-one <Expr> <Expr>)
;;        |  (let-void <offset> <Expr>)
;;        |  (let-void-box <offset> <Expr>)
;;        |  (install-value <offset> <Expr> <Expr>)
;;        |  (install-value-box <offset> <Expr> <Expr>)
;;        |  (boxenv <offset> <Expr>)
;;        |  (application <Expr> <Expr> ...)
;;        |  (seq <Expr> ...)
;;        |  (branch <Expr> <Expr> <Expr>)
;;        |  (let-rec <Expr> ... <Expr>)
;;        |  (lam (<ts> ...) (<free-n> ...) <Expr>)
;;        |  (proc-const (<ts> ...) <Expr>)
;;        |  (indirect <symbol>)
;;        |  (case-lam <Expr>)
;;        |  (constant <const>)
;;        |  (quote <symbol>)     ;; maybe a variable reference?
;;        |  (primval <prim-symbol>)
;;  TextSegPart --> (<symbol> <Expr>)
;;
(define (impl->model expr)
  (define cycled (cycle-points expr))
  (define text-addr (make-hasheq))
  (define next-loc
    (let ([suffix 0])
      (λ ()
        (set! suffix (add1 suffix))
        (string->symbol (format "x~s" suffix)))))
  (define text-seg '())
  (cons 
    (let recur ([e expr])
      (match e
        [(compilation-top _ _ e) (recur e)]
        [(localref #f n #f #t #f) `(loc ,n)]
        [(localref #f n #t _ #f) `(loc-clr ,n)]
        [(localref #f n #f #f #f) `(loc-noclr ,n)]
        [(localref #t n #f #t #f) `(loc-box ,n)]
        [(localref #t n #t _ #f) `(loc-box-clr ,n)]
        [(localref #t n #f #f #f) `(loc-box-noclr ,n)]
        [(let-one r b #f #f) `(let-one ,(recur r) ,(recur b))]
        [(let-void n #f b) `(let-void ,n ,(recur b))]
        [(let-void n #t b) `(let-void-box ,n ,(recur b))]
        [(install-value 1 n #f r b) `(install-value ,n ,(recur r) ,(recur b))]
        [(install-value 1 n #t r b)
         `(install-value-box ,n ,(recur r) ,(recur b))]
        [(boxenv n b) `(boxenv ,n ,(recur b))]
        [(application f as) `(application ,(recur f) ,@(map recur as))]
        [(seq es) `(seq ,@(map recur es))]
        [(branch c t e) `(branch ,(recur c) ,(recur t) ,(recur e))]
        [(let-rec rs b) `(let-rec ,@(map recur rs) ,(recur b))]
        [(lam _ _ _ τs #f ns `(val/ref ...) _ _ b)
         `(lam ,τs ,(vector->list ns) ,(recur b))]
        [(closure l _)
         (define (model-rep)
           (match-let ([`(lam ,τs () ,b) (recur l)])
             `(proc-const ,τs ,b)))
          (if (hash-ref cycled e #f)
              `(indirect ,(let ([x (hash-ref text-addr e #f)])
                            (or x
                                (let ([x (next-loc)])
                                  (hash-set! text-addr e x)
                                  (set! text-seg (cons (list x (model-rep)) text-seg))
                                  x))))
              (model-rep))]
        [(case-lam _ ls) `(case-lam ,@(map recur ls))]
        [(? void?) `(constant ,(void))]
        [(? number?) `(constant ,e)]
        [(? boolean?) `(constant ,e)]
        [(? symbol?) `',e] ;; I think this corresponds to a variable reference (not sure)
        ;; "extended" cases
        [(primval n) `(primval ,(lookup-primitive n))]
        [_ (error 'impl->model "unrecognized form ~s" e)]))
   text-seg))

(define (cycle-points expr)
  (define seen (make-hasheq))
  (let recur ([e expr])
    (when (zo? e) ; i.e., not a literal
      (if (hash-ref seen e #f)
          (unless (closure? e)
            (error 'cycle-refs "illegal cycle through ~s" e))
          (begin
            (hash-set! seen e #t)
            (match e
              [(compilation-top _ _ e)
               (recur e)]
              [(localref _ _ _ _ _)
               (void)]
              [(let-one r b _ _)
               (recur r)
               (recur b)]
              [(let-void _ _ b)
               (recur b)]
              [(install-value _ _ _ r b)
               (recur r)
               (recur b)]
              [(boxenv _ b)
               (recur b)]
              [(application f as)
               (recur f) 
               (for-each recur as)]
              [(seq es)
               (for-each recur es)]
              [(branch c t e)
               (recur c)
               (recur t)
               (recur e)]
              [(let-rec rs b)
               (for-each recur rs) 
               (recur b)]
              [(lam _ _ _ _ _ _ _ _ _ b)
               (recur b)]
              [(closure l _)
               (recur l)]
              [(case-lam _ ls)
               (for-each recur ls)]
              [_ (void)])))))
  seen)

;;
;; input grammar:
;;  Prog --> `(,<Expr> ,<TextSegPart> ...)
;;  Expr --> (loc <offset>)
;;        |  (loc-clr <offset>)
;;        |  (loc-noclr <offset>)
;;        |  (loc-box <offset>)
;;        |  (loc-box-clr <offset>)
;;        |  (loc-box-noclr <offset>)
;;        |  (let-one <Expr> <Expr>)
;;        |  (let-void <offset> <Expr>)
;;        |  (let-void-box <offset> <Expr>)
;;        |  (install-value <offset> <Expr> <Expr>)
;;        |  (install-value-box <offset> <Expr> <Expr>)
;;        |  (boxenv <offset> <Expr>)
;;        |  (application <Expr> <Expr> ...)
;;        |  (seq <Expr> ...)
;;        |  (branch <Expr> <Expr> <Expr>)
;;        |  (let-rec <Expr> ... <Expr>)
;;        |  (lam (<ts> ...) (<free-n> ...) <Expr>)
;;        |  (proc-const (<ts> ...) <Expr>)
;;        |  (indirect <symbol>)
;;        |  (case-lam <Expr> ...)
;;        |  (constant <const>)
;;        |  (quote <symbol>)     ;; maybe a variable reference?
;;        |  (primval <prim-symbol>)
;;  TextSegPart --> (<symbol> <Expr>)
;;
;; ----
;; output grammar:
;;  Prog --> (prog ([<symbol> <Expr>] ...) <Expr>)
;;  TextSeg (removed)
;;  Expr (unchanged)
(define (model->prog pair) `(prog ,(cdr pair) ,(car pair)))

(define-syntax rec
  (syntax-rules ()
    [(_ id expr) (letrec ([id expr]) id)]))

(define-syntax trace-define
  (syntax-rules ()
    [(_ (name . args) body0 body1 ...)
     (define name
       (let ([depth 0])
         (lambda targs
           (set! depth (+ depth 1))
           (let loop ([n depth]) (unless (zero? n) (display #\|) (loop (- n 1))))
           (pretty-print (cons 'name targs))
           (call-with-values
             (lambda () (apply (lambda args body0 body1 ...) targs))
             (lambda targs
               (set! depth (- depth 1))
               (let loop ([n depth]) (unless (zero? n) (display #\|) (loop (- n 1))))
               (if (= (length targs) 1) (pretty-print (car targs)) (pretty-print (cons 'values targs)))
               (apply values targs))))))]
    [(_ name lexpr)
     (define name
       (let ([depth 0])
         (lambda args
           (set! depth (+ depth 1))
           (let loop ([n depth]) (unless (zero? n) (write #\|) (loop (- n 1))))
           (pretty-print (cons 'name args))
           (call-with-values
             (lambda () (apply lexpr args))
             (lambda args
               (set! depth (- depth 1))
               (let loop ([n depth]) (unless (zero? n) (write #\|) (loop (- n 1))))
               (if (= (length args) 1) (pretty-print (car args)) (pretty-print (cons 'values args)))
               (apply values args))))))]))

(define next-symbol
  (let ([n 0])
    (lambda ()
      (begin0
        (string->symbol (string-append "t." (number->string n)))
        (set! n (+ n 1))))))

;;
;; input grammar:
;;  Prog --> (prog ([<symbol> <Expr>] ...) <Expr>)
;;  Expr --> (loc <offset>)
;;        |  (loc-clr <offset>)
;;        |  (loc-noclr <offset>)
;;        |  (loc-box <offset>)
;;        |  (loc-box-clr <offset>)
;;        |  (loc-box-noclr <offset>)
;;        |  (let-one <Expr> <Expr>)
;;        |  (let-void <offset> <Expr>)
;;        |  (let-void-box <offset> <Expr>)
;;        |  (install-value <offset> <Expr> <Expr>)
;;        |  (install-value-box <offset> <Expr> <Expr>)
;;        |  (boxenv <offset> <Expr>)
;;        |  (application <Expr> <Expr> ...)
;;        |  (seq <Expr> ...)
;;        |  (branch <Expr> <Expr> <Expr>)
;;        |  (let-rec <Expr> ... <Expr>)
;;        |  (lam (<ts> ...) (<free-n> ...) <Expr>)
;;        |  (proc-const (<ts> ...) <Expr>)
;;        |  (indirect <symbol>)
;;        |  (case-lam <Expr> ...)
;;        |  (constant <const>)
;;        |  (quote <symbol>)     ;; maybe a variable reference?
;;        |  (primval <prim-symbol>)
;;
;; -----
;; output grammar:
;;  Prog --> (prog ([<symbol> <Expr>] ...) <Expr>)
;;  Expr --> (ref <ref-type> <symbol>)
;;        |  (boxref <ref-type> <symbol>)
;;        |  (let ([<symbol> <Expr>] ...) <Expr>)
;;        |  (set! <symbol> <Expr>)
;;        |  (set-box! <symbol> <Expr>)
;;        |  (boxenv <symbol>)
;;        |  (application <Expr> <Expr> ...)
;;        |  (seq <Expr> ...)
;;        |  (let-rec ([<symbol> <Expr>]) <Expr>)
;;        |  (lam ((<symbol> : <ts>) ...) <Expr>)
;;        |  (case-lam <Expr> ...)
;;        |  (constant <const>)
;;        |  (quote <symbol>)
;;        |  (primval <prim>)
;;
(define (reintroduce-variables x)
  (define (next-symbol* n env)
    (for/fold ([ls '()] [env env]) ([n n])
      (let ([x (next-symbol)]) (values (cons x ls) (cons x env)))))
  (define (Expr* env e*)
    (if (null? e*) '() (cons (Expr env (car e*)) (Expr* env (cdr e*)))))
  (define (Expr env x)
    (match x
      [`(loc ,n) `(ref normal ,(list-ref env n))]
      [`(loc-clr ,n) `(ref clr ,(list-ref env n))]
      [`(loc-noclr ,n) `(ref noclr ,(list-ref env n))]
      [`(loc-box ,n) `(boxref normal ,(list-ref env n))]
      [`(loc-box-clr ,n) `(boxref clr ,(list-ref env n))]
      [`(loc-box-noclr ,n) `(boxref noclr ,(list-ref env n))]
      [`(let-one ,e0 ,e1)
       (let ([x (next-symbol)])
         `(let ([,x ,(Expr env e0)]) ,(Expr (cons x env) e1)))]
      [`(let-void ,n (let-rec ,e* ... ,e))
       (let-values ([(x* env) (next-symbol* n env)])
         (let ([e* (Expr* env e*)] [e (Expr env e)])
           `(let-rec ,(map (lambda (x e) (list x e)) x* e*) ,e)))]
      [`(let-void ,n ,e)
       (let-values ([(x* env) (next-symbol* n env)])
         `(let ,(map (lambda (x) (list x `(constant ,(void)))) x*)
            ,(Expr env e)))]
      [`(let-void-box ,n ,e)
       (let-values ([(x* env) (next-symbol* n env)])
         `(let ,(map (lambda (x) (list x `(constant ,(void)))) x*)
            ,(let loop ([x* x*])
               (if (null? x*)
                   (Expr env e)
                   `(seq (boxenv ,(car x*)) ,(loop (cdr x*)))))))]
      [`(install-value ,n ,e0 ,e1)
       `(seq (set! ,(list-ref env n) ,(Expr env e0)) ,(Expr env e1))]
      [`(install-value-box ,n ,e0 ,e1)
       `(seq (set-box! ,(list-ref env n) ,(Expr env e0)) ,(Expr env e1))]
      [`(boxenv ,n ,e) `(seq (boxenv ,(list-ref env n)) ,(Expr env e))]
      [`(application ,e ,e* ...)
       (let-values ([(rx* env) (next-symbol* e* env)])
         `(application ,(Expr env e) ,@(Expr* env e*)))]
      [`(seq ,e* ...) `(seq ,@(Expr* env e*))]
      [`(branch ,e0 ,e1 ,e2) `(branch ,(Expr env e0) ,(Expr env e1) ,(Expr env e2))]
      [`(let-rec ,e* ... ,e)
       (if (null? e*)
           (Expr env e)
           (error 'reintroduce-variables
             "found let-rec outside of let-void ~s" x))]
      [`(lam (,ts* ...) (,n* ...) ,e)
       (let ([free-x* (map (lambda (n) (list-ref env n)) n*)])
         (let-values ([(x* env) (next-symbol* ts* env)])
           (let ([env (append free-x* env)])
             `(lam
                ,(map (lambda (x ts) (list x ': ts)) x* ts*)
                ,(Expr env e)))))]
      [`(proc-const (,ts* ...) ,e)
       (let-values ([(x* env) (next-symbol* ts* env)])
         `(lam ,(map (lambda (x ts) (list x ': ts)) x* ts*) ,(Expr env e)))]
      [`(indirect ,x) `(ref indirect ,x)]
      [`(case-lam ,e* ...) `(case-lam ,@(Expr* env e*))]
      [`(constant ,c) `(constant ,c)]
      [`(quote ,s) `(quote ,s)]
      [`(primval ,pr) `(primval ,pr)]))
  (define (Prog x)
    (match x
      [`(prog ([,x* ,e*] ...) ,e)
       (let ([e* (Expr* '() e*)] [e (Expr '() e)])
         `(prog ,(map list x* e*) ,e))]))
  (Prog x))

;;
;; input grammar:
;;  Prog --> (prog ([<symbol> <Expr>] ...) <Expr>)
;;  Expr --> (ref <ref-type> <symbol>)
;;        |  (boxref <ref-type> <symbol>)
;;        |  (let ([<symbol> <Expr>] ...) <Expr>)
;;        |  (set! <symbol> <Expr>)
;;        |  (set-box! <symbol> <Expr>)
;;        |  (boxenv <symbol>)
;;        |  (application <Expr> <Expr> ...)
;;        |  (seq <Expr> ...)
;;        |  (let-rec ([<symbol> <Expr>] ...) <Expr>)
;;        |  (lam ((<symbol> : <ts>) ...) <Expr>)
;;        |  (case-lam <Expr> ...)
;;        |  (constant <const>)
;;        |  (quote <symbol>)
;;        |  (primval <prim>)
;;
;; ------
;; output grammar:
;;  Prog   --> (prog ([<symbol> <Lamda>] ...) <Expr>)
;;  Lambda --> (lam ((<symbol> : <ts>) ...) <Expr>)
;;  Expr   --> <Lambda>
;;          |  (ref <ref-type> <symbol>)
;;          |  (boxref <ref-type> <symbol>)
;;          |  (let ([<symbol> <Expr>] ...) <Expr>)
;;          |  (set! <symbol> <Expr>)
;;          |  (set-box! <symbol> <Expr>)
;;          |  (boxenv <symbol> <Expr>)
;;          |  (application <Expr> <Expr> ...)
;;          |  (seq <Expr> <Expr> <Expr> ...)
;;          |  (let-rec ([<symbol> <Lambda>] ...) <Expr>)
;;          |  (case-lam <Lambda> ...)
;;          |  (constant <const>)
;;          |  (quote <symbol>)
;;          |  (primval <prim>)
;;
(define (check-grammar x)
  (define (Expr! e)
    (match e
      [`(lam ((,x* : ,ts*) ...) ,e) (Expr! e)]
      [`(ref ,type ,x) (void)]
      [`(boxref ,type ,x) (void)]
      [`(let ([,x* ,e*] ...) ,e) (for-each Expr! e*) (Expr! e)]
      [`(set! ,x ,e) (Expr! e)]
      [`(set-box! ,x ,e) (Expr! e)]
      [`(boxenv ,x) (void)]
      [`(application ,e ,e* ...) (Expr! e) (for-each Expr! e*)]
      [`(seq ,e0 ,e1 ,e* ...) (Expr! e0) (Expr! e1) (for-each Expr! e*)]
      [`(branch ,e0 ,e1 ,e2) (Expr! e0) (Expr! e1) (Expr! e2)]
      [`(let-rec ([,x* ,le*] ...) ,e) (for-each Lambda! le*) (Expr! e)]
      [`(case-lam ,le* ...) (for-each Lambda! le*)]
      [`(constant ,c) (void)]
      [`(quote ,x) (void)]
      [`(primval ,prim) (void)]
      [_ (error 'check-grammar "unmatched language form ~s" e)]))
  (define (Lambda! le)
    (match le
      [`(lam ((,x* : ,ts*) ...) ,e) (Expr! e)]
      [_ (error 'check-grammar "invalid lambda expression ~s" le)]))
  (define (Prog! x)
    (match x
      [`(prog ([,x* ,le*] ...) ,e) (for-each Lambda! le*) (Expr! e)]
      [_ (error 'check-grammar "invalid program form ~s" x)]))
  (Prog! x)
  x)

;;
;; input grammar:
;;  Prog   --> (prog ([<symbol> <Lamda>] ...) <Expr>)
;;  Lambda --> (lam ((<symbol> : <ts>) ...) <Expr>)
;;  Expr   --> <Lambda>
;;          |  (ref <ref-type> <symbol>)
;;          |  (boxref <ref-type> <symbol>)
;;          |  (let ([<symbol> <Expr>] ...) <Expr>)
;;          |  (set! <symbol> <Expr>)
;;          |  (set-box! <symbol> <Expr>)
;;          |  (boxenv <symbol>)
;;          |  (application <Expr> <Expr> ...)
;;          |  (seq <Expr> <Expr> <Expr> ...)
;;          |  (branch <Expr> <Expr> <Expr>)
;;          |  (let-rec ([<symbol> <Lambda>] ...) <Expr>)
;;          |  (case-lam <Lambda> ...)
;;          |  (constant <const>)
;;          |  (quote <symbol>)
;;          |  (primval <prim>)
;;
;; ------
;; output grammar:
;;  Lambda --> (lam ((<symbol> : <ts>) ...) <Expr>)
;;  AExpr  --> <Lambda>
;;          |  (case-lam <Expr> ...)
;;          |  (boxref <ref-type> <symbol>)
;;          |  (constant <const>)
;;          |  (primval <prim>)
;;          |  (primcall <prim> <AExpr> ...)
;;          |  (quote <symbol>)
;;  CExpr  --> (application <AExpr> <AExpr> ...)
;;          |  (branch <AExpr> <AExpr> <AExpr>)
;;          |  (set! <symbol> <AExpr>)
;;          |  (set-box! <symbol> <AExpr>)
;;          |  (boxenv <symbol>)
;;          |  (let-rec ([<symbol> <Lambda>] ...) <Expr>)
;;  Expr   --> <AExpr>
;;          |  <CExpr>
;;          |  (seq <Expr> <Expr>)
;;          |  (let (<symbol> <Expr>) <Expr>)
;;
(define (to-anormal-form x)
  (define (build-seq* e0 e1 e*)
    (if (null? e*)
        `(seq ,e0 ,e1)
        `(seq ,e0 ,(build-seq* e1 (car e*) (cdr e*)))))
  (define (build-let rx* re* body)
    (if (null? rx*)
        body
        (build-let (cdr rx*) (cdr re*)
          (let ([x (car rx*)])
            (if x
                `(let (,x ,(car re*)) ,body)
                `(seq ,(car re*) ,body))))))
  (define (AExpr* rx* re* e*)
    (if (null? e*)
        (values rx* re* '())
        (let-values ([(rx* re* e) (AExpr rx* re* (car e*))])
          (let-values ([(rx* re* e*) (AExpr* rx* re* (cdr e*))])
            (values rx* re* (cons e e*))))))
  (define (Binding* rx* re* x* e*)
    (if (null? x*)
        (values rx* re*)
        (let-values ([(rx* re* e) (CExpr rx* re* (car e*))])
          (Binding* (cons (car x*) rx*) (cons e re*) (cdr x*) (cdr e*)))))
  (define (Lam le)
    (match le
      [`(lam (,x* ...) ,e) (let ([e (Expr e)]) `(lam ,x* ,e))]))
  (define (AExpr rx* re* e)
    (match e
      [`(let ([,x* ,e*] ...) ,body)
        (let-values ([(rx* re*) (Binding* rx* re* x* e*)])
          (AExpr rx* re* body))]
      [`(seq ,e* ... ,e)
       (let ([re* (foldl (lambda (e re*) (cons (Expr e) re*)) re* e*)]
             [rx* (foldl (lambda (e rx*) (cons (next-symbol) rx*)) rx* e*)])
         (AExpr rx* re* e))]
      [`(ref ,ref-type ,x) (values rx* re* e)]
      [`(boxref ,ref-type ,x) (values rx* re* e)]
      [`(application (primval ,prim) ,e* ...)
       (let-values ([(rx* re* e*) (AExpr* rx* re* e*)])
         (values rx* re* `(primcall ,prim ,@e*)))]
      [`(application ,e ,e* ...)
       (let-values ([(rx* re* e) (AExpr rx* re* e)])
         (let-values ([(rx* re* e*) (AExpr* rx* re* e*)])
           (let ([t (next-symbol)])
             (values (cons t rx*) (cons `(application ,e ,@e*) re*) `(ref normal ,t)))))]
      [`(set! ,x ,e)
        (let-values ([(rx* re* e) (AExpr rx* re* e)])
          (values (cons #f rx*) (cons `(set! ,x ,e) re*) `(constant ,(void))))]
      [`(set-box! ,x ,e)
        (let-values ([(rx* re* e) (AExpr rx* re* e)])
          (values (cons #f rx*) (cons `(set-box! ,x ,e) re*) `(constant ,(void))))]
      [`(boxenv ,x) (values (cons #f rx*) (cons `(boxenv ,x) re*) `(constant ,(void)))]
      [`(branch ,e0 ,e1 ,e2)
        (let-values ([(rx* re* e0) (AExpr rx* re* e0)])
          (let ([e1 (Expr e1)] [e2 (Expr e2)] [t (next-symbol)])
            (values (cons t rx*) (cons `(branch ,e0 ,e1 ,e2) re*) `(varref normal ,t))))]
      [`(let-rec ([,x* ,le*] ...) ,e)
        (let ([le* (map Lam le*)] [e (Expr e)] [t (next-symbol)])
          (values (cons t rx*) (cons `(let-rec ,(map list x* le*) ,e) re*) `(ref normal ,t)))]
      [`(case-lam ,le* ...) (let ([le* (map Lam le*)]) (values rx* re* `(case-lam ,@le*)))]
      [`(constant ,const) (values rx* re* `(constant ,const))]
      [`(quote ,x) (values rx* re* `(quote ,x))]
      [`(primval ,x) (values rx* re* `(primval ,x))]
      [`(lam ((,x* : ,t*) ...) ,e)
        (let ([e (Expr e)])
          (values rx* re* `(lam ,(map (lambda (x t) (list x ': t)) x* t*) ,e)))]))
  (define (CExpr rx* re* e)
    (match e
      [`(let ([,x* ,e*] ...) ,body)
        (let-values ([(rx* re*) (Binding* rx* re* x* e*)])
          (CExpr rx* re* body))]
      [`(seq ,e* ... ,e)
       (let ([re* (foldl (lambda (e re*) (cons (Expr e) re*)) re* e*)]
             [rx* (foldl (lambda (e rx*) (cons (next-symbol) rx*)) rx* e*)])
         (CExpr rx* re* e))]
      [`(application (primval ,prim) ,e* ...)
       (let-values ([(rx* re* e*) (AExpr* rx* re* e*)])
         (values rx* re* `(primcall ,prim ,@e*)))]
      [`(application ,e ,e* ...)
       (let-values ([(rx* re* e) (AExpr rx* re* e)])
         (let-values ([(rx* re* e*) (AExpr* rx* re* e*)])
           (values rx* re* `(application ,e ,@e*))))]
      [`(set! ,x ,e)
        (let-values ([(rx* re* e) (AExpr rx* re* e)])
          (values rx* re* `(set! ,x ,e)))]
      [`(set-box! ,x ,e)
        (let-values ([(rx* re* e) (AExpr rx* re* e)])
          (values rx* re* `(set-box! ,x ,e)))]
      [`(boxenv ,x) (values rx* re* `(boxenv ,x))]
      [`(branch ,e0 ,e1 ,e2)
        (let-values ([(rx* re* e0) (AExpr rx* re* e0)])
          (let ([e1 (Expr e1)] [e2 (Expr e2)])
            (values rx* re* `(branch ,e0 ,e1 ,e2))))]
      [`(let-rec ([,x* ,le*] ...) ,e)
        (let ([le* (map Lam le*)] [e (Expr e)])
          (values rx* re* `(let-rec ,(map list x* le*) ,e)))]
      [`(case-lam ,le* ...) (let ([le* (map Lam le*)]) (values rx* re* `(case-lam ,@le*)))]
      [_ (AExpr rx* re* e)]))
  (define (Expr e)
    (match e
      [`(seq ,e0 ,e1 ,e* ...)
        (let ([e0 (Expr e0)] [e1 (Expr e1)] [e* (map Expr e*)])
          (build-seq* e0 e1 e*))]
      [`(let ([,x* ,e*] ...) ,body)
        (let-values ([(rx* re*) (Binding* '() '() x* e*)])
          (let ([body (Expr body)])
            (build-let rx* re* body)))]
      [_ (let-values ([(rx* re* body) (CExpr '() '() e)])
           (build-let rx* re* body))]))
  (define (Prog p)
    (match p
      [`(prog ([,x* ,le*] ...) ,e)
       (let ([le* (map Lam le*)] [e (Expr e)])
         `(let-rec ,(map list x* le*) ,e))]))
  (Prog x))

;; output grammar:
;;  Lambda --> (lam ((<symbol> : <ts>) ...) <Expr>)
;;  AExpr  --> <Lambda>
;;          |  (case-lam <Expr> ...)
;;          |  (boxref <ref-type> <symbol>)
;;          |  (constant <const>)
;;          |  (primval <prim>)
;;          |  (primcall <prim> <AExpr> ...)
;;          |  (quote <symbol>)
;;  CExpr  --> (application <AExpr> <AExpr> ...)
;;          |  (branch <AExpr> <AExpr> <AExpr>)
;;          |  (set! <symbol> <AExpr>)
;;          |  (set-box! <symbol> <AExpr>)
;;          |  (boxenv <symbol>)
;;          |  (let-rec ([<symbol> <Lambda>] ...) <Expr>)
;;          |  <AExpr>
;;  Expr   --> <CExpr>
;;          |  (seq <Expr> <Expr>)
;;          |  (let (<symbol> <Expr>) <Expr>)
;;
(define (cesk x)
  (define (empty-env) '())
  (define (extend-env rho x addr) (cons (cons x addr) rho))
  (define (extend-env* rho x* addr*) (foldl (lambda (x addr rho) (extend-env rho x addr)) rho x* addr*))
  (define (apply-env rho x)
    (cond
      [(assq x rho) => cdr]
      [else (error 'apply-env "reference to unbound variable ~s" x)]))
  (define (empty-store) '())
  (define (extend-store s addr val) (cons (cons addr val) s))
  (define (extend-store* s addr* val*) (foldl (lambda (addr val rho) (extend-store s addr val)) s addr* val*))
  (define (apply-store s addr)
    (cond
      [(assq addr s) => cdr]
      [else (error 'apply-store "reference to unallocated variable ~s" addr)]))
  (define (allocate s x) (gensym x))
  (define (allocate* s x*) (map (lambda (x) (allocate s x)) x*))
  (define (PrepPrimArgs e) e)
  (define (apply-proc e arg* s k)
    (define (return-vals x* expr rho)
      (let ([addr* (allocate* s (map car x*))])
        (let ([rho (extend-env* rho (map car x*) addr*)])
          (let ([s (extend-store* s addr* arg*)])
            (values expr rho s k)))))
    (define (find-clause x** expr* arg* k)
      (let ([l (length arg*)])
        (let loop ([x** x**] [expr* expr*])
          (if (null? x**)
              (error 'apply-proc "incorrect number of arguments")
              (let ([x* (car x**)])
                (if (= (length x*) l)
                    (k x* (car expr*))
                    (loop (cdr x**) (cdr expr*))))))))
    (match e
      [`(clo (,x* ...) ,expr ,rho) (return-vals x* expr rho)]
      [`(case-clo ,x** ,e* ,rho)
        (find-clause x** e* arg*
          (lambda (x* expr) (return-vals x* expr rho)))]
      [_ (error 'apply-proc "attempt to apply non-procedure value ~s" e)]))
  (define (apply-kont k val s)
    (match k
      [`(letk ,x ,rho ,e ,k)
        (let ([addr (allocate s x)])
          (let ([rho (extend-env rho x addr)])
            (let ([s (extend-store s addr val)])
              (values e rho s k))))]
      [`(seqk ,rho ,expr ,k)
        (values expr rho s k)]
      [`(halt) (values val (empty-env) (empty-store) k)]))
  (define (AExpr e rho s)
    (match e
      [`(constant ,c) c]
      [`(lam (,x* ...) ,e) `(clo ,x* ,e ,rho)]
      [`(case-lam (lam (,x** ...) ,e*) ...) `(case-clo ,x** ,e* ,rho)]
      [`(ref ,ref-type ,x) (apply-store s (apply-env rho x))]
      [`(boxref ,ref-type ,x) (unbox (apply-store s (apply-env rho x)))]
      [`(primval ,x) (eval x)]
      [`(primcall ,prim ,e* ...)
        (let ([e* (map (lambda (e) (AExpr e rho s)) e*)])
          (let ([e* (map PrepPrimArgs e*)])
            (apply (eval prim) e*)))]
      [`(quote ,x) x]))
  (define (step e rho s k)
    (match e
      [`(let (,x0 ,e0) ,e1)
        (values e0 rho s `(letk ,x0 ,rho ,e1 ,k))]
      [`(seq ,e0 ,e1)
        (values e0 rho s `(seqk ,rho ,e1 ,k))]
      [`(application ,e ,e* ...)
        (let ([e (AExpr e rho s)] [e* (map (lambda (e) (AExpr e rho s)) e*)])
          (apply-proc e e* s k))]
      [`(branch ,e0 ,e1 ,e2)
        (let ([e0 (AExpr e0 rho s)])
          (values (if (eq? e0 #f) e2 e1) rho s k))]
      [`(set! ,x ,e)
        (let ([s (extend-store s (apply-env x) (AExpr e rho s))])
          (apply-kont k `(constant ,(void))) s)]
      [`(set-box! ,x ,e)
        (let ([b (apply-store s (apply-env rho x))])
          (set-box! b (AExpr e rho s))
          (apply-kont k `(constant ,(void)) s))]
      [`(boxenv ,x)
        (let ([addr (apply-env rho x)])
          (let ([val (apply-store s addr)])
            (let ([s (extend-store s addr (box val))])
              (apply-kont k `(constant ,(void)) s))))]
      [`(let-rec ([,x* ,le*] ...) ,e)
        (let ([addr* (allocate* s x*)])
          (let ([rho (extend-env* rho x* addr*)])
            (let ([le* (map (lambda (le) (AExpr le rho s)) le*)])
              (let ([s (extend-store* s addr* le*)])
                (values e rho s k)))))]
      [_ (apply-kont k (AExpr e rho s) s)]))
  (define (value-exp? exp)
    (if (pair? exp)
        (and (not (memq (car exp) '(let seq application brnch set! set-box! boxenv let-rec)))
             (memq (car exp) '(clo case-clo))
             #t)
        #t))
  (define (step-driver exp rho s k)
    (let-values ([(exp rho s k) (step exp rho s k)])
      (if (and (value-exp? exp) (match k [`(halt) #t] [_ #f]))
          exp
          (step-driver exp rho s k))))
  (step-driver x (empty-env) (empty-store) `(halt)))

(define racket-source->bytecode (compose impl->model source->bytecode))
(define racket-source-file->bytecode (compose impl->model source-file->bytecode))
(define racket-zo-file->bytecode (compose impl->model zo-file->bytecode))

(define-syntax passes
  (syntax-rules ()
    [(_ ?x f ...) (let* ([x ?x] [x (f x)] ...) x)]))

(define (racket-source->anormal-form x)
  (passes x
    source->bytecode
    impl->model
    model->prog
    reintroduce-variables
    check-grammar
    to-anormal-form))

(provide (all-defined-out))
