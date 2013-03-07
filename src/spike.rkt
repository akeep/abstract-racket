#lang racket

(require "priminfo.rkt")
(require compiler/zo-parse)
(require compiler/compiler)

(define ip->bytecode
  (lambda (ip)
    (zo-parse ip)))

; Originally pulled out the code from the compilation-top, but it is unclear
; that we can just discard the prefix, so I've gone back to just zo-parse.
;  (match (zo-parse ip)
;    [(struct compilation-top (_ _ code)) code]
;    [_ #f])
;

(define zo-file->bytecode
  (lambda (fn)
    (call-with-input-file fn ip->bytecode)))

(define source-file->bytecode
  (let ([compile-file (let ([compile-files (compile-zos #f)])
                        (lambda (fn dir)
                          (compile-files (list fn) dir)))])
    (lambda (fn)
      (let ([dir (make-temporary-file "rkt-compile-tmp-~a" 'directory)])
        (compile-file fn dir)
        (zo-file->bytecode
          (path-replace-suffix (path->complete-path fn dir) "_rkt.zo"))))))

(define source->bytecode
  (lambda (expr)
    (ip->bytecode
      (let ([out (open-output-bytes)])
        (write (compile expr) out)
        (close-output-port out)
        (open-input-bytes (get-output-bytes out))))))

(define-syntax define-who
  (lambda (x)
    (syntax-case x ()
      [(k name e)
       (with-syntax ([who (datum->syntax #'k 'who)])
         #'(define name
             (let ()
               (define who 'name)
               e)))]
      [(k (name . args) body0 body1 ...)
       (with-syntax ([who (datum->syntax #'k 'who)])
         #'(define name
             (let ()
               (define who 'name)
               (lambda args body0 body1 ...))))])))

;; thoughts on how some of this fits into a cesk machine.
;; prefix: maybe this is some funky form of environment---we lookup syntax,
;;         module, and top-level definitions from here.
(define-who bytecode->cesk
  (lambda (bc)
    (let ([ht (make-hasheq)])
      (let loop ([bc bc])
        (when (zo? bc)
          (when (hash-ref ht bc #f)
            (error who "encountered cycle in code, hit ~s twice" bc))
          (hash-set! ht bc #t))
        (match bc
          [(struct compilation-top (max-let-depth prefix code)) ; top level of compilation
           ;; currently discarding the prefix---probably will need to determine how to incorporate
           (loop code)]
          [(struct prefix (num-lifts toplevels stxs)) ; prefix loaded into stack before running associated code
           ;; not sure what to do (yet) with prefix
           (error who "currently not processing prefixes, but found (prefix ~s ~s ~s)"
                  num-lifts toplevels stxs)]
          [(struct global-bucket (name)) ; element of prefix to represent global variables
           ;; should only appear inside prefix, and not handling prefix yet
           (error who "currently not processing prefixes, but found (global-bucket ~s), which can only appear in prefix"
                  name)]
          [(struct module-variable (modidx sym pos phase)) ; element of prefix to rerpresent variable from imported module (I think)
           ;; should only appear inside prefix, and not handling prefix yet
           (error who "currently not processing prefixes, but found (module-variable ~s ~s ~s ~s), which can only appear in prefix"
                  modidx sym pos phase)]
          [(struct stx (encoded)) ; element of prefix (or req) used to indicate syntax put into the initial stack (from a module require?)
           ;; should only appear inside prefix, and not handling prefix yet
           (error who "currently not processing prefixes, but found (stx ~s), which can only appear in prefix"
                  encoded)]
          [(struct def-values (ids rhs)) ; define values handler
           (loop rhs)]
          [(struct def-syntaxes (ids rhs prefix max-let-depth dummy)) ; define syntax 
           (loop rhs)]
          [(struct seq-for-syntax (forms prefix max-let-depth dummy))
           (for-each loop forms)]
          [(struct req (reqs dummy)) #f]
          [(struct seq (forms))
           (for-each loop forms)]
          [(struct splice (forms))
           (for-each loop forms)]
          [(struct inline-variant (direct inline))
           (loop direct)
           (loop inline)]
          [(struct mod (name srcname self-modidx prefix provides requires body
                             syntax-bodies unexported max-let-depth dummy lang-info
                             internal-context pre-submodules post-submodules))
           (for-each loop body)]
          [(struct provided (name src src-name nom-src src-phase protected?))
           ;; currently not tracking provided from mod
           (error who "currently not processing provide lists, but found (provided ~s ~s ~s ~s ~s ~s)"
                  name src src-name nom-src src-phase protected?)]
          [(struct lam (name flags num-params param-types rest? closure-map
                             closure-types toplevel-map max-let-depth body))
           (loop body)]
          [(struct closure (code gen-id))
           (loop code)]
          [(struct case-lam (name clauses))
           (for-each loop clauses)]
          [(struct let-one (rhs body flonum? unused?))
           (loop rhs)
           (loop body)]
          [(struct let-void (count boxes? body))
           (loop body)]
          [(struct install-value (count pos boxes? rhs body))
           (loop rhs)
           (loop body)]
          [(struct let-rec (procs body))
           (for-each loop procs)
           (loop body)]
          [(struct boxenv (pos body))
           (loop body)]
          [(struct localref (unbox? pos clear? other-clears? flonum?)) #f]
          [(struct toplevel (depth pos const? ready?)) #f]
          [(struct topsyntax (depth pos midpt)) #f]
          [(struct application (rator rands))
           (loop rator)
           (for-each loop rands)]
          [(struct branch (test then else))
           (loop test)
           (loop then)
           (loop else)]
          [(struct with-cont-mark (key val body))
           (loop key)
           (loop val)
           (loop body)]
          [(struct beg0 (seq))
           (for-each loop seq)]
          [(struct varref (toplevel dummy)) #f]
          [(struct assign (id rhs undef-ok?))
           (loop rhs)]
          [(struct apply-values (proc args-expr))
           (loop proc)
           (loop args-expr)]
          [(struct primval (id)) #f]
          [(struct wrapped (datum wraps tamper-status)) #f]
          [(struct top-level-rename (flag)) #f]
          [(struct mark-barrier (value)) #f]
          [(struct free-id-info (path0 symbol0 path1 symbol1 phase0 phase1 phase2
                                       use-current-inspector?))
           #f]
          [(struct lexical-rename (has-free-id-info? bool2 alist)) #f]
          [(struct phase-shift (amt src dest cancel-id)) #f]
          [(struct module-rename (phase kind set-id unmarshals rename mark-renames plus-kern?))
           #f]
          [(struct all-from-module (path phase src-phase exceptions prefix context))
           #f]
          [(struct simple-module-binding (path))
           #f]
          [(struct phased-module-binding (path phase export-name nominal-path nominal-export-name))
           #f]
          [(struct exported-nominal-module-binding (path export-name nominal-path nominal-export-name))
           #f]
          [(struct nominal-module-binding (path nominal-path))
           #f]
          [(struct exported-module-binding (path export-name))
           #f]
          [(struct simple-nominal-path (value))
           #f]
          [(struct imported-nominal-path (value import-phase))
           #f]
          [(struct phased-nominal-path (value import-phase phase))
           #f]
          [_ (printf "bytecode->cesk encountered ~s\n" bc)])))))

(provide zo-file->bytecode source->bytecode source-file->bytecode bytecode->cesk)

