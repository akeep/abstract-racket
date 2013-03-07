#lang racket

(require compiler/zo-parse)

(define lookup-primitive
  (let ([prim->num (let ([ns (make-base-empty-namespace)])
                     (parameterize ([current-namespace ns])
                       (namespace-require ''#%kernel)
                       (namespace-require ''#%unsafe)
                       (namespace-require ''#%flfxnum)
                       (namespace-require ''#%futures)
                       (foldl (lambda (l ls)
                                (let ([c (with-handlers ([exn:fail? (lambda (x) #f)]) (compile l))])
                                  (if c
                                    (let ([v (zo-parse
                                               (let ([out (open-output-bytes)])
                                                 (write c out)
                                                 (close-output-port out)
                                                 (open-input-bytes (get-output-bytes out))))])
                                      (match v
                                        [(struct compilation-top (_ prefix (struct primval (n))))
                                         (cons (cons l n) ls)]
                                        [_ ls]))
                                    ls)))
                              '() (namespace-mapped-symbols))))])
    (let ([num->prim (map (lambda (p) (cons (cdr p) (car p))) prim->num)])
      (lambda (x)
        (cond
          [(and (number? x) (assq x num->prim)) => cdr]
          [(and (symbol? x) (assq x prim->num)) => cdr]
          [else #f])))))

(provide lookup-primitive)
