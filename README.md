Abstract Machine for Racket Bytecode
=====================================

This repository is a first pass at an abstract machine implementation for analyzing Racket bytecode.  The current implemnetation is a concrete CESK machine that implements a subset of the Racket bytecode.  (Basically, primitives, plus the core evaluation forms.)

Usage
------

The main source file for the CESK machine is the `extended-eval.rkt` file, which can be loaded into Racket REPL as:

```racket
(require "extended-eval.rkt")
```

The `cesk` procedure implements the CESK evaluator.  The evaluator expects a transformed version of the byte code that can be produced by passing the quoted expression you wish to evaluate to `racket-source->anormal-form`.  For instance, if we wanted to run the classic factorial of 5 program would could evaluate it as follows:

```racket
(cesk
  (racket-source->anormal-form
    '(letrec ([factorial
               (lambda (n)
                 (if (zero? n)
                     1
                     (* n (factorial (- n 1)))))])
       (f 5))))
```

