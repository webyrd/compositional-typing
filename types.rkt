#lang racket

(require "faster-miniKanren/mk.rkt")

; '((x . bool) (y . int))
; '()

(define lookupo
  (lambda (gamma x type)
    (fresh (y t rest)
      (== `((,y . ,t) . ,rest) gamma)
      (symbolo y)
      (conde
        [(== x y) (== t type)]
        [(=/= x y)
         (lookupo rest x type)]))))

(run* (q) (lookupo '((w . bool) (z . int)) 'z q))


(run 5 (q) (lookupo q 'z 'int))

(define !-o
  (lambda (gamma expr type)
     (conde
        [(== #f expr) (== 'bool type)]
        [(== #t expr) (== 'bool type)]
        [(numbero expr) (== 'int type)]
        [(symbolo expr) (lookupo gamma expr type)]
        [(fresh (e)
           (== `(zero? ,e) expr)
           (== 'bool type)
           (!-o gamma e 'int))]
        [(fresh (e1 e2)
           (== `(+ ,e1 ,e2) expr)
           (== 'int type)
           (!-o gamma e1 'int)
           (!-o gamma e2 'int))]
        [(fresh (e1 e2 e3)
           (== `(if ,e1 ,e2 ,e3) expr)
           (!-o gamma e1 'bool)
           (!-o gamma e2 type)
           (!-o gamma e3 type))]
        [(fresh (e1 e2 t)
           (== `(,e1 ,e2) expr)
           (!-o gamma e1 `(-> ,t ,type))
           (!-o gamma e2 t))]
        [(fresh (x e t t^)
           (== `(lambda (,x) ,e) expr)
           (symbolo x)
           (== `(-> ,t ,t^) type)
           (!-o `((,x . ,t) . ,gamma) e t^))])))

(run 5 (gamma expr type) (!-o gamma expr type))
(run 5 (gamma expr) (!-o gamma expr 'int))
(run 5 (gamma expr) (!-o gamma expr 'bool))
(run* (gamma type) (!-o gamma '5 type))
(run* (gamma type) (!-o gamma '(+ 2 3) type))

(run* (type)
  (!-o '() '(lambda (z) z) type))

(run* (type)
  (!-o '() '(lambda (z) z) '(-> int int)))

(run* (type)
  (!-o '() '(lambda (z) z) '(-> int bool)))

(run 5 (expr)
  (!-o '() expr '(-> int int)))

(run 50 (expr type) (!-o '() expr type))

(run* (type)
  (!-o '() '(lambda (z) (z z)) type))
