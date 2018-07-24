;#lang racket

;(require "faster-miniKanren/mk.rkt")

(load "faster-miniKanren/mk-vicare.scm")
(load "faster-miniKanren/mk.scm")


(define lookupo
  (lambda (gamma x type)
    (fresh (y t rest)
      (symbolo x)
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
           (== `(lambda (,x : ,t) ,e) expr)
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




(define unboundo
  (lambda (gamma x)
    (fresh ()
      (symbolo x)
      (conde
        [(== '() gamma)]
        [(fresh (y t rest)
           (== `((,y . ,t) . ,rest) gamma)
           (symbolo y)
           (=/= x y)
           (unboundo rest x))]))))

(define not-function-typeo
  (lambda (t)
    ;; IMPORTANT: will need to add extra list cases if we add other
    ;; type constructors like cons or pair
    (symbolo t)))

(define doesnt-typeo
  (lambda (gamma expr)
     (conde
       #|
       ;; Uncomment to allow unbound variables
       ;; to be a source of type errors.
       [(symbolo expr) (unboundo gamma expr)]
       |#
        [(fresh (e)
           (== `(zero? ,e) expr)
           (conde
             [(fresh (t)
                (=/= 'int t)
                (!-o gamma e t))]
             [(doesnt-typeo gamma e)]))]
        [(fresh (e1 e2)
           (== `(+ ,e1 ,e2) expr)
           (conde
             [(!-o gamma e1 'int)
              (conde
                [(fresh (t2)
                   (=/= 'int t2)
                   (!-o gamma e2 t2))]
                [(doesnt-typeo gamma e2)])]
             [(fresh (t1)
                (=/= 'int t1)
                (!-o gamma e1 t1)
                (conde
                  [(!-o gamma e2 'int)]
                  [(fresh (t2)
                     (=/= 'int t2)
                     (!-o gamma e2 t2))]
                  [(doesnt-typeo gamma e2)]))]
             [(doesnt-typeo gamma e1)
              (conde
                [(!-o gamma e2 'int)]
                [(fresh (t2)
                   (=/= 'int t2)
                   (!-o gamma e2 t2))]
                [(doesnt-typeo gamma e2)])]))]
        [(fresh (e1 e2 t t1 t2 t3)
           (== `(,e1 ,e2) expr)
           (conde
             [
              ;; case 1: e1 has a type, e2 doesn't
              (doesnt-typeo gamma e2)
              (!-o gamma e1 t)
              (conde
                [(not-function-typeo t)
                 ;; two type errors
                 ]
                [
                 ;;   1b: e1 has a function type                 
                 (== `(-> ,t1 ,t2) t)
                 ;; just the one type error
                 ])]
             [(doesnt-typeo gamma e1)
              ;; case 2: e1 doesn't have a type
              (conde
                [
                 ;;   2a: e2 has a type
                 (!-o gamma e2 t)
                 ;; just the one type error
                 ]
                [
                 ;;   2b: e2 doesn't have a type
                 (doesnt-typeo gamma e2)
                 ;; two type errors
                 ])
              ]
             [
              ;; case 3: e1 and e2 have types
              (conde
                [
                 ;;   3a: e1 doesn't have a function type
                 (!-o gamma e1 t1)
                 (!-o gamma e2 t2)
                 (not-function-typeo t1)
                 ]
                [
                 ;;   3b: e1 has a function type,
                 ;;       but type of e2 is not consistent
                 ;;       with type of e1
                 (=/= t1 t3)
                 (!-o gamma e1 `(-> ,t1 ,t2))
                 (!-o gamma e2 t3)                                  
                 ])

              ])
           

           
           )]
        [(fresh (x e t)
           (== `(lambda (,x : ,t) ,e) expr)
           (symbolo x)
           (doesnt-typeo `((,x . ,t) . ,gamma) e))]
        )))

(run 100 (expr) (doesnt-typeo '() expr))

(run 10 (e t) (doesnt-typeo '() `(lambda (y : ,t) ,e)))

(run 10 (e t) (doesnt-typeo '() `(lambda (y : int) ,e)))

(run 10 (expr)
  (fresh (e e2)
    (== `((lambda (y : int) ,e) ,e2) expr)
    (doesnt-typeo '() expr)))

(run* (t) (doesnt-typeo `((y . int)) `(zero? y)))

(run* (t) (doesnt-typeo `((y . ,t)) `(zero? y)))



;; alternative approach, based on inferring the wrong type for an expression

#|
(define not-lookupo
  (lambda (gamma x type)
    (fresh ()
      (symbolo x)
      (conde
        [(== '() gamma)]
        [(fresh (y t rest)
           (== `((,y . ,t) . ,rest) gamma)
           (symbolo y)
           (conde
             [(== x y) (=/= t type)]
             [(=/= x y)
              (not-lookupo rest x type)]))]))))

(run* (q) (not-lookupo '((w . bool) (z . int)) 'z q))

(run 5 (q) (not-lookupo q 'z 'int))

(define not-!-o
  (lambda (gamma expr type)
     (conde
        [(== #f expr) (=/= 'bool type)]
        [(== #t expr) (=/= 'bool type)]
        [(numbero expr) (=/= 'int type)]
        [(symbolo expr) (not-lookupo gamma expr type)]
        [(fresh (e)
           (== `(zero? ,e) expr)
           (conde
             [(fresh (t)
                (=/= 'bool type)
                (conde
                  [(!-o gamma e t)]
                  [(not-!-o gamma e t)]))]
             [(== 'bool type)
              (not-!-o gamma e 'int)]))]
        )))

(run 5 (gamma expr type) (not-!-o gamma expr type))

(run 10 (expr) (not-!-o '() expr 'int))
|#
