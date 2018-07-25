#lang racket

(require "faster-miniKanren/mk.rkt")

(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (unless (equal? expected produced)
           (printf "Failed: ~a~%Expected: ~a~%Computed: ~a~%" 'tested-expression expected produced)
           (error 'test "")))))))

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
  (lambda (gamma expr type proof-tree)
     (conde
        [(== #f expr) (== 'bool type)
         (== `(!-o #f ,gamma ,expr ,type) proof-tree)]
        [(== #t expr) (== 'bool type)
         (== `(!-o #t ,gamma ,expr ,type) proof-tree)]
        [(numbero expr) (== 'int type)
         (== `(!-o num ,gamma ,expr ,type) proof-tree)]
        [(symbolo expr) (lookupo gamma expr type)
         (== `(!-o var ,gamma ,expr ,type) proof-tree)]
        [(fresh (e proof-tree-e)
           (== `(zero? ,e) expr)
           (== 'bool type)
           (!-o gamma e 'int proof-tree-e)
           (== `(!-o zero? ,gamma ,expr ,type (,proof-tree-e)) proof-tree))]
        [(fresh (e1 e2 proof-tree-e1 proof-tree-e2)
           (== `(+ ,e1 ,e2) expr)
           (== 'int type)
           (!-o gamma e1 'int proof-tree-e1)
           (!-o gamma e2 'int proof-tree-e2)
           (== `(!-o + ,gamma ,expr ,type (,proof-tree-e1 ,proof-tree-e2)) proof-tree))]
        [(fresh (e1 e2 e3 proof-tree-e1 proof-tree-e2 proof-tree-e3)
           (== `(if ,e1 ,e2 ,e3) expr)
           (!-o gamma e1 'bool proof-tree-e1)
           (!-o gamma e2 type proof-tree-e2)
           (!-o gamma e3 type proof-tree-e3)
           (== `(!-o if ,gamma ,expr ,type (,proof-tree-e1 ,proof-tree-e2 ,proof-tree-e3)) proof-tree))]
        [(fresh (e1 e2 t proof-tree-e1 proof-tree-e2)
           (== `(,e1 ,e2) expr)
           (!-o gamma e1 `(-> ,t ,type) proof-tree-e1)
           (!-o gamma e2 t proof-tree-e2)
           (== `(!-o app ,gamma ,expr ,type (,proof-tree-e1 ,proof-tree-e2)) proof-tree))]
        [(fresh (x e t t^ proof-tree-e)
           (== `(lambda (,x : ,t) ,e) expr)
           (symbolo x)
           (== `(-> ,t ,t^) type)
           (!-o `((,x . ,t) . ,gamma) e t^ proof-tree-e)
           (== `(!-o abs ,gamma ,expr ,type (,proof-tree-e)) proof-tree))])))

(run 5 (gamma expr type proof-tree) (!-o gamma expr type proof-tree))
(run 5 (gamma expr proof-tree) (!-o gamma expr 'int proof-tree))
(run 5 (gamma expr proof-tree) (!-o gamma expr 'bool proof-tree))
(run* (gamma type proof-tree) (!-o gamma '5 type proof-tree))
(run* (gamma type proof-tree) (!-o gamma '(+ 2 3) type proof-tree))

(run* (type proof-tree)
  (!-o '() '(lambda (z : int) z) type proof-tree))

(run* (type proof-tree)
  (!-o '() '(lambda (z : int) z) '(-> int int) proof-tree))

(run* (type proof-tree)
  (!-o '() '(lambda (z : int) z) '(-> int bool) proof-tree))

(run 5 (expr proof-tree)
  (!-o '() expr '(-> int int) proof-tree))

(run 50 (expr type proof-tree) (!-o '() expr type proof-tree))

(run* (type proof-tree)
  (fresh (t)
    (!-o '() '(lambda (z : ,t) (z z)) type proof-tree)))




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
  (lambda (gamma expr proof-tree)
     (conde
       #|
       ;; Uncomment to allow unbound variables
       ;; to be a source of type errors.
       [(symbolo expr) (unboundo gamma expr)
       (== `(doesnt-typeo var ,gamma ,expr) proof-tree)]
       |#
        [(fresh (e proof-tree-e)
           (== `(zero? ,e) expr)
           (conde
             [(fresh (t)
                (=/= 'int t)
                (!-o gamma e t proof-tree-e)
                (== `(doesnt-typeo zero? (arg-not-an-int) ,gamma ,expr (,proof-tree-e)) proof-tree))]
             [(doesnt-typeo gamma e proof-tree-e)
              (== `(doesnt-typeo zero? (arg-has-not-type) ,gamma ,expr (,proof-tree-e)) proof-tree)]))]
        [(fresh (e1 e2 proof-tree-e1 proof-tree-e2)
           (== `(+ ,e1 ,e2) expr)
           (conde
             [(!-o gamma e1 'int proof-tree-e1)
              (conde
                [(fresh (t2)
                   (=/= 'int t2)
                   (!-o gamma e2 t2 proof-tree-e2)
                   (== `(doesnt-typeo + (arg2-not-an-int) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree))]
                [(doesnt-typeo gamma e2 proof-tree-e2)
                 (== `(doesnt-typeo + (arg2-has-no-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)])]
             [(fresh (t1)
                (=/= 'int t1)
                (!-o gamma e1 t1 proof-tree-e1)
                (conde
                  [(!-o gamma e2 'int proof-tree-e2)
                   (== `(doesnt-typeo (arg1-not-an-int) + ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)]
                  [(fresh (t2)
                     (=/= 'int t2)
                     (!-o gamma e2 t2 proof-tree-e2)
                     (== `(doesnt-typeo + (arg1-not-an-int arg2-not-an-int) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree))]
                  [(doesnt-typeo gamma e2 proof-tree-e2)
                   (== `(doesnt-typeo + (arg1-not-an-int arg2-has-no-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)]))]
             [(doesnt-typeo gamma e1 proof-tree-e1)
              (conde
                [(!-o gamma e2 'int proof-tree-e2)
                 (== `(doesnt-typeo + (arg1-has-no-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)]
                [(fresh (t2)
                   (=/= 'int t2)
                   (!-o gamma e2 t2 proof-tree-e2)
                   (== `(doesnt-typeo + (arg1-has-no-type arg2-not-an-int) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree))]
                [(doesnt-typeo gamma e2 proof-tree-e2)
                 (== `(doesnt-typeo + (arg1-has-no-type arg2-has-no-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)])]))]
        [(fresh (e1 e2 t t1 t2 t3 proof-tree-e1 proof-tree-e2)
           (== `(,e1 ,e2) expr)
           (conde
             [
              ;; case 1: e1 has a type, e2 doesn't
              (doesnt-typeo gamma e2 proof-tree-e2)
              (!-o gamma e1 t proof-tree-e1)
              (conde
                [(not-function-typeo t)
                 ;; 1a: e1 doesn't have a function type 
                 ;; two type errors
                 (== `(doesnt-typeo app (e1-not-function-type e2-no-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)]
                [
                 ;;   1b: e1 has a function type                 
                 (== `(-> ,t1 ,t2) t)
                 ;; just the one type error
                 (== `(doesnt-typeo app (e1-has-function-type e2-no-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)
                 ])]
             [(doesnt-typeo gamma e1 proof-tree-e1)
              ;; case 2: e1 doesn't have a type
              (conde
                [
                 ;;   2a: e2 has a type
                 (!-o gamma e2 t proof-tree-e2)
                 ;; just the one type error
                 (== `(doesnt-typeo app (e1-no-type e2-has-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)
                 ]
                [
                 ;;   2b: e2 doesn't have a type
                 (doesnt-typeo gamma e2 proof-tree-e2)
                 ;; two type errors
                 (== `(doesnt-typeo app (e1-no-type e2-no-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)
                 ])
              ]
             [
              ;; case 3: e1 and e2 have types
              (conde
                [
                 ;;   3a: e1 doesn't have a function type
                 (!-o gamma e1 t1 proof-tree-e1)
                 (!-o gamma e2 t2 proof-tree-e2)
                 (not-function-typeo t1)
                 (== `(doesnt-typeo app (e1-not-function-type e2-has-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)
                 ]
                [
                 ;;   3b: e1 has a function type,
                 ;;       but type of e2 is not consistent
                 ;;       with type of e1
                 (=/= t1 t3)
                 (!-o gamma e1 `(-> ,t1 ,t2) proof-tree-e1)
                 (!-o gamma e2 t3 proof-tree-e2)
                 (== `(doesnt-typeo app (e1-has-type e2-has-inconsistent-type) ,gamma ,expr (,proof-tree-e1 ,proof-tree-e2)) proof-tree)
                 ])
              ])
           )]
        [(fresh (x e t proof-tree-e)
           (== `(lambda (,x : ,t) ,e) expr)
           (symbolo x)
           (doesnt-typeo `((,x . ,t) . ,gamma) e proof-tree-e)
           (== `(doesnt-typeo abs (body-ill-typed) ,gamma ,expr (,proof-tree-e)) proof-tree))]
        )))

(run 100 (expr proof-tree) (doesnt-typeo '() expr proof-tree))

(run 10 (e t proof-tree) (doesnt-typeo '() `(lambda (y : ,t) ,e) proof-tree))

(run 10 (e t proof-tree) (doesnt-typeo '() `(lambda (y : int) ,e) proof-tree))

(run 10 (expr proof-tree)
  (fresh (e e2)
    (== `((lambda (y : int) ,e) ,e2) expr)
    (doesnt-typeo '() expr proof-tree)))

(run* (t proof-tree) (doesnt-typeo `((y . int)) `(zero? y) proof-tree))

(run* (t proof-tree) (doesnt-typeo `((y . ,t)) `(zero? y) proof-tree))

(run* (q proof-tree)
  (doesnt-typeo '() `(+ #f 5) proof-tree))

(test "argument ill-typed"
  (run* (proof-tree)
    (fresh (expr e e2)
      (== `((lambda (y : int)
              5)
            (zero? #f)) expr)
      (doesnt-typeo '() expr proof-tree)))
  '((doesnt-typeo app
                  (e1-has-function-type e2-no-type)
                  ()
                  ((lambda (y : int) 5) (zero? #f))
                  ((!-o abs
                        ()
                        (lambda (y : int) 5)
                        (-> int int)
                        ((!-o num ((y . int)) 5 int)))
                   (doesnt-typeo zero?
                                 (arg-not-an-int)
                                 ()
                                 (zero? #f)
                                 ((!-o #f
                                       ()
                                       #f
                                       bool)))))))

;; both sides ill-typed
(run* (proof-tree)
    (fresh (expr e e2)
      (== `((lambda (y : int)
              (+ y #t))
            (zero? #f)) expr)
      (doesnt-typeo '() expr proof-tree)))

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
