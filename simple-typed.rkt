#lang racket

;;; Relational type inferencer/evaluator for a subset of an ML-like language,
;;; using s-expression syntax.

;;; Trying to combine type inferencer and evaluator for the same
;;; language, to improve synthesis performance.

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


;;; Simply-typed with definition expansion

(define lookup-!-o
  (lambda (gamma x type)
    (fresh (y t rest z e gamma^)
      (symbolo x)
      (== `((,y ,t) . ,rest) gamma)
      (symbolo y)
      (conde
        [(== x y)
         (conde
           [(== t `(mono ,type))]
           [(== t `(poly ,gamma^ (lambda (,z) ,e)))
            (symbolo z)
            (!-o gamma^ `(lambda (,z) ,e) type)])]
        [(=/= x y)
         (lookup-!-o rest x type)]))))

(define !-o
  (lambda (gamma expr type)
    (conde
      [(== #f expr) (== 'bool type)]
      [(== #t expr) (== 'bool type)]
      [(numbero expr) (== 'int type)]
      [(== 'nil expr)
       (fresh (a)
         (== `(list ,a) type))]
      [(symbolo expr)
       (=/= expr 'nil)
       (lookup-!-o gamma expr type)]
      [(fresh (e a)
         (== `(null? ,e) expr)
         (== 'bool type)
         (!-o gamma e `(list ,a)))]      
      [(fresh (e a)
         (== `(car ,e) expr)
         (== a type)
         (!-o gamma e `(list ,a)))]
      [(fresh (e a)
         (== `(cdr ,e) expr)
         (== `(list ,a) type)
         (!-o gamma e `(list ,a)))]
      [(fresh (e)
         (== `(zero? ,e) expr)
         (== 'bool type)
         (!-o gamma e 'int))]
      [(fresh (e1 e2 a)
         (== `(cons ,e1 ,e2) expr)
         (== `(list ,a) type)
         (!-o gamma e2 `(list ,a))
         (!-o gamma e1 a))]
      [(fresh (e1 e2 t1 t2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,t1 ,t2) type)
         (!-o gamma e1 t1)
         (!-o gamma e2 t2))]
      [(fresh (e1 e2 e3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (!-o gamma e1 'bool)
         (!-o gamma e2 type)
         (!-o gamma e3 type))]
      [(fresh (f z e body t)
         (== `(let-poly ((,f (lambda (,z) ,e)))
                ,body)
             expr)
         (symbolo f)
         (symbolo z)

         ;; Make sure the right-hand-side of 'f' has a type, but then forget about the type.
         (fresh (forget-me)
           (!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
         
         ;; Add the right-hand-side of the binding (an expression) to the environment for use later.
         (!-o `((,f (poly ((,f (mono ,t)) . ,gamma)
                          (lambda (,z) ,e)))
                . ,gamma)
              body
              type))]
      [(fresh (x body t t^)
         (== `(lambda (,x) ,body) expr)
         (symbolo x)
         (== `(-> ,t ,t^) type)
         (!-o `((,x (mono ,t)) . ,gamma) body t^))]
      [(fresh (e1 e2 t)
         (== `(@ ,e1 ,e2) expr)
         (!-o gamma e1 `(-> ,t ,type))
         (!-o gamma e2 t))])))



(define lookup-evalo
  (lambda (env x val)
    (fresh (y v rest z e)
      (symbolo x)
      (== `((,y ,v) . ,rest) env)
      (symbolo y)
      (conde
        [(== x y)
         (conde
           [(== `(val ,val) v)]
           [(== `(rec (lambda (,z) ,e)) v)
            (symbolo z)
            (== `(closure (,z) ,e ,env) val)])]
        [(=/= x y)
         (lookup-evalo rest x val)]))))

(define evalo
  (lambda (env expr val)
    (conde
      [(== #f expr) (== #f val)]
      [(== #t expr) (== #t val)]
      [(numbero expr) (== expr val)]
      [(== 'nil expr) (== 'nil val)]
      [(symbolo expr)
       (=/= 'nil expr)
       (lookup-evalo env expr val)]
      [(fresh (e v)
         (== `(null? ,e) expr)
         (conde
           [(== 'nil v) (== #t val)]
           [(=/= 'nil v) (== #f val)])
         (evalo env e v))]      
      [(fresh (e b)
         (== `(car ,e) expr)
         (evalo env e `(cons ,val ,b)))]
      [(fresh (e b)
         (== `(cdr ,e) expr)
         (evalo env e `(cons ,b ,val)))]
      [(fresh (e v)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 v) (== #t val)]
           [(=/= 0 v) (== #f val)])
         (evalo env e v))]
      [(fresh (e1 e2 t v1 v2)
         (== `(cons ,e1 ,e2) expr)
         (== `(cons ,v1 ,v2) val)
         (evalo env e1 v1)
         (evalo env e2 v2))]
      [(fresh (e1 e2 v1 v2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,v1 ,v2) val)
         (evalo env e1 v1)
         (evalo env e2 v2))]
      [(fresh (e1 e2 e3 v1 v2 v3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (evalo env e1 v1)
         (conde
           [(== #t v1) (== v2 val) (evalo env e2 v2)]
           [(== #f v1) (== v3 val) (evalo env e3 v3)]))]
      [(fresh (f z e body t)
         (== `(let-poly ((,f (lambda (,z) ,e)))
                ,body)
             expr)
         (symbolo f)
         (symbolo z)
         (evalo `((,f (rec (lambda (,z) ,e))) . ,env) body val))]
      [(fresh (x body)
         (== `(lambda (,x) ,body) expr)
         (symbolo x)
         (== `(closure (,x) ,body ,env) val))]
      [(fresh (e1 e2 x body arg env^)
         (== `(@ ,e1 ,e2) expr)
         (symbolo x)
         (evalo env e1 `(closure (,x) ,body ,env^))
         (evalo env e2 arg)
         (evalo `((,x (val ,arg)) . ,env^) body val))])))








;; Assumption used in 'lookup-!-/evalo': !-/evalo extends 'gamma' and
;; 'env' at the same time, with the same variable names, in the same
;; order (and similarly for the initial 'gamma' and 'env', if
;; non-empty).  Furthermore, we assume (val ,v) and (mono ,t) entries
;; occur together, as do (rec (lambda (,z) ,e)) and
;; (poly ,gamma^ (lambda (,z) ,e)) entries.
(define lookup-!-/evalo
  (lambda (gamma env x type val)
    (fresh (y t v rest-gamma rest-env z e)
      (symbolo x)
      (== `((,y ,t) . ,rest-gamma) gamma)
      (== `((,y ,v) . ,rest-env) env)
      (symbolo y)
      (conde
        [(== x y)
         (conde
           [(== `(val ,val) v)
            (== `(mono ,type) t)]
           [(== `(rec (lambda (,z) ,e)) v)
            (symbolo z)
            (== `(closure (,z) ,e ,gamma ,env) val)
            (fresh (gamma^)
              (== `(poly ,gamma^ (lambda (,z) ,e)) t)
              ;; This is a call to '!-o', not a recursive call to 'lookup-!-/evalo'
              (!-o gamma^ `(lambda (,z) ,e) type))])]
        [(=/= x y)
         (lookup-!-/evalo rest-gamma rest-env x type val)]))))

(define !-/evalo
  (lambda (gamma env expr type val)
    (conde
      [(== #f expr) (== 'bool type) (== #f val)]
      [(== #t expr) (== 'bool type) (== #t val)]
      [(numbero expr) (== 'int type) (== expr val)]
      [(== 'nil expr)
       (== 'nil val)
       (fresh (a)
         (== `(list ,a) type))]
      [(symbolo expr)
       (=/= 'nil expr)
       (lookup-!-/evalo gamma env expr type val)]
      [(fresh (e a v)
         (== `(null? ,e) expr)
         (== 'bool type)
         (conde
           [(== 'nil v) (== #t val)]
           [(=/= 'nil v) (== #f val)])
         (!-/evalo gamma env e `(list ,a) v))]
      [(fresh (e a b)
         (== `(car ,e) expr)
         (== a type)
         (!-/evalo gamma env e `(list ,a) `(cons ,val ,b)))]
      [(fresh (e a b)
         (== `(cdr ,e) expr)
         (== `(list ,a) type)
         (!-/evalo gamma env e `(list ,a) `(cons ,b ,val)))]
      [(fresh (e v)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 v) (== #t val)]
           [(=/= 0 v) (== #f val)])
         (== 'bool type)
         (!-/evalo gamma env e 'int v))]
      [(fresh (e1 e2 a t v1 v2)
         (== `(cons ,e1 ,e2) expr)
         (== `(list ,a) type)
         (== `(cons ,v1 ,v2) val)
         (!-/evalo gamma env e2 `(list ,a) v2)
         (!-/evalo gamma env e1 a v1))]
      [(fresh (e1 e2 t1 t2 v1 v2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,t1 ,t2) type)
         (== `(pair ,v1 ,v2) val)
         (!-/evalo gamma env e1 t1 v1)
         (!-/evalo gamma env e2 t2 v2))]
      [(fresh (e1 e2 e3 v1 v2 v3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (!-/evalo gamma env e1 'bool v1)
         (conde
           [(== #t v1) (== v2 val) (!-/evalo gamma env e2 type v2)]
           [(== #f v1) (== v3 val) (!-/evalo gamma env e3 type v3)]))]
      [(fresh (f z e body t)
         (== `(let-poly ((,f (lambda (,z) ,e)))
                ,body)
             expr)
         (symbolo f)
         (symbolo z)

         ;; Make sure the right-hand-side of 'f' has a type, but then forget about the type.
         ;;
         ;; This is in case 'f' is not used in 'body'--we still must
         ;; make sure the right-hand-side of 'f' has a type.
         (fresh (forget-me)
           ;; This is a call to '!-o', not a recursive call to '!-/evalo'
           (!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
         
         (!-/evalo
          ;; Add the right-hand-side of the binding (an expression) to the environment for use later.
          `((,f (poly ((,f (mono ,t)) . ,gamma)
                      (lambda (,z) ,e)))
            . ,gamma)
          `((,f (rec (lambda (,z) ,e))) . ,env)
          body
          type
          val)

         )]
      [(fresh (x body t t^)
         (== `(lambda (,x) ,body) expr)
         (symbolo x)
         (== `(-> ,t ,t^) type)
         (== `(closure (,x) ,body ,gamma ,env) val)
         ;; This is a call to '!-o', not a recursive call to '!-/evalo'
         (!-o `((,x (mono ,t)) . ,gamma) body t^))]
      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(@ ,e1 ,e2) expr)
         (symbolo x)
         (!-/evalo gamma env e1 `(-> ,t ,type) `(closure (,x) ,body ,gamma^ ,env^))
         (!-/evalo gamma env e2 t arg)
         (!-/evalo `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val))])))


(test "!-/evalo-42-simple-run*"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (@ (@ append nil) nil))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list _.0)
     nil
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (@ (@ append nil) nil)))))


(test "!o-if-1"
  (run* (q)
    (fresh (expr)
      (== `(if (null? (cons 1 nil))
               3
               4)
          expr)
      (!-o '()
           expr                
           q)))
  '(int))

(test "!o-if-2"
  (run* (q)
    (fresh (expr)
      (== `(if (null? nil)
               3
               4)
          expr)
      (!-o '()       
           expr                
           q)))
  '(int))

(test "!-o-and-evalo-cons-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(cons 1 nil)
          expr)
      (!-o '() expr type)
      (evalo '() expr val)))
  '(((list int) (cons 1 nil))))

(test "1"
  (run* (q) (lookup-!-o `((w (mono bool)) (z (mono int))) 'z q))
  '(int))

(test "4"
  (run* (q) (lookup-!-o `((x (mono a))) 'x q))
  '(a))

(test "let-poly-type-1"
  (run* (q) (!-o '()
                 '(let-poly ((f (lambda (w)
                                  (@ w w))))
                    5)
                 q))
  '())

(test "let-poly-type-2"
  (run* (q) (!-o '()
                 '(let-poly ((f (lambda (w)
                                  (@ w 3))))
                    5)
                 q))
  '(int))

(test "5"
  (run* (q) (!-o `() 3 q))
  '(int))

(test "6"
  (run* (q) (!-o `() #f q))
  '(bool))

(test "7"
  (run* (q) (!-o `((x (mono bool))) `x q))
  '(bool))

(test "8"
  (run* (q) (!-o `() `(cons 2 43) q))
  '())

(test "9"
  (run* (q) (!-o `() `(@ (lambda (x) x) 3) q))
  '(int))

(test "10"
  (run* (q) (!-o `()
                 `(let-poly ((f (lambda (y) #f)))
                    (cons (@ f 3) (@ f #f)))
                 q))
  '())

(test "11"
  (run* (q) (!-o `()
                 `(let-poly ((f (lambda (y) y)))
                    (pair (@ f 3) (@ f #f)))
                 q))
  '((pair int bool)))

(test "12"
  (run* (q) (!-o `()
                 `(@ (lambda (f)
                       (pair (@ f 3) (@ f #f)))
                     (lambda (y) y))
                 q))
  '())

(test "13"
  (run* (q) (!-o `()
                 `(@ (lambda (f)
                       (pair (@ f 3) (@ f 4)))
                     (lambda (y) y))
                 q))
  '((pair int int)))

(test "14"
  (run* (q) (!-o `() 'nil q))
  '((list _.0)))

(test "16"
  (run* (q) (!-o `() `(car nil) q))
  '(_.0))

(test "17"
  (run* (q) (!-o `()
                 `(let-poly ((append (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1) l2))))))
                    append)
                 q))
  '((-> (list _.0) (-> (list _.0) (list _.0)))))

(test "18"
  (run* (q) (!-o `()
                 `(let-poly ((append (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (cons (car l1) nil)
                                                   (cons (cdr l1) l2)))))))
                    append)
                 q))
  '((-> (list _.0) (-> (list (list _.0)) (list (list _.0))))))

(test "19"
  (run* (q) (!-o `() `(pair (cons 3 nil) (cons #f nil)) q))
  '((pair (list int) (list bool))))

(test "20"
  (run* (q) (!-o `()
                 `(let-poly ((append (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2)))))))
                    append)
                 q))
  '((-> (list _.0) (-> (list _.0) (list _.0)))))

(test "21"
  (run* (q) (!-o `()
                 `(let-poly ((append (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2)))))))
                    (let-poly ((rev (lambda (l1)
                                      (if (null? l1)
                                          l1
                                          (@ (@ append (@ rev (cdr l1))) (cons (car l1) nil))))))
                      rev))
                 q))
  '((-> (list _.0) (list _.0))))

(test "22"
  (run* (q) (!-o `() `(lambda (f) (@ f f)) q))
  '())

(test "23"
  (run* (q) (!-o `() `(lambda (y) (cons #f y)) q))
  '((-> (list bool) (list bool))))

(test "24"
  (run* (q) (!-o `()
                 `(let-poly ((x (lambda (y) (cons #f y)))) x)
                 q))
  '((-> (list bool) (list bool))))

(test "25"
  (run 1 (q) (!-o `((x (mono (-> bool bool))) (z (mono bool)))
                  `(@ x ,q)
                  `bool))
  '(#f))

(test "26"
  (run 1 (q) (!-o `() `(lambda (x) ,q) `(-> bool bool)))
  '(#f))

(test "27"
  (run* (q) (!-o `() `(lambda (x) x) q))
  '((-> _.0 _.0)))

(test "28"
  (run* (q) (evalo `() #f q))
  '(#f))

(test "29"
  (run* (q) (evalo `() `(cons 3 #f) q))
  '((cons 3 #f)))

(test "evalo-if-1"
  (run* (q)
    (fresh (expr)
      (== `(if (null? (cons 1 nil))
               3
               4)
          expr)
      (evalo '()       
             expr                
             q)))
  '(4))

(test "evalo-if-2"
  (run* (q)
    (fresh (expr)
      (== `(if (null? nil)
               3
               4)
          expr)
      (evalo '()       
             expr                
             q)))
  '(3))

(test "30"
  (run* (q) (evalo `()
                   `(lambda (y) (cons #f y))
                   q))
  '((closure (y) (cons #f y) ())))

(test "31"
  (run* (q) (evalo `()
                   `(@ (lambda (x) x) 3)
                   q))
  '(3))

(test "32"
  (run* (q) (evalo `()
                   `(let-poly ((x (lambda (y) #f)))
                      (cons (@ x 3) (@ x #f)))
                   q))
  '((cons #f #f)))

(test "33"
  (run* (q) (evalo `()
                   `(let-poly ((f (lambda (y) y)))
                      (pair (@ f 3) (@ f #f)))
                   q))
  '((pair 3 #f)))

(test "34"
  (run* (q) (evalo `()
                   `(let-poly ((f (lambda (y) y)))
                      (pair (@ f 3) (@ f #f)))
                   q))
  '((pair 3 #f)))

(test "35"
  (run* (q) (evalo `()
                   `(@ (lambda (f) (pair (@ f 3) (@ f #f))) (lambda (y) y))
                   q))
  '((pair 3 #f)))

(test "36"
  (run* (q) (evalo `()
                   `(@ (lambda (f) (pair (@ f 3) (@ f 4))) (lambda (y) y))
                   q))
  '((pair 3 4)))

(test "37"
  (run* (q) (evalo `() `nil q))
  '(nil))

(test "38"
  (run* (q) (evalo `() `(cons 5 nil) q))
  '((cons 5 nil)))

(test "39"
  (run* (q) (evalo `() `(null? nil) q))
  '(#t))

(test "40"
  (run* (q) (evalo `()
                   `(let-poly ((append (lambda (l1)
                                         (lambda (l2)
                                           (if (null? l1)
                                               l2
                                               (cons (car l1)
                                                     (@ (@ append (cdr l1)) l2)))))))
                      (@ (@ append nil) nil))
                   q))
  '(nil))

(test "41"
  (run* (q) (evalo `()
                   `(let-poly ((append (lambda (l1)
                                         (lambda (l2)
                                           (if (null? l1)
                                               l2
                                               (cons (car l1)
                                                     (@ (@ append (cdr l1)) l2)))))))
                      (@ (@ append (cons 1 nil)) nil))
                   q))
  '((cons 1 nil)))


(test "42-type"
  (run* (q)
    (fresh (expr type)
      (== (list type expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (@ (@ append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil))))
          expr)
      (!-o '() expr type)))
  '(((list int)
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (@ (@ append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil)))))))

(test "42-value"
  (run* (q)
    (fresh (expr val)
      (== (list val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (@ (@ append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil))))
          expr)
      (evalo '() expr val)))
  '(((cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (@ (@ append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil)))))))

(test "42-type-and-value"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (@ (@ append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil))))
          expr)
      (!-o '() expr type)
      (evalo '() expr val)))
  '(((list int)
     (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (@ (@ append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil)))))))

(test "42-type-and-value-verify"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (@ (@ append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil))))
          expr)
      (== `(list int) type)
      (== `(cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil))))) val)
      (!-o '() expr type)
      (evalo '() expr val)))
  '(((list int)
     (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (@ (@ append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil)))))))



(test "43-type"
  (run* (q)
    (fresh (expr type)
      (== (list type expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))
          expr)
      (!-o '() expr type)))
  '(((list (list int))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (cons (@ (@ append nil) nil)
             (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                   (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                         nil)))))))

(test "43-type-with-append"
  (run* (q)
    (fresh (expr type)
      (== (list type expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (pair append
                   (cons (@ (@ append nil) nil)
                         (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                               (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                     nil)))))
          expr)
      (!-o '() expr type)))
  '(((pair (-> (list int) (-> (list int) (list int)))
           (list (list int)))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (pair append
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))))))

(test "43-value"
  (run* (q)
    (fresh (expr val)
      (== (list val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))
          expr)
      (evalo '() expr val)))
  '(((cons nil
           (cons (cons 1 (cons 2 nil))
                 (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                       nil)))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (cons (@ (@ append nil) nil)
             (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                   (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                         nil)))))))

(test "43-value-with-append"
  (run* (q)
    (fresh (expr val)
      (== (list val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (pair append
                   (cons (@ (@ append nil) nil)
                         (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                               (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                     nil)))))
          expr)
      (evalo '() expr val)))
  '(((pair (closure (l1)
                    (lambda (l2)
                      (if (null? l1)
                          l2
                          (cons (car l1)
                                (@ (@ append (cdr l1)) l2))))
                    ((append (rec (lambda (l1)
                                    (lambda (l2)
                                      (if (null? l1)
                                          l2
                                          (cons (car l1)
                                                (@ (@ append (cdr l1)) l2))))))))) 
           (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))       
       (pair append
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))))))

(test "43-type-and-value"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))
          expr)
      (!-o '() expr type)
      (evalo '() expr val)))
  '(((list (list int))
     (cons nil
           (cons (cons 1 (cons 2 nil))
                 (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                       nil)))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (cons (@ (@ append nil) nil)
             (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                   (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                         nil)))))))

(test "43-type-and-value-with-append"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (pair append
                   (cons (@ (@ append nil) nil)
                         (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                               (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                     nil)))))
          expr)
      (!-o '() expr type)
      (evalo '() expr val)))
  '(((pair (-> (list int) (-> (list int) (list int)))
           (list (list int)))
     (pair (closure (l1)
                    (lambda (l2)
                      (if (null? l1)
                          l2
                          (cons (car l1)
                                (@ (@ append (cdr l1)) l2))))
                    ((append (rec (lambda (l1)
                                    (lambda (l2)
                                      (if (null? l1)
                                          l2
                                          (cons (car l1)
                                                (@ (@ append (cdr l1)) l2))))))))) 
           (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (pair append
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))))))

(test "43-type-and-value-verify"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))
          expr)
      (== `(list (list int)) type)
      (== `(cons nil
                 (cons (cons 1 (cons 2 nil))
                       (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                             nil)))
          val)
      (!-o '() expr type)
      (evalo '() expr val)))
  '(((list (list int))
     (cons nil
           (cons (cons 1 (cons 2 nil))
                 (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                       nil)))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (cons (@ (@ append nil) nil)
             (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                   (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                         nil)))))))

(test "43-type-and-value-verify-with-append"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (pair append
                   (cons (@ (@ append nil) nil)
                         (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                               (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                     nil)))))
          expr)
      (== `(pair (-> (list int) (-> (list int) (list int)))
                 (list (list int)))
          type)
      (== `(pair (closure (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2))))
                          ((append (rec (lambda (l1)
                                          (lambda (l2)
                                            (if (null? l1)
                                                l2
                                                (cons (car l1)
                                                      (@ (@ append (cdr l1)) l2))))))))) 
                 (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
          val)
      (!-o '() expr type)
      (evalo '() expr val)))
  '(((pair (-> (list int) (-> (list int) (list int)))
           (list (list int)))
     (pair (closure (l1)
                    (lambda (l2)
                      (if (null? l1)
                          l2
                          (cons (car l1)
                                (@ (@ append (cdr l1)) l2))))
                    ((append (rec (lambda (l1)
                                    (lambda (l2)
                                      (if (null? l1)
                                          l2
                                          (cons (car l1)
                                                (@ (@ append (cdr l1)) l2))))))))) 
           (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (pair append
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))))))




(time
  (test "append-type-synthesis-a"
    (run 1 (q)
      (fresh (expr type f-body e)
        (== (list type expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons ,e
                           (@ (@ append (cdr l1)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(list (list int)) type)
        (!-o '() expr type)))
    '((((list (list int))
        (let-poly ((append (lambda (l1)
                             (lambda (l2)
                               (if (null? l1)
                                   l2
                                   (cons _.0
                                         (@ (@ append (cdr l1)) l2)))))))
          (cons (@ (@ append nil) nil)
                (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                      (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                            nil)))))
       (=/= ((_.0 1)) ((_.0 2)) ((_.0 3)) ((_.0 4)) ((_.0 5)) ((_.0 6))) (num _.0)))))

(time
  (test "append-type-synthesis-with-append-a"
    (run 1 (q)
      (fresh (expr type f-body e)
        (== (list type expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons ,e
                           (@ (@ append (cdr l1)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (!-o '() expr type)))
    '((((pair (-> (list int) (-> (list int) (list int)))
              (list (list int)))
        (let-poly ((append (lambda (l1)
                             (lambda (l2)
                               (if (null? l1)
                                   l2
                                   (cons _.0
                                         (@ (@ append (cdr l1)) l2)))))))
          (pair append
                (cons (@ (@ append nil) nil)
                      (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                            (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                  nil))))))
       (=/= ((_.0 1)) ((_.0 2)) ((_.0 3)) ((_.0 4)) ((_.0 5)) ((_.0 6))) (num _.0)))))

(time
  (test "append-value-synthesis-a"
    (run 1 (q)
      (fresh (expr val f-body e)
        (== (list val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons ,e
                           (@ (@ append (cdr l1)) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil)))
            val)
        (evalo '() expr val)))
    '(((cons nil
             (cons (cons 1 (cons 2 nil))
                   (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                         nil)))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (cons (@ (@ append nil) nil)
               (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                     (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(time
  (test "append-value-synthesis-with-append-a"
    (run 1 (q)
      (fresh (expr val f-body e clos)
        (== (list val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons ,e
                           (@ (@ append (cdr l1)) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
          val)
        (evalo '() expr val)))
    '(((pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-type-and-value-synthesis-a"
    (run 1 (q)
      (fresh (expr type val f-body e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons ,e
                           (@ (@ append (cdr l1)) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(list (list int)) type)
        (== `(cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil)))
            val)        
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((list (list int))
       (cons nil
             (cons (cons 1 (cons 2 nil))
                   (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                         nil)))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (cons (@ (@ append nil) nil)
               (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                     (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(time
  (test "append-type-and-value-synthesis-with-append-a"
    (run 1 (q)
      (fresh (expr type val f-body e clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons ,e
                           (@ (@ append (cdr l1)) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))




(time
  (test "append-type-synthesis-b"
    (run 1 (q)
      (fresh (expr type f-body e)
        (== (list type expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append (cdr ,e)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(list (list int)) type)
        (!-o '() expr type)))
    '(((list (list int))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr nil)) l2)))))))
         (cons (@ (@ append nil) nil)
               (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                     (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(time
  (test "append-value-synthesis-b"
    (run 1 (q)
      (fresh (expr val f-body e)
        (== (list val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append (cdr ,e)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil)))
            val)
        (evalo '() expr val)))
    '(((cons nil
             (cons (cons 1 (cons 2 nil))
                   (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                         nil)))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (cons (@ (@ append nil) nil)
               (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                     (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(time
  (test "append-type-and-value-synthesis-b"
    (run 1 (q)
      (fresh (expr type val f-body e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append (cdr ,e)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(list (list int)) type)
        (== `(cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil)))
            val)        
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((list (list int))
       (cons nil
             (cons (cons 1 (cons 2 nil))
                   (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                         nil)))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (cons (@ (@ append nil) nil)
               (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                     (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(test "null?-1"
  (run* (q)
    (fresh (expr)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append #f) l2)))))))
             (pair append
                   (cons (@ (@ append nil) nil)
                         (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                               (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                     nil)))))
          expr)
      (!-o '() expr q)))
  '())

(test "null?-2"
  (run* (q)
    (fresh (expr)
      (== `(null? #f)
          expr)
      (!-o '() expr q)))
  '())

(test "null?-3"
  (run* (q)
    (fresh (expr)
      (== `((lambda (l1)
              (null? l1))
            #f)
          expr)
      (!-o '() expr q)))
  '())

(test "null?-4"
  (run* (q)
    (fresh (expr)
      (== `(let-poly ((f (lambda (l1)
                           (null? l1)))) 
             (@ f #f))
          expr)
      (!-o '() expr q)))
  '())

(test "null?-5"
  (run* (q)
    (fresh (expr)
      (== `(let-poly ((f (lambda (l1)
                           (if (null? l1)
                               3
                               4))))
             (@ f #f))
          expr)
      (!-o '() expr q)))
  '())

(test "null?-6"
  (run* (q)
    (fresh (expr)
      (== `(let-poly ((f (lambda (l1)
                           (lambda (l2)
                             (if (null? l1)
                                 3
                                 4)))))
             (@ f #f))
          expr)
      (!-o '() expr q)))
  '())

(test "null?-7"
  (run* (q)
    (fresh (expr)
      (== `(let-poly ((f (lambda (l1)
                           (lambda (l2)
                             (if (null? l1)
                                 3
                                 4)))))
             (@ f (cons 1 nil)))
          expr)
      (!-o '() expr q)))
  '((-> _.0 int)))

(time
  (test "append-type-synthesis-c"
    (run 1 (q)
      (fresh (expr type f-body e)
        (== (list type expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(list (list int)) type)
        (!-o '() expr type)))
    '(((list (list int))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1) (@ (@ append nil) l2)))))))
         (cons (@ (@ append nil) nil)
               (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                     (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(time
  (test "append-type-synthesis-with-append-c"
    (run 1 (q)
      (fresh (expr type f-body e)
        (== (list type expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (!-o '() expr type)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append nil) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-value-synthesis-c"
    (run 1 (q)
      (fresh (expr val f-body e)
        (== (list val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append ,e) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil)))
            val)
        (evalo '() expr val)))
    '(((cons nil
             (cons (cons 1 (cons 2 nil))
                   (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                         nil)))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (cons (@ (@ append nil) nil)
               (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                     (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(time
  (test "append-type-and-value-synthesis-c"
    (run 1 (q)
      (fresh (expr type val f-body e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(list (list int)) type)
        (== `(cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil)))
            val)        
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((list (list int))
       (cons nil
             (cons (cons 1 (cons 2 nil))
                   (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                         nil)))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (cons (@ (@ append nil) nil)
               (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                     (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))


(time
  (test "append-type-and-value-synthesis-with-append-c"
    (run 1 (q)
      (fresh (expr type val f-body e clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-type-and-value-synthesis-with-append-d"
    (run 1 (q)
      (fresh (expr type val f-body e clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ ,e l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-type-and-value-synthesis-with-append-e-with-hint"
    (run 1 (q)
      (fresh (expr type val f-body e1 e2 clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)

        ;; hint!
        (symbolo e2)
        
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ ,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))




(test "!-/evalo-number-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `5
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '((int 5)))

(test "!-/evalo-nil-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `nil
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '(((list _.0) nil)))

(test "!-/evalo-pair-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(pair 1 #t)
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '(((pair int bool) (pair 1 #t))))

(test "!-/evalo-pair-2"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(pair 1 nil)
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '(((pair int (list _.0)) (pair 1 nil))))

(test "!-/evalo-cons-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(cons 1 nil)
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '(((list int) (cons 1 nil))))

(test "!-/evalo-car-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(car (cons 1 nil))
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '((int 1)))

(test "!-/evalo-cdr-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(cdr (cons 1 nil))
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '(((list int) nil)))

(test "!-/evalo-null?-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(null? (cons 1 nil))
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '((bool #f)))

(test "!-/evalo-null?-2"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(null? nil)
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '((bool #t)))

(test "!-/evalo-if-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(if (null? (cons 1 nil))
               3
               4)
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '((int 4)))

(test "!-/evalo-if-2"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(if (null? nil)
               3
               4)
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '((int 3)))

(test "!-/evalo-5"
  (run* (q)
    (fresh (type val)
      (== (list type val) q)
      (!-/evalo '() '() 3 type val)))
  '((int 3)))

(test "!-/evalo-6"
  (run* (q)
    (fresh (type val)
      (== (list type val) q)
      (!-/evalo '() '() #f type val)))
  '((bool #f)))

(test "!-/evalo-let-poly-type-1"
  (run* (q)
    (fresh (type val)
      (== (list type val) q)
      (!-/evalo '()
                '()
                '(let-poly ((f (lambda (w)
                                 (@ w w))))
                   5)
                type
                val)))
  '())

(test "!-/evalo-let-poly-type-2"
  (run* (q)
    (fresh (type val)
      (== (list type val) q)
      (!-/evalo '()
                '()
                '(let-poly ((f (lambda (w)
                                 (@ w 3))))
                   5)
                type
                val)))
  '((int 5)))

(test "!-/evalo-identity-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(lambda (w) w)
          expr)      
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '(((-> _.0 _.0) (closure (w) w () ()))))

(test "!-/evalo-identity-2"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(@ (lambda (w) w)
              3)
          expr)      
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '((int 3)))

(test "!-/evalo-identity-3"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(@ (lambda (w) w)
              (cons 1 nil))
          expr)
      (!-/evalo '()
                '()
                expr
                type
                val)))
  '(((list int) (cons 1 nil))))

(test "!-/evalo-null?-7a"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(@ (lambda (f)
                (@ f (cons 1 nil)))
              (lambda (l1)
                (lambda (l2)
                  (if (null? l1)
                      3
                      4))))
          expr)      
      (!-/evalo '()
                '()
                expr
                type
                val)))  
  '(((-> _.0 int) (closure (l2)
                           (if (null? l1) 3 4)
                           ((l1 (mono (list int))))
                           ((l1 (val (cons 1 nil))))))))

(test "!-/evalo-null?-7b"
  (run* (q)
    (fresh (expr type val)
      (== (list type val) q)
      (== `(let-poly ((f (lambda (l1)
                           (lambda (l2)
                             (if (null? l1)
                                 3
                                 4)))))
             (@ f (cons 1 nil)))
          expr)      
      (!-/evalo '()
                '()
                expr
                type
                val)))  
  '(((-> _.0 int)
     (closure (l2)
              (if (null? l1) 3 4)
              ((l1 (mono (list int)))
               (f (poly ((f (mono _.1)))
                        (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                3
                                4))))))
              ((l1 (val (cons 1 nil)))
               (f (rec (lambda (l1)
                         (lambda (l2)
                           (if (null? l1)
                               3
                               4))))))))))

(test "!-/evalo-rebuild-1"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((rebuild (lambda (l)
                                 (if (null? l)
                                     nil
                                     (cons (car l)
                                           (@ rebuild (cdr l)))))))
             rebuild)
          expr)
      (!-/evalo '() '() expr type val)))
  '(((-> (list _.0) (list _.0))
     (closure (l)
              (if (null? l)
                  nil
                  (cons (car l)
                        (@ rebuild (cdr l))))
              ((rebuild (poly ((rebuild (mono (-> (list _.0) (list _.0)))))
                              (lambda (l)
                                (if (null? l)
                                    nil
                                    (cons (car l)
                                          (@ rebuild (cdr l))))))))
              ((rebuild (rec (lambda (l)
                               (if (null? l)
                                   nil
                                   (cons (car l)
                                         (@ rebuild (cdr l)))))))))
     (let-poly ((rebuild (lambda (l)
                           (if (null? l)
                               nil
                               (cons (car l)
                                     (@ rebuild (cdr l)))))))
       rebuild))))

(test "!-/evalo-rebuild-2"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((rebuild (lambda (l)
                                 (if (null? l)
                                     nil
                                     (cons (car l)
                                           (@ rebuild (cdr l)))))))
             (@ rebuild nil))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list _.0)
     nil
     (let-poly ((rebuild (lambda (l)
                           (if (null? l)
                               nil
                               (cons (car l)
                                     (@ rebuild (cdr l)))))))
       (@ rebuild nil)))))

(test "!-/evalo-rebuild-3"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((rebuild (lambda (l)
                                 (if (null? l)
                                     nil
                                     (cons (car l)
                                           (@ rebuild (cdr l)))))))
             (@ rebuild (cons 1 nil)))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list int)
     (cons 1 nil)
     (let-poly ((rebuild (lambda (l)
                           (if (null? l)
                               nil
                               (cons (car l)
                                     (@ rebuild (cdr l)))))))
       (@ rebuild (cons 1 nil))))))

(test "!-/evalo-40-simple"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             append)
          expr)
      (!-/evalo '() '() expr type val)))
  '(((-> (list _.0) (-> (list _.0) (list _.0)))
     (closure (l1)
              (lambda (l2)
                (if (null? l1)
                    l2
                    (cons (car l1)
                          (@ (@ append (cdr l1)) l2))))
              ((append (poly ((append (mono (-> (list _.0) (-> (list _.0) (list _.0))))))
                             (lambda (l1)
                               (lambda (l2)
                                 (if (null? l1)
                                     l2
                                     (cons (car l1)
                                           (@ (@ append (cdr l1)) l2))))))))
              ((append (rec (lambda (l1)
                              (lambda (l2)
                                (if (null? l1)
                                    l2
                                    (cons (car l1)
                                          (@ (@ append (cdr l1)) l2)))))))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       append))))

(test "!-/evalo-41-simple"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (@ append nil))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((-> (list _.0) (list _.0))
     (closure (l2)
              (if (null? l1)
                  l2
                  (cons (car l1)
                        (@ (@ append (cdr l1)) l2)))
              ((l1 (mono (list _.0)))
               (append (poly ((append (mono (-> (list _.0) (-> (list _.0) (list _.0))))))
                             (lambda (l1)
                               (lambda (l2)
                                 (if (null? l1)
                                     l2
                                     (cons (car l1)
                                           (@ (@ append (cdr l1)) l2))))))))
              ((l1 (val nil))
               (append (rec (lambda (l1)
                              (lambda (l2)
                                (if (null? l1)
                                    l2
                                    (cons (car l1)
                                          (@ (@ append (cdr l1)) l2)))))))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (@ append nil)))))

(test "!-/evalo-42-simple"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (@ (@ append nil) nil))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list _.0)
     nil
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (@ (@ append nil) nil)))))

(test "!-/evalo-43-type-and-value"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list (list int))
     (cons nil
           (cons (cons 1 (cons 2 nil))
                 (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                       nil)))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (cons (@ (@ append nil) nil)
             (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                   (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                         nil)))))))

(test "!-/evalo-43-type-and-value-with-append"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            (@ (@ append (cdr l1)) l2)))))))
             (pair append
                   (cons (@ (@ append nil) nil)
                         (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                               (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                     nil)))))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((pair (-> (list int) (-> (list int) (list int)))
           (list (list int)))
     (pair (closure (l1)
                    (lambda (l2)
                      (if (null? l1)
                          l2
                          (cons (car l1)
                                (@ (@ append (cdr l1)) l2))))
                    ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                   (lambda (l1)
                                     (lambda (l2)
                                       (if (null? l1)
                                           l2
                                           (cons (car l1)
                                                 (@ (@ append (cdr l1)) l2))))))))
                    ((append (rec (lambda (l1)
                                    (lambda (l2)
                                      (if (null? l1)
                                          l2
                                          (cons (car l1)
                                                (@ (@ append (cdr l1)) l2))))))))) 
           (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      (@ (@ append (cdr l1)) l2)))))))
       (pair append
             (cons (@ (@ append nil) nil)
                   (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                         (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))))))


(time
  (test "append-!-/evalo-synthesis-with-append-c"
    (run 1 (q)
      (fresh (expr type val f-body e clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ (@ append ,e) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-!-/evalo-synthesis-with-append-d"
    (run 1 (q)
      (fresh (expr type val f-body e1 e2 clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ ,e1 l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-!-/evalo-synthesis-with-append-e-with-hint"
    (run 1 (q)
      (fresh (expr type val f-body e1 e2 clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)

        ;; hint!
        (symbolo e2)
        
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ ,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(printf "*** This next test takes a loooong time (if it ever comes back)!\n")
(time
  (test "append-!-/evalo-synthesis-with-append-e-without-hint"
    (run 1 (q)
      (fresh (expr type val f-body e1 e2 clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (@ ,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(printf "*** This next test takes a very looooooooooooooong time (if it ever comes back)!\n")
(time
  (test "append-!-/evalo-synthesis-with-append-z"
    (run 1 (q)
      (fresh (expr type val f-body e clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           ,e))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons (@ (@ append nil) nil)
                           (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                                 (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 1 (cons 2 nil))
                               (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                     nil))))
            val)
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  (@ (@ append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  (@ (@ append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
         (pair append
               (cons (@ (@ append nil) nil)
                     (cons (@ (@ append (cons 1 nil)) (cons 2 nil))
                           (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

