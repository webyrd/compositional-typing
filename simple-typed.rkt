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
           (error 'test (format "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
                                'tested-expression expected produced))))))))


;;; Simply-typed with definition expansion

(define lookupo
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
         (lookupo rest x type)]))))

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
       (lookupo gamma expr type)]
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
      #|
      ;; No reason to include '+' until/unless we support '+' in 'evalo'.
      [(fresh (e1 e2)
         (== `(+ ,e1 ,e2) expr)
         (== 'int type)
         (!-o gamma e1 'int)
         (!-o gamma e2 'int))]
     |#
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
         (== `(let-poly ((,f (lambda (,z) ,e))) ,body) expr)
         (symbolo f)
         (symbolo z)
         ;; Don't infer the type of 'e' yet!
         ;; Instead, add the 'e' expression to the environment for use later.
         (!-o `((,f (poly ((,f (mono ,t)) . ,gamma)
                          (lambda (,z) ,e)))
                . ,gamma)
              body
              type))]
      [(fresh (x e t t^)
         (== `(lambda (,x) ,e) expr)
         (symbolo x)
         (== `(-> ,t ,t^) type)
         (!-o `((,x (mono ,t)) . ,gamma) e t^))]
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
       (fresh (res1)
         (== val res1)
         (lookup-evalo env expr res1))]
      [(fresh (res1 e)
         (== `(null? ,e) expr)
         (conde
           [(== 'nil res1) (== #t val)]
           [(=/= 'nil res1) (== #f val)])
         (evalo env e res1))]      
      [(fresh (b e)
         (== `(car ,e) expr)
         (evalo env e `(cons ,val ,b)))]
      [(fresh (b e)
         (== `(cdr ,e) expr)
         (evalo env e `(cons ,b ,val)))]
      [(fresh (e res1)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 res1) (== #t val)]
           [(=/= 0 res1) (== #f val)])
         (evalo env e res1))]
      #|
      ;; No reason to include '+' until/unless we add support for addition constraints
      ;; (probably using CLP(FD) or SMT constraints).
      [(fresh (e1 e2 res1 res2)
          (== `(+ ,e1 ,e2) expr)
          (numbero res1)
          (numbero res2)
          (+o res1 res2 val)
          (evalo e1 env res1)
          (evalo e2 env res2))]
      |#
      [(fresh (e1 e2 t res1 res2)
         (== `(cons ,e1 ,e2) expr)
         (== `(cons ,res1 ,res2) val)
         (evalo env e1 res1)
         (evalo env e2 res2))]
      [(fresh (e1 e2 res1 res2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,res1 ,res2) val)
         (evalo env e1 res1)
         (evalo env e2 res2))]
      [(fresh (e1 e2 e3 res1 res2 res3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (evalo env e1 res1)
         (conde
           [(== #t res1) (== res2 val) (evalo env e2 res2)]
           [(=/= #t res2) (== res3 val) (evalo env e3 res3)]))]      
      [(fresh (f z e body t)
         (== `(let-poly ((,f (lambda (,z) ,e))) ,body) expr)
         (symbolo f)
         (symbolo z)
         (evalo `((,f (rec (lambda (,z) ,e))) . ,env) body val))]
      [(fresh (x body t t^)
         (== `(lambda (,x) ,body) expr)
         (== `(closure (,x) ,body ,env) val))]
      [(fresh (e1 e2 x body res1 res2 env2)
         (== `(@ ,e1 ,e2) expr)
         (== `(closure (,x) ,body ,env2) res1)
         (symbolo x)
         (evalo env e1 res1)
         (evalo env e2 res2)
         (evalo `((,x (val ,res2)) . ,env2) body val))])))


(test "1"
  (run* (q) (lookupo `((w (mono bool)) (z (mono int))) 'z q))
  '(int))

(test "4"
  (run* (q) (lookupo `((x (mono a))) 'x q))
  '(a))

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
                                         (if (null? l1) l2
                                             (cons (car l1) l2))))))
                    append)
                 q))
  '((-> (list _.0) (-> (list _.0) (list _.0)))))

(test "18"
  (run* (q) (!-o `()
                 `(let-poly ((append (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1) l2
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
                                         (if (null? l1) l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2)))))))
                    append)
                 q))
  '((-> (list _.0) (-> (list _.0) (list _.0)))))

(test "21"
  (run* (q) (!-o `()
                 `(let-poly ((append (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1) l2
                                             (cons (car l1)
                                                   (@ (@ append (cdr l1)) l2)))))))
                    (let-poly ((rev (lambda (l1)
                                      (if (null? l1) l1
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
                   `(let-poly ((append
                                (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1) l2
                                        (cons (car l1)
                                              (@ (@ append (cdr l1)) l2)))))))
                      (@ (@ append nil) nil))
                   q))
  '(nil))

(test "41"
  (run* (q) (evalo `()
                   `(let-poly ((append
                                (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1) l2
                                        (cons (car l1)
                                              (@ (@ append (cdr l1)) l2)))))))
                      (@ (@ append (cons 1 nil)) nil))
                   q))
  '((cons 1 nil)))
