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
         (== `(let-poly ((,f (lambda (,z) ,e))) ,body) expr)
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
           [(== #f v2) (== v3 val) (evalo env e3 v3)]))]
      [(fresh (f z e body t)
         (== `(let-poly ((,f (lambda (,z) ,e))) ,body) expr)
         (symbolo f)
         (symbolo z)
         (evalo `((,f (rec (lambda (,z) ,e))) . ,env) body val))]
      [(fresh (x body)
         (== `(lambda (,x) ,body) expr)
         (== `(closure (,x) ,body ,env) val))]
      [(fresh (e1 e2 x body v1 v2 env^)
         (== `(@ ,e1 ,e2) expr)
         (== `(closure (,x) ,body ,env^) v1)
         (symbolo x)
         (evalo env e1 v1)
         (evalo env e2 v2)
         (evalo `((,x (val ,v2)) . ,env^) body val))])))


(test "1"
  (run* (q) (lookup-!-o `((w (mono bool)) (z (mono int))) 'z q))
  '(int))

(test "4"
  (run* (q) (lookup-!-o `((x (mono a))) 'x q))
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
      (fresh (expr type e)
        (== (list type expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons ,e
                                              (@ (@ append (cdr l1)) l2)))))))
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
      (fresh (expr type e)
        (== (list type expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons ,e
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
      (fresh (expr val e)
        (== (list val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)        
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons ,e
                                              (@ (@ append (cdr l1)) l2)))))))
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
      (fresh (expr val e clos)
        (== (list val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons ,e
                                              (@ (@ append (cdr l1)) l2)))))))
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
      (fresh (expr type val e)
        (== (list type val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)        
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons ,e
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
                           nil))))))))

(time
  (test "append-type-and-value-synthesis-with-append-a"
    (run 1 (q)
      (fresh (expr type val e clos)
        (== (list type val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons ,e
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
      (fresh (expr type e)
        (== (list type expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons (car l1)
                                              (@ (@ append (cdr ,e)) l2)))))))
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
      (fresh (expr val e)
        (== (list val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)        
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons (car l1)
                                              (@ (@ append (cdr ,e)) l2)))))))
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
      (fresh (expr type val e)
        (== (list type val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)        
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons (car l1)
                                              (@ (@ append (cdr ,e)) l2)))))))
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
      (fresh (expr type e)
        (== (list type expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons (car l1)
                                              (@ (@ append ,e) l2)))))))
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
      (fresh (expr type e)
        (== (list type expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons (car l1)
                                              (@ (@ append ,e) l2)))))))
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
      (fresh (expr val e)
        (== (list val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)        
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons (car l1)
                                              (@ (@ append ,e) l2)))))))
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
      (fresh (expr type val e)
        (== (list type val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)        
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons (car l1)
                                              (@ (@ append ,e) l2)))))))
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
      (fresh (expr type val e clos)
        (== (list type val expr) q)
        (absento 1 e)
        (absento 2 e)
        (absento 3 e)
        (absento 4 e)
        (absento 5 e)
        (absento 6 e)
        (== `(let-poly ((append (lambda (l1)
                                  (lambda (l2)
                                    (if (null? l1)
                                        l2
                                        (cons (car l1)
                                              (@ (@ append ,e) l2)))))))
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
