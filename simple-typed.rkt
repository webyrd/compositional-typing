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
           (error 'test (format "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
                                'tested-expression expected produced))))))))


; Simply-typed with definition expansion

(define lookupo
  (lambda (gamma x type)
    (conde
     [(== x 'nil) (fresh (a)
                        (== `(list ,a) type))]
     [(== x 'car) (fresh (a)
                         (== `(-> (list ,a) ,a) type))]
     [(== x 'cdr) (fresh (a)
                             (== `(-> (list ,a) (list ,a)) type))]
     [(== x 'null?) (fresh (a)
                           (== `(-> (list ,a) bool) type))]
     [(=/= x 'nil) ; not 'car ..
      (=/= x 'car)
      (=/= x 'cdr)
      (=/= x 'null?)
       (lookupo-non-prim gamma x type)])))

(define lookupo-non-prim
  (lambda (gamma x type)
    (fresh (y t rest)
      (symbolo x)
      (== `((,y ,t) . ,rest) gamma)
      (symbolo y)
      (fresh (env e t2)
          (conde
           [(== x y) 
            (conde
             [(== t `(poly ,env ,e)) (!-o env e type)]
             [(== t `(mono ,t2)) (== t2 type)])]
           [(=/= x y)
            (lookupo-non-prim rest x type)])))))

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
           (== `(cons ,e1 ,e2) expr)
           (== `(list ,t) type)
           (!-o gamma e1 t)
           (!-o gamma e2 `(list ,t)))]
        [(fresh (e1 e2 t1 t2)
           (== `(pair ,e1 ,e2) expr)
           (== `(pair ,t1 ,t2) type)
           (!-o gamma e1 t1)
           (!-o gamma e2 t2))]
        [(fresh (e1 e2 e3 t)
           (== `(let-poly ((,e1 ,e2)) ,e3) expr)
           (symbolo e1)
    ;       (!-o ` e2 t) ;let rec
           (!-o `((,e1 (poly ((,e1 (mono ,t)) . ,gamma) ,e2)) . ,gamma) e3 type))]
        [(fresh (e1 e2 t)
           (== `(@ ,e1 ,e2) expr)
           (!-o gamma e1 `(-> ,t ,type))
           (!-o gamma e2 t))]
        [(fresh (x e t t^)
           (== `(lambda (,x) ,e) expr)
           (symbolo x)
           (== `(-> ,t ,t^) type)
           (!-o `((,x (mono ,t)) . ,gamma) e t^))])))

(define lookup_eval_o
  (lambda (x gamma res)
    (fresh (y v z rest body)
      (== `((,y ,v) . ,rest) gamma)
      (conde
       [(== x y)
        (conde
         [(== `(val ,res) v)]
         [(== `(rec (lambda (,z) ,body)) v) (== `(closure (,z) ,body ,gamma) res)])]
       [(=/= x y) (lookup_eval_o x rest res)]))))


(define eval
  (lambda (gamma expr res)
     (conde
        [(== #f expr) (== res expr)]
        [(== #t expr) (== res expr)]
        [(numbero expr) (== res expr)]
        [(== 'nil expr) (== res 'nil)]
        [(fresh (b e)
           (== `(car ,e) expr)
           (eval gamma e `(cons ,res ,b)))]
        [(fresh (b e)
           (== `(cdr ,e) expr)
           (eval gamma e `(cons ,b ,res)))]
        [(fresh (res1 e)
           (== `(null? ,e) expr)
           (conde
            [(== res1 'nil) (== #t res)]
            [(=/= res1 'nil) (== #f res)])
           (eval gamma e res1))]
        [(symbolo expr)
         (=/= expr 'nil)
         (fresh (res1)
           (== res res1)
           (lookup_eval_o expr gamma res1))]
        [(fresh (e res1)
           (== `(zero? ,e) expr)
           (conde
            [(== res1 0) (== res #t)]
            [(=/= res1 0) (== res #f)])
           (eval gamma e res1))]
        [(fresh (e1 e2 t res1 res2)
           (== `(cons ,e1 ,e2) expr)
           (== res `(cons ,res1 ,res2))
           (eval gamma e1 res1)
           (eval gamma e2 res2))]
      ;  [(fresh (e1 e2 res1 res2)
      ;     (== `(+ ,e1 ,e2) expr)
      ;     (eval e1 gamma res1)
      ;     (eval e2 gamma res2)
      ;     (numbero res1)
      ;     (numbero res2)
      ;     (== res (+ res1 res2)))]
        [(fresh (e1 e2 e3 res1 res2 res3)
           (== `(if ,e1 ,e2 ,e3) expr)
           (eval gamma e1 res1)
           (conde
            [(== res1 #t) (== res res2) (eval gamma e2 res2)]
            [(=/= res2 #t) (== res res3) (eval gamma e3 res3)]))]

        [(fresh (e1 e2 res1 res2)
           (== `(pair ,e1 ,e2) expr)
           (== `(pair ,res1 ,res2) res)
           (eval gamma e1 res1)
           (eval gamma e2 res2))]
        [(fresh (e1 e2 e3 t)
           (== `(let-poly ((,e1 ,e2)) ,e3) expr)
           (symbolo e1)
           (eval `((,e1 (rec ,e2)) . ,gamma) e3 res))]
        [(fresh (e1 e2 x body res1 res2 gamma2)
           (== `(@ ,e1 ,e2) expr)
           (== res1 `(closure (,x) ,body ,gamma2))
           (symbolo x)
           (eval gamma e1 res1)
           (eval gamma e2 res2)
           (eval `((,x (val ,res2)) . ,gamma2) body res))]
        [(fresh (x body t t^)
           (== `(lambda (,x) ,body) expr)
           (== res `(closure (,x) ,body ,gamma)))]
        )))

(test "1"
  (run* (q) (lookupo `((w (mono bool)) (z (mono int))) 'z q))
  '(int))

(test "2"
  (run* (q) (lookupo `((w (poly `() #f)) (z (mono int))) 'w q))
  '(bool))

(test "3"  
  (run* (q) (lookupo `((w (poly ((x (mono bool))) x)) (z (mono int))) 'w q))
  '(bool))

(run* (q) (lookupo `((x (mono a))) 'x q))

(run* (q) (!-o `() 3 q))
(run* (q) (!-o `() #f q))
(run* (q) (!-o `((x (mono bool))) `x q))

(run* (q) (!-o `() `(cons 2 43) q))


(run* (q) (!-o `() `(@ (lambda (x) x) 3) q))

(run* (q) (!-o `() `(let-poly ((f (lambda (y) #f))) (cons (@ f 3) (@ f #f))) q))

(run* (q) (!-o `() `(let-poly ((f (lambda (y) y))) (pair (@ f 3) (@ f #f))) q))

(run* (q) (!-o `() `(@ (lambda (f) (pair (@ f 3) (@ f #f))) (lambda (y) y)) q))
(run* (q) (!-o `() `(@ (lambda (f) (pair (@ f 3) (@ f 4))) (lambda (y) y)) q))



(run* (q) (!-o `()
               'nil q))

(run* (q) (lookupo `()
               'nil q))

(run* (q) (!-o `()
               `(@ car nil) q))


(run* (q) (!-o `()
               `(let-poly ((append
                          (lambda (l1)
                            (lambda (l2)
                              (if (@ null? l1) l2
                                  (cons (@ car l1)
                                        l2)))))) append) q))


(run* (q) (!-o `()
               `(let-poly ((append
                          (lambda (l1)
                            (lambda (l2)
                              (if (@ null? l1) l2
                                  (cons (cons (@ car l1) nil)
                                        (cons (@ cdr l1) l2))))))) append) q))

(run* (q) (!-o `() `(pair (cons 3 nil) (cons #f nil)) q))

(run* (q) (!-o `()
               `(let-poly ((append
                          (lambda (l1)
                            (lambda (l2)
                              (if (@ null? l1) l2
                                  (cons (@ car l1)
                                        (@ (@ append (@ cdr l1)) l2))))))) append) q))

(printf "This place:\n")


(run* (q) (!-o `()
                `(let-poly ((append
                          (lambda (l1)
                            (lambda (l2)
                              (if (@ null? l1) l2
                                  (cons (@ car l1)
                                        (@ (@ append (@ cdr l1)) l2)))))))
                           (let-poly ((rev
                                       (lambda (l1)
                                         (if (@ null? l1) l1
                                             (@ (@ append (@ rev (@ cdr l1))) (cons (@ car l1) nil))))))
                                     rev)) q))
      


(run* (q) (!-o `() `(lambda (f) (@ f f)) q))

(run* (q) (!-o `() `(lambda (y) (cons #f y)) q))

(run* (q) (!-o `() `(let-poly ((x (lambda (y) (cons #f y)))) x) q))
(run 1 (q) (!-o `((x (mono (-> bool bool))) (z (mono bool))) `(@ x ,q) `bool))

(run 1 (q) (!-o `() `(lambda (x) ,q) `(-> bool bool)))
(run* (q) (!-o `() `(lambda (x) x) q))

(run* (q) (eval `() #f  q))
(run* (q) (eval  `()`(cons 3 #f) q))
(run* (q) (eval  `() `(lambda (y) (cons #f y)) q))
(run* (q) (eval  `()`(@ (lambda (x) x) 3) q))

(run* (q) (eval  `()`(let-poly ((x (lambda (y) #f))) (cons (@ x 3) (@ x #f))) q))
(run* (q) (eval `() `(let-poly ((f (lambda (y) y))) (pair (@ f 3) (@ f #f))) q))

(run* (q) (eval `() `(let-poly ((f (lambda (y) y)))
                               (pair (@ f 3) (@ f #f))) q))

(run* (q) (eval `() `(@ (lambda (f) (pair (@ f 3) (@ f #f))) (lambda (y) y)) q))
(run* (q) (eval `() `(@ (lambda (f) (pair (@ f 3) (@ f 4))) (lambda (y) y)) q))

(run* (q) (eval `() `nil q))

(run* (q) (eval `() `(cons 5 nil) q))

(run* (q) (eval `() `(null? nil) q))

(run* (q) (eval `()
               `(let-poly ((append
                          (lambda (l1)
                            (lambda (l2)
                              (if (null? l1) l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
                          (@ (@ append nil) nil)) q))

(run* (q) (eval `()
               `(let-poly ((append
                          (lambda (l1)
                            (lambda (l2)
                              (if (null? l1) l2
                                  (cons (car l1)
                                        (@ (@ append (cdr l1)) l2)))))))
                          (@ (@ append (cons 1 nil)) nil)) q))
