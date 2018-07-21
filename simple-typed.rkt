#lang racket

(require "faster-miniKanren/mk.rkt")

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
    (fresh (y e rest)
      (symbolo x)
      (== `((,y ,e) . ,rest) gamma)
      (eval gamma e res))))


(define eval
  (lambda (gamma expr res)
     (conde
        [(== #f expr) (== res expr)]
        [(== #t expr) (== res expr)]
        [(numbero expr) (== res expr)]
        [(symbolo expr)
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
           (eval `((,e1 ,e2) . ,gamma) e3 res))]
        [(fresh (e1 e2 k e res1 res2)
           (== `(@ ,e1 ,e2) expr)
           (== res1 `(lambda (,k) ,e))
           (symbolo k)
           (eval gamma e1 res1)
           (eval gamma e2 res2)
           (eval `((,k ,res2) . ,gamma) e res))]
        [(fresh (x e t t^)
           (== `(lambda (,x) ,e) expr)
           (== res `(lambda (,x) ,e)))]
        )))


(run* (q) (lookupo `((w (mono bool)) (z (mono int))) 'z q))
(run* (q) (lookupo `((w (poly `() #f)) (z (mono int))) 'w q))
(run* (q) (lookupo `((w (poly ((x (mono bool))) x)) (z (mono int))) 'w q))

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

