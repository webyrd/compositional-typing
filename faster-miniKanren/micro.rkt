#lang racket

(define empty-s '())
(define (ext-s x v s) `((,x . ,v) . ,s)) ; (cons (cons x v) s)

(define empty-state `(,empty-s . 0))  ; (cons '() 0)

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

#|
(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

(let ((x (var 0))
      (y (var 1))
      (w (var 2)))
  (walk x `((,y . 5) (,x . ,y))))
|#

(define (assoc x ls)
  (cond
    [(null? ls) #f]
    [(equal? (car (car ls)) x) (car ls)]
    [else (assoc x (cdr ls))]))

(assoc 'y '((x . 3) (y . #f)))
(assoc 'w '((x . 3) (y . #f)))
;; ((x . 3) (y . 4))

(define (walk u s)
  (cond
    [(var? u)
     (cond
       [(assoc u s)
        (let ((pr (assoc u s)))
          (walk (cdr pr) s))]
       [else u])]
    [else u]))

#|
(define (walk u s)
  (cond
    [(var? u)
     (cond
       [(assoc u s) => (lambda (pr) (walk (cdr pr) s))]
       [else u])]
    [else u]))
|#

(let ((x (var 0))
      (y (var 1))
      (z (var 2)))
  (walk x `((,y . (,z)) (,x . ,y))))

#|
(let ((x (var 0))
      (y (var 1)))
  (walk x `((,y . ,x) (,x . ,y))))
|#

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      [(and (var? u) (var? v) (var=? u v))
       s]
      [(var? u) (ext-s u v s)]
      [(var? v) (ext-s v u s)]
      [(and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s)))]
      [(eqv? u v) s]
      [else #f])))

(unify 5 5 empty-s)
(unify 5 6 empty-s)

(let ((x (var 0))
      (y (var 1)))
  (unify x 5 (ext-s x y empty-s)))

(define unit
  (lambda (s/c)
    (cons s/c mzero)))

(define mzero '())

(define ==
  (lambda (u v) ; goal constructor
    (lambda (s/c) ; goal   st -> st*
      (let ((s (car s/c))
            (c (cdr s/c)))
        (let ((s (unify u v s)))
          (if s
              (unit `(,s . ,c))
              mzero))))))

(let ((g (== 5 5)))
  (g `(,empty-s . 0)))

(let ((g (== 5 6)))
  (g `(,empty-s . 0)))


(define call/fresh
  (lambda (f) ; goal constructor
    (lambda (s/c) ; goal  st->st*
      (let ((s (car s/c))
            (c (cdr s/c)))
        (let ((v (var c)))
          (let ((g (f v)))
            (let ((st `(,s . ,(add1 c))))
              (g st))))))))

(let ((g (call/fresh
          (lambda (x)
            (== x 5)))))
   (g `(,empty-s . 0)))

(let ((g (call/fresh
          (lambda (x)
            (call/fresh
              (lambda (y)
                (== x y)))))))
   (g `(,empty-s . 0)))

(define disj
  (lambda (g1 g2) ; goal constructor
    (lambda (s/c) ; goal  st->st*
      (mplus (g1 s/c)
             (g2 s/c)))))



(define mplus
  (lambda (str1 str2)
    (cond
      [(null? str1) str2]
      [(procedure? str1)
       ;; immature stream
       (lambda ()
         (mplus str2 (str1)))]
      [else (cons (car str1)
                  (mplus (cdr str1) str2))])))



#|
(run* (q)
  (== (list a b) q)
  (fresh (a b)
    (== a 7)
    (conde
      [(== b 5)]
      [(== b 6)])))
|#



(define bind
  (lambda (str g)
    (cond
      [(null? str) mzero]
      ; immature stream
      [(procedure? str)
       (lambda () (bind (str) g))]
      [else (mplus (g (car str))
                   (bind (cdr str) g))])))

(define conj
  (lambda (g1 g2) ; goal constructor
    (lambda (s/c) ; goal  st->st*
      (bind (g1 s/c)
            g2))))

(define a-and-b
  (conj
    (call/fresh (lambda (a) (== a 7)))
    (call/fresh (lambda (b)
                  (disj
                     (== b 5)
                     (== b 6))))))

(a-and-b `(,empty-s . 0))

(define fives
  (lambda (x)
    (disj
      (== x 5)
      (lambda (s/c)
        (lambda ()
          ((fives x) s/c))))))

(define sixes
  (lambda (x)
    (disj
      (== x 6)
      (lambda (s/c)
        (lambda ()
          ((sixes x) s/c))))))

(define fives-and-sixes
  (call/fresh
    (lambda (x)
      (disj (fives x) (sixes x)))))

(fives-and-sixes empty-state)

(let ((str (fives-and-sixes empty-state)))
  ((cdr str)))

#|
((call/fresh fives) empty-state)

(let ((str ((call/fresh fives) empty-state)))
  ((cdr str)))
|#