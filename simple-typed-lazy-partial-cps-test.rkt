; #lang racket

(load "faster-miniKanren/mk-vicare.scm")
(load "faster-miniKanren/mk.scm")
; (load "simple-typed-lazy-partial-cps.rkt")

; tests for evalo

(time
 (test "test-evalo-number"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              3
              res)))
   '(3)))

(time
 (test "test-evalo-boolean"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              #f
              res)))
   '(#f)))

(time
 (test "test-evalo-nil"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              'nil
              res)))
   '(nil)))

(time
 (test "test-evalo-null?"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(null? nil)
              res)))
   '(#t)))

(time
 (test "test-evalo-car"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(car (cons 1 nil))
              res)))
   '(1)))

(time
 (test "test-evalo-cdr"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(cdr (cons 1 nil))
              res)))
   '(nil)))

(time
 (test "test-evalo-zero?"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(zero? 1)
              res)))
   '(#f)))

(time
 (test "test-evalo-cons"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(cons 1 nil)
              res)))
   `((cons 1 nil))))


(time
 (test "test-evalo-pair"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(pair 1 nil)
              res)))
   `((pair 1 nil))))

(time
 (test "test-evalo-if1"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(if #t 1 2)
              res)))
   `(1)))

(time
 (test "test-evalo-if2"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(if (null? (cons 1 nil)) 1 2)
              res)))
   `(2)))

(time
 (test "test-evalo-let-poly"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `(let-poly ((id (lambda (x) x))) (id 3))
              res)))
   `(3)))

(time
 (test "test-evalo-lambda"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `((lambda (x) (cons x (cons x nil))) 1)
              res)))
   `((cons 1 (cons 1 nil)))))

(time
 (test "test-evalo-app2args"
   (run 1 (res)
     (fresh (q r s)
       (evalo '()
              `((lambda (x) (lambda (y) (cons x (cons y nil)))) 1 2)
              res)))
   `((cons 1 (cons 2 nil)))))

; tests for !-o

(time
 (test "test-!-o-number"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              3
              res)))
   '(int)))

(time
 (test "test-!-o-boolean"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              #f
              res)))
   '(bool)))

(time
 (test "test-!-o-nil"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(cons 1 nil)
              res)))
   '((list int))))

(time
 (test "test-!-o-null?"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(null? nil)
              res)))
   '(bool)))

(time
 (test "test-!-o-car"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(car (cons 1 nil))
              res)))
   '(int)))

(time
 (test "test-!-o-cdr"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(cdr (cons 1 nil))
              res)))
   '((list int))))

(time
 (test "test-!-o-zero?"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(zero? 1)
              res)))
   '(bool)))

(time
 (test "test-!-o-cons"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(cons 1 nil)
              res)))
   `((list int))))


(time
 (test "test-!-o-pair"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(pair 1 #t)
              res)))
   `((pair int bool))))

(time
 (test "test-!-o-if1"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(if #t 1 2)
              res)))
   `(int)))

(time
 (test "test-!-o-if2"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(if (null? (cons 1 nil)) 1 2)
              res)))
   `(int)))

(time
 (test "test-!-o-let-poly"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `(let-poly ((id (lambda (x) x))) (id 3))
              res)))
   `(int)))

(time
 (test "test-!-o-lambda"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `((lambda (x) (cons x (cons x nil))) 1)
              res)))
   `((list int))))

(time
 (test "test-!-o-app2arg"
   (run 1 (res)
     (fresh (q r s)
       (!-o '()
              `((lambda (x) (lambda (y) (cons x (cons y nil)))) 1 2)
              res)))
   `((list int))))

;; test for !-/evalo

(time
 (test "test-!-/evalo-number"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 3
                 typ
                 res)))
   '((int 3))))

(time
 (test "test-!-/evalo-boolean"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 #f
                 typ
                 res)))
   '((bool #f))))

(time
 (test "test-!-/evalo-nil"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(cons 1 nil)
                 typ
                 res)))
   `(((list int) (cons 1 nil)))))

(time
 (test "test-!-/evalo-null?"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(null? nil)
                 typ
                 res)))
   '((bool #t))))

(time
 (test "test-!-/evalo-car"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(car (cons 1 nil))
                 typ
                 res)))
   '((int 1))))

(time
 (test "test-!-/evalo-cdr"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(cdr (cons 1 nil))
                 typ
                 res)))
   '(((list int) nil))))

(time
 (test "test-!-/evalo-zero?"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(zero? 1)
                 typ
                 res)))
   '((bool #f))))

(time
 (test "test-!-/evalo-cons"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(cons 1 nil)
                 typ
                 res)))
   `(((list int) (cons 1 nil)))))


(time
 (test "test-!-/evalo-pair"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(pair 1 #t)
                 typ
                 res)))
   `(((pair int bool)(pair 1 #t)))))

(time
 (test "test-!-/evalo-if1"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(if #t 1 2)
                 typ
                 res)))
   `((int 1))))

(time
 (test "test-!-/evalo-if2"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                 '()
                 `(if (null? (cons 1 nil)) 1 2)
                 typ
                 res)))
   `((int 2))))

(time
 (test "test-!-/evalo-let-poly"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                    '()
                    `(let-poly ((id (lambda (x) x))) (id 3))
                    typ
                    res)))
   `((int 3))))

(time
 (test "test-!-/evalo-lambda"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                    '()
                    `((lambda (x) (cons x (cons x nil))) 1)
                    typ
                    res)))
   `(((list int) (cons 1 (cons 1 nil))))))

(time
 (test "test-!-/evalo-app2args"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo '()
                    '()
                    `((lambda (x) (lambda (y) (cons x (cons y nil)))) 1 2)
                    typ
                    res)))
   `(((list int) (cons 1 (cons 2 nil))))))


;; test for !-/evalo-lazy-cont

(time
 (test "!-/evalo-lazy-cont-number"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 3
                 typ
                 res)))
   '((int 3))))

(time
 (test "!-/evalo-lazy-cont-boolean"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 #f
                 typ
                 res)))
   '((bool #f))))

(time
 (test "!-/evalo-lazy-cont-nil"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(cons 1 nil)
                 typ
                 res)))
   `(((list int) (cons 1 nil)))))

(time
 (test "!-/evalo-lazy-cont-null?"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(null? nil)
                 typ
                 res)))
   '((bool #t))))

(time
 (test "!-/evalo-lazy-cont-car"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(car (cons 1 nil))
                 typ
                 res)))
   '((int 1))))

(time
 (test "!-/evalo-lazy-cont-cdr"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(cdr (cons 1 nil))
                 typ
                 res)))
   '(((list int) nil))))

(time
 (test "!-/evalo-lazy-cont-zero?"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(zero? 1)
                 typ
                 res)))
   '((bool #f))))

(time
 (test "!-/evalo-lazy-cont-cons"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(cons 1 nil)
                 typ
                 res)))
   `(((list int) (cons 1 nil)))))


(time
 (test "!-/evalo-lazy-cont-pair"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(pair 1 #t)
                 typ
                 res)))
   `(((pair int bool)(pair 1 #t)))))

(time
 (test "!-/evalo-lazy-cont-if1"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(if #t 1 2)
                 typ
                 res)))
   `((int 1))))

(time
 (test "!-/evalo-lazy-cont-if2"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                 '()
                 `(if (null? (cons 1 nil)) 1 2)
                 typ
                 res)))
   `((int 2))))

(time
 (test "!-/evalo-lazy-cont-let-poly"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                    '()
                    `(let-poly ((id (lambda (x) x))) (id 3))
                    typ
                    res)))
   `((int 3))))

(time
 (test "!-/evalo-lazy-cont-lambda"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                    '()
                    `((lambda (x) (cons x (cons x nil))) 1)
                    typ
                    res)))
   `(((list int) (cons 1 (cons 1 nil))))))


(time
 (test "!-/evalo-lazy-cont-app2args"
   (run 1 (typ res)
     (fresh (q r s)
       (!-/evalo-lazy-cont '()
                    '()
                    `((lambda (x) (lambda (y) (cons x (cons y nil)))) 1 2)
                    typ
                    res)))
   `(((list int) (cons 1 (cons 2 nil))))))

(time
 (test "evalo-higher-function"
   (run 1 (res) (evalo '() `(let-poly 
        ((map (lambda (f)
           (lambda (l)
              (if (null? l)
               nil
               (cons (f (car l)) (map f nil))))))) (map (lambda (k) (cons k nil)) (cons 1 nil))) res))
   `((cons (cons 1 nil) nil))))

(time
 (test "!-o-higher-function"
   (run 1 (typ) (!-o '() `(let-poly 
        ((map (lambda (f)
           (lambda (l)
              (if (null? l)
               nil
               (cons (f (car l)) (map f nil))))))) (map (lambda (k) (cons k nil)) (cons 1 nil))) typ))
   `((list (list int)))))

(time
 (test "!-o-higher-function"
   (run 1 (typ res) (!-/evalo-lazy-cont '() '() `(let-poly 
        ((map (lambda (f)
           (lambda (l)
              (if (null? l)
               nil
               (cons (f (car l)) (map f nil))))))) (map (lambda (k) (cons k nil)) (cons 1 nil))) typ res))
   `(((list (list int)) (cons (cons 1 nil) nil)))))


