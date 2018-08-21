(load "faster-miniKanren/mk-vicare.scm")
(load "faster-miniKanren/mk.scm")

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


(define append
  (lambda (l s)
    (cond
      ((null? l) s)
      (else (cons (car l) (append (cdr l) s))))))

(define append-cps
  (lambda (l s k)
    (cond
      ((null? l) (k s))
      (else (append-cps (cdr l) s (lambda (v)
                                    (k (cons (car l) v))))))))

(append-cps '(a b c) '(d e) (lambda (v) v))

(define appendo
  (lambda (l s out)
    (conde
      ((== '() l) (== s out))
      ((fresh (a d res)
         (== (cons a d) l)
         (== (cons a res) out)
         (appendo d s res))))))

(run* (q) (appendo '(a b c) '(d e) q))

(run* (q) (appendo q '(d e) '(a b c d e)))

(define appendo-cps
  (lambda (l s out k)
    (conde
      ((== '() l) (== s out) k)
      ((fresh (a d res)
         (== (cons a d) l)
         (appendo-cps d s res (fresh ()
                                (== (cons a res) out)
                                k)))))))

;; equivalent to
(define appendo
  (lambda (l s out)
    (conde
      ((== '() l) (== s out))
      ((fresh (a d res)
         (== (cons a d) l)
         (appendo d s res)
         (== (cons a res) out))))))

; loop
; (run 2 (q) (appendo q '(d e) '(a b c d e)))


(run* (q) (appendo-cps '(a b c) '(d e) q succeed))

;; loops
;; (run 2 (q) (appendo-cps q '(d e) '(a b c d e) succeed))
