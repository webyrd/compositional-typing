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

(define lookup-!-o
  (lambda (orig-gamma gamma x type/error)
    (conde
      [(== '() gamma)
       (lambdag@ (c)
         (let ((rg ((reify orig-gamma) c)))
           ((== `(error (unbound-var ,x ,rg)) type/error) c)))]
      [(fresh (y t rest z e gamma^)
         (symbolo x)
         (== `((,y ,t) . ,rest) gamma)
         (symbolo y)
         (conde
           [(== x y)
            (conde
              [(== t `(mono ,type/error))]
              [(== t `(poly ,gamma^ (lambda (,z) ,e)))
               (symbolo z)
               (!-o gamma^ `(lambda (,z) ,e) type/error)])]
           [(=/= x y)
            (lookup-!-o orig-gamma rest x type/error)]))])))

(define !-o
  (lambda (gamma expr type/error)
    (conde
      [(== #t expr) (== '(well-typed bool) type/error)]
      [(== #f expr) (== '(well-typed bool) type/error)]
      [(numbero expr) (== '(well-typed int) type/error)]
      [(symbolo expr)
       (=/= expr 'nil)
       (lookup-!-o gamma gamma expr type/error)]
      [(fresh (e)
         (== `(zero? ,e) expr)
         (== '(well-typed bool) type/error)
         (!-o gamma e '(well-typed int)))]
      [(fresh (e1 e2)
         (== `(+ ,e1 ,e2) expr)
         (== '(well-typed int) type/error)
         (!-o gamma e1 '(well-typed int))
         (!-o gamma e2 '(well-typed int)))]
      [(fresh (x body t t^)
         (== `(lambda (,x) ,body) expr)
         (symbolo x)
         (conde
           [(fresh (_)
              (== `(well-typed ,_) t^)
              (== `(well-typed (-> ,t ,t^)) type/error))]
           [(fresh (err _)
              (== `(well-typed ,_) t)
              (== `(error ,err) t^)
              (lambdag@ (c)
                (let ((rg ((reify gamma) c)))
                  ((== `(error (abs-bad-body ,err ,rg)) type/error) c))))]
           [(fresh (err _)
              (== `(error ,err) t)
              (== `(well-typed ,_) t^)
              (lambdag@ (c)
                (let ((rg ((reify gamma) c)))
                  ((== `(error (abs-bad-arg ,err ,rg)) type/error) c))))]
           [(fresh (err-t err-t^)
              (== `(error ,err-t) t)
              (== `(error ,err-t^) t^)
              (lambdag@ (c)
                (let ((rg ((reify gamma) c)))
                  ((== `(error (abs-bad-arg-and-body ,err-t ,err-t^ ,rg)) type/error) c))))])
         (!-o `((,x (mono ,t)) . ,gamma) body t^))]

      #|
      [(fresh (e1 e2 t)
         (== `(@ ,e1 ,e2) expr)
         (!-o gamma e1 `(-> ,t ,type))
         (!-o gamma e2 t))]
      |#
      
      )))

(test "unbound-1"
  (run* (q)
    (!-o '() 'w q))
  '((error (unbound-var w ()))))

(test "unbound-2"
  (run* (q)
    (fresh (x y z)
      (symbolo x)
      (== y z)
      (!-o '() 'w q)))
  '((error (unbound-var w ()))))

(test "abs-1"
  (run* (q)
    (!-o '() '(lambda (y) y) q))
  '((well-typed (-> (well-typed _.0) (well-typed _.0)))))

(test "abs-2"
  (run* (q)
    (!-o '() '(lambda (y) z) q))
  '((error (abs-bad-body (unbound-var z ((y (mono _.0)))) ()))))
