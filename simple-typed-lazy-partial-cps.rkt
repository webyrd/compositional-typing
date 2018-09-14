
;#lang racket

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
         (== `(,e1 ,e2) expr)
         (!-o gamma e1 `(-> ,t ,type))
         (!-o gamma e2 t))]
      [(fresh (e1 e2 e3 t1 t2)
         (== `(,e1 ,e2 ,e3) expr)
         (!-o gamma e1 `(-> ,t1 (-> ,t2 ,type)))
         (!-o gamma e2 t1)
         (!-o gamma e3 t2))]
      )))

;; Evaluation 

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
         (== `(,e1 ,e2) expr)
         (symbolo x)
         (evalo env e1 `(closure (,x) ,body ,env^))
         (evalo env e2 arg)
         (evalo `((,x (val ,arg)) . ,env^) body val))]
      [(fresh (e1 e2 e3 x y body arg1 arg2 env^)
         (== `(,e1 ,e2 ,e3) expr)
         (symbolo x)
         (symbolo y)
         (evalo env e1 `(closure (,x) (lambda (,y) ,body) ,env^))
         (evalo env e2 arg1)
         (evalo env e3 arg2)
         (evalo `((,x (val ,arg1)) . ((,y (val ,arg2)) . ,env^)) body val))]
      
      )))


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
         ;; FIXME -- this isn't right!  We need to infer the types of both e2 and e3
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
         (!-o `((,x (mono
                     ,t)) . ,gamma) body t^))]
      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(,e1 ,e2) expr)
         (symbolo x)
         (!-/evalo gamma env e1 `(-> ,t ,type) `(closure (,x) ,body ,gamma^ ,env^))
         (!-/evalo gamma env e2 t arg)
         (!-/evalo `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val))]
      [(fresh (e1 e2 e3 t2 t3 x y body arg2 arg3 gamma^ env^ some-gamma)
         (== `(,e1 ,e2 ,e3) expr)
         (symbolo x)
         (!-/evalo gamma env e1 `(-> ,t2 (-> ,t3 ,type)) `(closure (,x) (lambda (y) ,body) ,gamma^ ,env^))
         (!-/evalo gamma env e2 t2 arg2)
         (!-/evalo gamma env e3 t3 arg3)
         (!-/evalo `((,x (mono ,t2)) . ((,y (mono ,t3)) . ,gamma^)) `((,x (val ,arg2)) . ((,y (val ,arg3)) . ,env^)) body type val))]

      )))



;; Assumption used in 'lookup-!-/evalo-lazy-cont': !-/evalo-lazy extends 'gamma' and
;; 'env' at the same time, with the same variable names, in the same
;; order (and similarly for the initial 'gamma' and 'env', if
;; non-empty).  Furthermore, we assume (val ,v) and (mono ,t) entries
;; occur together, as do (rec (lambda (,z) ,e)) and
;; (poly ,gamma^ (lambda (,z) ,e)) entries.
(define lookup-!-/evalo-lazy-cont
  (lambda (gamma env x type val k)
    (fresh (y t v rest-gamma rest-env z e)
      (symbolo x)
      (== `((,y ,t) . ,rest-gamma) gamma)
      (== `((,y ,v) . ,rest-env) env)
      (symbolo y)
      (conde
        [(== x y)
         (conde
           [(== `(val ,val) v)
            (== `(mono ,type) t)
            k]
           [(== `(rec (lambda (,z) ,e)) v)
            (symbolo z)
            (== `(closure (,z) ,e ,gamma ,env) val)
            (fresh (gamma^)
              (== `(poly ,gamma^ (lambda (,z) ,e)) t)

              ;; ?? Is it possible to be lazy here??
              ;;
              ;; This is a call to '!-o', not a recursive call to 'lookup-!-/evalo-lazy-cont'
              k
             ; (!-o gamma^ `(lambda (,z) ,e) type) 

              )])]
        [(=/= x y)
         (lookup-!-/evalo-lazy-cont rest-gamma rest-env x type val k)]))))



(define !-/evalo-lazy-cont-aux
  (lambda (gamma env expr type val k)
    (conde
      [(symbolo expr)
       (=/= 'nil expr)
       (lookup-!-/evalo-lazy-cont gamma env expr type val k)]
      [(== #f expr) (== 'bool type) (== #f val) k]
      [(== #t expr) (== 'bool type) (== #t val) k]
      [(numbero expr) (== 'int type) (== expr val) k]
      [(== 'nil expr)
       (== 'nil val)
       (fresh (a)
         (== `(list ,a) type)) k]
      [(fresh (e a v)
         (== `(null? ,e) expr)
         (== 'bool type)
         (conde
           [(== 'nil v) (== #t val)]
           [(=/= 'nil v) (== #f val)])
         (!-/evalo-lazy-cont-aux gamma env e `(list ,a) v k))]
      [(fresh (e a b)
         (== `(car ,e) expr)
         (== a type)
         (!-/evalo-lazy-cont-aux gamma env e `(list ,a) `(cons ,val ,b) k))]
      [(fresh (e a b)
         (== `(cdr ,e) expr)
         (== `(list ,a) type)
         (!-/evalo-lazy-cont-aux gamma env e `(list ,a) `(cons ,b ,val) k))]
      [(fresh (e v)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 v) (== #t val)]
           [(=/= 0 v) (== #f val)])
         (== 'bool type)
         (!-/evalo-lazy-cont-aux gamma env e 'int v k))]
      [(fresh (e1 e2 a t v1 v2)
         (== `(cons ,e1 ,e2) expr)
         (== `(list ,a) type)
         (== `(cons ,v1 ,v2) val)
         (!-/evalo-lazy-cont-aux gamma env e2 `(list ,a) v2 succeed)
         (!-/evalo-lazy-cont-aux gamma env e1 a v1 k))]
      [(fresh (e1 e2 t1 t2 v1 v2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,t1 ,t2) type)
         (== `(pair ,v1 ,v2) val)
         (!-/evalo-lazy-cont-aux gamma env e1 t1 v1 succeed)
         (!-/evalo-lazy-cont-aux gamma env e2 t2 v2 k))]
      [(fresh (x body t t^)
         (== `(lambda (,x) ,body) expr)
         (symbolo x)
         (== `(-> ,t ,t^) type)
         (== `(closure (,x) ,body ,gamma ,env) val)
         (fresh ()
             k
            ; (!-o `((,x (mono ,t)) . ,gamma) body t^)
             )
         ;; Be lazy!  Don't worry about the type of the body yet!
         ;; We'll make sure the body is well typed in a separate call to '!-o'.
         ;;         
         #|
         ;; This is a call to '!-o', not a recursive call to '!-/evalo-lazy-cont-aux'
         (!-o `((,x (mono ,t)) . ,gamma) body t^)
         |#

         )]
      [(fresh (e1 e2 e3 v1 v2 v3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (!-/evalo-lazy-cont-aux gamma env e1 'bool v1 succeed)
         (conde
          [(== #t v1) (== v2 val) (!-/evalo-lazy-cont-aux gamma env e2 type v2 k)]
          [(== #f v1) (== v3 val) (!-/evalo-lazy-cont-aux gamma env e3 type v3 k)]))]
      [(fresh (f z e body t)
         (== `(let-poly ((,f (lambda (,z) ,e)))
                ,body)
             expr)
         (symbolo f)
         (symbolo z)

         ;; Be lazy!  Don't worry about the type of the right-hand-side of 'f' yet!
         ;; We'll make sure the right-hand-side is well typed in a separate call to '!-o'.
         ;;
         #|
         ;; Make sure the right-hand-side of 'f' has a type, but then forget about the type.
         ;;
         ;; This is in case 'f' is not used in 'body'--we still must
         ;; make sure the right-hand-side of 'f' has a type.
         (fresh (forget-me)
           ;; This is a call to '!-o', not a recursive call to '!-/evalo-lazy-cont-aux'
           (!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
         |#
         
         (!-/evalo-lazy-cont-aux
          ;; Add the right-hand-side of the binding (an expression) to the environment for use later.
          `((,f (poly ((,f (mono ,t)) . ,gamma)
                      (lambda (,z) ,e)))
            . ,gamma)
          `((,f (rec (lambda (,z) ,e))) . ,env)
          body
          type
          val
          (fresh ()
                 k
               ;  (fresh (forget-me)
                        ;; This is a call to '!-o', not a recursive call to '!-/evalo-lazy-cont-aux'
                        ;(!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
                 ))
         )]

      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(,e1 ,e2) expr)
         (symbolo x)
         (!-/evalo-lazy-cont-aux gamma env e1
                                 `(-> ,t ,type)
                                 `(closure (,x) ,body ,gamma^ ,env^)
                                 succeed)
         (!-/evalo-lazy-cont-aux gamma env e2 t arg succeed)
         (!-/evalo-lazy-cont-aux `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val k))]
      [(fresh (e1 e2 e3 t2 t3 x y body arg2 arg3 gamma^ env^ some-gamma)
         (== `(,e1 ,e2, e3) expr)
         (symbolo x)
         (symbolo y)
         (!-/evalo-lazy-cont-aux gamma env e1
                                 `(-> ,t2 (-> t3 ,type))
                                 `(closure (,x) (lambda (,y) ,body) ,gamma^ ,env^)
                                 succeed)
         (!-/evalo-lazy-cont-aux gamma env e2 t2 arg2 succeed)
         (!-/evalo-lazy-cont-aux gamma env e3 t3 arg3 succeed)
         (!-/evalo-lazy-cont-aux `((,x (mono ,t2)) . ((,y (mono ,t3)) . ,gamma^)) `((,x (val ,arg2)) . ((,y (val ,arg3)) . ,env^)) body type val k))]

      )))


(define !-/evalo-lazy-cont
  (lambda (gamma env expr type val)
      (fresh ()
        (!-/evalo-lazy-cont-aux gamma env expr type val succeed)
        (!-o gamma expr type)
        )
      ))













;; Assumption used in 'lookup-!-/evalo-lazy-nocont': !-/evalo-lazy extends 'gamma' and
;; 'env' at the same time, with the same variable names, in the same
;; order (and similarly for the initial 'gamma' and 'env', if
;; non-empty).  Furthermore, we assume (val ,v) and (mono ,t) entries
;; occur together, as do (rec (lambda (,z) ,e)) and
;; (poly ,gamma^ (lambda (,z) ,e)) entries.
(define lookup-!-/evalo-lazy-nocont
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

              ;; ?? Is it possible to be lazy here??
              ;;
              ;; This is a call to '!-o', not a recursive call to 'lookup-!-/evalo-lazy-nocont'
             ; (!-o gamma^ `(lambda (,z) ,e) type) 

              )])]
        [(=/= x y)
         (lookup-!-/evalo-lazy-nocont rest-gamma rest-env x type val)]))))



(define !-/evalo-lazy-nocont-aux
  (lambda (gamma env expr type val)
    (conde
      [(symbolo expr)
       (=/= 'nil expr)
       (lookup-!-/evalo-lazy-nocont gamma env expr type val)]
      [(== #f expr) (== 'bool type) (== #f val)]
      [(== #t expr) (== 'bool type) (== #t val)]
      [(numbero expr) (== 'int type) (== expr val)]
      [(== 'nil expr)
       (== 'nil val)
       (fresh (a)
         (== `(list ,a) type))]
      [(fresh (e a v)
         (== `(null? ,e) expr)
         (== 'bool type)
         (conde
           [(== 'nil v) (== #t val)]
           [(=/= 'nil v) (== #f val)])
         (!-/evalo-lazy-nocont-aux gamma env e `(list ,a) v))]
      [(fresh (e a b)
         (== `(car ,e) expr)
         (== a type)
         (!-/evalo-lazy-nocont-aux gamma env e `(list ,a) `(cons ,val ,b)))]
      [(fresh (e a b)
         (== `(cdr ,e) expr)
         (== `(list ,a) type)
         (!-/evalo-lazy-nocont-aux gamma env e `(list ,a) `(cons ,b ,val)))]
      [(fresh (e v)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 v) (== #t val)]
           [(=/= 0 v) (== #f val)])
         (== 'bool type)
         (!-/evalo-lazy-nocont-aux gamma env e 'int v))]
      [(fresh (e1 e2 a t v1 v2)
         (== `(cons ,e1 ,e2) expr)
         (== `(list ,a) type)
         (== `(cons ,v1 ,v2) val)
         (!-/evalo-lazy-nocont-aux gamma env e2 `(list ,a) v2)
         (!-/evalo-lazy-nocont-aux gamma env e1 a v1))]
      [(fresh (e1 e2 t1 t2 v1 v2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,t1 ,t2) type)
         (== `(pair ,v1 ,v2) val)
         (!-/evalo-lazy-nocont-aux gamma env e1 t1 v1)
         (!-/evalo-lazy-nocont-aux gamma env e2 t2 v2))]
      [(fresh (x body t t^)
         (== `(lambda (,x) ,body) expr)
         (symbolo x)
         (== `(-> ,t ,t^) type)
         (== `(closure (,x) ,body ,gamma ,env) val)

         ; (!-o `((,x (mono ,t)) . ,gamma) body t^)

         ;; Be lazy!  Don't worry about the type of the body yet!
         ;; We'll make sure the body is well typed in a separate call to '!-o'.
         ;;         
         #|
         ;; This is a call to '!-o', not a recursive call to '!-/evalo-lazy-nocont-aux'
         (!-o `((,x (mono ,t)) . ,gamma) body t^)
         |#

         )]
      [(fresh (e1 e2 e3 v1 v2 v3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (!-/evalo-lazy-nocont-aux gamma env e1 'bool v1)
         (conde
           [(== #t v1) (== v2 val) (!-/evalo-lazy-nocont-aux gamma env e2 type v2)]
           [(== #f v1) (== v3 val) (!-/evalo-lazy-nocont-aux gamma env e3 type v3)]))]
      [(fresh (f z e body t)
         (== `(let-poly ((,f (lambda (,z) ,e)))
                ,body)
             expr)
         (symbolo f)
         (symbolo z)

         ;; Be lazy!  Don't worry about the type of the right-hand-side of 'f' yet!
         ;; We'll make sure the right-hand-side is well typed in a separate call to '!-o'.
         ;;
         #|
         ;; Make sure the right-hand-side of 'f' has a type, but then forget about the type.
         ;;
         ;; This is in case 'f' is not used in 'body'--we still must
         ;; make sure the right-hand-side of 'f' has a type.
         (fresh (forget-me)
           ;; This is a call to '!-o', not a recursive call to '!-/evalo-lazy-nocont-aux'
           (!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
         |#
         
         (!-/evalo-lazy-nocont-aux
          ;; Add the right-hand-side of the binding (an expression) to the environment for use later.
          `((,f (poly ((,f (mono ,t)) . ,gamma)
                      (lambda (,z) ,e)))
            . ,gamma)
          `((,f (rec (lambda (,z) ,e))) . ,env)
          body
          type
          val
          ;;  (fresh (forget-me)
          ;; This is a call to '!-o', not a recursive call to '!-/evalo-lazy-nocont-aux'
          ;;(!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me)))
          )
         )]

      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(,e1 ,e2) expr)
         (symbolo x)
         (!-/evalo-lazy-nocont-aux gamma env e1
                                 `(-> ,t ,type)
                                 `(closure (,x) ,body ,gamma^ ,env^))
         (!-/evalo-lazy-nocont-aux gamma env e2 t arg)
         (!-/evalo-lazy-nocont-aux `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val))]
      [(fresh (e1 e2 e3 t2 t3 x y body arg2 arg3 gamma^ env^ some-gamma)
         (== `(,e1 ,e2, e3) expr)
         (symbolo x)
         (symbolo y)
         (!-/evalo-lazy-nocont-aux gamma env e1
                                 `(-> ,t2 (-> t3 ,type))
                                 `(closure (,x) (lambda (,y) ,body) ,gamma^ ,env^))
         (!-/evalo-lazy-nocont-aux gamma env e2 t2 arg2)
         (!-/evalo-lazy-nocont-aux gamma env e3 t3 arg3)
         (!-/evalo-lazy-nocont-aux `((,x (mono ,t2)) . ((,y (mono ,t3)) . ,gamma^)) `((,x (val ,arg2)) . ((,y (val ,arg3)) . ,env^)) body type val))]

      )))


(define !-/evalo-lazy-nocont
  (lambda (gamma env expr type val)
      (fresh ()
        (!-/evalo-lazy-nocont-aux gamma env expr type val)
        (!-o gamma expr type)
        )
      ))


; 値から逆算的に決めているから、if 文は evaluator でも推論しやすい
; #t にならないといけない -> #t になる値を探す

;; どういうものが求めにくい？
;; int list -> cons( int * int list ) みたいなやつかな

(time
 (test "append-eval-only-curried-cons-no-list-13"
   (run 1 (prog)
     (fresh (q r s)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) ((append (cdr l)) s)))))
           prog)
       (evalo '()
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))


(time
 (test "append-infer-and-eval-curried-cons-no-list-13"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) ((append (cdr l)) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh ()
              (!-o '()
                   expr
                   '(list (list int)))
              (evalo '()
                     expr
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil)))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

(time
 (test "append-eval-and-infer-curried-cons-no-list-13"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) ((append (cdr l)) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh ()
              (evalo '()
                     expr
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))
              (!-o '()
                   expr
                   '(list (list int)))
              )))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))





(time
 (test "append-eval/infer-curried-cons-no-list-13"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) ((append (cdr l)) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh () (!-/evalo-lazy-cont '() '()
                     expr
                     '(list (list int))
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))
              )))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

;;

(time
 (test "append-eval-only-uncurried-cons-no-list-13"
   (run 1 (prog)
     (fresh (q r s)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) (append (cdr l) s)))))
           prog)
       (evalo '()
              `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))


(time
 (test "append-infer-and-eval-uncurried-cons-no-list-13"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) (append (cdr l) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh ()
              (!-o '()
                   expr
                   '(list (list int)))
              (evalo '()
                     expr
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil)))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))

(time
 (test "append-eval-and-infer-uncurried-cons-no-list-13"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) (append (cdr l) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh ()
              (evalo '()
                     expr
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))
              (!-o '()
                   expr
                   '(list (list int)))
              )))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))



(time
 (test "append-eval/infer-uncurried-cons-no-list-13"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) (append (cdr l) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh () (!-/evalo-lazy-cont '() '()
                     expr
                     '(list (list int))
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))
              )))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))


;;

(time
 (test "append-eval-only-curried-cons-no-list-14"
   (run 1 (prog)
     (fresh (q r s)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) ((append (cdr l)) s)))))
           prog)
       (evalo '()
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

#|
(time
 (test "append-infer-and-eval-curried-cons-no-list-14"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) ((append (cdr l)) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh ()
              (!-o '()
                   expr
                   '(list (list int)))
              (evalo '()
                     expr
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil)))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))
|#

(time
 (test "append-eval-and-infer-curried-cons-no-list-14"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) ((append (cdr l)) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh ()
              (evalo '()
                     expr
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))
              (!-o '()
                   expr
                   '(list (list int)))
              )))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))





(time
 (test "append-eval/infer-curried-cons-no-list-14"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) ((append (cdr l)) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh () (!-/evalo-lazy-cont '() '()
                     expr
                     '(list (list int))
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))
              )))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

(time
 (test "append-eval-only-uncurried-cons-no-list-14"
   (run 1 (prog)
     (fresh (q r s)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) (append (cdr l) s)))))
           prog)
       (evalo '()
              `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))


#|
(time
 (test "append-infer-and-eval-uncurried-cons-no-list-with-append-14"
   (run 1 (prog)
     (fresh (q r s expr clos)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)       
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) (append (cdr l) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh ()
              (!-o '()
                   expr
                   `(list (list int)))
              (evalo '()
                     expr
                     '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil)))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))
|#


(time
 (test "append-eval-and-infer-uncurried-cons-no-list-14"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) (append (cdr l) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (fresh () (!-/evalo-lazy-cont '() '()
                     expr
                     '(list (list int))
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))
              )))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))

#|
(time
 (test "append-infer-and-eval-uncurried-cons-no-list-14"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) (append (cdr l) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (!-/evalo '() '()
              expr
              '(list (list int))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))
|#

(time
 (test "append-infer/eval-lazy-uncurried-cons-no-list-14"
   (run 1 (prog)
     (fresh (q r s expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s (car l) (append (cdr l) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
           expr)
       (!-/evalo-lazy-cont '() '()
              expr
              '(list (list int))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))

; test programs by Tsushima
; checking for evalo
#|
(time
 (test "test"
   (run 1 (dfn)
        (== dfn `(cons 2 nil))
        (evalo '() dfn '(cons 4 nil)))
   '((cons 2 nil))))
|#
;; current

(time
 (test "map-eval-only-uncurried-18"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (f)
              (lambda (l)
                (if (null? l)
                    nil
                    (cons (f ,q) (map ,r (cdr l)))))) ;(map f ,s)
           prog)
       (evalo '()
              `(let-poly ((map ,prog))
                 (cons (map (lambda (k) (cons k nil))
                            nil)
                       (cons (map (lambda (k) (cons 1 nil))
                                  (cons 3 nil))
                             (cons (map (lambda (k) (cons k nil))
                                        (cons 1 (cons 2 (cons 3 nil))))
                                   nil))))
              `(cons nil
                     (cons (cons (cons 1 nil) nil)
                           (cons (cons (cons 1 nil)
                                       (cons (cons 2 nil) (cons (cons 3 nil) nil)))
                                 nil))))))
   `((lambda (f)
       (lambda (l)
         (if (null? l)
             nil
             (cons (f (car l)) (map f (cdr l)))))))))

#|
(time
 (test "map-infer-evalo-18"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (f)
         (lambda (l)
            (if (null? l)
             nil
             (cons (f ,q) (map ,r (cdr l))))))
           prog)
       (!-o '() 
              `(let-poly ((map ,prog))
                 (cons (map (lambda (k) (cons k nil)) nil)(cons
                  (map (lambda (k) (cons 1 nil)) (cons 3 nil))
                  (cons (map (lambda (k) (cons k nil)) (cons 1 (cons 2 (cons 3 nil))))
                       nil))))
              `(list (list (list int))))))
   `((lambda (f)
         (lambda (l)
            (if (null? l)
             nil
             (cons (f (car l)) (map f (cdr l)))))))))
|#

(time
 (test "map-eval/infer-uncurried-18"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (f)
              (lambda (l)
                (if (null? l)
                    nil
                    (cons (f ,q) (map ,r (cdr l))))))
           prog)
       (!-/evalo-lazy-cont '() '() 
                           `(let-poly ((map ,prog))
                              (cons (map (lambda (k) (cons k nil))
                                         nil)
                                    (cons (map (lambda (k) (cons 1 nil))
                                               (cons 3 nil))
                                          (cons (map (lambda (k) (cons k nil))
                                                     (cons 1 (cons 2 (cons 3 nil))))
                                                nil))))
                           `(list (list (list int)))
                           `(cons nil
                                  (cons (cons (cons 1 nil) nil)
                                        (cons (cons (cons 1 nil)
                                                    (cons (cons 2 nil) (cons (cons 3 nil) nil)))
                                              nil))))))
   `((lambda (f)
       (lambda (l)
         (if (null? l)
             nil
             (cons (f (car l)) (map f (cdr l)))))))))

(time
 (test "map-!-/evalo-lazy-nocont-uncurried-18"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (f)
              (lambda (l)
                (if (null? l)
                    nil
                    (cons (f ,q) (map ,r (cdr l))))))
           prog)
       (!-/evalo-lazy-nocont '() '() 
                             `(let-poly ((map ,prog))
                                (cons (map (lambda (k) (cons k nil))
                                           nil)
                                      (cons (map (lambda (k) (cons 1 nil))
                                                 (cons 3 nil))
                                            (cons (map (lambda (k) (cons k nil))
                                                       (cons 1 (cons 2 (cons 3 nil))))
                                                  nil))))
                             `(list (list (list int)))
                             `(cons nil
                                    (cons (cons (cons 1 nil) nil)
                                          (cons (cons (cons 1 nil)
                                                      (cons (cons 2 nil) (cons (cons 3 nil) nil)))
                                                nil))))))
   `((lambda (f)
       (lambda (l)
         (if (null? l)
             nil
             (cons (f (car l)) (map f (cdr l)))))))))



#|
(time
 (test "map-eval/infer-18"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (f)
         (lambda (l)
            (if (null? l)
             nil
             (cons (f ,q) (map ,r ,s)))))
           prog)
       (!-/evalo-lazy-cont '() '() 
              `(let-poly ((map ,prog))
                 (map (lambda (k) (cons k nil)) (cons 1 (cons 2 nil))))
              `(list (list int))
              `(cons (cons 1 nil) (cons (cons 2 nil) nil))
              )))
   `((lambda (f)
         (lambda (l)
            (if (null? l)
             nil
             (cons (f (car l)) (map f (cdr l)))))))))
|#



#|
(time
 (test "append-eval-and-infer-curried-cons-no-list17"
   (run 1 (prog)
     (fresh (q r s k l expr)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons (car l) ((append (cdr l)) s)))))
           prog)
       (== `(let-poly ((append ,prog))
                          (cons ((append nil) nil)
                                (cons ((append (cons 1 nil)) (cons 2 nil))
                                      (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                            nil))))
           expr)
       (fresh ()
              (evalo '() 
                     expr
                     '(cons nil
                            (cons (cons 1 (cons 2 nil))
                                  (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))
        ;;(!-o expr '() '(list (list int)))
        )))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))
|#


#|
(time
 (test "append-infer/eval-curried-cons-no-list-all-def18"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,s ,k ((append ,l) s)))))
           prog)
       (!-/evalo '() '()
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(list (list int))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))




(if ,q
                    ,r
                    (,s ,k ((append ,l) s)))
|#



(time
 (test "append-eval-only-curried-cons-no-list-17"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,k ,s ((append (cdr l)) ,l)))))
           prog)
       (evalo '() 
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))


(time
 (test "append-eval-only-uncurried-cons-no-list-17"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,k ,s (append (cdr l) ,l)))))
           prog)
       (evalo '() 
              `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))


(time
 (test "append-infer-lazy/eval-curried-cons-no-list17"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,k ,s ((append (cdr l)) ,l)))))
           prog)
       (!-/evalo-lazy-cont '() '()
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(list (list int))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

(time
 (test "append-infer-lazy/eval-uncurried-cons-no-list17"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (,k ,s (append (cdr l) ,l)))))
           prog)
       (!-/evalo-lazy-cont '() '()
              `(let-poly ((append ,prog))
                 (cons (append nil nil)
                       (cons (append (cons 1 nil) (cons 2 nil))
                             (cons (append (cons 3 (cons 4 nil)) (cons 5 (cons 6 nil)))
                                   nil))))
              '(list (list int))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) (append (cdr l) s))))))))


;;




(time
 (test "append-eval-only-curried-cons-no-list-all-def17.5"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons ,s ((append (cdr l)) s)))))
           prog)
       (evalo '() 
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

(time
 (test "append-infer-lazy/eval-curried-cons-no-list-all-def17.5"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons ,s ((append (cdr l)) s)))))
           prog)
       (!-/evalo-lazy-cont '() '()
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(list (list int))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

(time
 (test "append-eval-only-curried-cons-no-list-all-def17.7"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons ,s ((append (cdr ,k)) s)))))
           prog)
       (evalo '() 
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

(time
 (test "append-infer-lazy/eval-curried-cons-no-list-all-def17.7"
   (run 1 (prog)
     (fresh (q r s k l)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (s)
                (if ,q
                    ,r
                    (cons ,s ((append (cdr ,k)) s)))))
           prog)
       (!-/evalo-lazy-cont '() '()
              `(let-poly ((append ,prog))
                 (cons ((append nil) nil)
                       (cons ((append (cons 1 nil)) (cons 2 nil))
                             (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                   nil))))
              '(list (list int))
              '(cons nil
                     (cons (cons 1 (cons 2 nil))
                           (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                 nil))))))
   '((lambda (l)
       (lambda (s)
         (if (null? l)
             s
             (cons (car l) ((append (cdr l)) s))))))))

#|
(time
 (test "append-eval-only-curried-cons-no-list-19"
   (run 1 (prog)
     (fresh (q r s)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
              (lambda (f)
                (if (null? l)
                    l
                    (cons (@ f (car l)) (@ ((@ map f) (cdr l)))))))
           prog)
       (evalo '()
              `(let-poly ((map ,prog))
                (cons (@ (@ map (lambda (x) (cons x nil))) nil)
                    (cons (@ (@ map (lambda (x) (cons x nil))) (cons 1 nil)) nil)))
              '(cons nil
                    (cons (cons 1 nil) nil)))))
   '((lambda (l)
       (lambda (f)
         (if (null? l)
             l
             (cons (@ f (car l)) (@ (@ map f) (cdr l)))))))))
|#

#|
(time
 (test "func-apply-eval-only-curried-cons-no-list-19"
   (run 1 (prog)
     (fresh (q r s)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== `(lambda (l)
                (if (null? l)
                    ,q
                    (cons (@ (lambda (x) (cons x nil)) ,s) (@ map (cdr l)))))
           prog)
       (evalo '()
              `(let-poly ((map ,prog))
                (cons (@ map nil)
                    (cons (@ map (cons 1 nil))
                          (cons (@ map (cons 1 (cons 2 nil)))) ; 
                          nil)))
              `(cons nil
                    (cons (cons (cons 1 nil) nil)
                          (cons (cons (cons 1 nil) (cons (cons 2 nil) nil) nil) nil)))))) ; [1] :: ([2] :: [])
   '((lambda (l)
         (if (null? l)
             nil
             (cons (@ (lambda (x) (cons x nil)) (car l)) (@ map (cdr l))))))))
|#






#|
(time
 (test "append/else-part with evalo"
   (run 1 (prog)
     (fresh (dfn)
        (absento 1 dfn)
        (absento 2 dfn)
        (absento 3 dfn)
        (absento 4 dfn)
        (absento 5 dfn)
        (absento 6 dfn)
        (== prog `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons ,dfn
                                              (@ (@ append (cdr l)) s)))))))
                       (@ (@ append (cons 3 (cons 4 nil))) (cons 2 nil))))
     (evalo '()
            prog
            '(cons 3 (cons 4 (cons 2 nil))))))
   '((car l))))
|#

#|
(time
 (test "append/result with evalo"
   (run 1 (result)
     (fresh (prog)
       (absento 1 prog)
       (absento 2 prog)
       (absento 3 prog)
       (absento 4 prog)
       (absento 5 prog)
       (absento 6 prog)
       (== prog `(let-poly ((append (lambda (l)
                                     (lambda (s)
                                       (if (null? l) s
                                           (cons (car l)
                                                 (@ (@ append (cdr l)) s)))))))
               (@ (@ append (cons 3 (cons 4 nil))) (cons 2 nil))))
     (evalo '()
            prog
            result)))
   '((car l))))


(time
 (test "append/then-part with evalo"
   (run 1 (dfn)
        (evalo '()
               `(let-poly ((append (lambda (l)
                                     (lambda (s)
                                       (if (null? l) ,dfn
                                           (cons (car l)
                                                 (@ (@ append (cdr l)) s)))))))
               (@ (@ append (cons 3 (cons 4 nil))) (cons 2 nil)))
               `(cons 3 (cons 4 (cons 2 nil)))))))

; test-append-else-hole with evalo 8.2s くらいかかる。
(time
(run 1 (dfn) (evalo '()
               `(let-poly ((append (lambda (l)
                                     (lambda (s)
                                       (if (null? l) s
                                           ,dfn)))))
               (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 2 nil))
                     (cons (@ (@ append (cons 2 (cons 3 nil))) nil)
                           nil))
                     ) `(cons (cons 3 (cons 4 (cons 2 nil)))
                              (cons (cons 2 (cons 3 nil)) nil)))))

; test-append-else-hole with !-/evalo 結果は返ってこない (少なくとも 1分以上)
; then 部分 -> dfn は正しく動くので、プログラムはあってるはず
(time
(run 1 (dfn) (!-/evalo '() '()
               `(let-poly ((append (lambda (l)
                                     (lambda (s)
                                       (if (null? l) s
                                           ,dfn)))))
               (cons (@ (@ append (cons 3 (cons 4 nil))) (cons 2 nil))
                     (cons (@ (@ append (cons 2 (cons 3 nil))) nil)
                           nil)))
               `(list (list int))
                       `(cons
                         (cons 3 (cons 4 (cons 2 nil)))
                         (cons (cons 2 (cons 3 nil))
                               nil)))))

; test programs by Tsushima
; checking for !-/evalo 

(run 1 (dfn) (!-/evalo '() '()
               `(let-poly ((append (lambda (l)
                                     (lambda (s)
                                       (if (null? l) s
                                           (cons ,dfn
                                                 (@ (@ append (cdr l)) s)))))))
               (@ (@ append (cons 3 (cons 4 nil))) (cons 2 nil))) `(list int) `(cons 3 (cons 4 (cons 2 nil)))))

(run 1 (result) (!-/evalo '() '()
               `(let-poly ((append (lambda (l)
                                     (lambda (s)
                                       (if (null? l) s
                                           (cons (car l)
                                                 (@ (@ append (cdr l)) s)))))))
               (@ (@ append (cons 3 (cons 4 nil))) (cons 2 nil))) `(list int) `(cons 3 ,result)))

(run 1 (dfn) (!-/evalo '() '()
               `(let-poly ((append (lambda (l)
                                     (lambda (s)
                                       (if (null? l) ,dfn
                                           (cons (car l)
                                                 (@ (@ append (cdr l)) s)))))))
               (@ (@ append (cons 3 (cons 4 nil))) (cons 2 nil))) `(list int) `(cons 3 (cons 4 (cons 2 nil)))))

|#
