;#lang racket

;;; Relational type inferencer/evaluator for a subset of an ML-like language,
;;; using s-expression syntax.

;;; Trying to combine type inferencer and evaluator for the same
;;; language, to improve synthesis performance.

;(require "faster-miniKanren/mk.rkt")


;;; Running in Chez rather than in Racket...
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
         (== `(,e1 ,e2) expr)
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
         (!-o `((,x (mono ,t)) . ,gamma) body t^))]
      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(,e1 ,e2) expr)
         (symbolo x)
         (!-/evalo gamma env e1 `(-> ,t ,type) `(closure (,x) ,body ,gamma^ ,env^))
         (!-/evalo gamma env e2 t arg)
         (!-/evalo `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val))])))





;; Use dynamic reordering of goals in procedure application, inspired by Greg Rosenbaltt's Barliman optimization.

;; Assumption used in 'lookup-!-/evalo-dynamic-application': !-/evalo-dynamic-application extends 'gamma' and
;; 'env' at the same time, with the same variable names, in the same
;; order (and similarly for the initial 'gamma' and 'env', if
;; non-empty).  Furthermore, we assume (val ,v) and (mono ,t) entries
;; occur together, as do (rec (lambda (,z) ,e)) and
;; (poly ,gamma^ (lambda (,z) ,e)) entries.
(define lookup-!-/evalo-dynamic-application
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
              ;; This is a call to '!-o', not a recursive call to 'lookup-!-/evalo-dynamic-application'
              (!-o gamma^ `(lambda (,z) ,e) type))])]
        [(=/= x y)
         (lookup-!-/evalo-dynamic-application rest-gamma rest-env x type val)]))))

;; Adapted from n-grams-for-synthesis/interp-app-optimization.scm,
;; written with Michael Ballantyne, which in turn was taken from Greg
;; Rosenblatt's Barliman optimizations.

(define-syntax let/vars
  (syntax-rules ()
    ((_ _ () body) body)
    ((_ _ () body ...) (begin body ...))
    ((_ st (qvar ...) body ...)
     (let ((scope (subst-scope (state-S st))))
       (let ((qvar (var scope)) ...)
         body ...)))))

(define (list-split-ground st xs)
  (let loop ((rprefix '()) (xs xs))
    (let ((tm (walk xs (state-S st))))
      (if (pair? tm)
        (loop (cons (walk (car tm) (state-S st)) rprefix) (cdr tm))
        (values rprefix xs)))))

(define (eval-randso gamma env expr type val)
  (conde
    ((== '() expr)
     (== '() val))
    ((fresh (a d t-a t-d v-a v-d)
       (== `(,a . ,d) expr)
       (== `(,t-a . ,t-d) type)
       (== `(,v-a . ,v-d) val)
       (!-/evalo-dynamic-application gamma env a t-a v-a)
       (eval-randso gamma env d t-d v-d)))))

(define (eval-!-/evalo-application gamma env rands t* a* body-goal)
  (define succeed unit)
  (lambdag@ (st)
    (let-values (((rrands rands-suffix) (list-split-ground st rands)))
      (let-values (((ggoals vgoals types-suffix args-suffix)
                    (let loop ((rands (reverse rrands))
                               (ggoals succeed)
                               (vgoals succeed)
                               (types t*)
                               (args a*))
                      (if (null? rands) (values ggoals vgoals types args)
                          (let ((rand (car rands)))
                            (let/vars st (types-rest args-rest)
                                      (let ((goal (fresh (arg typ)
                                                    (== `(,typ . ,types-rest) types)
                                                    (== `(,arg . ,args-rest) args)
                                                    (!-/evalo-dynamic-application gamma env rand typ arg))))
                                        (if (var? rand)
                                            (loop (cdr rands) ggoals (fresh () vgoals goal) types-rest args-rest)
                                            (loop (cdr rands) (fresh () ggoals goal) vgoals types-rest args-rest)))))))))
        ((fresh ()
           ggoals    ;; try ground arguments first
           body-goal ;; then the body
           vgoals    ;; then fill in unbound arguments
           ;; any unbound final segment of arguments
           (eval-randso gamma env rands-suffix types-suffix args-suffix)) st)))))

(define !-/evalo-dynamic-application
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
       (lookup-!-/evalo-dynamic-application gamma env expr type val)]
      [(fresh (e a v)
         (== `(null? ,e) expr)
         (== 'bool type)
         (conde
           [(== 'nil v) (== #t val)]
           [(=/= 'nil v) (== #f val)])
         (!-/evalo-dynamic-application gamma env e `(list ,a) v))]
      [(fresh (e a b)
         (== `(car ,e) expr)
         (== a type)
         (!-/evalo-dynamic-application gamma env e `(list ,a) `(cons ,val ,b)))]
      [(fresh (e a b)
         (== `(cdr ,e) expr)
         (== `(list ,a) type)
         (!-/evalo-dynamic-application gamma env e `(list ,a) `(cons ,b ,val)))]
      [(fresh (e v)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 v) (== #t val)]
           [(=/= 0 v) (== #f val)])
         (== 'bool type)
         (!-/evalo-dynamic-application gamma env e 'int v))]
      [(fresh (e1 e2 a t v1 v2)
         (== `(cons ,e1 ,e2) expr)
         (== `(list ,a) type)
         (== `(cons ,v1 ,v2) val)
         (!-/evalo-dynamic-application gamma env e2 `(list ,a) v2)
         (!-/evalo-dynamic-application gamma env e1 a v1))]
      [(fresh (e1 e2 t1 t2 v1 v2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,t1 ,t2) type)
         (== `(pair ,v1 ,v2) val)
         (!-/evalo-dynamic-application gamma env e1 t1 v1)
         (!-/evalo-dynamic-application gamma env e2 t2 v2))]
      [(fresh (e1 e2 e3 v1 v2 v3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (!-/evalo-dynamic-application gamma env e1 'bool v1)
         (conde
           [(== #t v1) (== v2 val) (!-/evalo-dynamic-application gamma env e2 type v2)]
           [(== #f v1) (== v3 val) (!-/evalo-dynamic-application gamma env e3 type v3)]))]
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
           ;; This is a call to '!-o', not a recursive call to '!-/evalo-dynamic-application'
           (!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
         
         (!-/evalo-dynamic-application
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
         ;; This is a call to '!-o', not a recursive call to '!-/evalo-dynamic-application'
         (!-o `((,x (mono ,t)) . ,gamma) body t^))]
      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(,e1 ,e2) expr)
         (symbolo x)
         (!-/evalo-dynamic-application gamma env e1 `(-> ,t ,type) `(closure (,x) ,body ,gamma^ ,env^))

         (eval-!-/evalo-application gamma env (list e2) (list t) (list arg)
                                    (!-/evalo-dynamic-application `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val))


         ;; now handled in 'eval-!-/evalo-application'
         #|
         (!-/evalo-dynamic-application gamma env e2 t arg)
         (!-/evalo-dynamic-application `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val)
         |#
         
         )])))






;; Try to be "less dumb" by avoiding (car (cons ...)), ((lambda ...) ...), etc.

;; Assumption used in 'lookup-!-/evalo-less-dumb': !-/evalo-less-dumb extends 'gamma' and
;; 'env' at the same time, with the same variable names, in the same
;; order (and similarly for the initial 'gamma' and 'env', if
;; non-empty).  Furthermore, we assume (val ,v) and (mono ,t) entries
;; occur together, as do (rec (lambda (,z) ,e)) and
;; (poly ,gamma^ (lambda (,z) ,e)) entries.
(define lookup-!-/evalo-less-dumb
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
              ;; This is a call to '!-o', not a recursive call to 'lookup-!-/evalo-less-dumb'
              (!-o gamma^ `(lambda (,z) ,e) type))])]
        [(=/= x y)
         (lookup-!-/evalo-less-dumb rest-gamma rest-env x type val)]))))

(define !-/evalo-less-dumb
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
       (lookup-!-/evalo-less-dumb gamma env expr type val)]
      [(fresh (e a v)
         (== `(null? ,e) expr)
         (== 'bool type)
         (conde
           [(== 'nil v) (== #t val)]
           [(=/= 'nil v) (== #f val)])
         (!-/evalo-less-dumb gamma env e `(list ,a) v))]
      [(fresh (e a b)
         (== `(car ,e) expr)
         (== a type)
         
         ;; be less dumb (hopefully)
         (conde
           [(symbolo e)]
           [(fresh (e1 e2)
              (== `(,e1 . ,e2) e)
              (=/= 'cons e1))])
         
         (!-/evalo-less-dumb gamma env e `(list ,a) `(cons ,val ,b)))]
      [(fresh (e a b)
         (== `(cdr ,e) expr)
         
         ;; be less dumb (hopefully)
         (conde
           [(symbolo e)]
           [(fresh (e1 e2)
              (== `(,e1 . ,e2) e)
              (=/= 'cons e1))])
         
         (== `(list ,a) type)
         (!-/evalo-less-dumb gamma env e `(list ,a) `(cons ,b ,val)))]
      [(fresh (e v)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 v) (== #t val)]
           [(=/= 0 v) (== #f val)])
         (== 'bool type)
         (!-/evalo-less-dumb gamma env e 'int v))]
      [(fresh (e1 e2 a t v1 v2)
         (== `(cons ,e1 ,e2) expr)
         (== `(list ,a) type)
         (== `(cons ,v1 ,v2) val)
         (!-/evalo-less-dumb gamma env e2 `(list ,a) v2)
         (!-/evalo-less-dumb gamma env e1 a v1))]
      [(fresh (e1 e2 t1 t2 v1 v2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,t1 ,t2) type)
         (== `(pair ,v1 ,v2) val)
         (!-/evalo-less-dumb gamma env e1 t1 v1)
         (!-/evalo-less-dumb gamma env e2 t2 v2))]
      [(fresh (e1 e2 e3 v1 v2 v3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (!-/evalo-less-dumb gamma env e1 'bool v1)
         (conde
           [(== #t v1) (== v2 val) (!-/evalo-less-dumb gamma env e2 type v2)]
           [(== #f v1) (== v3 val) (!-/evalo-less-dumb gamma env e3 type v3)]))]
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
           ;; This is a call to '!-o', not a recursive call to '!-/evalo-less-dumb'
           (!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
         
         (!-/evalo-less-dumb
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
         ;; This is a call to '!-o', not a recursive call to '!-/evalo-less-dumb'
         (!-o `((,x (mono ,t)) . ,gamma) body t^))]
      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(,e1 ,e2) expr)
         (symbolo x)

         ;; be less dumb (hopefully)
         (conde
           [(symbolo e1)]
           [(fresh (e11 e12)
              (== `(,e11 . ,e12) e1)
              (=/= 'lambda  e12))])
         
         (!-/evalo-less-dumb gamma env e1 `(-> ,t ,type) `(closure (,x) ,body ,gamma^ ,env^))
         (!-/evalo-less-dumb gamma env e2 t arg)
         (!-/evalo-less-dumb `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val))])))










;;; Try insisting on caniconical forms in expressions.

;; Assumption used in 'lookup-!-/evalo-canonical': !-/evalo-canonical extends 'gamma' and
;; 'env' at the same time, with the same variable names, in the same
;; order (and similarly for the initial 'gamma' and 'env', if
;; non-empty).  Furthermore, we assume (val ,v) and (mono ,t) entries
;; occur together, as do (rec (lambda (,z) ,e)) and
;; (poly ,gamma^ (lambda (,z) ,e)) entries.
(define lookup-!-/evalo-canonical
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
              ;; This is a call to '!-o', not a recursive call to 'lookup-!-/evalo-canonical'
              (!-o gamma^ `(lambda (,z) ,e) type))])]
        [(=/= x y)
         (lookup-!-/evalo-canonical rest-gamma rest-env x type val)]))))

(define !-/evalo-canonical
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
       (lookup-!-/evalo-canonical gamma env expr type val)]
      [(fresh (e a v)
         (== `(null? ,e) expr)
         (== 'bool type)
         (conde
           [(== 'nil v) (== #t val)]
           [(=/= 'nil v) (== #f val)])
         (!-/evalo-canonical gamma env e `(list ,a) v))]
      [(fresh (e a b)
         (== `(car ,e) expr)
         (== a type)
         (!-/evalo-canonical gamma env e `(list ,a) `(cons ,val ,b)))]
      [(fresh (e a b)
         (== `(cdr ,e) expr)
         (== `(list ,a) type)
         (!-/evalo-canonical gamma env e `(list ,a) `(cons ,b ,val)))]
      [(fresh (e v)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 v) (== #t val)]
           [(=/= 0 v) (== #f val)])
         (== 'bool type)
         (!-/evalo-canonical gamma env e 'int v))]
      [(fresh (e1 e2 a t v1 v2)
         (== `(cons ,e1 ,e2) expr)
         (== `(list ,a) type)
         (== `(cons ,v1 ,v2) val)
         (!-/evalo-canonical gamma env e2 `(list ,a) v2)
         (!-/evalo-canonical gamma env e1 a v1))]
      [(fresh (e1 e2 t1 t2 v1 v2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,t1 ,t2) type)
         (== `(pair ,v1 ,v2) val)
         (!-/evalo-canonical gamma env e1 t1 v1)
         (!-/evalo-canonical gamma env e2 t2 v2))]
      [(fresh (e1 e2 e3 v1 v2 v3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (!-/evalo-canonical gamma env e1 'bool v1)
         (conde
           [(== #t v1) (== v2 val) (!-/evalo-canonical gamma env e2 type v2)]
           [(== #f v1) (== v3 val) (!-/evalo-canonical gamma env e3 type v3)]))]
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
           ;; This is a call to '!-o', not a recursive call to '!-/evalo-canonical'
           (!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
         
         (!-/evalo-canonical
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
         ;; This is a call to '!-o', not a recursive call to '!-/evalo-canonical'
         (!-o `((,x (mono ,t)) . ,gamma) body t^))]
      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(,e1 ,e2) expr)
         (symbolo x)

         ;; Canonical form: disallow 'lambda' inside 'e1'
         (absento 'lambda e1)
         
         (!-/evalo-canonical gamma env e1 `(-> ,t ,type) `(closure (,x) ,body ,gamma^ ,env^))
         (!-/evalo-canonical gamma env e2 t arg)
         (!-/evalo-canonical `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val))])))







;; Assumption used in 'lookup-!-/evalo-lazy': !-/evalo-lazy extends 'gamma' and
;; 'env' at the same time, with the same variable names, in the same
;; order (and similarly for the initial 'gamma' and 'env', if
;; non-empty).  Furthermore, we assume (val ,v) and (mono ,t) entries
;; occur together, as do (rec (lambda (,z) ,e)) and
;; (poly ,gamma^ (lambda (,z) ,e)) entries.
(define lookup-!-/evalo-lazy
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
              ;; This is a call to '!-o', not a recursive call to 'lookup-!-/evalo-lazy'
              (!-o gamma^ `(lambda (,z) ,e) type)

              )])]
        [(=/= x y)
         (lookup-!-/evalo-lazy rest-gamma rest-env x type val)]))))

(define !-/evalo-lazy
  (lambda (gamma env expr type val)
    (fresh ()
      ;; be lazy about type inference--only perform type inference
      ;; when also doing evaluation of 'expr'
      (!-/evalo-lazy-aux gamma env expr type val)
      ;; make sure we finally check that the entire expression is well-typed
      (!-o gamma expr type))))

(define !-/evalo-lazy-aux
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
       (lookup-!-/evalo-lazy gamma env expr type val)]
      [(fresh (e a v)
         (== `(null? ,e) expr)
         (== 'bool type)
         (conde
           [(== 'nil v) (== #t val)]
           [(=/= 'nil v) (== #f val)])
         (!-/evalo-lazy-aux gamma env e `(list ,a) v))]
      [(fresh (e a b)
         (== `(car ,e) expr)
         (== a type)
         (!-/evalo-lazy-aux gamma env e `(list ,a) `(cons ,val ,b)))]
      [(fresh (e a b)
         (== `(cdr ,e) expr)
         (== `(list ,a) type)
         (!-/evalo-lazy-aux gamma env e `(list ,a) `(cons ,b ,val)))]
      [(fresh (e v)
         (== `(zero? ,e) expr)
         (conde
           [(== 0 v) (== #t val)]
           [(=/= 0 v) (== #f val)])
         (== 'bool type)
         (!-/evalo-lazy-aux gamma env e 'int v))]
      [(fresh (e1 e2 a t v1 v2)
         (== `(cons ,e1 ,e2) expr)
         (== `(list ,a) type)
         (== `(cons ,v1 ,v2) val)
         (!-/evalo-lazy-aux gamma env e2 `(list ,a) v2)
         (!-/evalo-lazy-aux gamma env e1 a v1))]
      [(fresh (e1 e2 t1 t2 v1 v2)
         (== `(pair ,e1 ,e2) expr)
         (== `(pair ,t1 ,t2) type)
         (== `(pair ,v1 ,v2) val)
         (!-/evalo-lazy-aux gamma env e1 t1 v1)
         (!-/evalo-lazy-aux gamma env e2 t2 v2))]
      [(fresh (e1 e2 e3 v1 v2 v3)
         (== `(if ,e1 ,e2 ,e3) expr)
         (!-/evalo-lazy-aux gamma env e1 'bool v1)
         (conde
           [(== #t v1) (== v2 val) (!-/evalo-lazy-aux gamma env e2 type v2)]
           [(== #f v1) (== v3 val) (!-/evalo-lazy-aux gamma env e3 type v3)]))]
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
           ;; This is a call to '!-o', not a recursive call to '!-/evalo-lazy-aux'
           (!-o `((,f (mono ,forget-me)) . ,gamma) `(lambda (,z) ,e) forget-me))
         |#
         
         (!-/evalo-lazy-aux
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

         ;; Be lazy!  Don't worry about the type of the body yet!
         ;; We'll make sure the body is well typed in a separate call to '!-o'.
         ;;         
         #|
         ;; This is a call to '!-o', not a recursive call to '!-/evalo-lazy-aux'
         (!-o `((,x (mono ,t)) . ,gamma) body t^)
         |#

         )]
      [(fresh (e1 e2 t x body arg gamma^ env^ some-gamma)
         (== `(,e1 ,e2) expr)
         (symbolo x)
         (!-/evalo-lazy-aux gamma env e1 `(-> ,t ,type) `(closure (,x) ,body ,gamma^ ,env^))
         (!-/evalo-lazy-aux gamma env e2 t arg)
         (!-/evalo-lazy-aux `((,x (mono ,t)) . ,gamma^) `((,x (val ,arg)) . ,env^) body type val))])))





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
       (!-o '()
            expr
            '(list (list int)))
       (evalo '()
              expr
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
 (test "append-infer-and-eval-curried-cons-no-list-with-append-14"
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
                    (,s (car l) ((append (cdr l)) s)))))
           prog)
       (== `(let-poly ((append ,prog))
              (pair append
                    (cons ((append nil) nil)
                          (cons ((append (cons 1 nil)) (cons 2 nil))
                                (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                      nil)))))
           expr)
       (!-o '()
            expr
            `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int))))
       (evalo '()
              expr
              `(pair (closure . ,clos)
                     (cons nil
                           (cons (cons 1 (cons 2 nil))
                                 (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                       nil)))))))
   '((lambda (l) (lambda (s) (if (null? l) s (cons (car l) ((append (cdr l)) s))))))))

(time
 (test "append-eval-only-curried-cons-no-list-15"
   (run 1 (prog)
      (fresh (q r s t)
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
                     (,s (car l) ((append ,t) s)))))
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
 (test "append-infer-and-eval-curried-cons-no-list-with-append-15"
   (run 1 (prog)
     (fresh (q r s t expr clos)
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
                    (,s (car l) ((append ,t) s)))))
           prog)
       (== `(let-poly ((append ,prog))
              (pair append
                    (cons ((append nil) nil)
                          (cons ((append (cons 1 nil)) (cons 2 nil))
                                (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                      nil)))))
           expr)
       (!-o '()
            expr
            `(pair (-> (list int) (-> (list int) (list int)))
                   (list (list int))))
       (evalo '()
              expr
              `(pair (closure . ,clos)
                     (cons nil
                           (cons (cons 1 (cons 2 nil))
                                 (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                                       nil)))))))
   '((lambda (l) (lambda (s) (if (null? l) s (cons (car l) ((append (cdr l)) s))))))))


(time
 (test "append-eval-only-curried-cons-no-list-15.5"
   (run 1 (prog)
      (fresh (q r s t)
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
                     (,s (car l) (,t s)))))
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
 (test "append-eval-only-curried-cons-no-list-16"
   (run 1 (prog)
      (fresh (q r s t)
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
                     (,s (car l) ,t))))
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
|#

#|
(time
 (test "append-eval-only-curried-cons-no-list-18"
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
                 ,q))
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
|#

(test "reverse-forward"
  (run 1 (q)
    (evalo '()
           `(let-poly ((append (lambda (l)
                                 (lambda (s)
                                   (if (null? l) s
                                       (cons (car l)
                                             ((append (cdr l)) s)))))))
              (let-poly ((reverse (lambda (xs)
                                    (if (null? xs)
                                        nil
                                        ((append (reverse (cdr xs))) (cons (car xs) nil))))))
                (cons (reverse nil)
                      (cons (reverse (cons 1 nil))
                            (cons (reverse (cons 2 (cons 3 nil)))
                                  (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                        nil))))))
           q))    
  '((cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil))))))

(test "reverse-1"
  (run 1 (defn)
    (fresh (q r s)
      (absento 1 defn)
      (absento 2 defn)
      (absento 3 defn)
      (absento 4 defn)
      (absento 5 defn)
      (absento 6 defn)

      (== `(lambda (xs)
             (if (null? xs)
                 nil
                 ((,q (reverse ,r)) ,s)))
          defn)
         
      (== 'append q)
      (== '(cdr xs) r)
      (== '(cons (car xs) nil) s)
      
      (evalo '()
             `(let-poly ((append (lambda (l)
                                   (lambda (s)
                                     (if (null? l) s
                                         (cons (car l)
                                               ((append (cdr l)) s)))))))
                (let-poly ((reverse ,defn))
                  (cons (reverse nil)
                        (cons (reverse (cons 1 nil))
                              (cons (reverse (cons 2 (cons 3 nil)))
                                    (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                          nil))))))
             '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
  '((lambda (xs)
       (if (null? xs)
           nil
           ((append (reverse (cdr xs))) (cons (car xs) nil))))))

(test "reverse-illtyped-hole-synthesis-1a"
  (run 1 (defn)
    (fresh (q r s)
      (absento 1 defn)
      (absento 2 defn)
      (absento 3 defn)
      (absento 4 defn)
      (absento 5 defn)
      (absento 6 defn)

      (== `(lambda (xs)
             (if (null? xs)
                 nil
                 (((lambda (l) (lambda (s) ((append l) s))) (reverse (cdr xs))) (cons (car xs) nil))))
          defn)
      
      (evalo '()
             `(let-poly ((append (lambda (l)
                                   (lambda (s)
                                     (if (null? l) s
                                         (cons (car l)
                                               ((append (cdr l)) s)))))))
                (let-poly ((reverse ,defn))
                  (cons (reverse nil)
                        (cons (reverse (cons 1 nil))
                              (cons (reverse (cons 2 (cons 3 nil)))
                                    (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                          nil))))))
             '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
  '((lambda (xs)
       (if (null? xs)
           nil
           (((lambda (l) (lambda (s) ((append l) s))) (reverse (cdr xs))) (cons (car xs) nil))))))

#|
(time
  (test "reverse-illtyped-simple-hole-synthesis-1e-with-type-only"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (cdr xs))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (!-o '()
             prog
             '(list (list int)))))
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) nil))))))
|#

(time
  (test "reverse-illtyped-simple-hole-synthesis-1e-with-type-and-eval"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (cdr xs))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (!-o '()
             prog
             '(list (list int)))
        (evalo '()
               prog
               '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))

#|
(time
  (test "reverse-illtyped-simple-hole-synthesis-1e-eval-only"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (cdr xs))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (evalo '()
               prog
               '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))
|#

(time
  (test "reverse-illtyped-simple-hole-synthesis-1f-with-type-and-eval"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (cdr ,r))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (!-o '()
             prog
             '(list (list int)))
        (evalo '()
               prog
               '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))

#|
(time
  (test "reverse-illtyped-simple-hole-synthesis-1f-eval-only"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (cdr ,r))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (evalo '()
               prog
               '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))
|#

(time
  (test "reverse-illtyped-simple-hole-synthesis-1g-with-type-and-eval"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (,s ,r))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (!-o '()
             prog
             '(list (list int)))
        (evalo '()
               prog
               '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))

#|
(time
  (test "reverse-illtyped-simple-hole-synthesis-1g-eval-only"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (,s ,r))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (evalo '()
               prog
               '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))
|#

(time
  (test "reverse-illtyped-simple-hole-synthesis-1g-with-type-and-eval-with-reverse"
    (run 1 (defn)
      (fresh (q r s prog clos)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (,s ,r))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (pair reverse
                       (cons (reverse nil)
                             (cons (reverse (cons 1 nil))
                                   (cons (reverse (cons 2 (cons 3 nil)))
                                         (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                               nil)))))))
            prog)

        (!-o '()
             prog
             `(pair (-> (list int) (list int))
                    (list (list int))))
        (evalo '()
               prog
               `(pair (closure . ,clos)
                      (cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil))))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))

(time
  (test "reverse-illtyped-simple-hole-synthesis-1h-with-type-and-eval"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse ,r)) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (!-o '()
             prog
             '(list (list int)))
        (evalo '()
               prog
               '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))

(time
  (test "reverse-illtyped-simple-hole-synthesis-1e-with-eval-only"
    (run 1 (defn)
      (fresh (q r s prog)
        (absento 1 defn)
        (absento 2 defn)
        (absento 3 defn)
        (absento 4 defn)
        (absento 5 defn)
        (absento 6 defn)

        (== `(lambda (xs)
               (if (null? xs)
                   nil
                   ((append (reverse (cdr xs))) ,q)))
            defn)

        (== `(let-poly ((append (lambda (l)
                                  (lambda (s)
                                    (if (null? l) s
                                        (cons (car l)
                                              ((append (cdr l)) s)))))))
               (let-poly ((reverse ,defn))
                 (cons (reverse nil)
                       (cons (reverse (cons 1 nil))
                             (cons (reverse (cons 2 (cons 3 nil)))
                                   (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                         nil))))))
            prog)

        (evalo '()
               prog
               '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
    '((lambda (xs)
        (if (null? xs)
            nil
            ((append (reverse (cdr xs))) (cons (car xs) nil)))))))

(test "reverse-illtyped-hole-synthesis-1b"
  (run 1 (defn)
    (fresh (q r s)
      (absento 1 defn)
      (absento 2 defn)
      (absento 3 defn)
      (absento 4 defn)
      (absento 5 defn)
      (absento 6 defn)

      (== `(lambda (xs)
             (if (null? xs)
                 nil
                 (((lambda (l) (lambda (s) (cons l s))) (reverse (cdr xs))) (cons (car xs) nil))))
          defn)
      
      (evalo '()
             `(let-poly ((append (lambda (l)
                                   (lambda (s)
                                     (if (null? l) s
                                         (cons (car l)
                                               ((append (cdr l)) s)))))))
                (let-poly ((reverse ,defn))
                  (cons (reverse nil)
                        (cons (reverse (cons 1 nil))
                              (cons (reverse (cons 2 (cons 3 nil)))
                                    (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                          nil))))))
             '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
  '())

(test "reverse-illtyped-hole-synthesis-1b-with-reverse"
  (run 1 (q)
    (fresh (defn r s prog clos)
      (absento 1 defn)
      (absento 2 defn)
      (absento 3 defn)
      (absento 4 defn)
      (absento 5 defn)
      (absento 6 defn)

      (== `(lambda (xs)
             (if (null? xs)
                 nil
                 (((lambda (l) (lambda (s) (cons l s))) (reverse (cdr xs))) (cons (car xs) nil))))
          defn)

      (== `(let-poly ((append (lambda (l)
                                (lambda (s)
                                  (if (null? l) s
                                      (cons (car l)
                                            ((append (cdr l)) s)))))))
             (let-poly ((reverse ,defn))
               (pair reverse
                     (cons (reverse nil)
                           (cons (reverse (cons 1 nil))
                                 (cons (reverse (cons 2 (cons 3 nil)))
                                       (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                             nil)))))))
          prog)
      
      (evalo '()
             prog
             `((pair (closure . ,clos)
                     (cons nil
                           (cons (cons nil (cons 1 nil))
                                 (cons (cons (cons nil (cons 3 nil)) (cons 2 nil))
                                       (cons (cons (cons (cons nil (cons 6 nil)) (cons 5 nil)) (cons 4 nil))
                                             nil)))))))))    
  '())

(test "reverse-illtyped-hole-synthesis-1d-with-reverse-does-this-really-work?"
  (run 1 (defn)
    (fresh (q r s prog clos)
      (absento 1 defn)
      (absento 2 defn)
      (absento 3 defn)
      (absento 4 defn)
      (absento 5 defn)
      (absento 6 defn)

      ;;(== '((append l) s) q)
      
      (== `(lambda (xs)
             (if (null? xs)
                 nil
                 (((lambda (l) (lambda (s) ,q)) (reverse (cdr xs))) (cons (car xs) nil))))
          defn)

      (== `(let-poly ((append (lambda (l)
                                (lambda (s)
                                  (if (null? l) s
                                      (cons (car l)
                                            ((append (cdr l)) s)))))))
             (let-poly ((reverse ,defn))
               (pair reverse
                     (cons (reverse nil)
                           (cons (reverse (cons 1 nil))
                                 (cons (reverse (cons 2 (cons 3 nil)))
                                       (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                             nil)))))))
          prog)

      (!-o '()
           prog
           '(pair (-> (list int) (list int))
                  (list (list int))))
      (evalo '()
             prog
             `(pair (closure . ,clos)
                    (cons nil
                          (cons (cons 1 nil)
                                (cons (cons 3 (cons 2 nil))
                                      (cons (cons 6 (cons 5 (cons 4 nil)))
                                            nil))))))))    
  '((lambda (xs) (if (null? xs) nil (((lambda (l) (lambda (s) ((append l) s))) (reverse (cdr xs))) (cons (car xs) nil))))))

(test "reverse-illtyped-hole-synthesis-1d"
  (run 1 (defn)
    (fresh (q r s prog)
      (absento 1 defn)
      (absento 2 defn)
      (absento 3 defn)
      (absento 4 defn)
      (absento 5 defn)
      (absento 6 defn)

      (== `(lambda (xs)
             (if (null? xs)
                 nil
                 (((lambda (l) (lambda (s) ,q)) (reverse (cdr xs))) (cons (car xs) nil))))
          defn)

      (== `(let-poly ((append (lambda (l)
                                (lambda (s)
                                  (if (null? l) s
                                      (cons (car l)
                                            ((append (cdr l)) s)))))))
             (let-poly ((reverse ,defn))
               (cons (reverse nil)
                     (cons (reverse (cons 1 nil))
                           (cons (reverse (cons 2 (cons 3 nil)))
                                 (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                       nil))))))
          prog)

      (!-o '()
           prog
           '(list (list int)))
      (evalo '()
             prog
             '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
  '())

(test "reverse-illtyped-hole-synthesis-1c"
  (run 1 (defn)
    (fresh (q r s)
      (absento 1 defn)
      (absento 2 defn)
      (absento 3 defn)
      (absento 4 defn)
      (absento 5 defn)
      (absento 6 defn)

      (== `(lambda (xs)
             (if (null? xs)
                 nil
                 (((lambda (l) (lambda (s) ,q)) (reverse (cdr xs))) (cons (car xs) nil))))
          defn)
      
      (evalo '()
             `(let-poly ((append (lambda (l)
                                   (lambda (s)
                                     (if (null? l) s
                                         (cons (car l)
                                               ((append (cdr l)) s)))))))
                (let-poly ((reverse ,defn))
                  (cons (reverse nil)
                        (cons (reverse (cons 1 nil))
                              (cons (reverse (cons 2 (cons 3 nil)))
                                    (cons (reverse (cons 4 (cons 5 (cons 6 nil))))
                                          nil))))))
             '(cons nil (cons (cons 1 nil) (cons (cons 3 (cons 2 nil)) (cons (cons 6 (cons 5 (cons 4 nil))) nil)))))))    
  '())




(test "!-/evalo-42-simple-run*"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append (cdr l1)) l2)))))))
             ((append nil) nil))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list _.0)
     nil
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       ((append nil) nil)))))


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
                                  (w w))))
                    5)
                 q))
  '())

(test "let-poly-type-2"
  (run* (q) (!-o '()
                 '(let-poly ((f (lambda (w)
                                  (w 3))))
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
  (run* (q) (!-o `() `((lambda (x) x) 3) q))
  '(int))

(test "10"
  (run* (q) (!-o `()
                 `(let-poly ((f (lambda (y) #f)))
                    (cons (f 3) (f #f)))
                 q))
  '())

(test "11"
  (run* (q) (!-o `()
                 `(let-poly ((f (lambda (y) y)))
                    (pair (f 3) (f #f)))
                 q))
  '((pair int bool)))

(test "12"
  (run* (q) (!-o `()
                 `((lambda (f)
                       (pair (f 3) (f #f)))
                     (lambda (y) y))
                 q))
  '())

(test "13"
  (run* (q) (!-o `()
                 `((lambda (f)
                       (pair (f 3) (f 4)))
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
                                                   ((append (cdr l1)) l2)))))))
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
                                                   ((append (cdr l1)) l2)))))))
                    (let-poly ((rev (lambda (l1)
                                      (if (null? l1)
                                          l1
                                          ((append (rev (cdr l1))) (cons (car l1) nil))))))
                      rev))
                 q))
  '((-> (list _.0) (list _.0))))

(test "22"
  (run* (q) (!-o `() `(lambda (f) (f f)) q))
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
                  `(x ,q)
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
                   `((lambda (x) x) 3)
                   q))
  '(3))

(test "32"
  (run* (q) (evalo `()
                   `(let-poly ((x (lambda (y) #f)))
                      (cons (x 3) (x #f)))
                   q))
  '((cons #f #f)))

(test "33"
  (run* (q) (evalo `()
                   `(let-poly ((f (lambda (y) y)))
                      (pair (f 3) (f #f)))
                   q))
  '((pair 3 #f)))

(test "34"
  (run* (q) (evalo `()
                   `(let-poly ((f (lambda (y) y)))
                      (pair (f 3) (f #f)))
                   q))
  '((pair 3 #f)))

(test "35"
  (run* (q) (evalo `()
                   `((lambda (f) (pair (f 3) (f #f))) (lambda (y) y))
                   q))
  '((pair 3 #f)))

(test "36"
  (run* (q) (evalo `()
                   `((lambda (f) (pair (f 3) (f 4))) (lambda (y) y))
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
                                                     ((append (cdr l1)) l2)))))))
                      ((append nil) nil))
                   q))
  '(nil))

(test "41"
  (run* (q) (evalo `()
                   `(let-poly ((append (lambda (l1)
                                         (lambda (l2)
                                           (if (null? l1)
                                               l2
                                               (cons (car l1)
                                                     ((append (cdr l1)) l2)))))))
                      ((append (cons 1 nil)) nil))
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
                                            ((append (cdr l1)) l2)))))))
             ((append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil))))
          expr)
      (!-o '() expr type)))
  '(((list int)
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       ((append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil)))))))

(test "42-value"
  (run* (q)
    (fresh (expr val)
      (== (list val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append (cdr l1)) l2)))))))
             ((append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil))))
          expr)
      (evalo '() expr val)))
  '(((cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       ((append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil)))))))

(test "42-type-and-value"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append (cdr l1)) l2)))))))
             ((append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil))))
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
                                      ((append (cdr l1)) l2)))))))
       ((append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil)))))))

(test "42-type-and-value-verify"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append (cdr l1)) l2)))))))
             ((append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil))))
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
                                      ((append (cdr l1)) l2)))))))
       ((append (cons 1 (cons 2 (cons 3 nil)))) (cons 4 (cons 5 nil)))))))



(test "43-type"
  (run* (q)
    (fresh (expr type)
      (== (list type expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append (cdr l1)) l2)))))))
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                               nil))))
          expr)
      (!-o '() expr type)))
  '(((list (list int))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       (cons ((append nil) nil)
             (cons ((append (cons 1 nil)) (cons 2 nil))
                   (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                            ((append (cdr l1)) l2)))))))
             (pair append
                   (cons ((append nil) nil)
                         (cons ((append (cons 1 nil)) (cons 2 nil))
                               (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                      ((append (cdr l1)) l2)))))))
       (pair append
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                            ((append (cdr l1)) l2)))))))
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                      ((append (cdr l1)) l2)))))))
       (cons ((append nil) nil)
             (cons ((append (cons 1 nil)) (cons 2 nil))
                   (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                            ((append (cdr l1)) l2)))))))
             (pair append
                   (cons ((append nil) nil)
                         (cons ((append (cons 1 nil)) (cons 2 nil))
                               (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                     nil)))))
          expr)
      (evalo '() expr val)))
  '(((pair (closure (l1)
                    (lambda (l2)
                      (if (null? l1)
                          l2
                          (cons (car l1)
                                ((append (cdr l1)) l2))))
                    ((append (rec (lambda (l1)
                                    (lambda (l2)
                                      (if (null? l1)
                                          l2
                                          (cons (car l1)
                                                ((append (cdr l1)) l2))))))))) 
           (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))       
       (pair append
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                            ((append (cdr l1)) l2)))))))
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                      ((append (cdr l1)) l2)))))))
       (cons ((append nil) nil)
             (cons ((append (cons 1 nil)) (cons 2 nil))
                   (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                            ((append (cdr l1)) l2)))))))
             (pair append
                   (cons ((append nil) nil)
                         (cons ((append (cons 1 nil)) (cons 2 nil))
                               (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                ((append (cdr l1)) l2))))
                    ((append (rec (lambda (l1)
                                    (lambda (l2)
                                      (if (null? l1)
                                          l2
                                          (cons (car l1)
                                                ((append (cdr l1)) l2))))))))) 
           (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       (pair append
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                            ((append (cdr l1)) l2)))))))
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                      ((append (cdr l1)) l2)))))))
       (cons ((append nil) nil)
             (cons ((append (cons 1 nil)) (cons 2 nil))
                   (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                            ((append (cdr l1)) l2)))))))
             (pair append
                   (cons ((append nil) nil)
                         (cons ((append (cons 1 nil)) (cons 2 nil))
                               (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                      ((append (cdr l1)) l2))))
                          ((append (rec (lambda (l1)
                                          (lambda (l2)
                                            (if (null? l1)
                                                l2
                                                (cons (car l1)
                                                      ((append (cdr l1)) l2))))))))) 
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
                                ((append (cdr l1)) l2))))
                    ((append (rec (lambda (l1)
                                    (lambda (l2)
                                      (if (null? l1)
                                          l2
                                          (cons (car l1)
                                                ((append (cdr l1)) l2))))))))) 
           (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       (pair append
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr l1)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                         ((append (cdr l1)) l2)))))))
          (cons ((append nil) nil)
                (cons ((append (cons 1 nil)) (cons 2 nil))
                      (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr l1)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                         ((append (cdr l1)) l2)))))))
          (pair append
                (cons ((append nil) nil)
                      (cons ((append (cons 1 nil)) (cons 2 nil))
                            (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr l1)) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                        ((append (cdr l1)) l2)))))))
         (cons ((append nil) nil)
               (cons ((append (cons 1 nil)) (cons 2 nil))
                     (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr l1)) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr l1)) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                        ((append (cdr l1)) l2)))))))
         (cons ((append nil) nil)
               (cons ((append (cons 1 nil)) (cons 2 nil))
                     (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr l1)) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr ,e)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                        ((append (cdr nil)) l2)))))))
         (cons ((append nil) nil)
               (cons ((append (cons 1 nil)) (cons 2 nil))
                     (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr ,e)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                        ((append (cdr l1)) l2)))))))
         (cons ((append nil) nil)
               (cons ((append (cons 1 nil)) (cons 2 nil))
                     (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append (cdr ,e)) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                        ((append (cdr l1)) l2)))))))
         (cons ((append nil) nil)
               (cons ((append (cons 1 nil)) (cons 2 nil))
                     (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(test "null?-1"
  (run* (q)
    (fresh (expr)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append #f) l2)))))))
             (pair append
                   (cons ((append nil) nil)
                         (cons ((append (cons 1 nil)) (cons 2 nil))
                               (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
             (f #f))
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
             (f #f))
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
             (f #f))
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
             (f (cons 1 nil)))
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
                           ((append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil))))
            expr)
        (== `(list (list int)) type)
        (!-o '() expr type)))
    '(((list (list int))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1) ((append nil) l2)))))))
         (cons ((append nil) nil)
               (cons ((append (cons 1 nil)) (cons 2 nil))
                     (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                        ((append nil) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append ,e) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                        ((append (cdr l1)) l2)))))))
         (cons ((append nil) nil)
               (cons ((append (cons 1 nil)) (cons 2 nil))
                     (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                        ((append (cdr l1)) l2)))))))
         (cons ((append nil) nil)
               (cons ((append (cons 1 nil)) (cons 2 nil))
                     (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                           nil))))))))

(time
  (test "append-value-synthesis-with-append-c"
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
                     (cons (car l1)
                           ((append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

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
                           ((append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  ;; swap order of calls to evalo and !-o
  (test "append-value-and-type-synthesis-with-append-c"
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
                           ((append ,e) l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
        ;; swap order of calls to evalo and !-o
        (evalo '() expr val)
        (!-o '() expr type)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(printf "**** commenting out append-value-synthesis-with-append-d test, which isn't returning\n")
#|
(time
  (test "append-value-synthesis-with-append-d"
    (run 1 (q)
      (fresh (expr type val f-body e clos)
        (== (list val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)

        #|
        ;; uncommenting this == fills in the hole, and shows the test is consistent
        (== `(append (cdr l1)) e)
        |#
        
        (== `(lambda (l1)
               (lambda (l2)
                 (if (null? l1)
                     l2
                     (cons (car l1)
                           (,e l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))
|#

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
                           (,e l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))


(printf "**** commenting out append-value-and-type-synthesis-with-append-d test, which isn't returning\n")
#|
(time
  ;; swap order of calls to evalo and !-o
  (test "append-value-and-type-synthesis-with-append-d"
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
                           (,e l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
        ;; swap order of calls to evalo and !-o
        (evalo '() expr val)
        (!-o '() expr type)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))
|#

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
                           (,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                 (w w))))
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
                                 (w 3))))
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
      (== `((lambda (w) w)
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
      (== `((lambda (w) w)
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
      (== `((lambda (f)
                (f (cons 1 nil)))
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
             (f (cons 1 nil)))
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
                                           (rebuild (cdr l)))))))
             rebuild)
          expr)
      (!-/evalo '() '() expr type val)))
  '(((-> (list _.0) (list _.0))
     (closure (l)
              (if (null? l)
                  nil
                  (cons (car l)
                        (rebuild (cdr l))))
              ((rebuild (poly ((rebuild (mono (-> (list _.0) (list _.0)))))
                              (lambda (l)
                                (if (null? l)
                                    nil
                                    (cons (car l)
                                          (rebuild (cdr l))))))))
              ((rebuild (rec (lambda (l)
                               (if (null? l)
                                   nil
                                   (cons (car l)
                                         (rebuild (cdr l)))))))))
     (let-poly ((rebuild (lambda (l)
                           (if (null? l)
                               nil
                               (cons (car l)
                                     (rebuild (cdr l)))))))
       rebuild))))

(test "!-/evalo-rebuild-2"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((rebuild (lambda (l)
                                 (if (null? l)
                                     nil
                                     (cons (car l)
                                           (rebuild (cdr l)))))))
             (rebuild nil))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list _.0)
     nil
     (let-poly ((rebuild (lambda (l)
                           (if (null? l)
                               nil
                               (cons (car l)
                                     (rebuild (cdr l)))))))
       (rebuild nil)))))

(test "!-/evalo-rebuild-3"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((rebuild (lambda (l)
                                 (if (null? l)
                                     nil
                                     (cons (car l)
                                           (rebuild (cdr l)))))))
             (rebuild (cons 1 nil)))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list int)
     (cons 1 nil)
     (let-poly ((rebuild (lambda (l)
                           (if (null? l)
                               nil
                               (cons (car l)
                                     (rebuild (cdr l)))))))
       (rebuild (cons 1 nil))))))

(test "!-/evalo-40-simple"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append (cdr l1)) l2)))))))
             append)
          expr)
      (!-/evalo '() '() expr type val)))
  '(((-> (list _.0) (-> (list _.0) (list _.0)))
     (closure (l1)
              (lambda (l2)
                (if (null? l1)
                    l2
                    (cons (car l1)
                          ((append (cdr l1)) l2))))
              ((append (poly ((append (mono (-> (list _.0) (-> (list _.0) (list _.0))))))
                             (lambda (l1)
                               (lambda (l2)
                                 (if (null? l1)
                                     l2
                                     (cons (car l1)
                                           ((append (cdr l1)) l2))))))))
              ((append (rec (lambda (l1)
                              (lambda (l2)
                                (if (null? l1)
                                    l2
                                    (cons (car l1)
                                          ((append (cdr l1)) l2)))))))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
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
                                            ((append (cdr l1)) l2)))))))
             (append nil))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((-> (list _.0) (list _.0))
     (closure (l2)
              (if (null? l1)
                  l2
                  (cons (car l1)
                        ((append (cdr l1)) l2)))
              ((l1 (mono (list _.0)))
               (append (poly ((append (mono (-> (list _.0) (-> (list _.0) (list _.0))))))
                             (lambda (l1)
                               (lambda (l2)
                                 (if (null? l1)
                                     l2
                                     (cons (car l1)
                                           ((append (cdr l1)) l2))))))))
              ((l1 (val nil))
               (append (rec (lambda (l1)
                              (lambda (l2)
                                (if (null? l1)
                                    l2
                                    (cons (car l1)
                                          ((append (cdr l1)) l2)))))))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       (append nil)))))

(test "!-/evalo-42-simple"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)      
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append (cdr l1)) l2)))))))
             ((append nil) nil))
          expr)
      (!-/evalo '() '() expr type val)))
  '(((list _.0)
     nil
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       ((append nil) nil)))))

(test "!-/evalo-43-type-and-value"
  (run* (q)
    (fresh (expr type val)
      (== (list type val expr) q)
      (== `(let-poly ((append (lambda (l1)
                                (lambda (l2)
                                  (if (null? l1)
                                      l2
                                      (cons (car l1)
                                            ((append (cdr l1)) l2)))))))
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                      ((append (cdr l1)) l2)))))))
       (cons ((append nil) nil)
             (cons ((append (cons 1 nil)) (cons 2 nil))
                   (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                            ((append (cdr l1)) l2)))))))
             (pair append
                   (cons ((append nil) nil)
                         (cons ((append (cons 1 nil)) (cons 2 nil))
                               (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                ((append (cdr l1)) l2))))
                    ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                   (lambda (l1)
                                     (lambda (l2)
                                       (if (null? l1)
                                           l2
                                           (cons (car l1)
                                                 ((append (cdr l1)) l2))))))))
                    ((append (rec (lambda (l1)
                                    (lambda (l2)
                                      (if (null? l1)
                                          l2
                                          (cons (car l1)
                                                ((append (cdr l1)) l2))))))))) 
           (cons nil (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 (cons 5 (cons 6 nil)))) nil))))
     (let-poly ((append (lambda (l1)
                          (lambda (l2)
                            (if (null? l1)
                                l2
                                (cons (car l1)
                                      ((append (cdr l1)) l2)))))))
       (pair append
             (cons ((append nil) nil)
                   (cons ((append (cons 1 nil)) (cons 2 nil))
                         (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           ((append ,e) l2)))))
            f-body)        
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           (,e1 l2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-!-/evalo-dynamic-application-synthesis-with-append-e-with-hint"
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
                           (,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
        (!-/evalo-dynamic-application '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-!-/evalo-less-dumb-synthesis-with-append-e-with-hint"
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
                           (,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
        (!-/evalo-less-dumb '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-!-/evalo-lazy-synthesis-with-append-e-with-hint"
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
                           (,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
        (!-/evalo-lazy '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(time
  (test "append-!-/evalo-canonical-synthesis-with-append-e-with-hint"
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
                           (,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
        (!-/evalo-canonical '() '() expr type val)))
    '(((pair (-> (list int) (-> (list int) (list int)))
             (list (list int)))
       (pair (closure (l1)
                      (lambda (l2)
                        (if (null? l1)
                            l2
                            (cons (car l1)
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                           (,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))

(printf "**** commenting out append-!-/evalo-synthesis-with-append-e-without-hint test, which isn't returning\n")
#|
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
                           (,e1 ,e2)))))
            f-body)
        (== `(let-poly ((append ,f-body))
               (pair append
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))
|#


(printf "**** commenting out append-!-/evalo-synthesis-with-append-z test, which isn't returning\n")
#|
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
                     (cons ((append nil) nil)
                           (cons ((append (cons 1 nil)) (cons 2 nil))
                                 (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
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
                                  ((append (cdr l1)) l2))))
                      ((append (poly ((append (mono (-> (list int) (-> (list int) (list int))))))
                                     (lambda (l1)
                                       (lambda (l2)
                                         (if (null? l1)
                                             l2
                                             (cons (car l1)
                                                   ((append (cdr l1)) l2))))))))
                      ((append (rec (lambda (l1)
                                      (lambda (l2)
                                        (if (null? l1)
                                            l2
                                            (cons (car l1)
                                                  ((append (cdr l1)) l2)))))))))
             (cons nil
                   (cons (cons 1 (cons 2 nil))
                         (cons (cons 3 (cons 4 (cons 5 (cons 6 nil))))
                               nil))))
       (let-poly ((append (lambda (l1)
                            (lambda (l2)
                              (if (null? l1)
                                  l2
                                  (cons (car l1)
                                        ((append (cdr l1)) l2)))))))
         (pair append
               (cons ((append nil) nil)
                     (cons ((append (cons 1 nil)) (cons 2 nil))
                           (cons ((append (cons 3 (cons 4 nil))) (cons 5 (cons 6 nil)))
                                 nil)))))))))
|#


;; stutter example taken from 'Type-and-Example-Directed Program Synthesis' by
;; Peter-Michael Osera and Steve Zdancewic (PLDI '15)
(time
  (test "stutter-!-o-with-stutter-1"
    (run 1 (q)
      (fresh (expr type f-body)
        (== (list type expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 (stutter (cdr l))))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (!-o '() expr type)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter
               (cons (stutter nil)
                     (cons (stutter (cons 0 nil))
                           (cons (stutter (cons 1 (cons 0 nil)))
                                 nil)))))))))

(time
  (test "stutter-evalo-with-stutter-1"
    (run 1 (q)
      (fresh (expr val f-body clos)
        (== (list val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 (stutter (cdr l))))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (evalo '() expr val)))
    '(((pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l) (if (null? l) nil (cons (car l) (cons (car l) (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil) (cons (stutter (cons 0 nil)) (cons (stutter (cons 1 (cons 0 nil))) nil)))))))))

(time
  (test "stutter-!-o-and-evalo-with-stutter-1"
    (run 1 (q)
      (fresh (expr type val f-body clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 (stutter (cdr l))))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 0 nil)))
                                         nil)))))))))

(time
  (test "stutter-!-/evalo-with-stutter-1"
    (run 1 (q)
      (fresh (expr type val f-body clos)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 (stutter (cdr l))))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 0 nil)))
                                         nil)))))))))

(time
  (test "stutter-evalo-with-stutter-synthesis-1"
    (run 1 (q)
      (fresh (expr val f-body clos e)
        (== (list val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 (stutter ,e)))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                                     nil))))
            val)
        (evalo '() expr val)))
    '(((pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l) (if (null? l) nil (cons (car l) (cons (car l) (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil) (cons (stutter (cons 0 nil)) (cons (stutter (cons 1 (cons 0 nil))) nil)))))))))

(time
  (test "stutter-!-o-and-evalo-with-synthesis-stutter-1"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 (stutter ,e)))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                                     nil))))
            val)        
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 0 nil)))
                                         nil)))))))))

(time
  (test "stutter-!-/evalo-with-stutter-synthesis-1"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 (stutter ,e)))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                                     nil))))
            val)        
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 0 nil)))
                                         nil)))))))))




(time
  (test "stutter-evalo-with-stutter-synthesis-2"
    (run 1 (q)
      (fresh (expr val f-body clos e)
        (== (list val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 ,e))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                                     nil))))
            val)
        (evalo '() expr val)))
    '(((pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l) (if (null? l) nil (cons (car l) (cons (car l) (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil) (cons (stutter (cons 0 nil)) (cons (stutter (cons 1 (cons 0 nil))) nil)))))))))

(time
  (test "stutter-!-o-and-evalo-with-synthesis-stutter-2"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 ,e))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                                     nil))))
            val)        
        (!-o '() expr type)
        (evalo '() expr val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 0 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-with-stutter-synthesis-2a"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 ,e))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)        
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  (test "stutter-!-/evalo-with-stutter-synthesis-2b"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 ,e))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                                     nil))))
            val)        
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 0 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-lazy-with-stutter-synthesis-2a"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 ,e))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)        
        (!-/evalo-lazy '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-dynamic-application-with-stutter-synthesis-2a"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 ,e))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)
        (!-/evalo-dynamic-application '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-less-dumb-with-stutter-synthesis-2a"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 ,e))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)
        (!-/evalo-less-dumb '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))


(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-canonical-with-stutter-synthesis-2a"
    (run 1 (q)
      (fresh (expr type val f-body clos e)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car l)
                                 ,e))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)        
        (!-/evalo-canonical '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(printf "!!!!   none of the following tests seem to come back in a reasonable time...\n")

(printf "****   these tests really should be doing better, given the type information...\n")

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-dynamic-application-with-stutter-synthesis-3a"
    (run 1 (q)
      (fresh (expr type val f-body clos e1 e2)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)        
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car ,e1)
                                 ,e2))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)
        (!-/evalo-dynamic-application '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-less-dumb-with-stutter-synthesis-3a"
    (run 1 (q)
      (fresh (expr type val f-body clos e1 e2)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)        
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car ,e1)
                                 ,e2))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)
        (!-/evalo-less-dumb '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-canonical-with-stutter-synthesis-3a"
    (run 1 (q)
      (fresh (expr type val f-body clos e1 e2)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)        
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car ,e1)
                                 ,e2))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)
        (!-/evalo-canonical '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-lazy-with-stutter-synthesis-3a"
    (run 1 (q)
      (fresh (expr type val f-body clos e1 e2)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)        
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car ,e1)
                                 ,e2))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)
        (!-/evalo-lazy '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-with-stutter-synthesis-3a"
    (run 1 (q)
      (fresh (expr type val f-body clos e1 e2)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)        
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car ,e1)
                                 ,e2))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)        
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  (test "stutter-!-/evalo-with-stutter-synthesis-3b"
    (run 1 (q)
      (fresh (expr type val f-body clos e1 e2)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons (car ,e1)
                                 ,e2))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                                     nil))))
            val)        
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 0 nil)))
                                         nil)))))))))

(time
  ;; use unique numbers for all examples
  (test "stutter-!-/evalo-with-stutter-synthesis-4a"
    (run 1 (q)
      (fresh (expr type val f-body clos e1 e2)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons ,e1
                                 ,e2))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 2 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                                     nil))))
            val)        
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 2 (cons 2 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 2 nil)))
                                         nil)))))))))

(time
  (test "stutter-!-/evalo-with-stutter-synthesis-4b"
    (run 1 (q)
      (fresh (expr type val f-body clos e1 e2)
        (== (list type val expr) q)
        (absento 1 f-body)
        (absento 2 f-body)
        (absento 3 f-body)
        (absento 4 f-body)
        (absento 5 f-body)
        (absento 6 f-body)
        (== `(lambda (l)
               (if (null? l)
                     nil
                     (cons (car l)
                           (cons ,e1
                                 ,e2))))
            f-body)
        (== `(let-poly ((stutter ,f-body))
               (pair stutter
                     (cons (stutter nil)
                           (cons (stutter (cons 0 nil))
                                 (cons (stutter (cons 1 (cons 0 nil)))
                                       nil)))))
            expr)
        (== `(pair (-> (list int) (list int))
                   (list (list int)))
            type)
        (== `(pair (closure . ,clos)
                   (cons nil
                         (cons (cons 0 (cons 0 nil))
                               (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                                     nil))))
            val)        
        (!-/evalo '() '() expr type val)))
    '(((pair (-> (list int) (list int))
             (list (list int)))
       (pair (closure (l)
                      (if (null? l)
                          nil
                          (cons (car l)
                                (cons (car l)
                                      (stutter (cdr l)))))
                      ((stutter (poly ((stutter (mono (-> (list int) (list int)))))
                                      (lambda (l)
                                        (if (null? l)
                                            nil
                                            (cons (car l)
                                                  (cons (car l)
                                                        (stutter (cdr l)))))))))
                      ((stutter (rec (lambda (l)
                                       (if (null? l)
                                           nil
                                           (cons (car l)
                                                 (cons (car l)
                                                       (stutter (cdr l))))))))))
             (cons nil
                   (cons (cons 0 (cons 0 nil))
                         (cons (cons 1 (cons 1 (cons 0 (cons 0 nil))))
                               nil))))
       (let-poly ((stutter (lambda (l)
                             (if (null? l)
                                 nil
                                 (cons (car l)
                                       (cons (car l)
                                             (stutter (cdr l))))))))
         (pair stutter (cons (stutter nil)
                             (cons (stutter (cons 0 nil))
                                   (cons (stutter (cons 1 (cons 0 nil)))
                                         nil)))))))))

;;; interesting examples

;; fail due to self-application
(run* (expr val)
  (fresh (e)
    (== `((lambda (x) 3) (lambda (y) (y y))) expr)
    (!-/evalo '()
              '()
              expr
              'int
              val)))

(run 1000 (expr val)
  (fresh (e)
    (== `((lambda (x) 3) ,e) expr)
    (!-/evalo '()
              '()
              expr
              'int
              val)))

(run 100 (expr type val)
  (fresh (e)
    (== `((lambda (x) (cons x (cons 3 nil))) ,e) expr)
    (!-/evalo '()
              '()
              expr
              type
              val)))

;; diverges!
#;(run 1 (expr type val)
  (fresh (e)
    (== `((lambda (x) 3)
          (let-poly ((f (lambda (x) (f x))))
            (f 4)))
        expr)
    (!-/evalo '()
              '()
              expr
              type
              val)))
