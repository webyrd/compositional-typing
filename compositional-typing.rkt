#lang racket

(require "faster-miniKanren/mk.rkt")

(provide not-in-delta
         U-delta
         removeo)

(define not-in-delta
  (lambda (x delta)
    (fresh ()
      (symbolo x)
      (conde
        [(== '() delta)]
        [(fresh (y t rest)
           (== `((,y . ,t) . ,rest) delta)
           (symbolo y)
           (=/= x y)
           (not-in-delta x rest))]))))

(define U-delta
  (lambda (delta1 delta2 delta)
    (conde
      [(== '() delta1) (== delta2 delta)]
      [(fresh (x t rest)
         (== `((,x . ,t) . ,rest) delta1)
         (symbolo x)
         (conde
           [(fresh (res)
              (== `((,x . ,t) . ,res) delta)
              (not-in-delta x delta2)
              (U-delta rest delta2 res))]
           [(fresh (delta2^ res)
              (== `((,x . ,t) . ,res) delta)
              (removeo `(,x . ,t) delta2 delta2^)
              (U-delta rest delta2^ res))]))])))

(define removeo
  (lambda (pr delta delta^)
    (fresh (x t y ty res)
      (== `(,x . ,t) pr)
      (symbolo x)
      (== `((,y . ,ty) . ,res) delta)
      (symbolo y)
      (conde
        [(== x y)
         (== t ty)
         (== res delta^)]
        [(=/= x y)
         (fresh (res^)
           (== `((,y . ,ty) . ,res^) delta^)
           (removeo pr res res^))]))))
