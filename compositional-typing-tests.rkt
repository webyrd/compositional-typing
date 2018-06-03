#lang racket

(require "faster-miniKanren/mk.rkt")
(require "compositional-typing.rkt")
(require rackunit)


(check-equal?
  (run* (delta1 delta2 delta)
    (== `((x . int) (y . (-> int bool))) delta1)
    (== `((x . int) (y . (-> int bool))) delta2)
    (U-delta delta1 delta2 delta))
  '((((x . int) (y -> int bool))
     ((x . int) (y -> int bool))
     ((x . int) (y -> int bool))))
  "U-delta-1")

(check-equal?
  (run* (delta1 delta2 delta alpha beta)
    (== `((x . int) (y . (-> int ,beta))) delta1)
    (== `((x . int) (y . (-> ,alpha bool))) delta2)
    (U-delta delta1 delta2 delta))
  '((((x . int) (y -> int bool))
     ((x . int) (y -> int bool))
     ((x . int) (y -> int bool))
     int
     bool))
  "U-delta-2")
