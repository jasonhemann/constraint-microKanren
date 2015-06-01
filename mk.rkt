#lang racket
(require "make-constraints.rkt")
(require "micro-w-constraints.rkt")
(require rackunit)
(provide (combine-out
          (all-from-out "make-constraints.rkt")
          (all-from-out "micro-w-constraints.rkt")))

(check-equal?
 (call/initial-state
  (symbolo #f))
 '())

(check-equal?
 (call/initial-state
  (== #t #f))
 '())

(check-equal?
 (call/initial-state
  (call/fresh
   (lambda (x)
     (conj
      (== #t x)
      (=/= #t x)))))
 '())

(check-equal?
 (call/initial-state
  (call/fresh
   (lambda (x)
     (conj
      (=/= #t x)
      (== #t x)))))
 '())

(check-match
 (call/initial-state 
  (call/fresh
   (lambda (q)
     (listo q))))
 (list _))

(check-equal?
 (call/initial-state
  (call/fresh
   (lambda (q)
     (conj
      (listo q)
      (absento '() q)))))
 '())
(check-match
 (call/initial-state
  (call/fresh
   (lambda (q)
     (conj
      (listo q)
      (absento q '())))))
 (list _))
(check-equal?
 (call/initial-state 
  (call/fresh
   (lambda (q)
     (conj
      (listo q)
      (conj
       (absento '() q)
       (not-pairo q))))))
 '())
(check-equal?
 (call/initial-state 
  (call/fresh
   (lambda (q)
     (conj
      (listo q)
      (conj
       (absento q '())
       (not-pairo q))))))
 '())
(check-equal?
 (call/initial-state 
  (call/fresh
   (lambda (q)
     (conj
      (listo q)
      (conj
       (=/= q '())
       (not-pairo q))))))
 '())
(check-match
 (call/initial-state 
   (call/fresh
     (lambda (q)
       (conj
         (listo q)
         (=/= q '())))))
 (list _))
(check-equal?
 (call/initial-state
  (call/fresh
   (lambda (q)
     (conj
      (listo q)
      (symbolo q)))))
 '())
