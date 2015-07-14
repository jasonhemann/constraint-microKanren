#lang racket
(provide var? pull call/fresh conj disj call/initial-state-maker)
(define (var n) n)
(define ($append $1 $2)
  (cond
    ((null? $1) $2)
    ((promise? $1) (delay/name ($append $2 (force $1))))
    ((pair? $1) (cons (car $1) ($append (cdr $1) $2)))))
(define ($append-map g $)
  (cond
    ((null? $) '())
    ((promise? $) (delay/name ($append-map g (force $))))
    ((pair? $) ($append (g (car $)) ($append-map g (cdr $))))))
(define (pull $) (if (promise? $) (pull (force $)) $))
(define (take n $)
  (cond
    ((null? $) '())
    ((and n (zero? (- n 1))) (list (car $)))
    (else (cons (car $) 
            (take (and n (- n 1)) (pull (cdr $)))))))
(define (var? n) (number? n))
(define ((call/initial-state-maker initial-state) n g) ;; curry further
  (take n (pull (g `(,initial-state . 0)))))
(define ((call/fresh f) s/c)
  (let ((s (car s/c)) (c (cdr s/c)))
    ((f (var c)) `(,s . ,(+ 1 c)))))
(define ((disj g1 g2) s/c) ($append (g1 s/c) (g2 s/c)))
(define ((conj g1 g2) s/c) ($append-map g2 (g1 s/c)))
