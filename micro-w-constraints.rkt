#lang racket
(provide var? pull call/fresh conj disj call/initial-state-maker)
(define (var n) n)
(define ($append $1 $2)
  (cond
    ((null? $1) $2)
    ((pair? $1) (cons (car $1) ($append (cdr $1) $2)))
    ((procedure? $1) (lambda () ($append $2 ($1))))))
(define ($append-map g $)
  (cond
    ((null? $) `())
    ((pair? $) ($append (g (car $)) ($append-map g (cdr $))))
    ((procedure? $) (lambda () ($append-map g ($))))))
(define (pull $) (if (procedure? $) (pull ($)) $))
(define (var? n) (number? n))
(define (call/initial-state-maker initial-state) ;; curry further
  (lambda (g) (pull (g `(,initial-state . 0)))))
(define ((call/fresh f) s/c)
  (let ((s (car s/c)) (c (cdr s/c)))
    ((f (var c)) `(,s . ,(+ 1 c)))))
(define ((disj g1 g2) s/c) ($append (g1 s/c) (g2 s/c)))
(define ((conj g1 g2) s/c) ($append-map g2 (g1 s/c)))
