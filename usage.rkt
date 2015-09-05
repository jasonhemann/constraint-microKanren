#lang racket
(require "paper-code.rkt")
(require rackunit)

;; miniKanren wrappers
(define-syntax disj+
  (syntax-rules ()
    ((_ g) g)
    ((_ g0 g ...) (disj g0 (disj+ g ...)))))

(define-syntax conj+
  (syntax-rules ()
    ((_ g) g)
    ((_ g0 g ...) (conj g0 (conj+ g ...)))))

(define-syntax-rule (conde (g0 g ...) (g0* g* ...) ...)
  (disj+ (conj+ g0 g ...) (conj+ g0* g* ...) ...))

(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g ...) (conj+ g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/fresh (lambda (x0) (fresh (x ...) g0 g ...))))))

;; Slightly new run, run interface
(define-syntax-rule (run n/b (q) g g* ...)
  (call/initial-state n/b (fresh (q) g g* ...)))

(define-relation (membero x ls o)
  (fresh (a d)
    (== `(,a . ,d) ls)
    (conde
      ((== x a) (== ls o))
      ((=/= x a) (membero x d o)))))

(test-equal? "membero test1"
  (run #f (q) (membero 'x '(a x x) q))
  '((#hasheqv((== . ((2 . 0) (x . 3) ((3 . 4) . 2) ((1 . 2) a x x)))
            (=/= . ((x . 1)))
            (absento . ())
            (symbolo . ())
            (not-pairo . ())
            (booleano . ())
            (listo . ()))
   .
   5))) 

(test-equal? "membero test2"
  (run #f (q)
          (fresh (y z)
                 (== q `(,y ,z))
                 (membero 'x `(a ,y x) z)))
'((#hasheqv((== . ((4 . 2) (x . 5) ((5 . 6) . 4) ((3 . 4) a 1 x) (0 1 2)))
            (=/= . ((x . 3)))
            (absento . ())
            (symbolo . ())
            (not-pairo . ())
            (booleano . ())
            (listo . ()))
   .
   7)
  (#hasheqv((==
             .
             ((6 . 2)
              (x . 7)
              ((7 . 8) . 6)
              ((5 . 6) . 4)
              ((3 . 4) a 1 x)
              (0 1 2)))
            (=/= . ((x . 5) (x . 3)))
            (absento . ())
            (symbolo . ())
            (not-pairo . ())
            (booleano . ())
            (listo . ()))
   .
   9)))

;; Example from talk
(define-relation (lookup Γ x τ)
  (fresh (y τ2 Γ2)
    (== `((,y . ,τ2) . ,Γ2) Γ)
    (conde
      ((== x y) (== τ τ2) (listo Γ2))
      ((=/= x y) (lookup Γ2 x τ))))) 

(define-relation (⊢ Γ e τ)
  (conde
    ((booleano e) (== τ 'bool) (listo Γ))
    ((symbolo e) (lookup Γ e τ))
    ((fresh (x b)
       (== `(λ (,x) ,b) e)
       (symbolo x)
       (fresh (τ1 τ2)
         (== `(,τ1 -> ,τ2) τ)             
         (⊢ `((,x . ,τ1) . ,Γ) b τ2))))
    ((fresh (e1 e2)
       (== `(,e1 ,e2) e)
       (fresh (τ1)
         (⊢ Γ e1 `(,τ1 -> τ))
         (⊢ Γ e2 τ1))))))

(test-equal? "test ⊢"
  (call/initial-state 1
    (fresh (q) (⊢ '() q '(bool -> bool))))
  '((#hasheqv((== . ((4 . bool) ((3 -> 4) bool -> bool) ((λ (1) 2) . 0)))
              (=/= . ())
              (absento . ())
              (symbolo . (1))
              (not-pairo . ())
              (booleano . (2))
              (listo . (((1 . 3)))))
     .
     5)))
