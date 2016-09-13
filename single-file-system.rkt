#lang racket
(require (for-syntax syntax/parse))
(require (for-syntax racket/syntax))
(provide (all-defined-out))

;; miniKanren online play-withable system
;; microKanren constraints play-withable system
;; Numbers system that uses booleans. 

(define (((make-constraint-goal-constructor key) . terms) S/c)
  (let ((S (ext-S (car S/c) key terms)))
    (if (invalid? S) '() (list `(,S . ,(cdr S/c))))))

(define (ext-S S key terms)
  (hash-update S key ((curry cons) (apply list* terms))))

(define-syntax-rule (make-invalid? (cid ...) p ...)
  (λ (S) 
    (let ((cid (hash-ref S 'cid)) ...)
      (cond
        ((valid-== (hash-ref S '==))
         => (λ (s) (or (p s) ...)))
        (else #t)))))

(define-syntax (make-constraint-system stx)
  (syntax-parse stx
    [(_ (cid:id ...) p ...)
     (with-syntax 
       ([invalid? (syntax-local-introduce #'invalid?)]
        [S0 (syntax-local-introduce #'S0)]
        [== (syntax-local-introduce #'==)])
       #'(begin 
           (define invalid? (make-invalid? (cid ...) p ...))
           (define S0
             (make-immutable-hasheqv '((==) (cid) ...)))
           (define == (make-constraint-goal-constructor '==))
           (define cid (make-constraint-goal-constructor 'cid))
           ...))]))

(define (valid-== ==) 
  (foldr
    (λ (pr s) 
      (and s (unify (car pr) (cdr pr) s)))
    '()
    ==))

#| Term ⨯ Term ⨯ Subst ⟶ Bool |#  
(define (same-s? u v s) (equal? (unify u v s) s))

#| Term ⨯ Term ⨯ Subst ⟶ Bool |#  
(define (mem? u v s)
  (let ((v (walk v s)))
    (or (same-s? u v s)
        (and (pair? v)
             (or (mem? u (car v) s)
                 (mem? u (cdr v) s))))))

#| Term ⨯ Subst ⟶ Bool |#  
(define (walk-to-end x s)
  (let ((x (walk x s)))
    (if (pair? x) (walk-to-end (cdr x) s) x)))

#| Nat ⟶ Var |#
(define (var n) n)

#| Term ⟶ Bool |#
(define (var? n) (number? n))

#| Var ⨯ Term ⨯ Subst ⟶ Bool |#  
(define (occurs? x v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) (eqv? x v))
      ((pair? v) (or (occurs? x (car v) s)
                     (occurs? x (cdr v) s)))
      (else #f))))

#| Var ⨯ Term ⨯ Subst ⟶ Maybe Subst |#
(define (ext-s x v s) 
  (cond 
    ((occurs? x v s) #f) 
    (else `((,x . ,v) . ,s))))

#| Term ⨯ Subst ⟶ Term |#  
(define (walk u s)
  (let ((pr (assv u s)))
    (if pr (walk (cdr pr) s) u)))

#| Term ⨯ Term ⨯ Subst ⟶ Maybe Subst |#  
(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((eqv? u v) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
;o
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else #f))))

#| (Var ⟶ Goal) ⟶ State ⟶ Stream |#
(define ((call/fresh f) S/c)
  (let ((S (car S/c)) (c (cdr S/c)))
    ((f (var c)) `(,S . ,(+ 1 c)))))

#| Stream ⟶ Stream ⟶ Stream |#
(define ($append $1 $2)
  (cond
    ((null? $1) $2)
    ((promise? $1) (delay/name ($append $2 (force $1))))
    (else (cons (car $1) ($append (cdr $1) $2)))))

#| Goal ⟶ Stream ⟶ Stream |#
(define ($append-map g $)
  (cond
    ((null? $) `())
    ((promise? $) (delay/name ($append-map g (force $))))
    (else ($append (g (car $)) ($append-map g (cdr $))))))

#| Goal ⟶ Goal ⟶ Goal |#
(define ((disj g1 g2) S/c) ($append (g1 S/c) (g2 S/c)))

#| Goal ⟶ Goal ⟶ Goal |#
(define ((conj g1 g2) S/c) ($append-map g2 (g1 S/c)))

#| Stream ⟶ Mature Stream |#
(define (pull $) (if (promise? $) (pull (force $)) $))

#| Maybe Nat⁺ ⨯ Mature ⟶ List State |#
(define (take n $)
  (cond
    ((null? $) '())
    ((and n (zero? (- n 1))) (list (car (pull $))))
    (else (cons (car $) 
            (take (and n (- n 1)) (pull (cdr $)))))))

#| Maybe Nat⁺ ⨯ Goal ⟶ List State |#
(define (call/initial-state n g)
  (take n (pull (g `(,S0 . 0)))))

(define-syntax-rule (define-relation (rid . args) g)
  (define ((rid . args) S/c) (delay/name (g S/c))))

(make-constraint-system 
  (=/= absento symbolo not-pairo booleano listo)
  (λ (s)
    (ormap
      (λ (pr) (same-s? (car pr) (cdr pr) s))
      =/=))
  (λ (s)
    (ormap
      (λ (pr) (mem? (car pr) (cdr pr) s))
      absento))
  (λ (s)
    (ormap
      (λ (y)
        (let ((t (walk y s)))
          (not (or (symbol? t) (var? t)))))
      symbolo))
  (λ (s)
    (ormap
      (λ (n)
        (let ((t (walk n s)))
          (not (or (not (pair? t)) (var? t)))))
      not-pairo))
  (let ((not-b
          (λ (s)
            (or (ormap
                  (λ (pr) (same-s? (car pr) (cdr pr) s))
                  =/=)
                (ormap
                  (λ (pr) (mem? (car pr) (cdr pr) s))
                  absento)))))
    (λ (s)
      (ormap
        (λ (b)
          (let ((s1 (unify b #t s)) (s2 (unify b #t s)))
            (and s1 s2 (not-b s1) (not-b s2))))
        booleano)))
  (λ (s)
    (ormap
      (λ (b)
        (let ((b (walk b s)))
          (not (or (var? b) (boolean? b)))))
      booleano))
  (λ (s)
    (ormap
     (λ (b)
       (ormap
         (λ (y) (same-s? y b s))
         symbolo))
     booleano))
  (λ (s)
    (ormap
      (λ (l)
        (let ((end (walk-to-end l s)))
          (ormap 
            (λ (y) (same-s? y end s))
            symbolo)))
      listo))
  (λ (s)
    (ormap
      (λ (l)
        (let ((end (walk-to-end l s)))
          (ormap 
            (λ (b) (same-s? b end s))
            booleano)))
      listo))
  (λ (s)
    (ormap
      (λ (l)
        (let ((end (walk-to-end l s)))
          (let ((s^ (unify end '() s)))
            (and s^
                 (ormap 
                   (λ (n) (same-s? end n s))
                   not-pairo)
                 (or 
                  (ormap 
                    (λ (pr) (same-s? (car pr) (cdr pr) s^))
                    =/=)
                  (ormap 
                    (λ (pr) (mem? (car pr) (cdr pr) s^))
                    absento))))))
      listo))
  (λ (s)
    (ormap
      (λ (l)
        (let ((end (walk-to-end l s)))
          (ormap
            (λ (pr) 
              (and 
                (null? (walk (car pr) s)) 
                (mem? end (cdr pr) s)))
            absento)))
      listo)))


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

(define-syntax-rule (conda (g0 g1 g ...) ... (gn0 gn ...))
  (ifte* (g0 (conj+ g1 g ...)) ... (conj+ gn0 gn ...)))

(define-syntax-rule (condu (g0 g1 g ...) ... (gn0 gn ...))
  (conda ((once g0) g ...) ... ((once gn0) gn ...)))

(define (apply-subst v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) v)
      ((pair? v) (cons (apply-subst (car v) s)
                       (apply-subst (cdr v) s)))
      (else v))))

(define (build-r v s c)
  (cond
    ((var? v) `((,v . ,(+ (length s) c)) . ,s))
    ((pair? v) (build-r (cdr v) (build-r (car v) s c) c))
    (else s)))

(define (project-var0 s/c)
  (let ((v (apply-subst (var 0) (car s/c))))
    (let ((v (apply-subst v (build-r v '() (cdr s/c)))))
      (apply-subst v (build-r v '() 0)))))

(define-syntax-rule (run n (q) g0 g ...)
  (call/initial-state n (fresh (q) g0 g ...)))

(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g ...) (conj+ g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/fresh (lambda (x0) (fresh (x ...) g0 g ...))))))

;; (define-syntax-rule (program-and-query ((n (λ args gexp)) ...) q)
;;   (letrec ((n (λ args (λ (s/c) (delay/name (gexp s/c))))) ...) q))

(define syntax->list
  (lambda (e)
    (syntax-case e ()
      [() '()]
      [(x . r) (cons #'x (syntax->list #'r))])))

(define-syntax defmatche
  (lambda (stx)
    (syntax-case stx ()
      [(defmatche (name args ...) clause ...)
       #'(define-relation (name args ...)
           (matche (args ...) clause ...))])))

(define-syntax lambdae
  (syntax-rules ()
    ((_ (x ...) c c* ...)
     (lambda (x ...) (matche (x ...) c c* ...)))))

(define-syntax matche
  (lambda (stx)    
    (syntax-case stx ()
      [(matche (v ...) ([pat ...] g ...) ...)
       (let ()
         (define remove-duplicates
           (lambda (ls eq-pred)
             (cond
               [(null? ls) '()]
               [(memf (lambda (x) (eq-pred (car ls) x)) (cdr ls))
                (remove-duplicates (cdr ls) eq-pred)]
               [else (cons (car ls) (remove-duplicates (cdr ls) eq-pred))])))
         (define parse-pattern
           (lambda (args pat)
             (syntax-case #`(#,args #,pat) ()
               [(() ()) #'(() () ())]
               [((a args ...) [p pat ...])
                (with-syntax ([(p^ (c ...) (x ...))
                               (parse-patterns-for-arg #'a #'p)])
                  (with-syntax ([([pat^ ...] (c^ ...) (x^ ...))
                                 (parse-pattern #'(args ...) #'[pat ...])])
                    #'([p^ pat^ ...] (c ... c^ ...) (x ... x^ ...))))]
               [x (error 'parse-pattern "bad syntax ~s ~s" args pat)])))
         (define parse-patterns-for-arg
           (lambda (v pat)
             (define loop
               (lambda (pat)
                 (syntax-case pat (unquote ?? ?) ; ?? is the new _, since _ isn't legal in R6
                   [(unquote ??)
                    (with-syntax ([_new (generate-temporary #'?_)])
                      #'((unquote _new) () (_new)))]
                   [(unquote x)
                    (when (free-identifier=? #'x v)
                      (error 'matche "argument ~s appears in pattern at an invalid depth"
                             (syntax->datum #'x)))
                    #'((unquote x) () (x))]
                   [(unquote (? c x))
                    (when (free-identifier=? #'x v)
                      (error 'matche "argument ~s appears in pattern at an invalid depth"
                             (syntax->datum #'x)))
                    #'((unquote x) ((c x)) (x))]
                   [(a . d)
                    (with-syntax ([((pat1 (c1 ...) (x1 ...))
                                    (pat2 (c2 ...) (x2 ...)))
                                   (map loop (syntax->list #'(a d)))])
                      #'((pat1 . pat2) (c1 ... c2 ...) (x1 ... x2 ...)))]
                   [x #'(x () ())])))
             (syntax-case pat (unquote ?)
               [(unquote u)
                (cond
                  [(and (identifier? #'u)
                        (free-identifier=? v #'u))
                   #'((unquote u) () ())]
                  [else (loop pat)])]
               [(unquote (? c u))
                (cond
                  [(and (identifier? #'u)
                        (free-identifier=? v #'u))
                   #'((unquote u) ((c x)) ())]
                  [else (loop pat)])]
               [else (loop pat)])))
         (unless
             (andmap (lambda (y) (= (length (syntax->datum #'(v ...))) (length y)))
                     (syntax->datum #'([pat ...] ...)))
           (error 'matche "pattern wrong length blah"))
         (with-syntax ([(([pat^ ...] (c ...) (x ...)) ...)
                        (map (lambda (y) (parse-pattern #'(v ...) y))
                             (syntax->list #'([pat ...] ...)))])
           (with-syntax ([((x^ ...) ...)
                          (map (lambda (ls)
                                 (remove-duplicates (syntax->list ls) free-identifier=?))
                               (syntax->list #'((x ...) ...)))])
             (with-syntax ([body
                            #'(conde
                                [(fresh (x^ ...) c ... (== `[pat^ ...] ls) g ...)]
                                ...)])
               #'(let ([ls (list v ...)]) body)))))]
      [(matche v (pat g ...) ...)
       #'(matche (v) ([pat] g ...) ...)])))

(defmatche (append l₁ l₂ l₁++l₂)
  ((() ,b ,b))
  (((,h . ,t₁) ,b (,h . ,t₂)) (append t₁ b t₂)))

(defmatche (nrev l₁ l₂) 
  ((() ()))
  (((,h . ,t) ,l₂) 
   (fresh (r)
     (nrev t r) (append r `(,h) l₂))))

(let ((u/v* (hash-ref (caar (run 1 (q) (nrev '(a b c) q))) '==)))
  (let ((u* (map car u/v*))
        (v* (map cdr u/v*)))
    (project-var0 (cons (unify u* v* '()) 25))))
