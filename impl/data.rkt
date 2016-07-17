#lang typed/racket/base

(provide (all-defined-out))

(require "utils/main.rkt"
         racket/set
         racket/match)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Utils
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct (X Y) VMap ([m : (HashTable X (℘ Y))] [version : Integer]) #:transparent #:mutable)

(: ⊥vm (∀ (X Y) → (VMap X Y)))
(define (⊥vm) (VMap ((inst make-hash X (℘ Y))) 0))

(: vm⊔! (∀ (X Y) (VMap X Y) X Y → Integer))
(define (vm⊔! vm x y)
  (match-define (VMap m i) vm)
  (cond
    [(∋ (hash-ref m x →∅) y) i]
    [else
     (hash-update! m x (λ ([ys : (℘ Y)]) (set-add ys y)) →∅)
     (define i* (+ 1 i))
     (set-VMap-version! vm i*)
     i*]))

(: vm@ (∀ (X Y) (VMap X Y) X → (℘ Y)))
(define (vm@ vm x) (hash-ref (VMap-m vm) x →∅))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-e . ::= . -v
            -x
            (struct -@ [fun : -e] [arg : -e])
            (struct -if [if : -e] [then : -e] [else : -e])
            (struct -set! [var : Symbol] [rhs : -e]))
(-v . ::= . -o
            -b
            (struct -λ [var : Symbol] [body : -e]))
(-o . ::= . 'sub1 'add1 'integer? 'procedure? 'zero?)
(-b . ::= . Number 'N)
(struct -x ([name : Symbol]) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Semantics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|Answer|# (-A . ::= . -V
                       (struct -err [msg : String]))
#|Value |# (-V . ::= . -o
                       -b
                       (struct -clo [var : Symbol] [body : -⟦e⟧] [env : -ρ]))

#|Value Address|# (struct -α  ([var : Symbol] [ctx : Any]) #:transparent)
#|Stack Address|# (struct -αₖ ([exp : -⟦e⟧] [env : -ρ]) #:transparent)
#|Environment  |# (-ρ . ::= . (HashTable Symbol -α))
#|Value Store  |# (define-type -σ  (VMap -α  -V))
#|Stack Store  |# (define-type -σₖ (VMap -αₖ -⟦k⟧))
#|Configuration|# (-ς . ::= . #|function begin |# -αₖ
                              #|function return|# (struct -r [ans : -A] [target : -αₖ]))

;; Stacks are not first-class, so computation doesn't care about stack-store for now
#|Compiled expression  |# (-⟦e⟧ . ::= . (-ρ -σ -σₖ -⟦k⟧ → (℘ -ς)))
#|Compiled continuation|# (-⟦k⟧ . ::= . (-A -σ -σₖ     → (℘ -ς)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Constants
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ⊥ρ : -ρ (hasheq))

(define-predicate -o? -o)
(define-predicate -b? -b)

(define-syntax-rule (for*/ans (clauses ...) e ...)
  (for*/fold ([acc : (℘ -ς) ∅]) (clauses ...)
    (∪ acc (let () e ...))))

(define ⊕ ∪)
(define σ⊔!  (inst vm⊔! -α  -V))
(define σₖ⊔! (inst vm⊔! -αₖ -⟦k⟧))

(define σ@  (inst vm@ -α  -V))
(define σₖ@ (inst vm@ -αₖ -⟦k⟧))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Derived Syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: -let : Symbol -e -e → -e)
(define (-let x eₓ e)
  (-@ (-λ x e) eₓ))

(: -let* : (Listof Symbol) (Listof -e) -e → -e)
(define (-let* xs eₓs e)
  (match* (xs eₓs)
    [('() '()) e]
    [((cons x xs*) (cons eₓ eₓs*))
     (-let x eₓ (-let* xs* eₓs* e))]))

(: -begin : (Listof -e) → -e)
(define -begin
  (match-lambda
    ['() 1]
    [(list e) e]
    [(cons e es) (-let (gensym 'let_) e (-begin es))]))

(: -begin0 : -e (Listof -e) → -e)
(define (-begin0 e₀ es)
  (define x (gensym 'begin0_))
  (-let x e₀ (-begin (list (-begin es) (-x x)))))

(:* -and -or : (Listof -e) → -e)
(define -and
  (match-lambda
    [(list) 1]
    [(list e) e]
    [(list e₁ es ...) (-if e₁ (-and es) 0)]))
(define -or
  (match-lambda
    [(list) 0]
    [(list e) e]
    [(list e₁ es ...)
     (define x (gensym 'or_))
     (-let x e₁ (-if (-x x) (-x x) (-or es)))]))

(: -λ* : (Pairof Symbol (Listof Symbol)) -e → -λ)
(define (-λ* xs e)
  (match-define (cons x xs*) xs)
  (cond
    [(null? xs*) (-λ x e)]
    [else        (-λ x (-λ* xs* e))]))

(: -@* : -e (Pairof -e (Listof -e)) → -@)
(define (-@* e es)
  (match-define (cons eₓ es*) es)
  (cond
    [(null? es*) (-@ e eₓ)]
    [else        (-@* (-@ e eₓ) es*)]))
