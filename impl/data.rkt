#lang typed/racket/base

(provide (all-defined-out))

(require "utils/main.rkt"
         racket/set
         racket/match)

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
#|Environment  |# (-ρ   . ::= . (HashTable Symbol -α))
#|Value Store  |# (-σ   . ::= . (HashTable -α (℘ -V)))
                  (-Δσ  . ::= . -σ)
#|Stack Store  |# (-σₖ  . ::= . (HashTable -αₖ (℘ -⟦k⟧)))
                  (-Δσₖ . ::= . -σₖ)
#|Configuration|# (-ς . ::= . #|function begin |# -αₖ
                              #|function return|# (struct -r [ans : -A] [target : -αₖ]))

;; Stacks are not first-class, so computation doesn't care about stack-store for now
#|Compiled expression  |# (-⟦e⟧ . ::= . (-ρ -σ -⟦k⟧ → (Values (℘ -ς) -Δσ -Δσₖ)))
#|Compiled continuation|# (-⟦k⟧ . ::= . (-A -σ     → (Values (℘ -ς) -Δσ -Δσₖ)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Constants
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ⊥ρ  : -ρ  (hasheq))
(define ⊥σ  : -σ  (hash))
(define ⊥σₖ : -σₖ (hash))

(define-predicate -o? -o)
(define-predicate -b? -b)

(define-syntax-rule (for*/ans (clauses ...) e ...)
  (for*/fold ([ςs  : (℘ -ς) ∅ ]
              [δσ  : -Δσ    ⊥σ ]
              [δσₖ : -Δσₖ   ⊥σₖ])
             (clauses ...)
    (define-values (ςs* δσ* δσₖ*) (let () e ...))
    (values (∪   ςs  ςs* )
            (⊔/m δσ  δσ* )
            (⊔/m δσₖ δσₖ*))))

(define-syntax ⊕
  (syntax-rules ()
    [(_) (values ∅ ⊥σ ⊥σₖ)]
    [(_ e) e]
    [(_ e e* ...)
     (let-values ([(ςs  δσ  δσₖ ) (let () e)]
                  [(ςs* δσ* δσₖ*) (⊕ e* ...)])
       (values (∪   ςs  ςs* )
               (⊔/m δσ  δσ* )
               (⊔/m δσₖ δσₖ*)))]))


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
