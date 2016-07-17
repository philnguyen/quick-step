#lang typed/racket/base

(provide ↓ rt)

(require "utils/main.rkt"
         "data.rkt"
         racket/set
         racket/match)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compile Expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: ↓ : -e → -⟦e⟧)
;; Compile expression into computation
;; that maps current state to store-deltas and set of next configurations.
;; This is essentially a big-step interpreter written in CPS.
(define ↓
  (match-lambda
    [(and v (or (? -b?) (? -o?)))
     (λ (ρ σ σₖ ⟦k⟧)
       (⟦k⟧ v σ σₖ))]
    [(-x x)
     (λ (ρ σ σₖ ⟦k⟧)
       (for*/ans ([V (σ@ σ (hash-ref ρ x))])
         (⟦k⟧ V σ σₖ)))]
    [(-λ x e)
     (define ⟦e⟧ (↓ e))
     (λ (ρ σ σₖ ⟦k⟧)
       (⟦k⟧ (-clo x ⟦e⟧ ρ) σ σₖ))]
    [(-if e e₁ e₂)
     (define ⟦e⟧  (↓ e ))
     (define ⟦e₁⟧ (↓ e₁))
     (define ⟦e₂⟧ (↓ e₂))
     (λ (ρ σ σₖ ⟦k⟧)
       (⟦e⟧ ρ σ σₖ (if∷ ⟦e₁⟧ ⟦e₂⟧ ρ ⟦k⟧)))]
    [(-@ e₁ e₂)
     (define ⟦e₁⟧ (↓ e₁))
     (define ⟦e₂⟧ (↓ e₂))
     (λ (ρ σ σₖ ⟦k⟧)
       (⟦e₁⟧ ρ σ σₖ (ar∷ ⟦e₂⟧ ρ ⟦k⟧)))]
    [(-set! x e)
     (define ⟦e⟧ (↓ e))
     (λ (ρ σ σₖ ⟦k⟧)
       (⟦e⟧ ρ σ σₖ (set!∷ (hash-ref ρ x) ⟦k⟧)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compose Continuation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The interpreted language's continuation is that of the meta-language,
;; except chunked at function boundaries and allocated in the continuation store

(define-syntax-rule (define-kont (f fields ...) (⟦k⟧ A σ σₖ) e ...)
  ;; Memoization ensures the same function is returned for the same stack behavior
  (define/memo (f fields ... [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (λ (A σ σₖ)
      (cond [(-err? A) (⟦k⟧ A σ σₖ)] ; TODO: faster if has `αₖ`
            [else e ...]))))

(define/memo (rt [αₖ : -αₖ]) : -⟦k⟧
  (λ (A σ σₖ) {set (-r A αₖ)}))

(define-kont (if∷ [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ]) (⟦k⟧ V σ σₖ)
  (define (t) (⟦e⟧₁ ρ σ σₖ ⟦k⟧))
  (define (f) (⟦e⟧₂ ρ σ σₖ ⟦k⟧))
  (match V
    [0  (f)]
    ['N (⊕ (t) (f))]
    [_  (t)]))

(define-kont (ar∷ [⟦e⟧ : -⟦e⟧] [ρ : -ρ]) (⟦k⟧ V σ σₖ)
  (⟦e⟧ ρ σ σₖ (fn∷ V ⟦k⟧)))

(define-kont (fn∷ [Vₕ : -V]) (⟦k⟧ Vₓ σ σₖ)

  (: clo-app : Symbol -⟦e⟧ -ρ → (℘ -ς))
  (define (clo-app x ⟦e⟧ ρ)
    (define α (-α x #f)) ; 0CFA
    (define ρ* (hash-set ρ x α))
    (define αₖ (-αₖ ⟦e⟧ ρ*))
    (σ⊔!  σ  α  Vₓ)
    (σₖ⊔! σₖ αₖ ⟦k⟧)
    {set αₖ})

  (match Vₕ
    [(-clo x ⟦e⟧ ρ) (clo-app x ⟦e⟧ ρ)]
    [(? -o? o)     (⟦k⟧ (δ o Vₓ) σ σₖ)]
    [(? -b? b)     (⟦k⟧ (-err (format "apply non-function: ~a" b)) σ σₖ)]))

(define-kont (set!∷ [α : -α]) (⟦k⟧ V σ σₖ)
  (σ⊔! σ α V)
  (⟦k⟧ 1 σ σₖ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Interpret Primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: δ : -o -V → -A)
(define (δ o V)
  (define (err) (-err (format "~a: ~a" o V)))
  (case o
    [(sub1 add1)
     (match V
       [(or 'N (? number?)) 'N]
       [_ (err)])]
    [(integer?)
     (match V
       [(or 'N (? number?)) 1]
       [_ 0])]
    [(procedure?)
     (match V
       [(or (? -o?) (? -clo?)) 1]
       [_ 0])]
    [(zero?)
     (match V
       ['N 'N]
       [(? number? n) (if (= n 0) 1 0)]
       [_ (err)])]
    [else (error 'δ "unhandled: ~a" o)]))
