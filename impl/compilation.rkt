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
     (λ (ρ σ ⟦k⟧)
       (⟦k⟧ v σ))]
    [(-x x)
     (λ (ρ σ ⟦k⟧)
       (for*/ans ([V (hash-ref σ (hash-ref ρ x))])
         (⟦k⟧ V σ)))]
    [(-λ x e)
     (define ⟦e⟧ (↓ e))
     (λ (ρ σ ⟦k⟧)
       (⟦k⟧ (-clo x ⟦e⟧ ρ) σ))]
    [(-if e e₁ e₂)
     (define ⟦e⟧  (↓ e ))
     (define ⟦e₁⟧ (↓ e₁))
     (define ⟦e₂⟧ (↓ e₂))
     (λ (ρ σ ⟦k⟧)
       (⟦e⟧ ρ σ (if∷ ⟦e₁⟧ ⟦e₂⟧ ρ ⟦k⟧)))]
    [(-@ e₁ e₂)
     (define ⟦e₁⟧ (↓ e₁))
     (define ⟦e₂⟧ (↓ e₂))
     (λ (ρ σ ⟦k⟧)
       (⟦e₁⟧ ρ σ (ar∷ ⟦e₂⟧ ρ ⟦k⟧)))]
    [(-set! x e)
     (define ⟦e⟧ (↓ e))
     (λ (ρ σ ⟦k⟧)
       (⟦e⟧ ρ σ (set!∷ (hash-ref ρ x) ⟦k⟧)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compose Continuation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The interpreted language's continuation is that of the meta-language,
;; except chunked at function boundaries and allocated in the continuation store

(define-syntax-rule (define-pusher (f fields ...) (⟦k⟧ A σ) e ...)
  ;; Memoization ensures the same function is returned for the same stack behavior
  (define/memo (f fields ... [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
    (λ (A σ)
      (cond [(-err? A) (⟦k⟧ A σ)] ; TODO: faster if has `αₖ`
            [else e ...]))))

(define/memo (rt [αₖ : -αₖ]) : -⟦k⟧
  (λ (A σ)
    (values {set (-r A αₖ)} ⊥σ ⊥σₖ)))

(define-pusher (if∷ [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ]) (⟦k⟧ V σ)
  (define (t) (⟦e⟧₁ ρ σ ⟦k⟧))
  (define (f) (⟦e⟧₂ ρ σ ⟦k⟧))
  (match V
    [0  (f)]
    ['N (⊕ (t) (f))]
    [_  (t)]))

(define-pusher (ar∷ [⟦e⟧ : -⟦e⟧] [ρ : -ρ]) (⟦k⟧ V σ)
  (⟦e⟧ ρ σ (fn∷ V ⟦k⟧)))

(define-pusher (fn∷ [Vₕ : -V]) (⟦k⟧ Vₓ σ)

  (: clo-app : Symbol -⟦e⟧ -ρ → (Values (℘ -ς) -Δσ -Δσₖ))
  (define (clo-app x ⟦e⟧ ρ)
    (define α (-α x #f)) ; 0CFA
    (define ρ* (hash-set ρ x α))
    (define αₖ (-αₖ ⟦e⟧ ρ*))
    (values {set αₖ} (⊔ ⊥σ α Vₓ) (⊔ ⊥σₖ αₖ ⟦k⟧)))

  (match Vₕ
    [(-clo x ⟦e⟧ ρ) (clo-app x ⟦e⟧ ρ)]
    [(? -o? o)     (⟦k⟧ (δ o Vₓ) σ)]
    [(? -b? b)     (⟦k⟧ (-err (format "apply non-function: ~a" b)) σ)]))

(define-pusher (set!∷ [α : -α]) (⟦k⟧ V σ)
  (define-values (ςs δσ δσₖ) (⟦k⟧ 1 (⊔ σ α V)))
  (values ςs (⊔ δσ α V) δσₖ))


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
