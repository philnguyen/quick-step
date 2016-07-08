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
;; that maps current state to store-deltas and set of next configurations 
(define ↓
  (match-lambda
    [(and v (or (? -b?) (? -o?)))
     (λ (ρ σ ⟦k⟧)
       (⟦k⟧ v σ))]
    [(-x x)
     (λ (ρ σ ⟦k⟧)
       (for*/ans ([V (in-set (hash-ref σ (hash-ref ρ x)))])
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
       (⟦e⟧ ρ σ (push-if ⟦e₁⟧ ⟦e₂⟧ ρ ⟦k⟧)))]
    [(-@ e₁ e₂)
     (define ⟦e₁⟧ (↓ e₁))
     (define ⟦e₂⟧ (↓ e₂))
     (λ (ρ σ ⟦k⟧)
       (⟦e₁⟧ ρ σ (push-ar ⟦e₂⟧ ρ ⟦k⟧)))]
    [(-set! x e)
     (define ⟦e⟧ (↓ e))
     (λ (ρ σ ⟦k⟧)
       (⟦e⟧ ρ σ (push-set! (hash-ref ρ x) ⟦k⟧)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Compile Stack
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Memoization ensures the same function is returned for the same stack behavior

(define/memo (rt [αₖ : -αₖ]) : -⟦k⟧
  (λ (A σ)
    (values {set (-r A αₖ)} ⊥σ ⊥σₖ)))

(define/memo (push-if [⟦e⟧₁ : -⟦e⟧] [⟦e⟧₂ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (λ (A σ)
    (match A
      [(? -err? err) (⟦k⟧ err σ)] ; TODO: faster if had `αₖ` here
      [0             (⟦e⟧₂ ρ σ ⟦k⟧)]
      ['N            (⊔/ans (⟦e⟧₁ ρ σ ⟦k⟧) (⟦e⟧₂ ρ σ ⟦k⟧))]
      [_             (⟦e⟧₁ ρ σ ⟦k⟧)])))

(define/memo (push-ar [⟦e⟧ : -⟦e⟧] [ρ : -ρ] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (λ (A σ)
    (cond
      [(-err? A) (⟦k⟧ A σ)] ; TODO: faster if had `αₖ` here
      [else      (⟦e⟧ ρ σ (push-fn A ⟦k⟧))])))

(define/memo (push-fn [Vₕ : -V] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (λ (A σ)
    (cond
      [(-err? A) (⟦k⟧ A σ)] ; TODO: faster if had `αₖ` here
      [else
       (define Vₓ : -V A)
       (match Vₕ
         [(-clo x ⟦e⟧ ρ)
          (define α (-α x #|0CFA|# #f))
          (define ρ* (hash-set ρ x α))
          (define αₖ (-αₖ ⟦e⟧ ρ*))
          (define δσ  (⊔ ⊥σ  α  Vₓ))
          (define δσₖ (⊔ ⊥σₖ αₖ ⟦k⟧))
          (values {set αₖ} δσ δσₖ)]
         [(? -o? o)
          (⟦k⟧ (δ o Vₓ) σ)]
         [(? -b? b)
          (⟦k⟧ (-err (format "apply non-function: ~a" b)) σ)])])))

(define/memo (push-set! [α : -α] [⟦k⟧ : -⟦k⟧]) : -⟦k⟧
  (λ (A σ)
    (cond
      [(-err? A) (⟦k⟧ A σ)] ; TODO: faster if had `αₖ` here
      [else
       (define-values (ςs δσ δσₖ) (⟦k⟧ 1 (⊔ σ α A)))
       (values ςs (⊔ δσ α A) δσₖ)])))


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
