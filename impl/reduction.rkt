#lang typed/racket/base

(provide ↝* ↝)

(require "utils/main.rkt"
         "data.rkt"
         "compilation.rkt"
         racket/set
         racket/match)

(: ↝* : -αₖ → (Values (℘ -A) -σ -σₖ))
;; Given initial configuration, explore state space then return answers and final stores
(define (↝* αₖ)
  
  (define seen : (HashTable -ς (Pairof Integer Integer)) (make-hash))
  (define-set ans : -A)
  (define σ  : -σ  (⊥vm))
  (define σₖ : -σₖ (⊥vm))
  
  (let loop! ([front : (℘ -ς) {set αₖ}])
    (cond
      [(set-empty? front)
       (printf "~a configs, |σ| = ~a, |σₖ| = ~a~n"
               (+ 1 (hash-count seen)) (hash-count (VMap-m σ)) (hash-count (VMap-m σₖ)))
       (values ans σ σₖ)]
      [else

       ;; Compute new frontier and store deltas
       (define front₁ (for*/ans ([ς front]) (↝ ς σ σₖ)))

       ;; Skip visited states in next frontier, and
       ;; collect answer for the start context
       (define-set front* : -ς)
       (define σ² (cons (VMap-version σ) (VMap-version σₖ)))
       (for ([ς front₁])
         ;; Skip visited states
         (unless (equal? σ² (hash-ref seen ς #f))
           (hash-set! seen ς σ²)
           (front*-add! ς))
         ;; Collect answer
         (match ς
           [(-r A (== αₖ)) (ans-add! A)]
           [_ (void)]))
       
       (loop! front*)])))

(: ↝ : -ς -σ -σₖ → (℘ -ς))
;; Step to next configurations and return store deltas
;; TODO: Could have kept `ςs` partitioned in the first place to avoid this dispatch
;; But keep it simple for now
(define (↝ ς σ σₖ)
  (match ς
    [(and αₖ (-αₖ ⟦e⟧ ρ))
     (⟦e⟧ ρ σ σₖ (rt αₖ))]
    [(-r A αₖ)
     (for*/ans ([⟦k⟧ (σₖ@ σₖ αₖ)])
       (⟦k⟧ A σ σₖ))]))
