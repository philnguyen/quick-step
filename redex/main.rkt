#lang racket/base

(require redex
         racket/set
         racket/match
         racket/contract)

(define-language Λ
  ;; Syntax
  [e ::= v x (e e) (if e e e) (set! x e)]
  [v ::= o b (λ (x) e)]
  [o ::= add1 integer? procedure?]
  [b ::= integer ℤ]
  [x ::= variable-not-otherwise-mentioned]
  ;; Semantics
  [#|Answer       |# A  ::= V (err string)]
  [#|Value        |# V  ::= o b (clo x e ρ)]
  [#|Kontinuation |# κ  ::= (φ ... αₖ)]
  [#|Kont. Frame  |# φ  ::= (ar e ρ) (fn V) (if e e ρ) (set! α)]
  [#|Value Address|# α  ::= any]
  [#|Kont. Address|# αₖ ::= (e ρ)] ; fixed choice, from P4F
  [#|Environment  |# ρ  ::= (side-condition (name ρ  any) (ρ?  (term ρ )))]
  [#|Value Store  |# σ  ::= (side-condition (name σ  any) (σ?  (term σ )))]
  [#|Kont. Store  |# σₖ ::= (side-condition (name σₖ any) (σₖ? (term σₖ)))]
  [#|Configuration|# ς  ::= #|function begin |# αₖ
                            #|function return|# (A αₖ)]
  [#|State        |# Σ  ::= (ς σ σₖ)])

(define α?  (redex-match? Λ α ))
(define αₖ? (redex-match? Λ αₖ))
(define V?  (redex-match? Λ V))
(define x?  (redex-match? Λ x))
(define κ?  (redex-match? Λ κ))
(define ρ?  (hash/c x?  α?         #:flat? #t))
(define σ?  (hash/c α?  (set/c V?) #:flat? #t))
(define σₖ? (hash/c αₖ? (set/c κ?) #:flat? #t))
(define-term ⊥ρ ,(hash))
(define-term ⊥σ ,(hash))

(define-metafunction Λ
  𝑰 : e -> Σ
  ;; Load initial state
  [(𝑰 e) (αₖ ⊥σ σₖ)
   (where αₖ (e ⊥ρ))
   (where σₖ ,(hash (term αₖ) (set)))])

;; quick-step on (narrow) states (↝ ⊆ Σ × Σ)
(define ↝
  (reduction-relation Λ #:domain Σ

   ;; There's no separate stack component (though the stack-store maps addresses to stacks).
   ;; The stack is accumulated and destroyed (or saved to store) during each "quick" step.
   ;; This state space is an abstraction of small-step,
   ;; where there are only 2 classes of states:

   ;; ⟨⟨e,ρ⟩, σ, σₖ⟩ marks the beginning of function body `e` in context `ρ`
   ;; This `⟨e,ρ⟩` is also the stack address to return to when done.                      
   [(αₖ σ σₖ) . --> . Σ
    Eval
    (judgment-holds ((αₖ) αₖ σ σₖ . ↓ₑ . Σ))]

   ;; ⟨⟨A,⟨e,ρ⟩⟩, σ, σₖ⟩ marks the finished evaluation of closure body `⟨e,ρ⟩` with result `A`,
   ;; about to return to each stack in `σₖ(⟨e,ρ⟩)`
   [((A αₖ) σ σₖ) . --> . Σ
    Kont
    (judgment-holds (κ . ∈ . (@ σₖ αₖ)))
    (judgment-holds (κ A σ σₖ . ↓ₖ . Σ))]))

;; Big-step-ish relation that:
;; - When jumping to another λ's body, pushes the current stack and "pauses"
;;   at the start of this new body
;; - When done evaluating a λ's body, returns the "local" result
(define-judgment-form Λ
  #:contract (κ αₖ σ σₖ . ↓ₑ . Σ)
  #:mode     (I I  I I  . ↓ₑ . O)

  ;; Bases
  
  [(κ  o    σ σₖ . ↓ₖ . Σ)
   -------------------------------------------------------------------"E-Op"
   (κ (o _) σ σₖ . ↓ₑ  . Σ)]

  [(κ  b    σ σₖ . ↓ₖ . Σ)
   -------------------------------------------------------------------"E-Base"
   (κ (b _) σ σₖ . ↓ₑ . Σ)]

  [(κ (clo x e ρ)   σ σₖ . ↓ₖ . Σ)
   -------------------------------------------------------------------"E-Lam"
   (κ ((λ (x) e) ρ) σ σₖ . ↓ₑ . Σ)]

  [(V . ∈ . (@ σ (@ ρ x)))
   (κ V     σ σₖ . ↓ₖ . Σ)
   -------------------------------------------------------------------"E-Var"
   (κ (x ρ) σ σₖ . ↓ₑ . Σ)]

  ;; Pushes
  
  [(((if e_1 e_2 ρ) φ ... αₖ) (    e          ρ) σ σₖ . ↓ₑ . Σ)
   -------------------------------------------------------------------"E-If"
   ((               φ ... αₖ) ((if e e_1 e_2) ρ) σ σₖ . ↓ₑ . Σ)]

  [(((ar e_2 ρ) φ ... αₖ) ( e_1      ρ) σ σₖ . ↓ₑ . Σ)
   -------------------------------------------------------------------"E-App"
   ((           φ ... αₖ) ((e_1 e_2) ρ) σ σₖ . ↓ₑ . Σ)]

  [(((set! (@ ρ x)) φ ... αₖ) (        e  ρ) σ σₖ . ↓ₑ . Σ)
   -------------------------------------------------------------------"E-Set!"
   ((               φ ... αₖ) ((set! x e) ρ) σ σₖ . ↓ₑ . Σ)]
  )

(define-judgment-form Λ
  #:contract (κ A σ σₖ . ↓ₖ . Σ)
  #:mode     (I I I I  . ↓ₖ . O)

  [-------------------------------------------------------------------"K-Ret"
   ((αₖ) V σ σₖ . ↓ₖ . ((V αₖ) σ σₖ))]

  [(maybe-t? V)
   ((           φ ... αₖ) (e ρ) σ σₖ . ↓ₑ . Σ)
   -------------------------------------------------------------------"K-IfT"
   (((if e _ ρ) φ ... αₖ) V     σ σₖ . ↓ₖ . Σ)]

  [(maybe-f? V)
   ((           φ ... αₖ) (e ρ) σ σₖ . ↓ₑ . Σ)
   -------------------------------------------------------------------"K-IfF"
   (((if _ e ρ) φ ... αₖ) V     σ σₖ . ↓ₖ . Σ)]

  [(((fn V)   φ ... αₖ) (e ρ) σ σₖ . ↓ₑ . Σ)
   -------------------------------------------------------------------"K-AppSwap"
   (((ar e ρ) φ ... αₖ) V     σ σₖ . ↓ₖ . Σ)]

  [(where α    x) ; 0CFA
   (where ρ_1  (ext ρ x α))
   (where κ    (φ ... αₖ))
   (where αₖ_1 (e ρ_1))
   (where σ_1  (⊔ σ α V))
   (where σₖ_1 (⊔ σₖ αₖ_1 κ))
   -------------------------------------------------------------------"K-AppClo"
   (((fn (clo x e ρ)) φ ... αₖ) V σ σₖ . ↓ₖ . (αₖ_1 σ_1 σₖ_1))]

  [((       φ ... αₖ) (δ o V) σ σₖ . ↓ₖ . Σ)
   -------------------------------------------------------------------"K-AppOp"
   (((fn o) φ ... αₖ) V       σ σₖ . ↓ₖ . Σ)]

  [-------------------------------------------------------------------"K-AppErr"
   (((fn b) φ ... αₖ) _ σ σₖ . ↓ₖ . ((err ,(format "apply ~a" (term b))) σ σₖ))]

  [((         φ ... αₖ) 1 (⊔ σ α V) σₖ . ↓ₖ . Σ)
   -------------------------------------------------------------------"K-Set!"
   (((set! α) φ ... αₖ) V σ         σₖ . ↓ₖ . Σ)]

  [-------------------------------------------------------------------"K-Err"
   ((_ _ ... αₖ) (err string) σ σₖ . ↓ₖ . (((err string) αₖ) σ σₖ))]
  )

(define-metafunction Λ
  δ : o V -> A
  [(δ add1 b          ) ℤ]
  [(δ add1 o          ) (err "add1")]
  [(δ add1 (clo _ _ _)) (err "add1")]
  [(δ integer? b          ) 1]
  [(δ integer? o          ) 0]
  [(δ integer? (clo _ _ _)) 0]
  [(δ procedure? b          ) 0]
  [(δ procedure? o          ) 1]
  [(δ procedure? (clo _ _ _)) 1])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Non-deterministically pick an element in set/list
(define-judgment-form Λ
  #:contract (any . ∈ . any)
  #:mode     (O   . ∈ . I)
  [(side-condition ,(set? (term any_xs)))
   (where {_ ... any_x _ ...} ,(set->list (term any_xs)))
   -------------------------------------------------------------------"∈-Set"
   (any_x . ∈ . any_xs)]
  [-------------------------------------------------------------------"∈-List"
   (any_x . ∈ . {_ ... any_x _ ...})])

;; Look up in map
(define-metafunction Λ
  @ : any any -> any
  [(@ any_m any_x) ,(hash-ref (term any_m) (term any_x))])

;; Join 2 multimaps
(define-metafunction Λ
  ⊔ : any any any -> any
  [(⊔ any_m any_x any_y)
   ,(hash-update (term any_m) (term any_x) (λ (s) (set-add s (term any_y))) set)])

;; Update map
(define-metafunction Λ
  ext : any any any -> any
  [(ext any_m any_x any_y) ,(hash-set (term any_m) (term any_x) (term any_y))])

;; See if `V` is plausibly true (non-0) or false (0)
(define-relation Λ
  maybe-t? ⊆ V
  [(maybe-t? number)
   (side-condition (not (equal? 0 (term number))))]
  [(maybe-t? ℤ)]
  [(maybe-t? o)]
  [(maybe-t? (clo _ _ _))])
(define-relation Λ
  maybe-f? ⊆ V
  [(maybe-f? 0)]
  [(maybe-f? ℤ)])

;; Render state space from running `e`
(define (viz e) (traces ↝ (term (𝑰 ,e))))

;; Render derivation tree of first "quick-step"s on `e`
(define-syntax-rule (show-first-step e)
  (let ()
    (define-term αₖ₁ (e ⊥ρ))
    (show-derivations
     (build-derivations
      ((αₖ₁) αₖ₁ ⊥σ ,(hash (term αₖ₁) (set)) . ↓ₑ . Σ))
     #:racket-colors? #t)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-term e1
  ((λ (x)
     (if (add1 (add1 (add1 x)))
         (set! x 43)
         44))
   42))

;; (viz (term e1))
;; (show-first-step e1)
