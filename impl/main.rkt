#lang typed/racket/base

(provide run run/parse)

(require "utils/main.rkt"
         "data.rkt"
         "parse.rkt"
         "compilation.rkt"
         "reduction.rkt"
         )

(: run : -e → (Values (℘ -A) -σ))
(define (run e)
  (define-values (As σ σₖ) (↝* (-αₖ (↓ e) ⊥ρ)))
  (values As σ))

(: run/parse : Any → (Values (℘ -A) -σ))
(define (run/parse e) (run (parse e)))

(: bm : -e → Void)
(define (bm e)
  (collect-garbage) (collect-garbage) (collect-garbage)
  (time (run e) (void)))

(require/typed/provide profile
  [profile-thunk (∀ (X) ([(→ X)] [#:delay Nonnegative-Real #:repeat Natural] . ->* . X))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define e.sat-10
  (parse
   `(let* ([try (λ (f) (or (f 0) (f 1)))]
           [p (λ* (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀)
                (and x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀))]
           [solve
            (λ (q)
              (try (λ (n₁)
                     (try (λ (n₂)
                            (try (λ (n₃)
                                   (try (λ (n₄)
                                          (try (λ (n₅)
                                                 (try (λ (n₆)
                                                        (try (λ (n₇)
                                                               (try (λ (n₈)
                                                                      (try (λ (n₉)
                                                                             (try (λ (n₁₀)
                                                                                    (@* q n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀)))
                                                                             )))))))))))))))))))])
      (solve p))))

(define e.kcfa3
  (parse
   `((λ (f1)
       (let* ((a (f1 1)))
         (f1 0)))
     (λ (x1)
       ((λ (f2)
          (let* ((b (f2 1)))
            (f2 0)))
        (λ (x2)
          ((λ (f3)
             (let* ((c (f3 1)))
               (f3 0)))
           (λ (x3)
             ((λ (z) (@* z x1 x2 x3))
              (λ* (y1 y2 y3) y1))))))))))

#;(define e.pair
  (parse
   '(let* ([cons (λ* (x y msg) (if msg x y))]
           [car (λ (p) (p 1))]
           [cdr (λ (p) (p 2))]
           [cadr (λ (p) (car (cdr p)))]
           [Y (λ* (f x)
                (@* (λ (g) (f (λ (x) ((g g) x))))
                    (λ (g) (f (λ (x) ((g g) x))))
                    x))]
           [foldr (Y (λ* (foldr f x₀ xs)
                       (if (procedure? xs)
                           (@* f (car xs) (@* foldr f x₀ (cdr xs)))
                           x₀)))]
           [map (λ* (f xs)
                  (@* foldr (λ* (x ys) (@* cons (f x) ys)) 0 xs))])
      (car (@* map add1 (@* cons 1 (@* cons 2 (@* cons 3 0))))))))
