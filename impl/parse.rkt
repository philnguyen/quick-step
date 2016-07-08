#lang typed/racket/base

(provide parse)

(require "data.rkt"
         racket/match)

(: parse : Any → -e)
(define parse
  (match-lambda
    ;; Sugar
    [`(let ([,(? symbol? x) ,eₓ]) ,e)
     (-@ (-λ x (parse e)) (parse eₓ))]
    [`(let* ([,(? symbol? x) ,eₓ] ...) ,e)
     (-let* (cast x (Listof Symbol)) (map parse eₓ) (parse e))]
    [`(begin ,e ...) (-begin (map parse e))]
    [`(begin0 ,e₀ ,e ...) (-begin0 (parse e₀) (map parse e))]
    [`(and ,e ...) (-and (map parse e))]
    [`(or ,e ...) (-or (map parse e))]
    [`(λ* (,(? symbol? x) ,(? symbol? xs) ...) ,e) (-λ* (cons x (cast xs (Listof Symbol))) (parse e))]
    [`(@* ,e₁ ,e₂ ,es ...) (-@* (parse e₁) (cons (parse e₂) (map parse es)))]
    ;; Core
    [(? number? n) n]
    [(? -o? o) o]
    [`(λ (,(? symbol? x)) ,e) (-λ x (parse e))]
    [`(if ,e ,e₁ ,e₂) (-if (parse e) (parse e₁) (parse e₂))]
    [`(set! ,(? symbol? x) ,e) (-set! x (parse e))]
    [`(,e₁ ,e₂) (-@ (parse e₁) (parse e₂))]
    [(? symbol? x) (-x x)] ; so can't have `x` overlapping with `o`
    [e (error 'parse "can't: ~a" e)]))
