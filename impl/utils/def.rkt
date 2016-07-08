#lang typed/racket/base

(provide ::= #;define-type/pred define-parameter :*)

(require
 (for-syntax racket/base
             (except-in racket/syntax format-symbol)
             syntax/parse
             "pretty.rkt"))

;; Define type `t` along with predicate `t?`
(define-syntax (define-type/pred stx)
  (syntax-case stx ()
    [(_ τ e) (with-syntax ([τ? (format-id #'τ "~a?" #'τ)])
               #'(begin (define-type τ e)
                        (define-predicate τ? τ)))]))

(begin-for-syntax
  (define-syntax-class sid
    #:description "identifier prefixed with `-`"
    (pattern id
       #:fail-unless
       (regexp-match? #rx"-.+" (symbol->string (syntax-e #'id)))
       "struct name must be prefixed with `-`")))

;; define data-type hierarchy
(define-syntax-rule (τ . ::= . σ ...)
  (τ . ::=/ac . (σ ...) ()))
(define-syntax ::=/ac
  (syntax-rules (struct)
    [(_ τ () (σ ...))
     (define-type τ (U σ ...))]
    [(_ τ ((struct k fs ...) clauses ...) (σ ...))
     (begin (struct k (fs ...) #:transparent)
            (τ . ::=/ac . (clauses ...) (k σ ...)))]
    [(_ τ (τ₁ clauses ...) (σ ...))
     (τ . ::=/ac . (clauses ...) (τ₁ σ ...))]))

;; Shorthand for defining parameter
(define-syntax define-parameter
  (syntax-rules (:)
    [(_ x : τ v) (define x : (Parameterof τ) (make-parameter v))]))

;; define the same type for multiple identifiers
(define-syntax (:* stx)
  (syntax-parse stx
    #:literals (:)
    [(_ x:id ... : τ ...)
     #'(begin (: x : τ ...) ...)]))
