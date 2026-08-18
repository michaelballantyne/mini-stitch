#lang racket

;; ---------------------------------------------------------------------------
;; tests/support.rkt --- shared helpers for the test files
;; ---------------------------------------------------------------------------
;;
;; Infrastructure, not algorithm: neither implementation in src/ uses anything
;; here.  These three helpers exist so that the test files can read stitch's own
;; corpus files, which are text, and can compare two implementations that keep
;; programs in two different representations.
;;
;;   parse         String -> Term.  Read one program in stitch's surface syntax
;;                 into a micro-stitch tree.  expr.rkt owns the parser (and its
;;                 error messages); we unfold its arena representation back into
;;                 an ordinary tree.
;;   term->string  Pattern -> String.  Print a micro-stitch Term, Argument or
;;                 Pattern by folding it into a scratch corpus and deferring to
;;                 expr.rkt's printer, so that both systems print character for
;;                 character alike.  A hole prints as `??` and the paper's &d as
;;                 `&d`; neither can occur in a finished abstraction body.
;;   canonical     Pattern -> String.  The body printed with its abstraction
;;                 variables renumbered in order of first appearance, left to
;;                 right.  Two searches can introduce variables in different
;;                 orders and still mean the same abstraction, so bodies are
;;                 compared through this.
;; ---------------------------------------------------------------------------

(require "../src/expr.rkt"
         "../src/micro.rkt")

(provide parse term->string canonical)

;; parse : String -> Term
(define (parse text)
  (define c (make-corpus))
  (define root (parse-program! c text))
  (let unfold ([i root])
    (define n (corpus-node c i))
    (cond [(app? n) (app (unfold (app-fun n)) (unfold (app-arg n)))]
          [(lam? n) (lam (unfold (lam-body n)))]
          [else n])))

;; term->string : Pattern -> String
(define scratch-corpus (make-corpus))
(define (term->string t)
  (define (intern t)
    (cond [(app? t) (add-node! scratch-corpus (app (intern (app-fun t))
                                                   (intern (app-arg t))))]
          [(lam? t) (add-node! scratch-corpus (lam (intern (lam-body t))))]
          [(eq? t 'hole) (add-node! scratch-corpus (prim '??))]
          [(captured? t)
           (add-node! scratch-corpus (prim (string->symbol
                                            (format "&~a" (captured-i t)))))]
          [else (add-node! scratch-corpus t)]))
  (expr->string scratch-corpus (intern t)))

;; canonical : Pattern -> String
(define (canonical p)
  (define seen '())
  (define (rename t)
    (cond [(ivar? t)
           (unless (memv (ivar-i t) seen)
             (set! seen (append seen (list (ivar-i t)))))
           (ivar (index-of seen (ivar-i t)))]
          [(app? t) (app (rename (app-fun t)) (rename (app-arg t)))]
          [(lam? t) (lam (rename (lam-body t)))]
          [else t]))
  (term->string (rename p)))

(module+ test
  (require rackunit)

  (test-case "parsing and printing round-trip through micro's trees"
    (check-equal? (term->string (parse "(a a a)")) "(a a a)")
    (check-equal? (term->string (parse "((f x) y)")) "(f x y)")
    (check-equal? (term->string (parse "(lambda (+ $0 b))")) "(lam (+ $0 b))")
    (check-equal? (parse "(f x)") (app (prim 'f) (prim 'x)))
    (check-equal? (parse "(lam $0)") (lam (var 0))))

  (test-case "holes, captures and canonical renaming"
    (check-equal? (term->string (app (prim 'f) 'hole)) "(f ??)")
    (check-equal? (term->string (captured 0)) "&0")
    ;; the variables are renumbered in order of first appearance
    (check-equal? (canonical (parse "(f #1 #0)")) "(f #0 #1)")
    (check-equal? (canonical (parse "(f #0 #1)")) "(f #0 #1)")))
