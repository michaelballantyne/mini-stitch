#lang racket

;; ---------------------------------------------------------------------------
;; tests/microkanren-test.rkt --- rediscovering miniKanren's macros
;; ---------------------------------------------------------------------------
;;
;; microKanren (Hemann and Friedman 2013) is a ~50-line functional core for
;; relational programming; miniKanren's user-facing operators are macros
;; written on top of it (miniKanren-wrappers.scm in jasonhemann/microKanren).
;; The first two of those macros are, verbatim:
;;
;;   (define-syntax Zzz
;;     (syntax-rules () ((_ g) (lambda (s/c) (lambda () (g s/c))))))
;;   (define-syntax fresh   ; at one variable
;;     (syntax-rules () ((_ (x) g) (call/fresh (lambda (x) g)))))
;;
;; Zzz delays a goal (its argument moves under binders -- the reason it must
;; be a macro); fresh introduces a logic variable under a name the USER
;; chooses (a binder-position pattern variable).  This benchmark asks
;; whether macro-compress, given only hand-expanded USES of the core --
;; goals written as a person would write them if the macros did not exist --
;; invents these macros back.  It does, in the order the wrappers file
;; defines them: Zzz first (utility 1515), then fresh (utility 1), and then
;; nothing.
;;
;; The corpus, translated into this repository's object language.  The one
;; translation rule beyond notation: the object language has no nullary
;; lambdas, so microKanren's thunk (lambda () e) becomes a unary lambda
;; with an unused binder -- Zzz g here is (lambda (s) (lambda (d) (g s))).
;; Binder spellings vary per site, as real code's do; that also matters for
;; the search's width (a corpus that spells every state variable `s/c`, as
;; real microKanren output would, lets every partial template that bakes
;; the spelling in survive the two-programs rule, and the enumeration does
;; not finish -- see notes/2026-08-18-1930-microkanren-experiment.md, which
;; also measures the fused alternatives this corpus's winner dominates).
;;
;;   raco test tests/microkanren-test.rkt   (a few seconds)
;; ---------------------------------------------------------------------------

(require rackunit (file "../src/macro-micro.rkt"))

;; P1 = expansion of (fresh (x) (== x 1) (eats x)):
;;      (call/fresh (lambda (x) (conj (Zzz (== x 1)) (Zzz (eats x)))))
(define p1 '(call/fresh (lambda (x)
              (conj (lambda (s1) (lambda (d1) ((== x 1) s1)))
                    (lambda (s2) (lambda (d2) ((eats x) s2)))))))
;; P2 = expansion of (conde ((likes 2)) ((== 3 4))), one delay per clause
(define p2 '(disj (lambda (t1) (lambda (e1) ((likes 2) t1)))
                  (lambda (t2) (lambda (e2) ((== 3 4) t2)))))
;; P3 = expansion of (fresh (q) (halts q))
(define p3 '(call/fresh (lambda (q)
              (lambda (u1) (lambda (f1) ((halts q) u1))))))
(define programs (list p1 p2 p3))

;; the two macros we hope to recover
(define Zzz `(lambda (,(tvar 0)) (lambda (,(tvar 1)) (,(pvar 0) ,(tvar 0)))))
(define fresh1 `(call/fresh (lambda (,(pvar 0)) ,(pvar 1))))

(module+ test
  (test-case "macro-compress rediscovers Zzz, then fresh, then stops"
    (define steps (macro-compress programs 2 3))
    (check-equal? (length steps) 2)
    ;; iteration 1: Zzz.  Every delayed goal in the corpus is a site; the
    ;; five sites pay 404 each (the delay's two lambdas, two binders, and
    ;; the state reference, less the call) against the template's 505
    (check-equal? (mdef-template (learned-macro (first steps))) Zzz)
    (check-equal? (mdef-syntax-rules (learned-macro (first steps)))
                  '(syntax-rules ()
                     [(_ %x0) (lambda (%t0) (lambda (%t1) (%x0 %t0)))]))
    (check-equal? (learned-utility (first steps)) 1515)
    (check-equal? (learned-programs (first steps))
                  '((call/fresh (lambda (x) (conj (m0 (== x 1)) (m0 (eats x)))))
                    (disj (m0 (likes 2)) (m0 (== 3 4)))
                    (call/fresh (lambda (q) (m0 (halts q))))))
    ;; iteration 2: fresh, over a corpus whose bodies are m0 calls.  The
    ;; margin is the thinnest possible: a call/fresh site's scaffolding
    ;; (call/fresh, lambda, the binder's atom, three forms) costs 303 and
    ;; the call replacing it costs 201 plus 100 to pass the binder's name
    ;; -- 102 saved per site, twice, against a 203 template
    (check-equal? (mdef-template (learned-macro (second steps))) fresh1)
    (check-equal? (learned-utility (second steps)) 1)
    (check-equal? (learned-programs (second steps))
                  '((m1 x (conj (m0 (== x 1)) (m0 (eats x))))
                    (disj (m0 (likes 2)) (m0 (== 3 4)))
                    (m1 q (m0 (halts q))))))

  (test-case "fresh needs its binder-position pattern variable"
    ;; on the Zzz-rewritten corpus, both fresh bodies mention their own
    ;; variable through an m0 call's argument, so the template-binder
    ;; variant of fresh is blocked by H1 at every site
    (define m0 (mdef 'm0 1 Zzz))
    (define library (list m0))
    (define rewritten
      '((call/fresh (lambda (x) (conj (m0 (== x 1)) (m0 (eats x)))))
        (call/fresh (lambda (q) (m0 (halts q))))))
    (define fresh1-tvar `(call/fresh (lambda (,(tvar 0)) ,(pvar 0))))
    (for ([p (in-list rewritten)])
      (check-equal? (valid-sites library 'm1 fresh1-tvar p
                                 (expand-under library p))
                    (hash))
      (check-equal? (hash-count
                     (valid-sites library 'm1 fresh1 p
                                  (expand-under library p)))
                    1))))
