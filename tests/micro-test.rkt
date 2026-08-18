#lang racket

;; ---------------------------------------------------------------------------
;; tests/micro-test.rkt --- micro against mini, and both against real stitch
;; ---------------------------------------------------------------------------
;;
;; The point of writing the specification twice.  For each corpus, micro's
;; slow-but-obvious answer (src/micro.rkt) must agree with mini's fast one
;; (src/search.rkt): the same utility, the same corpus cost after rewriting, and
;; -- when the winner is not a tie -- the same body.  A handful of cases are
;; also pinned to numbers transcribed from the real Rust binary, so that the two
;; Racket systems cannot agree with each other while both drifting away from
;; stitch.
;;
;; Bodies are compared up to renaming the abstraction variables (tests/support.rkt's
;; `canonical`), because the two searches introduce them in different orders --
;; micro fills the leftmost hole, mini the most recently created one -- so the
;; same abstraction can come out as (f #0 #1) here and (f #1 #0) there.
;;
;; The last test is the one corpus class where micro and stitch genuinely
;; disagree, and micro is right; see
;; notes/2026-08-17-2030-stitch-utility-overcount-bug.md.
;;
;;   raco test tests/micro-test.rkt
;; ---------------------------------------------------------------------------

(require rackunit
         "support.rkt"
         "../src/micro.rkt"
         (only-in "../src/expr.rkt" corpus-from-programs)
         (prefix-in mini: "../src/search.rkt"))

;; check-agrees : String (Listof String) [Natural] -> Void
;; Run both implementations on the same corpus and compare.
(define (check-agrees name texts [max-arity 2])
  (define start (current-inexact-milliseconds))
  (define programs (map parse texts))
  (define micro (micro-search programs max-arity))
  (define elapsed (- (current-inexact-milliseconds) start))
  (define mini (mini:search (corpus-from-programs texts) max-arity))
  (cond
    [(not mini) (check-false micro (format "~a: mini found nothing" name))]
    [else
     (check-not-false micro (format "~a: micro found nothing" name))
     (when micro
       (define utility (abstraction-utility micro programs))
       (define-values (rewritten _) (rewrite-corpus micro programs 'fn_0))
       (check-equal? utility (mini:abstraction-utility mini)
                     (format "~a: utility" name))
       (check-equal? (- (corpus-cost programs) (corpus-cost rewritten))
                     (mini:abstraction-compressive mini)
                     (format "~a: cost after rewriting" name))
       (check-equal? (pattern-arity micro) (mini:abstraction-arity mini)
                     (format "~a: arity" name))
       (check-equal? (canonical micro) (canonical (parse (mini:abstraction-body mini)))
                     (format "~a: body" name))
       (printf "  ~a: ~a  utility ~a  (micro ~ams)\n"
               name (term->string micro) utility (round elapsed)))]))

(module+ test
  (test-case "micro agrees with mini: stitch's smallest corpora"
    ;; every corpus here is a file in stitch/data/basic, named to match
    (check-agrees "simple1" '("(a a a)" "(b b b)"))
    (check-agrees "simple2" '("(a (lam (a a)))" "(b (lam (b b)))"))
    (check-agrees "identical" '("(a b c d e)" "(a b c d e)"))
    (check-agrees "simple_hof" '("(a (lam ((a $0) (a $0))))"
                                 "(a (lam (($0 b) ($0 b))))"))
    (check-agrees "tmp_minimal" '("(a b)" "(a c)"))
    (check-agrees "ctx_thread_2" '("(lam (lam (+ (a b c $0 f) (a b c $0 f))))"
                                   "(lam (lam (+ (a b z $0 f) (a b z $0 f))))"))
    (check-agrees "ctx_thread_1" '("(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))"
                                   "(A (lam (lam (+ (a b z $0 f) (a b z $0 f)))))"))
    ;; hof is the largest corpus micro can still be asked about; it is also the
    ;; one where the two searches number the abstraction variables differently,
    ;; which is what `canonical` is for
    (check-agrees "hof"
                  '("(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))"
                    "(lam (app (app cons (app dec $0)) (app (app cons (app dec $0)) empty)))"
                    "(lam (app (app cons (app (app plus $0) $0)) (app (app cons (app (app plus $0) $0)) empty)))")))

  (test-case "micro agrees with mini: hand-written corner cases"
    ;; an abstraction variable used twice: the multiuse bonus, which micro gets
    ;; for free because rewriting really does delete the second copy
    (check-agrees "multiuse" '("(f a a)" "(f b b)"))
    ;; a location that matches but would capture, so it cannot be rewritten
    (check-agrees "capture" '("(lam (g (f a b) $0))"
                              "(lam (g (f a c) $0))"
                              "(h (f a $0))"))
    ;; two arguments, one of them a function
    (check-agrees "two-args" '("(f (g x) (h y))" "(f (g z) (h w))"))
    ;; a lambda inside the body, with a variable under it
    (check-agrees "under-lam" '("(m (lam (p $0 q)) r)" "(m (lam (p $0 s)) r)"))
    ;; nothing shared: no abstraction at all
    (check-agrees "nothing" '("(a b)" "(c d)"))))

;; check-against-stitch : String (Listof String) String Natural Cost Cost -> Void
;; The numbers on the right are transcribed from
;;   stitch/target/release/compress data/basic/NAME.json --max-arity=2 --iterations=1
;; so this ties micro to the real system and not just to mini.
(define (check-against-stitch name texts body arity utility final-cost)
  (define programs (map parse texts))
  (define micro (micro-search programs 2))
  (check-not-false micro name)
  (when micro
    (define-values (rewritten _) (rewrite-corpus micro programs 'fn_0))
    (check-equal? (canonical micro) (canonical (parse body)) (format "~a: body" name))
    (check-equal? (pattern-arity micro) arity (format "~a: arity" name))
    (check-equal? (abstraction-utility micro programs) utility
                  (format "~a: utility" name))
    (check-equal? (corpus-cost rewritten) final-cost
                  (format "~a: final cost" name))))

(module+ test
  (test-case "micro agrees with the real stitch binary"
    (check-against-stitch "simple1" '("(a a a)" "(b b b)")
                          "(#0 #0 #0)" 1 200 402)
    (check-against-stitch "simple_hof" '("(a (lam ((a $0) (a $0))))"
                                         "(a (lam (($0 b) ($0 b))))")
                          "(#0 #0)" 1 201 808)
    (check-against-stitch "identical" '("(a b c d e)" "(a b c d e)")
                          "(a b c d e)" 0 304 200)
    (check-against-stitch "ctx_thread_1"
                          '("(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))"
                            "(A (lam (lam (+ (a b z $0 f) (a b z $0 f)))))")
                          "(A (lam (lam (+ (#0 $0 f) (#0 $0 f)))))" 1 1011 806)
    (check-against-stitch "hof"
                          '("(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))"
                            "(lam (app (app cons (app dec $0)) (app (app cons (app dec $0)) empty)))"
                            "(lam (app (app cons (app (app plus $0) $0)) (app (app cons (app (app plus $0) $0)) empty)))")
                          "(app (app cons (app #1 #0)) (app (app cons (app #1 #0)) empty))"
                          2 2320 1111))

  (test-case "two iterations, against the real stitch binary"
    ;; compress data/basic/ctx_thread_1.json --max-arity=2 --iterations=2 reports
    ;;   fn_0 arity 1 utility 1011 body (A (lam (lam (+ (#0 $0 f) (#0 $0 f)))))
    ;;   fn_1 arity 1 utility  101 body (fn_0 (a b #0))
    ;;   original_cost 2426  final_cost 402
    ;; Learning the second abstraction means searching the corpus the first one
    ;; rewrote, so this exercises the rewriter's output, not just its cost.
    (define steps
      (micro-compress (map parse '("(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))"
                                   "(A (lam (lam (+ (a b z $0 f) (a b z $0 f)))))"))
                      2 2))
    (check-equal? (map (lambda (s) (term->string (learned-body s))) steps)
                  '("(A (lam (lam (+ (#0 $0 f) (#0 $0 f)))))" "(fn_0 (a b #0))"))
    (check-equal? (map (lambda (s) (pattern-arity (learned-body s))) steps)
                  '(1 1))
    (check-equal? (map learned-utility steps) '(1011 101))
    (check-equal? (map (lambda (s) (corpus-cost (learned-programs s))) steps)
                  '(806 402))
    (check-equal? (map term->string (learned-programs (last steps)))
                  '("(fn_1 c)" "(fn_1 z)")))

  (test-case "where micro and stitch genuinely disagree, and why"
    ;; This is the one class of corpus on which micro's answer differs from
    ;; mini's -- and micro is the one that is right.  Real stitch says so
    ;; itself: on this corpus
    ;;
    ;;   stitch/target/release/compress FILE --max-arity=1 --iterations=1
    ;;
    ;; aborts on its own rewrite cost-mismatch assertion (rewriting.rs:145),
    ;;
    ;;   (#0 #0): ... finished: utility=605, compressive_utility=606, arity=1
    ;;     left: 705   right: 604
    ;;
    ;; where `left` is what stitch's own rewriter actually produced -- exactly
    ;; the 705 micro computes below -- and `right` is what its analytic utility
    ;; predicted.
    ;;
    ;; What goes wrong is the multiuse bonus meeting nested matches.  The first
    ;; program is X = (Y Y) with Y = (Z Z) and Z = (a a), so (#0 #0) matches at
    ;; X, at both copies of Y, and at all four copies of Z.  stitch credits Y's
    ;; saving twice, once per occurrence.  But rewriting X to (fn_0 Y) is
    ;; precisely the move that *deletes* one of the two copies of Y, so only one
    ;; of them is ever rewritten.  stitch's self-overlap correction does not
    ;; catch it, because it deliberately ignores overlaps that land at an
    ;; argument position -- the rewriter does descend into arguments, and
    ;; normally that is right; what it misses is that a multiply-used variable
    ;; keeps only one of them.
    ;;
    ;; micro cannot make this mistake, because it does not predict the saving:
    ;; it rewrites the corpus and weighs the result.  mini reproduces stitch
    ;; faithfully, so it inherits the over-count.
    (define texts '("(((a a) (a a)) ((a a) (a a)))" "((a f) (a f))"))
    (define programs (map parse texts))
    (define body (parse "(#0 #0)"))
    (define-values (rewritten predicted) (rewrite-corpus body programs 'fn_0))
    (check-equal? (map term->string rewritten)
                  '("(fn_0 (fn_0 (a a)))" "(fn_0 (a f))"))
    (check-equal? (corpus-cost programs) 1210)
    (check-equal? (corpus-cost rewritten) 705)     ; stitch's own `left: 705`
    (check-equal? predicted 705)
    (check-equal? (abstraction-utility body programs) 504)
    ;; and that really is the best (#0 #0) can do here, so micro picks it
    (check-equal? (term->string (micro-search programs 1)) "(#0 #0)")
    ;; mini reproduces stitch's number, over-counting one copy of Y by 101
    (check-equal? (mini:abstraction-utility
                   (mini:search (corpus-from-programs texts) 1))
                  605))

  (test-case "micro agrees with mini across two iterations"
    ;; The second iteration learns from the corpus the first one rewrote, so
    ;; feeding micro's rewritten programs to mini checks the rewriter too.
    (define texts '("(f (g a) (g a))" "(f (g b) (g b))" "(k (g a))"))
    (define steps (micro-compress (map parse texts) 2 2))
    (check-equal? (length steps) 2)
    (for ([step (in-list steps)] [k (in-naturals)])
      (printf "  iteration ~a: ~a  utility ~a  cost ~a\n"
              k (term->string (learned-body step))
              (learned-utility step) (corpus-cost (learned-programs step))))
    ;; each iteration's answer must be the one mini would have found on the
    ;; corpus that iteration started from
    (for/fold ([texts texts]) ([step (in-list steps)])
      (define mini (mini:search (corpus-from-programs texts) 2))
      (check-not-false mini)
      (when mini
        (check-equal? (learned-utility step) (mini:abstraction-utility mini))
        ;; compressive = utility + cost of the body, by the definition of
        ;; utility -- an algebraic identity both systems must satisfy
        (check-equal? (+ (learned-utility step) (term-cost (learned-body step)))
                      (mini:abstraction-compressive mini)))
      (map term->string (learned-programs step)))
    (void)))
