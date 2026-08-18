#lang racket

;; ---------------------------------------------------------------------------
;; tests/fuzz.rkt --- micro-stitch as the oracle, mini-stitch as the suspect
;; ---------------------------------------------------------------------------
;;
;; tests/differential.rkt checks mini-stitch against the real binary, so it can
;; only find places where mini is *unfaithful*.  It cannot find places where
;; stitch itself is wrong, because there mini is wrong in exactly the same way.
;; This module is the other oracle: micro-stitch computes an abstraction's
;; utility by actually rewriting the corpus and weighing the result
;; (src/micro.rkt, `abstraction-utility`), which is the definition; mini
;; computes stitch's analytic formula.  Where the two disagree, the formula is
;; wrong.
;;
;; This is how the utility over-count in real stitch was found; see
;; notes/2026-08-17-2030-stitch-utility-overcount-bug.md.  The scripts that
;; found it were scratch, so the README's fuzz claims could not be re-run from
;; the repo.  This is the checked-in, seeded version of them: same seed, same
;; corpora, same tallies, every run.
;;
;; WHAT IS CHECKED, per random corpus:
;;
;;     mini's search picks a body A and claims utility u.
;;     micro rewrites the corpus with that same body A and measures utility u*.
;;
;;   * AGREE      u = u*   -- the formula is right here
;;   * OVER-COUNT u > u*   -- the formula promises compression the rewriter
;;                            cannot deliver: the known stitch bug
;;   * UNDER-COUNT u < u*  -- would be a *different*, unknown bug (the formula
;;                            leaving money on the table), and none has ever
;;                            been seen
;;
;; and the invariant this module asserts is the bug note's scope claim:
;;
;;     the disagreement is always an over-count, never an under-count, and it
;;     only happens on self-similar corpora (a multiuse variable whose argument
;;     contains further matches of the same pattern).
;;
;; So there are two generators.  "unbiased" builds small random trees over a few
;; primitives, with the occasional lambda and de Bruijn variable; it is expected
;; to produce *zero* disagreements.  "biased" deliberately duplicates children,
;; `(t t)`, which is the shape the bug needs; it produces over-counts in roughly
;; a quarter of its corpora.
;;
;; NOTE on what is compared: mini's *search*, not `compress`.  Rewriting a
;; corpus that triggers the over-count makes mini's own cost-mismatch oracle
;; raise (src/rewrite.rkt, `check-cost-mismatch`) -- which is the right thing
;; for `compress` to do and useless for a fuzzer, since it stops the run before
;; anything can be tallied.  The claimed utility is read straight off the
;; abstraction the search returns.
;;
;; NOTE on bodies: micro is asked about *mini's* body, not its own favourite.
;; Two different bodies can be worth the same, so comparing which body each
;; system picks would report ties as bugs; comparing utilities of one body
;; cannot.
;;
;;   raco test tests/fuzz.rkt
;;   racket tests/fuzz.rkt --trials 5000 --mode both [--seed 20260817]
;; ---------------------------------------------------------------------------

(require rackunit
         "../src/expr.rkt"
         "../src/search.rkt"
         (prefix-in micro: "../src/micro.rkt")
         ;; `parse` reads a program text into one of micro's trees; see
         ;; tests/support.rkt, which is where the two representations meet
         (only-in "support.rkt" parse))

;; ---------------------------------------------------------------------------
;; Data
;; ---------------------------------------------------------------------------

;; A Corpus is a (Listof String): a handful of programs in stitch's surface
;; syntax, the same thing the corpus .json files hold.
;;
;; A Mode is one of 'unbiased or 'biased -- which generator made the corpus.
;;
;; A Judgement is one of 'agree, 'over-count or 'under-count: how mini's claimed
;; utility compared with micro's measured one.

;; A Scored is a (scored Corpus String Cost Cost): a corpus on which mini's
;; search found an abstraction, the body it picked, the utility it claimed, and
;; the utility micro measured for that same body.
(struct scored (corpus body claimed measured) #:transparent)

;; A Tally is a (tally Natural Natural Natural (Listof Scored) (Listof Scored)):
;; how many corpora were tried, how many of them mini found an abstraction on,
;; how many of those agreed, and the disagreements themselves in both
;; directions.  The disagreements are kept, not just counted, because a failing
;; assertion should be able to print a reproducer.
(struct tally (trials scored agree over under) #:transparent)

;; The seed everything defaults to.  Changing it changes every number this
;; module prints, so don't, casually.
(define DEFAULT-SEED 20260817)

;; The corpora stay tiny: micro rewrites the whole corpus once per candidate it
;; scores, and the bug shows up in trees of a dozen nodes.
(define MAX-NODES 30)

;; The alphabet.  Three primitives is few enough that unrelated random programs
;; still share subterms often enough for the search to find something.
(define PRIMS '("a" "b" "f"))

;; ---------------------------------------------------------------------------
;; Generating corpora
;; ---------------------------------------------------------------------------

;; make-rng : Natural -> Pseudo-Random-Generator
;; A generator seeded so that the same seed gives the same corpora forever.
(define (make-rng seed)
  (define rng (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator rng]) (random-seed seed))
  rng)

;; random-term : Pseudo-Random-Generator Natural Natural -> String
;; A random program of roughly `fuel` leaves, written under `depth` enclosing
;; lambdas (so that the `$i` it may emit are bound).  Applications are binary
;; here, which costs no generality: stitch's parser curries anyway.
(define (random-term rng fuel depth)
  (cond
    [(<= fuel 1)
     (if (and (> depth 0) (< (random 10 rng) 4))
         (format "$~a" (random depth rng))
         (list-ref PRIMS (random (length PRIMS) rng)))]
    [(< (random 10 rng) 2)
     (format "(lam ~a)" (random-term rng (sub1 fuel) (add1 depth)))]
    [else
     (define left (add1 (random (max 1 (sub1 fuel)) rng)))
     (format "(~a ~a)" (random-term rng left depth)
             (random-term rng (- fuel left) depth))]))

;; self-similar-term : Pseudo-Random-Generator Natural -> String
;; A random program built by repeatedly doubling: start from a tiny term and a
;; few times over replace t by (t t) -- or, now and then, by (t s) for a fresh
;; small s, so the corpus is not only perfect binary trees.  This is the shape
;; the over-count needs: a pattern with a multiuse variable matches at the root
;; *and* inside what that variable receives.
(define (self-similar-term rng depth)
  (let double ([t (random-term rng (add1 (random 3 rng)) depth)]
               [k (add1 (random 3 rng))])
    (cond
      [(zero? k) t]
      [else
       (double (if (< (random 10 rng) 7)
                   (format "(~a ~a)" t t)
                   (format "(~a ~a)" t (random-term rng 2 depth)))
               (sub1 k))])))

;; term-size : Term -> Natural
;; Nodes in the tree -- the budget micro's rewriting is paid out of.
(define (term-size t)
  (cond [(app? t) (+ 1 (term-size (app-fun t)) (term-size (app-arg t)))]
        [(lam? t) (add1 (term-size (lam-body t)))]
        [else 1]))

;; corpus-nodes : Corpus -> Natural
(define (corpus-nodes programs)
  (for/sum ([p (in-list programs)]) (term-size (parse p))))

;; random-corpus : Pseudo-Random-Generator Mode -> Corpus
;; Two to four programs from the mode's generator, redrawn until the whole
;; corpus fits in MAX-NODES.  Doubling overshoots often, so rejection is simpler
;; than trying to make the generators respect a budget.
(define (random-corpus rng mode)
  (let draw ()
    (define programs
      (for/list ([_ (in-range (+ 2 (random 3 rng)))])
        (if (eq? mode 'biased)
            (self-similar-term rng 0)
            (random-term rng (+ 2 (random 4 rng)) 0))))
    (if (<= (corpus-nodes programs) MAX-NODES) programs (draw))))

;; ---------------------------------------------------------------------------
;; Scoring one corpus
;; ---------------------------------------------------------------------------

;; score-corpus : Corpus -> (U Scored #f)
;; Run mini's search on this corpus at max-arity 2 and have micro measure, by
;; rewriting, what the body the search chose is really worth.  #f when the
;; search finds nothing worth abstracting, which is most small random corpora.
(define (score-corpus programs)
  (define a (search (corpus-from-programs programs) 2))
  (cond
    [(or (not a) (<= (abstraction-utility a) 0)) #f]
    [else
     ;; Any error in here is itself a finding, so it is re-raised with the
     ;; corpus attached rather than swallowed.
     (define measured
       (with-handlers ([exn:fail?
                        (lambda (e)
                          (error 'score-corpus "on ~s: ~a" programs (exn-message e)))])
         (micro:abstraction-utility (parse (abstraction-body a))
                                    (map parse programs))))
     (scored programs (abstraction-body a) (abstraction-utility a) measured)]))

;; judge : Scored -> Judgement
(define (judge s)
  (cond [(= (scored-claimed s) (scored-measured s)) 'agree]
        [(> (scored-claimed s) (scored-measured s)) 'over-count]
        [else 'under-count]))

(module+ test
  (test-case "scoring a corpus mini and micro agree on"
    ;; stitch/data/basic/simple1: (#0 #0 #0) is worth 200 by either account.
    (define s (score-corpus '("(a a a)" "(b b b)")))
    (check-equal? (scored-body s) "(#0 #0 #0)")
    (check-equal? (scored-claimed s) 200)
    (check-equal? (scored-measured s) 200)
    (check-equal? (judge s) 'agree))

  (test-case "a corpus with nothing worth abstracting scores as #f"
    (check-false (score-corpus '("a" "b")))))

;; ---------------------------------------------------------------------------
;; Batches
;; ---------------------------------------------------------------------------

;; fuzz : Mode Natural Natural -> Tally
;; Draw `trials` corpora from `mode`'s generator, seeded with `seed`, and sort
;; what mini claims about each against what micro measures.
(define (fuzz mode trials seed)
  (define rng (make-rng seed))
  (for/fold ([t (tally 0 0 0 '() '())] #:result t)
            ([_ (in-range trials)])
    (define s (score-corpus (random-corpus rng mode)))
    (cond
      [(not s) (struct-copy tally t [trials (add1 (tally-trials t))])]
      [else
       (define t* (struct-copy tally t
                               [trials (add1 (tally-trials t))]
                               [scored (add1 (tally-scored t))]))
       (case (judge s)
         [(agree) (struct-copy tally t* [agree (add1 (tally-agree t*))])]
         [(over-count) (struct-copy tally t* [over (cons s (tally-over t*))])]
         [else (struct-copy tally t* [under (cons s (tally-under t*))])])])))

;; print-tally : Mode Tally -> Void
(define (print-tally mode t)
  (printf "~a: ~a corpora, ~a with an abstraction -> ~a AGREE, ~a OVER-COUNT, ~a UNDER-COUNT\n"
          mode (tally-trials t) (tally-scored t) (tally-agree t)
          (length (tally-over t)) (length (tally-under t))))

;; reproducers : (Listof Scored) Natural -> String
;; A few of these disagreements, written out for a failing assertion to print.
(define (reproducers ss n)
  (string-join
   (for/list ([s (in-list ss)] [_ (in-range n)])
     (format "~s: body ~s claimed ~a, measured ~a"
             (scored-corpus s) (scored-body s) (scored-claimed s) (scored-measured s)))
   "\n"))

;; ---------------------------------------------------------------------------
;; The tests
;; ---------------------------------------------------------------------------

(module+ test
  ;; The regression case: the corpus from the bug note, which is the smallest
  ;; over-count anyone has written down.  With X = (Y Y), Y = (Z Z), Z = (a a),
  ;; the pattern (#0 #0) matches at X, both Ys and all four Zs, and stitch
  ;; credits every one of those matches -- but rewriting X to (fn_0 Y) passes
  ;; ONE copy of Y, deleting the other copy and the matches inside it.  The
  ;; over-count is exactly Y's marginal utility, 101.
  ;;
  ;; Real stitch panics on this corpus (its rewriter produces 705 where its
  ;; formula promised 604); mini reproduces the same numbers.
  (test-case "regression: the bug note's reproducer over-counts by 101"
    (define s (score-corpus '("(((a a) (a a)) ((a a) (a a)))" "((a f) (a f))")))
    (check-equal? (scored-body s) "(#0 #0)")
    (check-equal? (scored-claimed s) 605)    ; compressive 606, less the body's 1
    (check-equal? (scored-measured s) 504)   ; compressive 505, less the body's 1
    (check-equal? (- (scored-claimed s) (scored-measured s)) 101)
    (check-equal? (judge s) 'over-count))

  ;; The batch.  300 corpora per mode runs in well under a second; the numbers
  ;; below are the seeded ones, and they change only if the generators or the
  ;; utility computation change.
  (test-case "fuzzing mini's analytic utility against micro's measured utility"
    (define unbiased (fuzz 'unbiased 300 DEFAULT-SEED))
    (define biased (fuzz 'biased 300 DEFAULT-SEED))
    (print-tally 'unbiased unbiased)
    (print-tally 'biased biased)

    ;; A generator that stopped producing abstractions would make every other
    ;; assertion here vacuous.
    (check-true (> (tally-scored unbiased) 50) "unbiased mode found nothing to score")
    (check-true (> (tally-scored biased) 50) "biased mode found nothing to score")

    ;; The invariant, in both modes: the analytic utility never *under*-states
    ;; what rewriting achieves.  An under-count would be a new bug -- the
    ;; formula missing compression that the rewriter finds -- and none has ever
    ;; been observed (0 in the 4239 scored corpora of the original fuzzing, 0
    ;; here).
    (check-equal? (tally-under unbiased) '()
                  (format "mini under-counted:\n~a" (reproducers (tally-under unbiased) 3)))
    (check-equal? (tally-under biased) '()
                  (format "mini under-counted:\n~a" (reproducers (tally-under biased) 3)))

    ;; Scope, the other half of the note's claim: without deliberate
    ;; self-similarity there is no disagreement at all.  (If this ever fires,
    ;; the honest fix is to weaken it to the directionality check above and add
    ;; a caveat to the bug note's "no disagreements on unbiased corpora"
    ;; framing -- not to delete the assertion.)
    (check-equal? (tally-over unbiased) '()
                  (format "unbiased corpora disagreed:\n~a"
                          (reproducers (tally-over unbiased) 3)))

    ;; And the bug is still there to be found: biased corpora over-count often.
    ;; This one is a canary on the fuzzer, not on mini -- if a future change to
    ;; the generators stopped producing the bug's shape, the suite would
    ;; otherwise go quietly green.
    (check-true (> (length (tally-over biased)) 20)
                "biased mode no longer reproduces the over-count")))

;; ---------------------------------------------------------------------------
;; Command line
;; ---------------------------------------------------------------------------
;;
;;   racket tests/fuzz.rkt --trials 5000 --mode both --seed 20260817
;;
;; for runs bigger than the test suite should sit through.  With the default
;; seed the first 300 corpora of each mode are exactly the ones the tests use.

(module+ main
  (define trials 1000)
  (define mode 'both)
  (define seed DEFAULT-SEED)
  (command-line
   #:program "fuzz"
   #:once-each
   [("--trials") n "how many corpora per mode" (set! trials (string->number n))]
   [("--mode") m "unbiased, biased or both" (set! mode (string->symbol m))]
   [("--seed") s "PRNG seed" (set! seed (string->number s))])
  (unless (memq mode '(unbiased biased both))
    (error 'fuzz "--mode must be unbiased, biased or both, not ~a" mode))
  (for ([m (in-list (if (eq? mode 'both) '(unbiased biased) (list mode)))])
    (define t (fuzz m trials seed))
    (print-tally m t)
    (for ([s (in-list (reverse (tally-under t)))])
      (printf "  UNDER-COUNT ~s: body ~s claimed ~a, measured ~a\n"
              (scored-corpus s) (scored-body s) (scored-claimed s) (scored-measured s)))
    (unless (null? (tally-over t))
      (printf "  first over-counts:\n~a\n" (reproducers (reverse (tally-over t)) 3)))))
