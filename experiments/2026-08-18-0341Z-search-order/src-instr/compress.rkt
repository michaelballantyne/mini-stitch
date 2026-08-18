#lang racket

;; ---------------------------------------------------------------------------
;; compress.rkt --- the iteration loop and the entry point
;; ---------------------------------------------------------------------------
;;
;; One run of the search finds one abstraction.  Library learning wants a
;; library, so stitch simply repeats: rewrite the corpus with the abstraction it
;; just found, and search the rewritten corpus for the next one.  The new
;; primitive `fn_0` is a primitive like any other, so the second iteration can
;; build abstractions that call it, and nothing downstream needs to know it was
;; invented rather than given.  That is the whole of this module: a loop, plus
;; the JSON front end.
;;
;; The corpus is rebuilt from scratch each iteration, from the *printed*
;; rewritten programs.  Round-tripping through text is not the fastest way to do
;; it, but it is the honest one: it proves the rewriter emits programs the
;; parser accepts, and it keeps `expr.rkt`'s invariants (one sealed span, one
;; set of analyses) intact instead of trying to patch a corpus in place.
;;
;; DATA DEFINITIONS
;;
;; A Step records what one iteration did:
;;   name         the symbol the abstraction was named, `fn_0`, `fn_1`, ...
;;   body         its body, printed in stitch's format
;;   arity        how many arguments it takes
;;   utility      cost saved by rewriting, minus the size of the abstraction
;;   num-uses     occurrences of all its match locations (stitch's `num_uses`;
;;                see search.rkt on why unused locations are counted)
;;   cost-before  total cost of the corpus this iteration started from
;;   cost-after   total cost of the corpus it produced
;;
;; A Result is the whole run:
;;   original-cost  cost of the corpus as given
;;   final-cost     cost of the corpus after the last iteration
;;   steps          the Steps, in order
;;   programs       the final rewritten programs, as strings
;;
;; The loop stops after `iterations` steps or as soon as an iteration finds no
;; abstraction worth applying, whichever comes first -- so `steps` can be
;; shorter than `iterations`, exactly as `num_abstractions` can be in stitch's
;; output (`compression`, compression.rs:2119-2180).
;; ---------------------------------------------------------------------------

(require "expr.rkt"
         "search.rkt"
         "rewrite.rkt"
         json
         racket/cmdline)

(provide (struct-out step)
         (struct-out result)
         compress
         corpus-cost)

(struct step (name body arity utility num-uses cost-before cost-after)
  #:transparent)

(struct result (original-cost final-cost steps programs) #:transparent)

;; corpus-cost : Corpus -> Cost
;; The total cost of the corpus: the sum over program roots of the cost of that
;; program *as a tree*.  Two identical programs count twice, which is what
;; stitch reports as `original_cost` (`init_cost`, compression.rs:1908).
(define (corpus-cost c)
  (for/sum ([r (in-list (corpus-roots c))]) (cost c r)))

;; compress : (Listof String) [#:max-arity Natural] [#:iterations Natural]
;;            -> Result
;; Learn up to `iterations` abstractions, rewriting between each.
(define (compress programs #:max-arity [max-arity 2] #:iterations [iterations 3])
  (define original-cost (corpus-cost (corpus-from-programs programs)))
  (let loop ([k 0] [programs programs] [cost-so-far original-cost] [steps '()])
    (cond
      [(>= k iterations) (result original-cost cost-so-far (reverse steps) programs)]
      [else
       (define c (corpus-from-programs programs))
       (define a (search c max-arity))
       (cond
         ;; No abstraction pays for itself: stop early rather than emit a
         ;; primitive nobody uses.
         [(or (not a) (<= (abstraction-utility a) 0))
          (result original-cost cost-so-far (reverse steps) programs)]
         [else
          (define name (string->symbol (format "fn_~a" k)))
          (define rewritten (rewrite-with c a name))
          (define after (corpus-cost (corpus-from-programs rewritten)))
          (loop (add1 k)
                rewritten
                after
                (cons (step name
                            (abstraction-body a)
                            (abstraction-arity a)
                            (abstraction-utility a)
                            (abstraction-num-uses a)
                            cost-so-far
                            after)
                      steps))])])))

;; ---------------------------------------------------------------------------
;; Reporting
;; ---------------------------------------------------------------------------

;; print-result : Result [Output-Port] -> Void
;; A human-readable summary, modelled on stitch's but much smaller.
(define (print-result r [out (current-output-port)])
  (fprintf out "original cost: ~a\n" (result-original-cost r))
  (cond
    [(null? (result-steps r)) (fprintf out "\nno compressive abstraction found\n")]
    [else
     (for ([s (in-list (result-steps r))])
       (fprintf out "\n~a  arity ~a  utility ~a  uses ~a  cost ~a -> ~a\n"
                (step-name s) (step-arity s) (step-utility s)
                (step-num-uses s) (step-cost-before s) (step-cost-after s))
       (fprintf out "    ~a\n" (step-body s)))])
  (fprintf out "\nfinal cost: ~a   compression ratio: ~a\n"
           (result-final-cost r)
           (~r (/ (result-original-cost r) (result-final-cost r)) #:precision 4))
  (fprintf out "\nrewritten programs:\n")
  (for ([p (in-list (result-programs r))]) (fprintf out "    ~a\n" p)))

;; ---------------------------------------------------------------------------
;; Command line
;; ---------------------------------------------------------------------------
;;
;;   racket src/compress.rkt CORPUS.json [--max-arity N] [--iterations N]
;;
;; where CORPUS.json is a JSON array of program strings -- stitch's
;; `programs-list` format, which is what everything in stitch/data/basic is.

;; flags-first : (Vectorof String) -> (Vectorof String)
;; Move switches (and the value each one takes) ahead of the positional
;; argument, so that the file name may be written either before or after them.
;; Racket's `command-line` stops looking for switches at the first positional
;; argument; stitch's own command line does not, and it reads more naturally
;; with the corpus first.
(define (flags-first argv)
  (let loop ([args (vector->list argv)] [switches '()] [positional '()])
    (cond
      [(null? args) (list->vector (append (reverse switches) (reverse positional)))]
      [(and (regexp-match? #rx"^-" (car args)) (pair? (cdr args)))
       (loop (cddr args) (cons (cadr args) (cons (car args) switches)) positional)]
      [else (loop (cdr args) switches (cons (car args) positional))])))

(module+ main
  (define max-arity 2)
  (define iterations 3)
  (define file
    (parameterize ([current-command-line-arguments
                    (flags-first (current-command-line-arguments))])
     (command-line
      #:program "compress"
      #:once-each
      [("-a" "--max-arity") n "maximum arity of an abstraction (default 2)"
                              (set! max-arity (string->number n))]
      [("-i" "--iterations") n "maximum number of abstractions (default 3)"
                               (set! iterations (string->number n))]
      #:args (corpus-file) corpus-file)))
  (define programs
    (let ([j (call-with-input-file file read-json)])
      (unless (and (list? j) (andmap string? j))
        (error 'compress "~a: expected a JSON array of program strings" file))
      j))
  (printf "corpus: ~a  (~a programs)\n" file (length programs))
  (print-result (compress programs #:max-arity max-arity #:iterations iterations)))

;; ---------------------------------------------------------------------------
;; Tests
;; ---------------------------------------------------------------------------
;;
;; End-to-end against the real binary,
;; `stitch/target/release/compress FILE --max-arity=A --iterations=I`.  The
;; systematic version of this lives in tests/differential.rkt; these are the
;; cases worth having in the unit suite.

(module+ test
  (require rackunit)

  (test-case "fn_k is nothing but a primitive to the parser"
    ;; Which is the entire reason iteration can round-trip through text.
    (define c (corpus-from-programs (list "(fn_0 a)" "(fn_0 b)")))
    (define f (app-fun (corpus-node c (car (corpus-roots c)))))
    (check-equal? (corpus-node c f) (prim 'fn_0))
    (check-equal? (cost c f) COST-PRIM))

  (test-case "hof, three iterations"
    ;; stitch/data/basic/hof.json --max-arity=2 --iterations=3.  Two
    ;; abstractions, and then the third iteration finds nothing.  Note fn_1:
    ;; it wraps fn_0 in a lambda, and its third match location is *unused* --
    ;; there the argument would be `(app plus $0)`, which mentions the variable
    ;; fn_1's own lambda binds.  So num_uses is 3 but only two calls appear.
    (define r (compress
               (list "(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))"
                     "(lam (app (app cons (app dec $0)) (app (app cons (app dec $0)) empty)))"
                     "(lam (app (app cons (app (app plus $0) $0)) (app (app cons (app (app plus $0) $0)) empty)))")
               #:max-arity 2 #:iterations 3))
    (check-equal? (result-original-cost r) 4343)
    (check-equal? (result-final-cost r) 907)
    (check-equal? (length (result-steps r)) 2)
    (define fn0 (car (result-steps r)))
    (check-equal? (step-name fn0) 'fn_0)
    (check-equal? (step-body fn0)
                  "(app (app cons (app #1 #0)) (app (app cons (app #1 #0)) empty))")
    (check-equal? (step-arity fn0) 2)
    (check-equal? (step-utility fn0) 2320)
    (check-equal? (step-num-uses fn0) 3)
    (check-equal? (step-cost-after fn0) 1111)
    (define fn1 (cadr (result-steps r)))
    (check-equal? (step-name fn1) 'fn_1)
    (check-equal? (step-body fn1) "(lam (fn_0 $0 #0))")
    (check-equal? (step-arity fn1) 1)
    (check-equal? (step-utility fn1) 1)
    (check-equal? (step-num-uses fn1) 3)
    (check-equal? (result-programs r)
                  (list "(fn_1 inc)"
                        "(fn_1 dec)"
                        "(lam (fn_0 $0 (app plus $0)))")))

  (test-case "nuts-bolts, two iterations: fn_1 is built out of fn_0"
    ;; The first three programs of stitch/data/cogsci/nuts-bolts.json, at
    ;; --max-arity=2 --iterations=2.  The point of the case is the second
    ;; abstraction, whose body *calls the first* -- the invented primitive
    ;; really is just a primitive, so the next iteration abstracts over it with
    ;; no special handling anywhere.
    (define r (compress
               (list
                "(C (C (T (T c (M 2 0 0 0)) (M 4 0 0 0)) (T (T c (M 2 0 0 0)) (M 4.25 0 0 0))) (T (repeat (T l (M 1 0 -0.5 (/ 0.5 (tan (/ pi 6))))) 6 (M 1 (/ (* 2 pi) 6) 0 0)) (M 2 0 0 0)))"
                "(C (T (repeat (T l (M 1 0 -0.5 (/ 0.5 (tan (/ pi 6))))) 6 (M 1 (/ (* 2 pi) 6) 0 0)) (M 2 0 0 0)) (T (repeat (T l (M 1 0 -0.5 (/ 0.5 (tan (/ pi 6))))) 6 (M 1 (/ (* 2 pi) 6) 0 0)) (M 1 0 0 0)))"
                "(C (C (T (repeat (T l (M 1 0 -0.5 (/ 0.5 (tan (/ pi 6))))) 6 (M 1 (/ (* 2 pi) 6) 0 0)) (M 2 0 0 0)) (T (repeat (T l (M 1 0 -0.5 (/ 0.5 (tan (/ pi 6))))) 6 (M 1 (/ (* 2 pi) 6) 0 0)) (M 2.25 0 0 0))) (T (repeat (T l (M 1 0 -0.5 (/ 0.5 (tan (/ pi 6))))) 6 (M 1 (/ (* 2 pi) 6) 0 0)) (M 1 0 0 0)))")
               #:max-arity 2 #:iterations 2))
    (check-equal? (result-original-cost r) 20702)
    (check-equal? (result-final-cost r) 3734)
    (check-equal? (length (result-steps r)) 2)
    (define fn0 (car (result-steps r)))
    (define fn1 (cadr (result-steps r)))
    (check-equal? (step-body fn0)
                  "(T (repeat (T l (M 1 0 -0.5 (/ 0.5 (tan (/ pi 6))))) 6 (M 1 (/ (* 2 pi) 6) 0 0)) (M #0 0 0 0))")
    (check-equal? (step-utility fn0) 13534)
    (check-equal? (step-num-uses fn0) 6)
    (check-equal? (step-cost-after fn0) 4340)
    (check-equal? (step-name fn1) 'fn_1)
    (check-equal? (step-body fn1) "(C (fn_0 2) (fn_0 #0))")
    (check-equal? (step-utility fn1) 202)
    (check-equal? (step-num-uses fn1) 2)
    (check-equal? (result-programs r)
                  (list "(C (C (T (T c (M 2 0 0 0)) (M 4 0 0 0)) (T (T c (M 2 0 0 0)) (M 4.25 0 0 0))) (fn_0 2))"
                        "(fn_1 1)"
                        "(C (fn_1 2.25) (fn_0 1))"))
    ;; the recorded costs chain up
    (check-equal? (step-cost-before fn0) (result-original-cost r))
    (check-equal? (step-cost-after fn0) (step-cost-before fn1))
    (check-equal? (step-cost-after fn1) (result-final-cost r)))

  (test-case "an incompressible corpus yields no steps"
    (define r (compress (list "(f x)" "(g y)") #:max-arity 2 #:iterations 3))
    (check-equal? (result-steps r) '())
    (check-equal? (result-final-cost r) (result-original-cost r))
    (check-equal? (result-programs r) (list "(f x)" "(g y)"))))
