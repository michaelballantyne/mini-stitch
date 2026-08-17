#lang racket

;; ---------------------------------------------------------------------------
;; rewrite.rkt --- applying a learned abstraction to the corpus
;; ---------------------------------------------------------------------------
;;
;; The search hands us an abstraction plus the list of corpus locations where it
;; is actually going to be used.  This module does the mechanical part: walk
;; each original program from the root down, and wherever a used location is
;; reached, replace the whole subtree by a call `(fn_k a1 ... ak)` to the new
;; primitive.  The arguments are the original subtrees the abstraction variables
;; stand for, rewritten in turn -- a match sitting inside an argument is still
;; rewritten.
;;
;; Two things make this more than a substitution:
;;
;; DE BRUIJN FIXUP.  An argument is *lifted*: in the original program it sat
;; under some lambdas of the matched subtree, and in the rewritten program it
;; sits outside them, at the call site.  Any variable in it that pointed at a
;; binder above the match root now counts too many binders and has to be
;; renumbered.  A tiny worked example, the whole story in four lines:
;;
;;     program           (lam (lam ($1 $0)))
;;     abstraction       fn_0 = (lam (#0 $0))          -- note the lam is in the
;;                                                        BODY, not the argument
;;     match location    (lam ($1 $0))   -- the inner lam, sitting under 1 lambda
;;     argument          $1              -- the subtree at the hole
;;
;;   In the program, `$1` is read from inside two lambdas and refers to the
;;   outer one.  In the rewritten program `(lam (fn_0 $0))` that same subtree is
;;   written at the call site, inside only one lambda, so it must be spelled
;;   `$0` to refer to the same binder.  Its de Bruijn index drops by 1 -- which
;;   is exactly the `shift` that argument extraction already recorded when it
;;   crossed that lambda (expr.rkt's `arg-shift`).
;;
;;   The catch is that not every variable in an argument moves.  `(lam $0)` as
;;   an argument binds its own `$0`, which must be left alone.  So the shift is
;;   not applied blindly to the argument's variables; it is applied to exactly
;;   those whose *binder lies at or above the match root*.  Hence a ShiftRule.
;;
;; A ShiftRule is a (cons Natural Integer): a depth cutoff and a (negative)
;; shift amount.  While rewriting inside an argument we track `depth`, the
;; number of lambdas of the ORIGINAL program enclosing the node we are at.  A
;; variable `$i` at depth d is bound by the lambda at nesting level d - i
;; (levels counting from the outside, the innermost enclosing lambda being level
;; d).  The rule's cutoff is the depth of the match location, so `d - i <= cutoff`
;; says "this variable's binder is at or above the match root", and those
;; variables -- and only those -- get `shift` added.  Rules stack: an argument
;; lifted out of a match that is itself inside the argument of an outer match
;; can need two shifts, and both apply.  (`ShiftRule`, rewriting.rs:8-13; the
;; test, rewriting.rs:106-119.)
;;
;; UNUSED LOCATIONS.  A pattern can match at a location that cannot be rewritten
;; there: the argument would have to capture a lambda belonging to the
;; abstraction body (search.rkt zeroes those), or the location is swallowed by a
;; larger overlapping match that the greedy top-down pass takes first.  Those
;; locations are matched but *unused*, and the rewriter must leave them alone.
;; This is why the rewriter tests membership in the abstraction's `used` list
;; and not in its match locations (rewriting.rs:36-37).
;;
;; THE MISMATCH ASSERT.  Afterwards, the total cost of the rewritten programs
;; must equal the original cost minus the compressive utility the search
;; computed -- to the unit.  The two numbers are arrived at by completely
;; different routes (one analytic, one by actually doing the work), so their
;; agreement checks the utility formula, the overlap correction, the used/unused
;; split, and this rewriter all at once.  It is the correctness oracle of the
;; whole system, and stitch keeps it in release builds too
;; (rewriting.rs:144-152).
;;
;; PARITY: `rewrite_fast` (rewriting.rs:15-155), single-threaded and without
;; --eta-long (rewriting.rs:62-89), which is off by default.
;; ---------------------------------------------------------------------------

(require "expr.rkt"
         "search.rkt"
         racket/set)

(provide rewrite-with rewrite-into)

;; ---------------------------------------------------------------------------
;; The rewrite
;; ---------------------------------------------------------------------------

;; rewrite-into : Corpus Abstraction Symbol -> (values Corpus (Listof Idx))
;; Rewrite every program of `c` with the abstraction, naming it `name`, and
;; return the fresh corpus the rewritten programs were built in together with
;; their roots.  The fresh corpus is left unsealed: it is a scratch arena for
;; printing and costing, not a corpus to search.
;;
;; PARITY: `rewrite_fast`'s `helper` (rewriting.rs:24-142).  stitch builds one
;; arena per program with structural hashing off; we use one shared arena with
;; it on, which changes nothing observable because `cost` is the cost of a node
;; as a tree and printing follows the tree too.
(define (rewrite-into c a name)
  (define out (make-corpus))
  (define inv (add-node! out (prim name)))
  (define used (list->seteqv (abstraction-used a)))
  (define args (abstraction-args a))

  ;; shift-of : Natural Integer (Listof ShiftRule) -> Integer
  ;; How much to add to the index of a variable `$i` read at `depth`, given the
  ;; rules in force.  Every rule whose cutoff the variable reaches or passes
  ;; contributes; more than one can (rewriting.rs:108-118).
  (define (shift-of i depth rules)
    (for/sum ([rule (in-list rules)]
              #:when (<= (- depth i) (car rule)))
      (cdr rule)))

  ;; walk : Idx Natural (Listof ShiftRule) -> Idx
  ;; Rewrite the subtree at `idx` of the original corpus into `out`.  `depth` is
  ;; how many lambdas of the original program enclose it.
  (define (walk idx depth rules)
    (cond
      ;; A used match location: emit the curried call.  Argument #0 is applied
      ;; first, so it prints leftmost -- stitch iterates its abstraction
      ;; variables in index order and wraps an App around the accumulator each
      ;; time (`iterate_one_zid_per_argument`, pattern_args.rs:71-73; the loop,
      ;; rewriting.rs:40-93).  Verified against the real binary: for the
      ;; abstraction `(app (app cons (app #1 #0)) ...)` on data/basic/hof.json
      ;; it prints `(fn_0 $0 inc)`, i.e. #0 then #1.
      [(set-member? used idx)
       (for/fold ([expr inv]) ([one (in-list (hash-ref args idx))])
         (define shift (arg-shift one))
         (define rules*
           (if (zero? shift) rules (cons (cons depth shift) rules)))
         ;; The argument's own subtree sits `-shift` lambdas deeper than the
         ;; match location, and that is the depth its variables are read at
         ;; (rewriting.rs:56).
         (add-node! out (app expr (walk (arg-unshifted one) (- depth shift) rules*))))]
      [else
       (define n (corpus-node c idx))
       (cond
         [(prim? n) (add-node! out n)]
         [(var? n)
          (define i (var-i n))
          (define j (+ i (shift-of i depth rules)))
          (unless (>= j 0)
            (error 'rewrite "variable $~a at depth ~a shifted to $~a" i depth j))
          (add-node! out (var j))]
         [(app? n)
          (define f (walk (app-fun n) depth rules))
          (define x (walk (app-arg n) depth rules))
          (add-node! out (app f x))]
         [(lam? n) (add-node! out (lam (walk (lam-body n) (add1 depth) rules)))]
         [(ivar? n) (error 'rewrite "an original program cannot contain #~a"
                           (ivar-i n))])]))

  (define roots (for/list ([r (in-list (corpus-roots c))]) (walk r 0 '())))
  (check-cost-mismatch c a out roots)
  (values out roots))

;; check-cost-mismatch : Corpus Abstraction Corpus (Listof Idx) -> Void
;; The oracle: rewriting must save exactly the compressive utility the search
;; predicted.  Raise a loud, informative error if it did not
;; (rewriting.rs:144-152).
(define (check-cost-mismatch c a out roots)
  (define before (for/sum ([r (in-list (corpus-roots c))]) (cost c r)))
  (define after (for/sum ([r (in-list roots)]) (cost out r)))
  (unless (= after (- before (abstraction-compressive a)))
    (error 'rewrite
           (string-append
            "cost mismatch: rewriting gave ~a but the search promised ~a\n"
            "  original cost:       ~a\n"
            "  compressive utility: ~a\n"
            "  abstraction:         ~a (arity ~a)\n"
            "  used locations:      ~a")
           after (- before (abstraction-compressive a))
           before (abstraction-compressive a)
           (abstraction-body a) (abstraction-arity a)
           (abstraction-used a))))

;; rewrite-with : Corpus Abstraction Symbol -> (Listof String)
;; The rewritten programs, printed.  Strings are the interface between
;; iterations: compress.rkt parses them straight back into a fresh corpus, in
;; which `fn_k` is simply another primitive.
(define (rewrite-with c a name)
  (define-values (out roots) (rewrite-into c a name))
  (for/list ([r (in-list roots)]) (expr->string out r)))

;; ---------------------------------------------------------------------------
;; Tests
;; ---------------------------------------------------------------------------
;;
;; The expected strings and costs are all taken from the real binary,
;; `stitch/target/release/compress FILE --max-arity=A --iterations=1`.

(module+ test
  (require rackunit "search.rkt")

  ;; check-rewrite : (Listof String) Natural (Listof String) -> Void
  ;; Search this corpus, rewrite it, and check the printed programs.  The cost
  ;; mismatch assert fires inside `rewrite-with`, so simply getting here is
  ;; already a check.
  (define (check-rewrite programs max-arity expected)
    (define c (corpus-from-programs programs))
    (define a (search c max-arity))
    (check-not-false a)
    (check-equal? (rewrite-with c a 'fn_0) expected)
    (void))

  (test-case "hof: two arguments, in index order"
    ;; stitch/data/basic/hof.json.  The abstraction is
    ;; (app (app cons (app #1 #0)) (app (app cons (app #1 #0)) empty)), so the
    ;; call must pass #0 first: `(fn_0 $0 inc)`, not `(fn_0 inc $0)`.
    (check-rewrite
     (list "(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))"
           "(lam (app (app cons (app dec $0)) (app (app cons (app dec $0)) empty)))"
           "(lam (app (app cons (app (app plus $0) $0)) (app (app cons (app (app plus $0) $0)) empty)))")
     2
     (list "(lam (fn_0 $0 inc))"
           "(lam (fn_0 $0 dec))"
           "(lam (fn_0 $0 (app plus $0)))")))

  (test-case "arity zero: a plain name for a repeated subtree"
    ;; stitch/data/basic/identical.json: rewritten to just `fn_0` twice.
    (check-rewrite (list "(a b c d e)" "(a b c d e)") 2 (list "fn_0" "fn_0")))

  (test-case "the de Bruijn fixup"
    ;; The abstraction `(h (lam (foo #0 p q r)))` has a lambda in its BODY, and
    ;; the argument is read from under it.  Real binary, max-arity 1:
    ;;   body (h (lam (foo #0 p q r))), arity 1, utility 304
    ;;   rewritten ["(lam (lam (fn_0 $1)))", "(lam (lam (fn_0 $0)))"]
    ;; In the first program the argument is spelled `$2`: read from under three
    ;; lambdas, it refers to the outermost.  At the call site it is read from
    ;; under only two, so it must become `$1`.  Likewise `$1` becomes `$0` in
    ;; the second.  This is the header's worked example, one lambda deeper.
    (define c (corpus-from-programs
               (list "(lam (lam (h (lam (foo $2 p q r)))))"
                     "(lam (lam (h (lam (foo $1 p q r)))))")))
    (define a (search c 1))
    (check-equal? (abstraction-body a) "(h (lam (foo #0 p q r)))")
    (check-equal? (abstraction-utility a) 304)
    (check-equal? (rewrite-with c a 'fn_0)
                  (list "(lam (lam (fn_0 $1)))" "(lam (lam (fn_0 $0)))")))

  (test-case "a lambda inside the argument keeps its own variable"
    ;; Same abstraction, but the argument is now `(k (lam (u1 $0)) $2)`.  Its
    ;; inner `$0` is bound by the argument's own lambda, whose binder is BELOW
    ;; the match root, so the shift rule must not touch it; only the `$2` moves.
    ;; Real binary, max-arity 1 (arity 1 is what forces the whole thing to be a
    ;; single argument rather than splitting `u1` off):
    ;;   ["(lam (lam (fn_0 (k (lam (u1 $0)) $1))))",
    ;;    "(lam (lam (fn_0 (k (lam (u2 $0)) $0))))"]
    (define c (corpus-from-programs
               (list "(lam (lam (h (lam (foo (k (lam (u1 $0)) $2) p q r)))))"
                     "(lam (lam (h (lam (foo (k (lam (u2 $0)) $1) p q r)))))")))
    (define a (search c 1))
    (check-equal? (abstraction-body a) "(h (lam (foo #0 p q r)))")
    (check-equal? (rewrite-with c a 'fn_0)
                  (list "(lam (lam (fn_0 (k (lam (u1 $0)) $1))))"
                        "(lam (lam (fn_0 (k (lam (u2 $0)) $0))))")))

  (test-case "ctx_thread_1: the argument is the head of an application spine"
    ;; stitch/data/basic/ctx_thread_1.json, max-arity 2.  The body is
    ;; (A (lam (lam (+ (#0 $0 f) (#0 $0 f))))) -- one variable used twice, and
    ;; the `$0` inside it belongs to the body's own lambda, not to the argument.
    (check-rewrite (list "(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))"
                         "(A (lam (lam (+ (a b z $0 f) (a b z $0 f)))))")
                   2
                   (list "(fn_0 (a b c))" "(fn_0 (a b z))")))

  (test-case "map_minimal"
    ;; stitch/data/basic/map_minimal.json, max-arity 2:
    ;; body (app (app cons #1) (app rec (app cdr #0))).
    (check-rewrite
     (list "(lam (app (app cons (app (app + (app car $0)) (app car $0))) (app rec (app cdr $0))))"
           "(lam (app (app cons (app (app - (app car $0)) t1)) (app rec (app cdr $0))))")
     2
     (list "(lam (fn_0 $0 (app (app + (app car $0)) (app car $0))))"
           "(lam (fn_0 $0 (app (app - (app car $0)) t1)))")))

  (test-case "a match nested inside an argument is rewritten too"
    ;; The abstraction is `(#0 f g h)`, and one program contains it twice, the
    ;; inner occurrence sitting exactly at the `#0` position of the outer one.
    ;; The rewriter recurses into arguments, so both are replaced and the call
    ;; nests.  Real binary, max-arity 1:
    ;;   body (#0 f g h), arity 1, utility 303, num_uses 3
    ;;   rewritten ["(m (fn_0 (fn_0 z1) y1))", "(n (fn_0 z2 y2))"]
    ;; Note this is *not* the self-overlap case: the overlap happens at a
    ;; variable position, which costs nothing, so all three locations are used.
    (check-rewrite (list "(m (z1 f g h f g h y1))" "(n (z2 f g h y2))")
                   1
                   (list "(m (fn_0 (fn_0 z1) y1))" "(n (fn_0 z2 y2))")))

  ;; -------------------------------------------------------------------------
  ;; Unused locations
  ;; -------------------------------------------------------------------------

  (test-case "a matched location that cannot be rewritten is skipped"
    ;; Constructed for this test, because nothing in stitch/data/basic exercises
    ;; the used/unused split at iterations=1.
    ;;
    ;; The winning abstraction is `(f (lam (g #0 q r)) z)`.  The third program
    ;; contains that shape too -- so it IS a match location -- but there `#0`
    ;; would have to be `$0`, the variable bound by the lambda that is part of
    ;; the abstraction *body*.  The abstraction cannot pass that as an argument
    ;; (there is nothing to name it at the call site), so extraction marks it
    ;; with a sentinel, the search gives the location zero utility, and the
    ;; rewriter must leave the third program untouched.
    ;;
    ;; Note the consequence for reporting: num_uses counts all three match
    ;; locations, while only two calls appear in the output.  The real binary
    ;; agrees -- it too says num_uses 3 and leaves program three alone:
    ;;   body (f (lam (g #0 q r)) z), arity 1, utility 304, num_uses 3
    ;;   original_cost 1819, final_cost 1009
    ;;   rewritten ["(fn_0 a)", "(fn_0 b)", "(lam (f (lam (g $0 q r)) z))"]
    (define programs (list "(f (lam (g a q r)) z)"
                           "(f (lam (g b q r)) z)"
                           "(lam (f (lam (g $0 q r)) z))"))
    (define c (corpus-from-programs programs))
    (define a (search c 2))
    (check-equal? (abstraction-body a) "(f (lam (g #0 q r)) z)")
    (check-equal? (abstraction-arity a) 1)
    (check-equal? (abstraction-utility a) 304)
    (check-equal? (abstraction-num-uses a) 3)      ; all match locations
    (check-equal? (length (abstraction-used a)) 2) ; ... but only two are used
    (define rewritten (rewrite-with c a 'fn_0))
    (check-equal? rewritten
                  (list "(fn_0 a)" "(fn_0 b)" "(lam (f (lam (g $0 q r)) z))"))
    ;; and the costs line up with the real binary's
    (define before (for/sum ([r (in-list (corpus-roots c))]) (cost c r)))
    (define out (corpus-from-programs rewritten))
    (define after (for/sum ([r (in-list (corpus-roots out))]) (cost out r)))
    (check-equal? before 1819)
    (check-equal? after 1009)))
