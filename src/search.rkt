#lang racket

;; ---------------------------------------------------------------------------
;; search.rkt --- branch and bound for the best abstraction
;; ---------------------------------------------------------------------------
;;
;; This is Algorithm 1 of the paper: start from the pattern `??`, which matches
;; everywhere, and repeatedly pick a partial pattern off a worklist and expand
;; one of its holes in every way that still matches somewhere.  A pattern with
;; no holes left is a candidate abstraction; score it, and keep the best.
;;
;; What makes that finish in reasonable time is the branch and bound:
;;
;;   * every pattern carries an *upper bound* on the utility of any finished
;;     abstraction it could still grow into.  The worklist is a max-heap on that
;;     bound, and any pattern whose bound cannot beat the best abstraction found
;;     so far is thrown away rather than expanded.
;;   * before the search even starts we score every subtree of the corpus as an
;;     arity-zero abstraction.  That is cheap and gives the bound something to
;;     bite on immediately.
;;   * five prunings discard patterns that are provably dominated by (or
;;     equivalent to) some other pattern the search will consider anyway.
;;
;; The subtle part is not the loop, it is the *utility*: how much does replacing
;; every occurrence of this pattern by a call to a new abstraction actually save?
;; See "Utility" below.
;;
;; WHAT WE DO DIFFERENTLY FROM micro.rkt
;;
;; micro.rkt computes the same answer by the enumeration this algorithm exists
;; to replace, so almost everything in this module is machinery micro does not
;; have:
;;
;;   * micro's frontier is a FIFO list processed level by level, and every
;;     candidate that matches anywhere is expanded.  There is no upper bound to
;;     maintain, hence no priority queue and no branch and bound.  Ours is a
;;     max-heap on the bound, and a pattern whose bound cannot beat the best
;;     abstraction so far is discarded unexpanded.
;;   * micro has no arity-zero priming: an arity-zero abstraction is just a
;;     candidate with no abstraction variables, and its enumeration reaches it
;;     like any other.  We score all of them up front, so that the bound has
;;     something to bite on from the first pop.
;;   * micro has no analytic utility at all.  Its `abstraction-utility`
;;     literally rewrites the corpus and subtracts costs, which is the
;;     definition; the multiuse bonus, the self-overlap correction, the
;;     used/unused split and the `num-paths` weighting below are all things that
;;     follow from that definition and have to be re-derived here because we
;;     refuse to do the rewriting.
;;   * micro keeps only the prunings that change the answer (zero matches, the
;;     two-programs rule, the free-variable rule, and the two Section 4.3
;;     filters).  The dominance-safe prunings -- single-use pruning above all --
;;     exist here purely for speed.
;;
;; The one thing micro does that we do not is get self-similar corpora right;
;; see rewrite.rkt's `check-cost-mismatch`.
;;
;; DATA DEFINITIONS
;;
;; A Cost is an integer, in the units of expr.rkt's cost model.
;;
;; An Abstraction is the result of a search: the winning abstraction plus
;; everything the rewriter and the reporter need.
;;   pattern       the winning Pattern, or #f for an arity-zero winner
;;   body-idx      for an arity-zero winner, the Idx of its body; else #f
;;   body          the body printed in stitch's format
;;   arity         how many arguments it takes
;;   utility       cost saved by rewriting, minus the size of the abstraction
;;   compressive   cost saved by rewriting
;;   used          the match locations that will actually be rewritten, sorted
;;   args          a Hash from a used location to the list of Args (expr.rkt's,
;;                 one per abstraction variable in order) it passes there
;;   num-uses      total occurrences of ALL the match locations, counting DAG
;;                 sharing.  Note "all": this is stitch's `usages`
;;                 (compression.rs:1177), which is summed before the used /
;;                 unused split is known and so counts unused locations too.
;;                 It is what the real binary reports as `num_uses`.
;;
;; UTILITY
;;
;; Rewriting one occurrence of a pattern replaces `body` by `(fn a1 ... ak)`.
;; That costs a new primitive plus k applications and saves the concrete part of
;; the body -- the arguments are still there, just moved.  Hence, per location,
;;
;;   util-once = body-utility - (COST-NEW-PRIM + COST-APP * arity)
;;               + sum over multiply-used variables of (uses-1) * cost(argument)
;;
;; The last term is where abstraction really wins: a variable used k times is
;; passed once and duplicated k times inside the body, so k-1 copies of the
;; argument disappear from the program.  Two corrections follow:
;;
;;   * a location whose argument would have to capture a lambda *inside* the
;;     abstraction body cannot be rewritten at all, so its utility is zeroed;
;;   * overlapping locations cannot both be rewritten, so an outer location is
;;     charged for the utility already credited to any inner location it
;;     swallows (this is the paper's accept/reject DP, specialized).
;;
;; Locations left with nothing to contribute are *unused*: matched but not
;; rewritten.  Total utility sums the rest, weighted by how often each unique
;; subtree occurs, and subtracts the size of the abstraction itself (stitch's
;; `structure_penalty`, fixed at 1 here).
;;
;; PARITY
;;
;; Written to agree with real stitch on its default configuration; `file.rs:NN`
;; citations point at stitch/src.  Deliberate omissions, all inert by default:
;; tasks and weights (each program is its own task, weight 1), symbolic
;; variables, TDFA, eta-long mode, `inverse_argument_capture`, tracking, and
;; multithreading (which is why the worklist here is a plain heap and the
;; pruning cutoff a plain variable).
;; ---------------------------------------------------------------------------

(require "expr.rkt"
         "pattern.rkt"
         data/heap
         racket/set)

(provide (struct-out abstraction)
         search
         ;; exposed for testing and for compress.rkt's reporting
         utility-upper-bound
         arity-zero-best)

(module+ test (require rackunit))

;; An Abstraction; see the header for the fields.
(struct abstraction
  (pattern body-idx body arity utility compressive used args num-uses)
  #:transparent)

;; ---------------------------------------------------------------------------
;; The upper bound
;; ---------------------------------------------------------------------------

;; utility-upper-bound : Corpus (Listof Idx) -> Cost
;; The most any finished abstraction matching exactly these locations could
;; save.  At each location the very best imaginable case is that the whole
;; subtree collapses to a bare call to the new abstraction, saving its entire
;; cost but paying for the new primitive; and that best case cannot be negative,
;; because an abstraction that would lose money there simply would not be used.
;; Multiply by the number of occurrences of the subtree.
;;
;; This ignores body utility entirely, which is what makes it monotone: expanding
;; a hole only ever removes match locations, so a child's bound is a sub-sum of
;; its parent's.  The search asserts that.  (`compressive_utility_upper_bound`,
;; compression.rs:1521-1534, where `cost_of_node_all[n]` is `cost(n) *
;; num_paths(n)`, compression.rs:1945; `noncompressive_utility_upper_bound` is
;; identically 0, compression.rs:1540-1551.)
(define (utility-upper-bound c locs)
  (for/sum ([loc (in-list locs)])
    (max 0 (* (num-paths c loc) (- (cost c loc) COST-NEW-PRIM)))))

(module+ test
  (test-case "utility-upper-bound"
    ;; "(a a a)" and "(b b b)": `a` occurs 3 times and costs 100, so it is
    ;; worth exactly nothing (100 - 100 = 0); the whole program costs 302 and
    ;; occurs once, so it could save at most 202.
    (define c (corpus-from-programs (list "(a a a)" "(b b b)")))
    (define r0 (car (corpus-roots c)))
    (define aa (app-fun (corpus-node c r0)))
    (define a (app-fun (corpus-node c aa)))
    (check-equal? (utility-upper-bound c (list a)) 0)
    (check-equal? (utility-upper-bound c (list r0)) 202)
    (check-equal? (utility-upper-bound c (list aa)) 101)
    ;; sums over locations
    (check-equal? (utility-upper-bound c (list a aa r0)) 303)
    ;; and never goes negative, so it stays monotone under location subsetting
    (check-true (<= (utility-upper-bound c (list r0))
                    (utility-upper-bound c (list a r0))))))

;; ---------------------------------------------------------------------------
;; Prunings that depend only on the match locations
;; ---------------------------------------------------------------------------

;; single-use-prune? : Corpus (Listof Idx) -> Boolean
;; Discard a pattern that matches at a single unique subtree with no free
;; variables.  Whatever abstraction it grows into, the arity-zero abstraction
;; "the whole of that subtree" saves at least as much -- and we have already
;; scored every one of those.  The free-variable proviso matters because a
;; subtree with free variables is not a legal arity-zero body, so there is
;; nothing dominating this pattern in that case.
;;
;; PARITY: `should_prune_single_use` (compression.rs:1140-1148).  Note the
;; condition is on the number of *unique subtrees* matched, not on the number of
;; occurrences: one subtree occurring ten times is still pruned.
(define (single-use-prune? c locs)
  (and (null? (cdr locs))
       (set-empty? (free-vars c (car locs)))))

(module+ test
  (test-case "single-use pruning"
    (define c (corpus-from-programs (list "(f (g x) (g x))" "(lam (h $0))")))
    (define r0 (car (corpus-roots c)))
    (define gx (app-arg (corpus-node c r0)))
    ;; one closed subtree, however many times it occurs -> pruned
    (check-equal? (num-paths c gx) 2)
    (check-true (single-use-prune? c (list gx)))
    ;; two subtrees -> not pruned
    (check-false (single-use-prune? c (list gx r0)))
    ;; one subtree with a free variable -> not pruned, arity 0 cannot have it
    (define h$0 (lam-body (corpus-node c (cadr (corpus-roots c)))))
    (check-equal? (free-vars c h$0) (seteqv 0))
    (check-false (single-use-prune? c (list h$0)))))

;; single-task-prune? : Corpus (Listof Idx) -> Boolean
;; Discard a pattern that is confined to a single program.  This is stitch's
;; default and it is a semantic choice, not a speed hack: an abstraction is
;; supposed to capture something shared, and one that appears in only one
;; program often wins on raw cost while being useless.
;;
;; PARITY: `should_prune_single_task` (compression.rs:1150-1155), with the
;; default task labelling in which each program is its own task
;; (compression.rs:1813).  The Rust asks that every location have exactly one
;; task and that they all agree, which is the same as asking that the union of
;; the location's program sets have fewer than two members.
(define (single-task-prune? c locs)
  (define first-programs (programs-with c (car locs)))
  (and (= 1 (set-count first-programs))
       (for/and ([loc (in-list locs)])
         (equal? (programs-with c loc) first-programs))))

(module+ test
  (test-case "single-task pruning"
    (define c (corpus-from-programs (list "(f (g x))" "(h (g x))" "(f y)")))
    (define r0 (car (corpus-roots c)))
    (define r2 (caddr (corpus-roots c)))
    (define gx (app-arg (corpus-node c r0)))
    ;; (g x) is in two programs -> kept
    (check-false (single-task-prune? c (list gx)))
    ;; program 0's root is in program 0 only -> pruned
    (check-true (single-task-prune? c (list r0)))
    ;; two locations in two different programs -> kept
    (check-false (single-task-prune? c (list r0 r2)))
    ;; `f` heads both program 0 and program 2, so it is not single-task
    (define f (app-fun (corpus-node c r0)))
    (check-false (single-task-prune? c (list f)))))

;; ---------------------------------------------------------------------------
;; The two dominance prunings
;; ---------------------------------------------------------------------------
;;
;; Both are checked on *every* expansion, not just when a variable is added:
;; losing match locations can turn a previously useful variable into a useless
;; one.  Both consult the parent pattern's variables against the child's
;; locations, exactly as stitch does (compression.rs:1050-1057) -- a variable
;; introduced by this very expansion is not checked until the next one.

;; useless-abstract-prune? : Corpus Pattern (Listof Idx) -> Boolean
;; Discard a pattern that takes the same argument everywhere.  That variable is
;; not really a parameter; the pattern with the argument inlined into the body
;; is smaller and saves strictly more.  The argument must have no free variables
;; for the inlined version to be well formed -- an argument mentioning something
;; bound outside the match location cannot be written into the body.
;;
;; PARITY: `is_useless_abstract` (pattern_args.rs:123-142).  It iterates over
;; every *use* of every variable, not just the canonical one: two uses of the
;; same variable sit at different Paths and so see different arguments across
;; locations, and either one being constant is enough.  "The same argument"
;; means equal shifted Idxs, i.e. the same subtree as seen from the match root.
(define (useless-abstract-prune? c p locs)
  (for*/or ([uses (in-list (pattern-ivar-uses p))]
            [path (in-list uses)])
    (define shifted (for/list ([loc (in-list locs)])
                      (arg-shifted (extract-arg c loc path))))
    (and (for/and ([s (in-list (cdr shifted))]) (= s (car shifted)))
         (set-empty? (free-vars c (car shifted))))))

;; redundant-argument-prune? : Corpus Pattern (Listof Idx) -> Boolean
;; Discard a pattern in which two different variables receive the same argument
;; at every location.  The pattern that uses one variable twice instead matches
;; the same places, has smaller arity, and gets multiuse utility for the
;; repetition, so it strictly dominates.
;;
;; PARITY: `is_redundant_argument` (pattern_args.rs:144-172).  Unlike the
;; previous pruning this one compares variables, so it uses their canonical
;; Paths.
(define (redundant-argument-prune? c p locs)
  (define arity (pattern-arity p))
  (for*/or ([i (in-range arity)]
            [j (in-range (add1 i) arity)])
    (define pi (pattern-ivar-path p i))
    (define pj (pattern-ivar-path p j))
    (for/and ([loc (in-list locs)])
      (= (arg-shifted (extract-arg c loc pi))
         (arg-shifted (extract-arg c loc pj))))))

(module+ test
  (test-case "the two dominance prunings"
    ;; Corpus: (f a x) and (f a y), i.e. ((f a) x) and ((f a) y).
    ;; Pattern `(#0 #1 ??)` with #0 at (fun fun) and #1 at (fun arg), matching
    ;; both roots.  #0 sees `f` at both locations and #1 sees `a` at both.
    (define c (corpus-from-programs (list "(f a x)" "(f a y)")))
    (define locs (sort (corpus-roots c) <))
    (define p (pattern (app (app (pivar 0) (pivar 1)) 'hole)
                       (list '(arg))
                       (list (list '(fun fun)) (list '(fun arg)))
                       locs 0 0))
    ;; #0 is constantly `f` and `f` is closed -> useless abstraction
    (check-true (useless-abstract-prune? c p locs))
    ;; #0 = f and #1 = a differ, so they are not redundant
    (check-false (redundant-argument-prune? c p locs))
    ;; Now a pattern whose two variables both look at the same position class:
    ;; `(f #0 #1)` over (f a a) and (f b b) -- #0 and #1 always agree.
    (define c2 (corpus-from-programs (list "(f a a)" "(f b b)")))
    (define locs2 (sort (corpus-roots c2) <))
    (define p2 (pattern (app (app (prim 'f) (pivar 0)) (pivar 1))
                        '()
                        (list (list '(fun arg)) (list '(arg)))
                        locs2 0 0))
    (check-true (redundant-argument-prune? c2 p2 locs2))
    ;; but neither variable is constant across the two programs
    (check-false (useless-abstract-prune? c2 p2 locs2))))

;; ---------------------------------------------------------------------------
;; Expansions
;; ---------------------------------------------------------------------------

;; expands-to-rank : ExpandsTo -> Natural
;; expands-to<? : ExpandsTo ExpandsTo -> Boolean
;; stitch sorts the match locations by `(expands_to, loc)` before grouping them
;; (compression.rs:987), so the child patterns come out in a fixed order.  That
;; order is only observable through tie-breaking -- when two abstractions have
;; equal utility the first one found wins -- but we mirror it so that our body
;; strings match the real binary's.  The ordering is `#[derive(Ord)]` on
;; `ExpandsToInner` (expansion.rs:11-19), i.e. declaration order, with `Symbol`
;; ordered as its string (string_cache Atom's Ord).
(define (expands-to-rank e)
  (cond [(eq? e 'lam) 0]
        [(eq? e 'app) 1]
        [(var? e) 2]
        [(prim? e) 3]
        [(pivar? e) 4]
        [else (error 'expands-to-rank "not an expansion: ~a" e)]))

(define (expands-to<? a b)
  (define ra (expands-to-rank a))
  (define rb (expands-to-rank b))
  (cond [(not (= ra rb)) (< ra rb)]
        [(var? a) (< (var-i a) (var-i b))]
        [(prim? a) (string<? (symbol->string (prim-name a))
                             (symbol->string (prim-name b)))]
        [(pivar? a) (< (pivar-i a) (pivar-i b))]
        [else #f]))

;; syntactic-expansions : Corpus Pattern Path -> (Listof (cons ExpandsTo (Listof Idx)))
;; Group the pattern's match locations by what the corpus actually has at the
;; hole.  Each group is one way of expanding the hole into a piece of concrete
;; syntax, and it comes with exactly the locations where that piece is there --
;; which is the whole trick of stitch's incremental matching: no unification, a
;; table lookup and a groupby (`get_syntactic_expansions`, expansion.rs:161-168).
;;
;; PARITY: the grouping key is the head constructor of the argument's UNSHIFTED
;; subtree.  An argument that would capture a body lambda still reports its
;; variable and can still be expanded into it (see expr.rkt's discussion of
;; sentinels); such locations are filtered later, by utility, not here.
;; Locations stay sorted within each group.
(define (syntactic-expansions c p hole)
  (define groups (make-hash))
  (for ([loc (in-list (pattern-matches p))])
    (define e (arg-expands-to (extract-arg c loc hole)))
    (hash-update! groups e (lambda (ls) (cons loc ls)) '()))
  (for/list ([e (in-list (sort (hash-keys groups) expands-to<?))])
    (cons e (reverse (hash-ref groups e)))))

;; ivar-expansions : Corpus Pattern Path Natural
;;                   -> (Listof (cons ExpandsTo (Listof Idx)))
;; The other way to fill a hole: make it an argument.
;;   * Reusing an existing #i imposes an equality constraint, so the locations
;;     shrink to those where this hole sees the same argument #i already sees.
;;     "The same argument" is equality of shifted Idxs -- hash-consing makes
;;     that one integer comparison, and it is de Bruijn-correct because both
;;     sides are expressed relative to the match root.
;;   * A fresh variable constrains nothing, so it keeps every location; it is
;;     only allowed while the arity limit has room.
;; (`get_ivars_expansions`, expansion.rs:176-211; `compatible_locations`,
;; pattern_args.rs:237-249.)
(define (ivar-expansions c p hole max-arity)
  (define arity (pattern-arity p))
  (define reuses
    (for*/list ([i (in-range arity)]
                [canonical (in-value (pattern-ivar-path p i))]
                [locs (in-value (for/list ([loc (in-list (pattern-matches p))]
                                           #:when (= (arg-shifted (extract-arg c loc hole))
                                                     (arg-shifted (extract-arg c loc canonical))))
                                  loc))]
                #:unless (null? locs))
      (cons (pivar i) locs)))
  (if (< arity max-arity)
      (append reuses (list (cons (pivar arity) (pattern-matches p))))
      reuses))

(module+ test
  (test-case "grouping locations by what the hole sees"
    ;; Corpus: (f x), (f y), (lam z), and the shared leaves.  The initial
    ;; pattern's single hole is the empty path, so each location's "argument" is
    ;; itself, and the groups are the corpus's own constructors -- in stitch's
    ;; order: lam, app, then prims alphabetically.
    (define c (corpus-from-programs (list "(f x)" "(f y)" "(lam z)")))
    (define p (initial-pattern c (lambda (locs) 0)))
    (define groups (syntactic-expansions c p '()))
    (check-equal? (map car groups)
                  (list 'lam 'app (prim 'f) (prim 'x) (prim 'y) (prim 'z)))
    ;; the two applications group together, in ascending Idx order
    (define apps (cdr (assoc 'app groups)))
    (check-equal? apps (sort apps <))
    (check-equal? (length apps) 2)
    ;; `f` heads two of them, so its group is a single location
    (check-equal? (length (cdr (assoc (prim 'f) groups))) 1)))

(module+ test
  (test-case "ivar expansions reuse and freshness"
    ;; Corpus: (f a a) and (f b b).  Take the pattern `(f #0 ??)` -- #0 at
    ;; (fun arg) -- and expand the remaining hole at (arg).
    (define c (corpus-from-programs (list "(f a a)" "(f b b)")))
    (define locs (sort (corpus-roots c) <))
    (define p (pattern (app (app (prim 'f) (pivar 0)) 'hole)
                       (list '(arg)) (list (list '(fun arg))) locs 0 0))
    ;; reusing #0 keeps both locations, since the second argument equals the
    ;; first at both; a fresh #1 is also offered, with all locations
    (check-equal? (ivar-expansions c p '(arg) 2)
                  (list (cons (pivar 0) locs) (cons (pivar 1) locs)))
    ;; at the arity limit only the reuse survives
    (check-equal? (ivar-expansions c p '(arg) 1)
                  (list (cons (pivar 0) locs)))
    ;; With (f a a) and (f b c) instead, reuse only matches the first program,
    ;; so the equality constraint really does subset the locations.
    (define c2 (corpus-from-programs (list "(f a a)" "(f b c)")))
    (define locs2 (sort (corpus-roots c2) <))
    (define p2 (pattern (app (app (prim 'f) (pivar 0)) 'hole)
                        (list '(arg)) (list (list '(fun arg))) locs2 0 0))
    (define reuse (assoc (pivar 0) (ivar-expansions c2 p2 '(arg) 2)))
    (check-equal? (length (cdr reuse)) 1)))

;; free-variable-prune? : ExpandsTo Path -> Boolean
;; Discard an expansion that would put a variable in the body that no lambda of
;; the body binds.  The hole is under `path-lambda-depth` of the pattern's own
;; lambdas, so $0 .. $(d-1) are fine and $d and beyond escape.  An abstraction
;; with a free variable is not a function.
;; (`ExpandsTo::free_variable`, expansion.rs:56-63; compression.rs:1017.)
(define (free-variable-prune? e hole)
  (and (var? e) (>= (var-i e) (path-lambda-depth hole))))

(module+ test
  (test-case "free-variable pruning"
    ;; at the top of a body, every variable is free
    (check-true (free-variable-prune? (var 0) '()))
    ;; under one of the pattern's own lambdas, $0 is bound but $1 is not
    (check-false (free-variable-prune? (var 0) '(body arg)))
    (check-true (free-variable-prune? (var 1) '(body arg)))
    (check-false (free-variable-prune? (var 1) '(body body)))
    ;; only variables are ever pruned this way
    (check-false (free-variable-prune? (prim 'f) '()))
    (check-false (free-variable-prune? 'lam '()))))

;; ---------------------------------------------------------------------------
;; Exact utility of a finished pattern
;; ---------------------------------------------------------------------------

;; location-args : Corpus Pattern Idx -> (Listof Arg)
;; The arguments this pattern passes at one match location, one per abstraction
;; variable in order.  Read at each variable's canonical Path; the other uses
;; are constrained to see the same thing.
(define (location-args c p loc)
  (for/list ([i (in-range (pattern-arity p))])
    (extract-arg c loc (pattern-ivar-path p i))))

;; marginal-utilities : Corpus Pattern -> (U #f (Listof Cost))
;; The utility of one occurrence of the abstraction at each match location, in
;; the order of `pattern-matches`.  Returns #f when no location has anything to
;; offer, which autorejects the whole pattern.
;;
;; PARITY: `get_utility_of_loc_once` (compression.rs:1619-1660).  Two points:
;;   * a location where any argument contains a sentinel ivar is zeroed
;;     outright.  That argument would have to capture a lambda living inside the
;;     abstraction body, so the abstraction cannot be called there at all
;;     (`has_free_ivars`, pattern_args.rs:108-121).  stitch checks only the
;;     canonical use of each variable, which is enough because all uses of a
;;     variable see the same argument at any given location.
;;   * the multiuse bonus prices the argument by the cost of its *unshifted*
;;     subtree (`Arg::cost`, seeded at compression.rs:1254 and never updated
;;     while the zipper bubbles up).  Shifting never changes cost, so this is
;;     the same number either way.
(define (marginal-utilities c p)
  (define base (- (pattern-body-utility p)
                  (+ COST-NEW-PRIM (* COST-APP (pattern-arity p)))))
  (define multiuses (pattern-ivar-multiuses p))
  (define utils
    (for/list ([loc (in-list (pattern-matches p))])
      (define args (location-args c p loc))
      (cond
        [(for/or ([a (in-list args)]) (arg-captures? a)) 0]
        [else
         (+ base
            (for/sum ([iu (in-list multiuses)])
              (* (cdr iu) (cost c (arg-unshifted (list-ref args (car iu)))))))])))
  (and (for/or ([u (in-list utils)]) (> u 0)) utils))

;; correct-for-self-overlap : Corpus Pattern (Listof Cost) -> (Listof Cost)
;; Discount each location by the utility already credited to the match locations
;; nested inside it.  Two uses of an abstraction that overlap in the program
;; cannot both be rewritten; the rewriter is greedy top-down, so the outer one
;; wins, and the inner one's contribution has to come back off the outer one's.
;;
;; PARITY: compression.rs:1583-1616.  The loop runs over the match locations in
;; ascending Idx, which is bottom-up because the corpus arena is child-first --
;; so an inner location's own correction has already been applied by the time an
;; outer one subtracts it.  Only the pattern's self-overlap positions are looked
;; at, the corpus node at each such position is found by following the Path
;; (stitch reads `unshifted_id`, i.e. no de Bruijn adjustment), and a location
;; that ends up negative is clamped to 0 rather than allowed to poison its own
;; ancestors.
(define (correct-for-self-overlap c p marginals)
  (define paths (self-overlap-paths p))
  (cond
    [(null? paths) marginals]
    [else
     (define locs (pattern-matches p))
     (define index (for/hasheqv ([loc (in-list locs)] [i (in-naturals)])
                     (values loc i)))
     (define v (list->vector marginals))
     (for ([loc (in-list locs)] [i (in-naturals)])
       (define swallowed
         (for/sum ([path (in-list paths)])
           (define child (arg-unshifted (extract-arg c loc path)))
           (cond [(hash-ref index child #f) => (lambda (j) (vector-ref v j))]
                 [else 0])))
       (vector-set! v i (max 0 (- (vector-ref v i) swallowed))))
     (vector->list v)]))

;; compressive-utility : Corpus Pattern -> (values Cost (Listof Idx))
;; How much rewriting with this abstraction saves, and which of its match
;; locations are actually rewritten.  A location contributes its corrected
;; marginal utility once per occurrence of its subtree; a location left with
;; nothing to contribute is not rewritten at all.
;; (`compressive_utility` and `compressive_utility_from_marginals`,
;; compression.rs:1553-1616.)
(define (compressive-utility c p)
  (define marginals (marginal-utilities c p))
  (cond
    ;; An autorejected pattern saves nothing.  stitch reports an *empty* set of
    ;; unused locations here rather than marking them all unused
    ;; (compression.rs:1591), so every location still counts as used; it makes
    ;; no difference, since a pattern with zero compressive utility can never
    ;; beat a cutoff that is at worst 0.
    [(not marginals) (values 0 (pattern-matches p))]
    [else
     (define corrected (correct-for-self-overlap c p marginals))
     (values (for/sum ([loc (in-list (pattern-matches p))]
                       [u (in-list corrected)]
                       #:when (> u 0))
               (* u (num-paths c loc)))
             (for/list ([loc (in-list (pattern-matches p))]
                        [u (in-list corrected)]
                        #:when (> u 0))
               loc))]))

(module+ test
  (test-case "util-once: body, application penalty, and multiuse"
    ;; Corpus: (f a a) and (f b b).  Pattern `(f #0 #0)`, arity 1, matching both
    ;; roots.  Body utility = COST-PRIM (the `f`) + 2 * COST-APP = 102.
    ;; util-once = 102 - (100 + 1) + 1 * cost(argument) = 1 + 100 = 101.
    (define c (corpus-from-programs (list "(f a a)" "(f b b)")))
    (define locs (sort (corpus-roots c) <))
    (define p (pattern (app (app (prim 'f) (pivar 0)) (pivar 0))
                       '()
                       (list (list '(fun arg) '(arg)))
                       locs (+ COST-PRIM COST-APP COST-APP) 0))
    (check-equal? (marginal-utilities c p) (list 101 101))
    ;; each root occurs once, so compressive utility is 202 and both are used
    (define-values (cu used) (compressive-utility c p))
    (check-equal? cu 202)
    (check-equal? used locs)
    ;; Without the multiuse -- pattern `(f #0 #1)` -- the same body costs one
    ;; more application penalty and gains nothing: 102 - (100 + 2) = 0, so
    ;; every location is worthless and the pattern autorejects.
    (define q (pattern (app (app (prim 'f) (pivar 0)) (pivar 1))
                       '()
                       (list (list '(fun arg)) (list '(arg)))
                       locs (+ COST-PRIM COST-APP COST-APP) 0))
    (check-false (marginal-utilities c q))
    (define-values (cu2 used2) (compressive-utility c q))
    (check-equal? cu2 0)))

(module+ test
  (test-case "util-once: a capturing argument zeroes its location"
    ;; The pattern `(lam (f a #0))` matches both programs below, but in the
    ;; first one its argument is $0 -- the variable bound by the pattern's own
    ;; lambda.  There is no way to pass that in, so that location is matched but
    ;; can never be rewritten and its utility is forced to zero, while the
    ;; second location keeps its full 102.
    (define c (corpus-from-programs (list "(lam (f a $0))" "(lam (f a b))")))
    (define capturing (car (corpus-roots c)))
    (define ordinary (cadr (corpus-roots c)))
    (define locs (sort (list capturing ordinary) <))
    (define p (pattern (lam (app (app (prim 'f) (prim 'a)) (pivar 0)))
                       '()
                       (list (list '(body arg)))
                       locs
                       (+ COST-LAM COST-APP COST-APP COST-PRIM COST-PRIM) 0))
    (check-true (arg-captures? (extract-arg c capturing '(body arg))))
    (check-false (arg-captures? (extract-arg c ordinary '(body arg))))
    (define marginals (marginal-utilities c p))
    (define (util-at loc) (list-ref marginals (index-of locs loc)))
    (check-equal? (util-at capturing) 0)
    (check-equal? (util-at ordinary) 102)     ; 203 - (100 + 1)
    ;; so only the second location is rewritten
    (define-values (cu used) (compressive-utility c p))
    (check-equal? used (list ordinary))
    (check-equal? cu 102)))

(module+ test
  (test-case "self-overlap correction"
    ;; A crafted overlap.  The pattern `(#0 #1 x)` = ((#0 #1) x) matches inside
    ;; itself at its function position, and the corpus below is built so that
    ;; both an outer and an inner occurrence really are match locations:
    ;;   (p q x x) = ((((p q) x) x)
    ;; The inner ((p q) x) matches with #0=p, #1=q; the outer matches with
    ;; #0=(p q), #1=x -- and the inner one sits exactly at the outer one's
    ;; function position, which is concrete body, not an argument.  Rewriting
    ;; the outer one therefore destroys the inner one.  (Had the inner match
    ;; landed at an *argument* position instead, there would be no conflict:
    ;; the rewriter descends into arguments and rewrites them too, which is why
    ;; variable positions are excluded from the self-overlap check.)
    (define c (corpus-from-programs (list "(p q x x)" "(s t x x)")))
    (define outer0 (car (corpus-roots c)))
    (define inner0 (app-fun (corpus-node c outer0)))
    (define outer1 (cadr (corpus-roots c)))
    (define inner1 (app-fun (corpus-node c outer1)))
    (check-equal? (expr->string c inner0) "(p q x)")
    (define locs (sort (list inner0 inner1 outer0 outer1) <))
    ;; body utility: two apps + the prim x
    (define p (pattern (app (app (pivar 0) (pivar 1)) (prim 'x))
                       '() (list (list '(fun fun)) (list '(fun arg)))
                       locs (+ COST-APP COST-APP COST-PRIM) 0))
    (check-equal? (self-overlap-paths p) (list '(fun)))
    ;; util-once = 102 - (100 + 2) = 0 at every location, so nothing survives;
    ;; give the pattern a bigger body to make the arithmetic interesting.
    (define big (struct-copy pattern p [body-utility 300]))
    (check-equal? (marginal-utilities c big) (list 198 198 198 198))
    ;; each outer location swallows its inner one: 198 - 198 = 0, so the outer
    ;; locations are unused and only the inner ones are rewritten
    (define corrected (correct-for-self-overlap c big (marginal-utilities c big)))
    (define (corrected-at loc) (list-ref corrected (index-of locs loc)))
    (check-equal? (corrected-at inner0) 198)
    (check-equal? (corrected-at inner1) 198)
    (check-equal? (corrected-at outer0) 0)
    (check-equal? (corrected-at outer1) 0)
    (define-values (cu used) (compressive-utility c big))
    (check-equal? used (sort (list inner0 inner1) <))
    (check-equal? cu (* 2 198))))

;; ---------------------------------------------------------------------------
;; Finishing a pattern
;; ---------------------------------------------------------------------------

;; finish : Corpus Pattern Cost -> (U Abstraction #f)
;; Score a pattern with no holes left, returning it as an Abstraction if it
;; beats the current cutoff.  Total utility subtracts the size of the
;; abstraction body itself, which is stitch's structure penalty with its default
;; weight of 1 (`noncompressive_utility`, compression.rs:1507-1516).
;;
;; PARITY: compression.rs:1079-1119.  The assert that a finished pattern never
;; exceeds its own upper bound (compression.rs:1181) is the search's main
;; correctness oracle and is kept.  stitch tests the cutoff twice, first against
;; compressive utility alone -- which is itself an upper bound on total utility
;; -- to avoid the expensive step in between; that step is off by default, but
;; the double test is harmless and mirrored here.
(define (finish c p cutoff)
  (define-values (compressive used) (compressive-utility c p))
  (define utility (- compressive (pattern-body-utility p)))
  (unless (<= utility (pattern-upper-bound p))
    (error 'finish "utility ~a exceeds the pattern's upper bound ~a for ~a"
           utility (pattern-upper-bound p) (pattern->string p)))
  (and (> compressive cutoff)
       (> utility cutoff)
       (abstraction p
                    #f
                    (pattern->string p)
                    (pattern-arity p)
                    utility
                    compressive
                    used
                    (for/hasheqv ([loc (in-list used)])
                      (values loc (location-args c p loc)))
                    ;; stitch counts *all* match locations here, unused ones
                    ;; included (`usages`, compression.rs:1177)
                    (for/sum ([loc (in-list (pattern-matches p))])
                      (num-paths c loc)))))

;; ---------------------------------------------------------------------------
;; Arity-zero priming
;; ---------------------------------------------------------------------------

;; arity-zero-best : Corpus -> (U Abstraction #f)
;; Score every subtree of the corpus as an abstraction with no arguments -- a
;; plain name for a repeated piece of code -- and return the best.  Rewriting
;; replaces each occurrence by the new name, so the saving is
;; `num-paths * (cost - COST-NEW-PRIM)`, and then the abstraction itself costs
;; its own size.  Free variables are banned, as in any body, and the >= 2
;; programs rule applies.
;;
;; This runs before the search proper, and its winner both seeds the pruning
;; cutoff (which is what makes the bound bite from the very first pop) and is
;; itself a candidate answer -- for corpora with a big repeated constant it
;; often wins outright.  Single-use pruning is deliberately NOT applied here:
;; an arity-zero abstraction matches one subtree by construction.
;; (compression.rs:2002-2087.)
(define (arity-zero-best c)
  (for/fold ([best #f] [cutoff 0] #:result best)
            ([node (in-corpus-span c)])
    (define compressive (* (num-paths c node) (- (cost c node) COST-NEW-PRIM)))
    (define utility (- compressive (cost c node)))
    (cond
      [(and (set-empty? (free-vars c node))
            (>= (set-count (programs-with c node)) 2)
            (> utility 0)
            (> compressive cutoff)
            (> utility cutoff))
       (values (abstraction #f node (expr->string c node) 0
                            utility compressive (list node)
                            (hasheqv node '())
                            (num-paths c node))
               utility)]
      [else (values best cutoff)])))

(module+ test
  (test-case "arity-zero priming"
    ;; stitch's data/basic/identical.json: two copies of the same program, so
    ;; the whole program is the best arity-zero abstraction.
    ;;   cost((a b c d e)) = 4 apps + 5 prims = 504, occurring twice
    ;;   compressive = 2 * (504 - 100) = 808, utility = 808 - 504 = 304
    (define c (corpus-from-programs (list "(a b c d e)" "(a b c d e)")))
    (define a (arity-zero-best c))
    (check-equal? (abstraction-body a) "(a b c d e)")
    (check-equal? (abstraction-arity a) 0)
    (check-equal? (abstraction-utility a) 304)     ; real binary: utility 304
    (check-equal? (abstraction-num-uses a) 2)
    ;; A single leaf is never worth naming: 100 - 100 = 0 saved per use, and
    ;; here the leaves are all the two programs share.
    (check-false (arity-zero-best (corpus-from-programs (list "(f x)" "(g x)"))))
    ;; Nor is anything confined to one program.
    (check-false (arity-zero-best (corpus-from-programs (list "(a b c d e)" "(z)"))))
    ;; A free variable disqualifies a subtree, even a big shared one: every
    ;; subtree these two programs share -- ($0 a), ($0 a b), ($0 a b c),
    ;; ($0 a b c d) -- mentions $0, and none is a legal abstraction body.
    (check-false (arity-zero-best
                  (corpus-from-programs (list "(lam ($0 a b c d))"
                                              "(lam (m ($0 a b c d)))"))))))

;; ---------------------------------------------------------------------------
;; The search
;; ---------------------------------------------------------------------------

;; search : Corpus [Natural] -> (U Abstraction #f)
;; Find the abstraction of at most `max-arity` arguments that saves the most,
;; or #f if none saves anything.  Ties go to whichever the loop reaches first,
;; which is what makes this reproduce the real binary's choice of body.
;;
;; PARITY: `stitch_search` (compression.rs:943-1138) plus the worklist handling
;; of `get_worklist_item` (compression.rs:866-941), collapsed to one thread: the
;; buffers, the mutex and the done-list all degenerate to "keep the best so far
;; and its utility as the cutoff", because `inv_candidates` is 1 and a candidate
;; is only ever recorded when it strictly beats the cutoff.
(define (search c [max-arity 2])
  (define best (arity-zero-best c))
  (define cutoff (if best (abstraction-utility best) 0))

  ;; The worklist: a max-heap on the upper bound, so the most promising partial
  ;; pattern is always expanded next (compression.rs:598-608).  data/heap pops
  ;; the minimum, so the comparison is reversed.
  (define worklist
    (make-heap (lambda (a b) (>= (pattern-upper-bound a) (pattern-upper-bound b)))))
  (heap-add! worklist
             (initial-pattern c (lambda (locs) (utility-upper-bound c locs))))

  ;; consider! : Pattern ExpandsTo (Listof Idx) -> Void
  ;; Try one way of filling the current pattern's next hole: prune it, or score
  ;; it if it is finished, or push it back on the worklist if it is not.
  (define (consider! p expansion locs)
    (define hole (pattern-next-hole p))
    (unless (or (single-use-prune? c locs)
                (single-task-prune? c locs)
                (free-variable-prune? expansion hole))
      (define body-utility (+ (pattern-body-utility p) (expansion-cost expansion)))
      (define bound (utility-upper-bound c locs))
      (unless (<= bound (pattern-upper-bound p))
        (error 'search "upper bound went up: ~a > ~a when expanding ~a to ~a"
               bound (pattern-upper-bound p) (pattern->string p) expansion))
      (unless (or (<= bound cutoff)
                  ;; both dominance prunings look at the PARENT's variables
                  ;; against the CHILD's locations (compression.rs:1050-1057)
                  (useless-abstract-prune? c p locs)
                  (redundant-argument-prune? c p locs))
        (define child (expand-pattern p expansion locs body-utility bound))
        (cond
          [(pattern-finished? child)
           (define done (finish c child cutoff))
           (when done
             (set! best done)
             (set! cutoff (abstraction-utility done)))]
          [else (heap-add! worklist child)]))))

  ;; step! : Pattern -> Void
  ;; Expand the pattern's most recently created hole in every way that still
  ;; matches somewhere.
  (define (step! p)
    (define hole (pattern-next-hole p))
    (for ([group (in-list (append (syntactic-expansions c p hole)
                                  (ivar-expansions c p hole max-arity)))])
      (consider! p (car group) (cdr group))))

  (let loop ()
    (unless (zero? (heap-count worklist))
      (define p (heap-min worklist))
      (heap-remove-min! worklist)
      ;; the cutoff may have risen since this was pushed, so check again
      (when (> (pattern-upper-bound p) cutoff)
        (step! p))
      (loop)))
  best)

;; ---------------------------------------------------------------------------
;; End-to-end checks against the real binary
;; ---------------------------------------------------------------------------
;;
;; Each of these is `stitch/target/release/compress FILE --max-arity=2
;; --iterations=1`, whose reported body, arity, utility and num_uses we
;; reproduce exactly.  The full differential comparison lives outside the repo;
;; these are the small cases worth having in the unit test suite.

(module+ test
  ;; check-search : (Listof String) Natural String Natural Cost Natural -> Void
  ;; Search the corpus built from these programs and compare against what the
  ;; real binary reports.
  (define (check-search programs max-arity body arity utility num-uses)
    (define a (search (corpus-from-programs programs) max-arity))
    (check-not-false a)
    (when a
      (check-equal? (abstraction-body a) body)
      (check-equal? (abstraction-arity a) arity)
      (check-equal? (abstraction-utility a) utility)
      (check-equal? (abstraction-num-uses a) num-uses)))

  (test-case "simple1: an arity-1 abstraction beats naming anything"
    (check-search (list "(a a a)" "(b b b)") 2 "(#0 #0 #0)" 1 200 2))

  (test-case "simple2: the body may contain a lambda"
    (check-search (list "(a (lam (a a)))" "(b (lam (b b)))") 2
                  "(#0 (lam (#0 #0)))" 1 201 2))

  (test-case "identical: arity zero wins"
    (check-search (list "(a b c d e)" "(a b c d e)") 2 "(a b c d e)" 0 304 2))

  (test-case "hof: two arguments, one of them a function"
    (check-search
     (list "(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))"
           "(lam (app (app cons (app dec $0)) (app (app cons (app dec $0)) empty)))"
           "(lam (app (app cons (app (app plus $0) $0)) (app (app cons (app (app plus $0) $0)) empty)))")
     2
     "(app (app cons (app #1 #0)) (app (app cons (app #1 #0)) empty))" 2 2320 3))

  (test-case "ctx_thread_1: a body that is a lambda, with a variable under it"
    (check-search
     (list "(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))"
           "(A (lam (lam (+ (a b z $0 f) (a b z $0 f)))))")
     2 "(A (lam (lam (+ (#0 $0 f) (#0 $0 f)))))" 1 1011 2))

  (test-case "no abstraction is worth making"
    ;; stitch/data/basic/tmp_minimal.json: the real binary finds nothing.
    (check-false (search (corpus-from-programs (list "(a b)" "(a c)")) 2))))
