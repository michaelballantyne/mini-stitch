#lang racket

;; ---------------------------------------------------------------------------
;; pattern.rkt --- partial abstractions
;; ---------------------------------------------------------------------------
;;
;; A *pattern* is a partial abstraction: the body of an abstraction-under-
;; construction, with `??` holes standing for the parts the search has not yet
;; decided about and `#i` abstraction variables standing for the parts it has
;; decided to pass in as arguments.  The search grows a pattern one hole at a
;; time; when the last hole is gone the pattern is a finished abstraction.
;;
;; This module owns the pattern representation and the three things one does
;; with a pattern that are pure syntax:
;;
;;   * build the initial all-hole pattern and expand a hole,
;;   * print the body in stitch's own format,
;;   * detect *self-overlap*: the positions inside the pattern where the whole
;;     pattern could match again.  That matters because two overlapping uses of
;;     an abstraction cannot both be rewritten, so the utility calculation has
;;     to discount one of them (see search.rkt).
;;
;; Nothing here knows about utility, bounds, or the worklist.  The one place
;; search's vocabulary leaks in is that a Pattern carries its `body-utility`
;; and `upper-bound` fields along for the ride; the caller computes them.
;;
;; WHAT WE DO DIFFERENTLY FROM micro.rkt
;;
;; micro.rkt's patterns are bare trees, and it finds out where one matches by
;; structurally matching it against every subterm of every program -- the
;; paper's LambdaUnify, run again from scratch for every candidate.  A Pattern
;; here is a tree *plus* the bookkeeping that makes expansion incremental: the
;; paths of its holes, the paths where each abstraction variable is used, and
;; the match locations themselves.  Expanding a hole filters the parent's
;; locations rather than re-walking the corpus, which is sound because a child
;; pattern's locations are always a subset of its parent's (the observation
;; that justifies the paper's Lemma 2), and expansion never walks the corpus
;; again after the first pass.
;;
;; Self-overlap detection has no counterpart in micro.rkt at all.  micro scores
;; a candidate by actually rewriting the corpus, so two overlapping uses simply
;; cannot both happen; here utility is computed analytically before anything is
;; rewritten, so the overlap has to be found and discounted by hand.
;;
;; DATA DEFINITIONS
;;
;; A PatternTree is one of
;;   'hole        an unexpanded `??`
;;   (pivar i)    the abstraction variable #i, i >= 0
;;   (prim s)     a primitive              \
;;   (var i)      a de Bruijn variable      |  the Node shapes of expr.rkt,
;;   (app f x)    an application            |  but with PatternTree children
;;   (lam b)      a lambda                 /   instead of Idx children
;;
;; Patterns are tiny (a handful of nodes) and are rebuilt from scratch on every
;; expansion, so unlike the corpus they are plain trees: no arena, no interning.
;; Reusing expr.rkt's `app`/`lam`/`prim`/`var` structs is deliberate -- a
;; pattern really is a corpus subtree with pieces cut out -- but note that the
;; children of an `app` here are PatternTrees, not Idxs.
;;
;; A Path is expr.rkt's: a list of 'fun/'arg/'body steps, root first.  Inside a
;; pattern a Path names a position in the PatternTree; below a match location
;; the same Path names the corpus subtree that position matches.  This is
;; stitch's ZId, minus the interning (map section 1).
;;
;; An ExpandsTo is expr.rkt's, extended with (pivar i): the five ways a hole can
;; be filled.  'app and 'lam leave fresh holes behind; the three leaf shapes do
;; not.
;;
;; A Pattern is a (pattern PatternTree (Listof Path) (Listof (Listof Path))
;;                         (Listof Idx) Cost Cost) where
;;   tree          the body so far
;;   holes         the positions of the `??`s, MOST RECENTLY CREATED FIRST.
;;                 stitch keeps the same list oldest-first and indexes it from
;;                 the end (`HoleChoice::DepthFirst`, compression.rs:822); we
;;                 keep it reversed so that the depth-first choice is `car`.
;;   ivar-uses     one entry per abstraction variable, in order of first use;
;;                 each entry lists every Path where that variable occurs, in
;;                 order of use.  The first Path of an entry is the variable's
;;                 *canonical* one, which is the only one stitch consults when
;;                 asking what argument the variable receives
;;                 (`PatternArgs::variables`, pattern_args.rs:39).
;;   matches       the match locations: the Idxs of the unique corpus subtrees
;;                 this pattern matches, ALWAYS SORTED ASCENDING.  Ascending Idx
;;                 is bottom-up order, which the self-overlap correction relies
;;                 on.
;;   body-utility  the summed cost of the concrete constructors in `tree`
;;   upper-bound   an upper bound on the utility of any finished descendant
;;
;; The empty Path names the whole pattern, so the initial pattern is
;; `('hole, holes = (list '()), no variables, matching everything)`.
;;
;; PARITY
;;
;; stitch does not store patterns as trees at all: a Pattern is a set of hole
;; zippers plus a set of argument zippers plus the match locations, and the body
;; is reconstructed on demand by walking any one match location and cutting at
;; those zippers (`Pattern::to_expr`, compression.rs:513-552).  Keeping the tree
;; explicitly is the main representational simplification of mini-stitch, and it
;; is what lets self-overlap detection be ordinary tree unification instead of
;; stitch's ZipTrie.  Everything else in this module is written to agree with
;; the Rust step for step; `file.rs:NN` citations point at stitch/src.
;; ---------------------------------------------------------------------------

(require "expr.rkt"
         racket/set)

(provide (struct-out pivar)
         (struct-out pattern)
         initial-pattern
         pattern-arity pattern-finished? pattern-next-hole
         pattern-ivar-path pattern-ivar-multiuses
         expand-pattern
         expansion-cost
         path-lambda-depth
         pattern->string tree->string
         self-overlap-paths)

(module+ test (require rackunit))

;; ---------------------------------------------------------------------------
;; The pattern tree
;; ---------------------------------------------------------------------------

;; An abstraction variable inside a pattern.  It is a separate struct from
;; expr.rkt's `ivar` so that nothing can confuse a pattern's own #i with the
;; *sentinel* ivars that argument extraction leaves inside shifted corpus
;; subtrees -- the two are unrelated despite printing the same way.
(struct pivar (i) #:transparent)   ; Natural

;; A Pattern; see the header for the fields.
(struct pattern (tree holes ivar-uses matches body-utility upper-bound)
  #:transparent)

;; wildcard? : PatternTree -> Boolean
;; Does this position match anything?  Both holes and abstraction variables do:
;; a hole because it has not been decided yet, a variable because it will be
;; filled with whatever sits there.
(define (wildcard? t)
  (or (eq? t 'hole) (pivar? t)))

;; ---------------------------------------------------------------------------
;; Building patterns
;; ---------------------------------------------------------------------------

;; initial-pattern : Corpus ((Listof Idx) -> Cost) -> Pattern
;; The single-hole pattern `??`.  It matches every node in the corpus span --
;; every unique subtree is a place a one-hole pattern could sit.
;;
;; PARITY: `Pattern::single_hole` (compression.rs:437-512) starts from exactly
;; corpus_span and then filters, but all three filters are off in default mode:
;; `no_curried_bodies` and `eta_long` are flags, and `invalid_match_location`
;; (compression.rs:667) only fires for TDFA annotations or fused-lambda tags,
;; neither of which we model.  So in default mode nothing is excluded.
;;
;; The caller supplies the upper bound, as a function of the match locations,
;; because bounds are search's business.
(define (initial-pattern c upper-bound-of)
  (define matches (sequence->list (in-corpus-span c)))
  (pattern 'hole (list '()) '() matches 0 (upper-bound-of matches)))

(module+ test
  (test-case "initial-pattern matches the whole span"
    (define c (corpus-from-programs (list "(a a a)" "(b b b)")))
    (define p (initial-pattern c (lambda (locs) 0)))
    (check-equal? (pattern-tree p) 'hole)
    (check-equal? (pattern-holes p) (list '()))
    (check-equal? (pattern-arity p) 0)
    (check-false (pattern-finished? p))
    (check-equal? (length (pattern-matches p)) (corpus-span c))
    (check-equal? (pattern-matches p) (sort (pattern-matches p) <))))

;; pattern-arity : Pattern -> Natural
;; How many abstraction variables the pattern has introduced.
(define (pattern-arity p) (length (pattern-ivar-uses p)))

;; pattern-finished? : Pattern -> Boolean
;; Is there nothing left to decide?  A finished pattern is an abstraction.
(define (pattern-finished? p) (null? (pattern-holes p)))

;; pattern-next-hole : Pattern -> Path
;; The hole the search will expand next: the most recently created one, which
;; makes the search depth-first (compression.rs:822).
(define (pattern-next-hole p) (car (pattern-holes p)))

;; pattern-ivar-path : Pattern Natural -> Path
;; The canonical Path of abstraction variable #i, i.e. the position of its first
;; use.  stitch asks "what argument does #i receive here?" only at this Path
;; (`PatternArgs::variables`, pattern_args.rs:39); the other uses are constrained
;; to see the same argument, so any of them would do.
(define (pattern-ivar-path p i)
  (car (list-ref (pattern-ivar-uses p) i)))

;; pattern-ivar-multiuses : Pattern -> (Listof (cons Natural Natural))
;; For each abstraction variable used more than once, the pair (i . uses-1).
;; That count is how many copies of the argument the abstraction saves at each
;; location, which is where multiuse utility comes from
;; (`PatternArgs::multiuses`, pattern_args.rs:102-106).
(define (pattern-ivar-multiuses p)
  (for/list ([uses (in-list (pattern-ivar-uses p))]
             [i (in-naturals)]
             #:when (> (length uses) 1))
    (cons i (sub1 (length uses)))))

;; expansion-cost : ExpandsTo -> Cost
;; What filling a hole this way adds to the pattern's body utility: the local
;; cost of the constructor it introduces.  An abstraction variable adds nothing
;; -- it is not part of the body's structure, it is a parameter
;; (`local_expansion_utility`, expansion.rs:71-82).
(define (expansion-cost e)
  (cond [(eq? e 'app) COST-APP]
        [(eq? e 'lam) COST-LAM]
        [(var? e) COST-VAR]
        [(prim? e) COST-PRIM]
        [(pivar? e) 0]
        [else (error 'expansion-cost "not an expansion: ~a" e)]))

;; expansion->tree : ExpandsTo -> PatternTree
;; The subtree a hole becomes, with fresh holes for the new children.
(define (expansion->tree e)
  (cond [(eq? e 'app) (app 'hole 'hole)]
        [(eq? e 'lam) (lam 'hole)]
        [(or (var? e) (prim? e) (pivar? e)) e]
        [else (error 'expansion->tree "not an expansion: ~a" e)]))

;; expansion-holes : ExpandsTo Path -> (Listof Path)
;; The Paths of the holes that filling the hole at `hole` this way creates,
;; MOST RECENT FIRST.
;;
;; PARITY: the order matters, because the next hole chosen is the most recent
;; one.  `syntactic_expansion` (expansion.rs:85-97) pushes Func and then Arg
;; onto a list it reads from the end, so the *argument* of a new application is
;; expanded before its function.
(define (expansion-holes e hole)
  (cond [(eq? e 'app) (list (append hole '(arg)) (append hole '(fun)))]
        [(eq? e 'lam) (list (append hole '(body)))]
        [else '()]))

;; tree-replace : PatternTree Path PatternTree -> PatternTree
;; Replace the subtree at `path` (which must be a hole, though we do not check)
;; with `new`.
(define (tree-replace t path new)
  (cond
    [(null? path) new]
    [else
     (case (car path)
       [(fun) (unless (app? t) (error 'tree-replace "'fun step into ~a" t))
              (app (tree-replace (app-fun t) (cdr path) new) (app-arg t))]
       [(arg) (unless (app? t) (error 'tree-replace "'arg step into ~a" t))
              (app (app-fun t) (tree-replace (app-arg t) (cdr path) new))]
       [(body) (unless (lam? t) (error 'tree-replace "'body step into ~a" t))
               (lam (tree-replace (lam-body t) (cdr path) new))]
       [else (error 'tree-replace "bad path step: ~a" (car path))])]))

;; add-ivar-use : (Listof (Listof Path)) Natural Path -> (Listof (Listof Path))
;; Record that variable #i is used at `path`.  A brand new variable (i equal to
;; the current arity) gets a new entry; an existing one gets `path` appended, so
;; that the canonical (first) Path stays first.  Mirrors `PatternArgs::add_var`
;; (pattern_args.rs:75-80).
(define (add-ivar-use uses i path)
  (cond
    [(= i (length uses)) (append uses (list (list path)))]
    [(< i (length uses))
     (for/list ([u (in-list uses)] [j (in-naturals)])
       (if (= j i) (append u (list path)) u))]
    [else (error 'add-ivar-use "variable #~a skips ahead of arity ~a"
                 i (length uses))]))

;; expand-pattern : Pattern ExpandsTo (Listof Idx) Cost Cost -> Pattern
;; Fill the pattern's next hole with `expansion`, given the locations where the
;; result still matches and the caller's freshly computed body utility and upper
;; bound.  This is the one way patterns grow.
(define (expand-pattern p expansion matches body-utility upper-bound)
  (define hole (pattern-next-hole p))
  (pattern (tree-replace (pattern-tree p) hole (expansion->tree expansion))
           (append (expansion-holes expansion hole) (cdr (pattern-holes p)))
           (if (pivar? expansion)
               (add-ivar-use (pattern-ivar-uses p) (pivar-i expansion) hole)
               (pattern-ivar-uses p))
           matches
           body-utility
           upper-bound))

(module+ test
  (test-case "expanding holes builds a tree, newest hole first"
    ;; Grow `??` into `(#0 (lam ??))`, checking at each step which hole is next.
    (define c (corpus-from-programs (list "(a a a)" "(b b b)")))
    (define p0 (initial-pattern c (lambda (locs) 0)))
    ;; `??` -> `(?? ??)`; the argument hole is the most recent, so it is next
    (define p1 (expand-pattern p0 'app (pattern-matches p0) COST-APP 0))
    (check-equal? (pattern-tree p1) (app 'hole 'hole))
    (check-equal? (pattern-holes p1) (list '(arg) '(fun)))
    (check-equal? (pattern-next-hole p1) '(arg))
    ;; `(?? ??)` -> `(?? (lam ??))`
    (define p2 (expand-pattern p1 'lam (pattern-matches p1) (+ COST-APP COST-LAM) 0))
    (check-equal? (pattern-tree p2) (app 'hole (lam 'hole)))
    (check-equal? (pattern-holes p2) (list '(arg body) '(fun)))
    ;; fill the lambda's body with a fresh variable, then the function position
    ;; with the same variable
    (define p3 (expand-pattern p2 (pivar 0) (pattern-matches p2) (+ COST-APP COST-LAM) 0))
    (check-equal? (pattern-holes p3) (list '(fun)))
    (check-equal? (pattern-arity p3) 1)
    (check-equal? (pattern-ivar-path p3 0) '(arg body))
    (define p4 (expand-pattern p3 (pivar 0) (pattern-matches p3) (+ COST-APP COST-LAM) 0))
    (check-true (pattern-finished? p4))
    (check-equal? (pattern-tree p4) (app (pivar 0) (lam (pivar 0))))
    ;; the canonical path is still the first use, and #0 is now a multiuse
    (check-equal? (pattern-ivar-path p4 0) '(arg body))
    (check-equal? (pattern-ivar-multiuses p4) (list (cons 0 1)))
    (check-equal? (pattern-ivar-multiuses p3) '())))

;; path-lambda-depth : Path -> Natural
;; How many lambdas of the pattern enclose the position at this Path.  A hole at
;; depth d can be expanded into $0 ... $(d-1) but not $d: that variable would be
;; free at the top of the abstraction body, and an abstraction with free
;; variables is not a function (compression.rs:1017, expansion.rs:57-63).
(define (path-lambda-depth path)
  (for/sum ([step (in-list path)] #:when (eq? step 'body)) 1))

(module+ test
  (test-case "path-lambda-depth"
    (check-equal? (path-lambda-depth '()) 0)
    (check-equal? (path-lambda-depth '(fun arg)) 0)
    (check-equal? (path-lambda-depth '(body arg body fun)) 2)))

;; ---------------------------------------------------------------------------
;; Printing
;; ---------------------------------------------------------------------------

;; tree->string : PatternTree -> String
;; Print a pattern body the way stitch prints an abstraction: application spines
;; flattened, `(lam ...)`, `$i`, `#i`, and `??` for a hole.  Same conventions as
;; `expr->string`; stitch literally shares the printer, representing a hole as
;; the primitive named "??" (compression.rs:519, lambdas expr.rs:17).
(define (tree->string t)
  (define out (open-output-string))
  ;; emit : PatternTree Boolean -> Void ; left-of-app? suppresses parentheses
  (define (emit t left-of-app?)
    (cond
      [(eq? t 'hole) (write-string "??" out)]
      [(pivar? t) (fprintf out "#~a" (pivar-i t))]
      [(var? t) (fprintf out "$~a" (var-i t))]
      [(prim? t) (fprintf out "~a" (prim-name t))]
      [(app? t)
       (unless left-of-app? (write-string "(" out))
       (emit (app-fun t) #t)
       (write-string " " out)
       (emit (app-arg t) #f)
       (unless left-of-app? (write-string ")" out))]
      [(lam? t)
       (write-string "(lam " out)
       (emit (lam-body t) #f)
       (write-string ")" out)]
      [else (error 'tree->string "not a pattern tree: ~a" t)]))
  (emit t #f)
  (get-output-string out))

;; pattern->string : Pattern -> String
;; The pattern's body, printed.
(define (pattern->string p) (tree->string (pattern-tree p)))

(module+ test
  (test-case "printing patterns in stitch's format"
    (check-equal? (tree->string 'hole) "??")
    ;; the body real stitch reports for data/basic/simple2.json
    (check-equal? (tree->string (app (pivar 0) (lam (app (pivar 0) (pivar 0)))))
                  "(#0 (lam (#0 #0)))")
    ;; curried spines flatten, as in data/basic/simple1.json
    (check-equal? (tree->string (app (app (pivar 0) (pivar 0)) (pivar 0)))
                  "(#0 #0 #0)")
    ;; an unfinished pattern shows its holes
    (check-equal? (tree->string (app (app (prim 'app) 'hole) (lam (var 0))))
                  "(app ?? (lam $0))")))

;; ---------------------------------------------------------------------------
;; Self-overlap
;; ---------------------------------------------------------------------------
;;
;; Two uses of an abstraction cannot overlap in the rewritten program: if a
;; match location sits strictly inside another match location, only one of them
;; can actually be rewritten.  For that to be possible at all the pattern has to
;; be able to match inside *itself*, which is a property of the pattern alone.
;; The pattern `(#0 #1 x)` for example matches inside itself at the function
;; position, since `(#0 #1)` unifies with the whole pattern.
;;
;; search.rkt uses the answer to discount the utility of the outer location by
;; the utility already credited to the inner one.  Because the check happens
;; once per finished pattern and only says *where* overlap is possible (not
;; whether it happens at a particular location), an overapproximation is fine --
;; and stitch's is one, since it ignores the constraint that repeated variables
;; must receive the same argument (pattern_args.rs:344-347).
;;
;; PARITY: stitch does this with a trie of the argument zippers
;; (`can_self_unify`, pattern_args.rs:344-359, driving `find_self_unification
;; _points` and `unifies`).  With a real tree it is just unification, but two
;; details of the Rust are easy to get wrong and are load-bearing:
;;
;;   * Which positions are considered.  Not every internal position: the walk
;;     descends only while the trie still has an argument zipper below it, and
;;     stops as soon as it reaches one.  So the candidate positions are exactly
;;     the non-root positions that have an abstraction variable strictly below
;;     them (pattern_args.rs:315-322).  A position with no variable underneath
;;     is skipped because the pattern there is fully concrete, hence either
;;     identical to the whole pattern (which is not a *proper* overlap) or
;;     strictly smaller than it, so it cannot match the whole pattern.
;;   * What counts as a wildcard.  Only abstraction variables, on either side
;;     (pattern_args.rs:259-261).  Holes never arise: the check runs only on
;;     finished patterns.
;;
;; stitch works against one example match location rather than a pattern tree,
;; and so has one rule we do not need: `overall_loc == partial_loc` unifies
;; immediately (pattern_args.rs:263-265).  That is a shortcut for "the same
;; corpus subtree", and since both sides then carve variables out of the *same*
;; subtree they unify structurally anyway.

;; contains-pivar? : PatternTree -> Boolean
;; Is there an abstraction variable somewhere in this subtree?  This is the trie
;; test: stitch's `partial_abs` is None exactly when the answer is no.
(define (contains-pivar? t)
  (cond [(pivar? t) #t]
        [(app? t) (or (contains-pivar? (app-fun t)) (contains-pivar? (app-arg t)))]
        [(lam? t) (contains-pivar? (lam-body t))]
        [else #f]))

;; unify? : PatternTree PatternTree -> Boolean
;; Could these two patterns match the same term?  Wildcards match anything;
;; everything else must agree constructor for constructor.
(define (unify? a b)
  (cond
    [(wildcard? a) #t]
    [(wildcard? b) #t]
    [(and (app? a) (app? b)) (and (unify? (app-fun a) (app-fun b))
                                  (unify? (app-arg a) (app-arg b)))]
    [(and (lam? a) (lam? b)) (unify? (lam-body a) (lam-body b))]
    [(or (app? a) (app? b) (lam? a) (lam? b)) #f]   ; shape mismatch
    [else (equal? a b)]))                            ; two leaves

(module+ test
  (test-case "unify?"
    (check-true (unify? (pivar 0) (app (prim 'f) (prim 'x))))
    (check-true (unify? (app (pivar 0) (pivar 1)) (app (prim 'f) (lam (var 0)))))
    ;; repeated variables are NOT required to agree -- the overapproximation
    (check-true (unify? (app (pivar 0) (pivar 0)) (app (prim 'f) (prim 'g))))
    (check-false (unify? (app (prim 'f) (pivar 0)) (app (prim 'g) (pivar 0))))
    (check-false (unify? (lam (pivar 0)) (app (pivar 0) (pivar 1))))
    (check-false (unify? (var 0) (var 1)))
    (check-true (unify? (var 3) (var 3)))))

;; self-overlap-paths : Pattern -> (Listof Path)
;; The proper internal positions at which the pattern can match inside itself.
(define (self-overlap-paths p)
  (define whole (pattern-tree p))
  (define found '())
  ;; walk : PatternTree Path -> Void ; `rpath` is the position, reversed
  (define (walk t rpath)
    (cond
      [(not (contains-pivar? t)) (void)]   ; nothing to unify with below here
      [(pivar? t) (void)]                  ; a variable is not an overlap point
      [else
       (when (and (pair? rpath) (unify? whole t))
         (set! found (cons (reverse rpath) found)))
       (cond
         [(app? t) (walk (app-fun t) (cons 'fun rpath))
                   (walk (app-arg t) (cons 'arg rpath))]
         [(lam? t) (walk (lam-body t) (cons 'body rpath))]
         [else (void)])]))
  (walk whole '())
  (reverse found))

(module+ test
  (test-case "self-overlap of (#0 #1 x)"
    ;; stitch's own example (pattern_args.rs:345-346): `(#0 #1 x)` is
    ;; ((#0 #1) x), and its function position (#0 #1) unifies with the whole
    ;; pattern because #0 absorbs (#0 #1) and #1 absorbs x.
    (define p (pattern (app (app (pivar 0) (pivar 1)) (prim 'x))
                       '() (list (list '(fun fun)) (list '(fun arg)))
                       '() 0 0))
    (check-equal? (self-overlap-paths p) (list '(fun)))))

(module+ test
  (test-case "self-overlap: positions with no variable below are skipped"
    ;; `(#0 (f x))`: the argument position (f x) is concrete, so the walk never
    ;; even looks at it -- and rightly so, since a concrete proper subtree is
    ;; strictly smaller than the pattern.
    (define p (pattern (app (pivar 0) (app (prim 'f) (prim 'x)))
                       '() (list (list '(fun))) '() 0 0))
    (check-equal? (self-overlap-paths p) '())))

(module+ test
  (test-case "self-overlap: a variable position is not an overlap point"
    ;; `(#0 #0)` unifies with its own function position #0, but #0 is a
    ;; variable, and variables are excluded (pattern_args.rs:320-323): an
    ;; argument is not a use of the abstraction.
    (define p (pattern (app (pivar 0) (pivar 0))
                       '() (list (list '(fun) '(arg))) '() 0 0))
    (check-equal? (self-overlap-paths p) '())))

(module+ test
  (test-case "self-overlap: overlap can be nested, and shapes must agree"
    ;; `(f (#0 #1 x))`: the spine (#0 #1) sits two levels down, and it unifies
    ;; with the whole pattern (#0 absorbs the head `f`, #1 absorbs the rest).
    ;; Its parent ((#0 #1) x) does not: `f` is a leaf and (#0 #1) is an app.
    ;; So overlap points need not be near the root.
    (define p1 (pattern (app (prim 'f) (app (app (pivar 0) (pivar 1)) (prim 'x)))
                        '() (list (list '(arg fun fun)) (list '(arg fun arg)))
                        '() 0 0))
    (check-equal? (self-overlap-paths p1) (list '(arg fun)))
    ;; `(#0 (#1 y) x)` = ((#0 (#1 y)) x): the function position (#0 (#1 y))
    ;; does not unify with the whole pattern, because its argument (#1 y) is an
    ;; app while the whole pattern's argument `x` is a leaf.
    (define p2 (pattern (app (app (pivar 0) (app (pivar 1) (prim 'y))) (prim 'x))
                        '() (list (list '(fun fun)) (list '(fun arg fun)))
                        '() 0 0))
    (check-equal? (self-overlap-paths p2) '())
    ;; ... whereas `(#0 (#1 y) (z y))` does overlap at its function position,
    ;; since there (#1 y) unifies with (z y).
    (define p3 (pattern (app (app (pivar 0) (app (pivar 1) (prim 'y)))
                             (app (prim 'z) (prim 'y)))
                        '() (list (list '(fun fun)) (list '(fun arg fun)))
                        '() 0 0))
    (check-equal? (self-overlap-paths p3) (list '(fun)))))

(module+ test
  (test-case "self-overlap: lambdas"
    ;; `(lam (#0 #1))` cannot overlap itself: its only internal position with a
    ;; variable below it is the lam body, and (#0 #1) is an app, not a lam.
    (define p (pattern (lam (app (pivar 0) (pivar 1)))
                       '() (list (list '(body fun))) '() 0 0))
    (check-equal? (self-overlap-paths p) '())
    ;; but `(lam (lam #0))` does: the inner (lam #0) unifies with the whole.
    (define q (pattern (lam (lam (pivar 0)))
                       '() (list (list '(body body))) '() 0 0))
    (check-equal? (self-overlap-paths q) (list '(body)))))
