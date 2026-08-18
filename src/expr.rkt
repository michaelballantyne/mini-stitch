#lang racket

;; ---------------------------------------------------------------------------
;; expr.rkt --- the corpus of mini-stitch
;; ---------------------------------------------------------------------------
;;
;; This module begins mini-stitch, which computes what micro.rkt computes --
;; the abstraction that compresses a corpus most -- but fast enough to run on
;; real corpora.  (The agreement is exact except on one corpus family where
;; real stitch's own utility accounting, which mini reproduces, disagrees
;; with micro's scoring-by-rewriting; see tests/micro-test.rkt.)  The language is the same one (ast.rkt); the
;; representation is not.  micro.rkt keeps each program as an ordinary immutable
;; tree and asks whether two subtrees agree with `equal?`.  mini-stitch instead
;; stores every subtree of every program exactly once, in a single hash-consed
;; arena, so that subtree equality is integer `=` and one step of the search can
;; advance every occurrence of a subtree at once.
;;
;; Everything in mini-stitch therefore happens against one shared, hash-consed
;; *corpus*.  This module owns that arena.  It knows how to
;;
;;   * build it (parse s-expression programs into it, interning as it goes),
;;   * print any node back out in stitch's own syntax,
;;   * answer the bottom-up questions the search asks about nodes (cost, free
;;     variables, how many times a subtree occurs, which programs contain it),
;;   * and extract the *argument* a partial abstraction would capture at a
;;     given hole -- the one genuinely subtle piece, because lifting a subtree
;;     out from under lambdas changes its de Bruijn indices.
;;
;; Nothing here knows about patterns, utility, or search.
;;
;; DATA DEFINITIONS
;;
;; A Node is ast.rkt's, with Idx children: (prim s), (var i), (ivar i),
;; (app f x) with f and x Idxs, and (lam b) with b an Idx.  Two notes on the
;; ivar case, which is the one this module leans on hardest: parsed programs
;; never contain an abstraction variable, and this module puts them to a second
;; use as the *sentinel* marker that argument extraction leaves behind (see
;; below).
;;
;; An Idx is a natural number: the position of a Node in the corpus arena.
;; The arena is append-only and *child-first*: a node's children always have
;; strictly smaller Idxs than the node itself.  Adding a node interns it, so
;; two structurally identical subtrees anywhere in the corpus are the same Idx
;; and subtree equality is integer =.  This is the single most load-bearing
;; property in the whole system: it makes "does this pattern match here" and
;; "do these two holes see the same argument" pointer comparisons, and it lets
;; one step of the search advance every occurrence of a subtree at once.
;;
;; A Corpus bundles the arena, the intern table, the list of program roots, the
;; *span*, and memo tables for the analyses.  The span is the number of nodes
;; created by parsing the programs.  It matters because the arena keeps growing
;; afterwards: argument extraction adds de Bruijn-shifted copies of subtrees.
;; Only nodes below the span are real corpus subtrees, so only they can be
;; match locations, and only they have occurrence counts and program sets.
;; (The Rust calls this `corpus_span`, a Range; here it is just the length.)
;;
;; An ExpandsTo describes the root constructor of a subtree -- what a hole
;; would have to expand into to match there.  It is one of
;;   'app, 'lam, (var i), (prim s), (ivar i)
;; i.e. the node itself for leaves, and a bare symbol for the two branching
;; shapes (whose children are irrelevant to the grouping).  It is compared with
;; equal?.  Mirrors `ExpandsTo` / `expands_to_of_node` (stitch expansion.rs:11,
;; :149).
;;
;; A Path is a list of steps from a match root down into the subtree at that
;; root.  A step is one of 'fun, 'arg (into the two children of an app) and
;; 'body (into the body of a lam).  Paths run root-first: '(body arg) means
;; "the argument of the application in the body of this lambda".  These are
;; stitch's zippers (ZNode::Func / ::Arg / ::Body), minus the interning.
;;
;; An Arg is the result of extracting the subtree at a Path as an abstraction
;; argument; see `extract-arg` below.
;;
;; PARITY
;;
;; This module is written to agree with real stitch node for node, so that
;; mini-stitch can be differentially tested against it.  Comments citing
;; `file.rs:NN` refer to the stitch submodule under stitch/src, or to the
;; pinned `lambdas` crate (rev 2c9bfd0) where marked.
;;
;; Known deviation: stitch's parser accepts *fused-lambda tags* -- `lam_1`,
;; `$0_1` (lambdas parse_expr.rs:145-206) -- which make `$0_1` and `$0_2`
;; distinct nodes even though the tags are inert unless --fused-lambda-tags is
;; passed.  Following the design note (map section 7, "drop tags"), Node has no
;; tag field; the parser raises a clear error instead of silently conflating
;; tagged variables.  Three corpora in stitch/data/basic use tags (simple3,
;; simple4, simple5) and are therefore out of reach until tags are added back.
;; ---------------------------------------------------------------------------

(require "ast.rkt"
         data/gvector
         racket/set)

(provide
 ;; the language and the cost model, passed straight through
 (all-from-out "ast.rkt")
 node-children
 ;; corpus
 corpus?
 make-corpus corpus-node corpus-size corpus-roots corpus-span
 in-corpus-span add-node!
 parse-program! add-program! seal-corpus! corpus-from-programs
 ;; printing
 expr->string
 ;; analyses
 cost free-vars free-ivars? num-paths programs-with expands-to
 ;; argument extraction
 (struct-out arg)
 extract-arg follow-path)

(module+ test (require rackunit))

;; ---------------------------------------------------------------------------
;; Nodes
;; ---------------------------------------------------------------------------
;;
;; The node structs and the cost constants come from ast.rkt.  They are
;; transparent, so `equal?` and `equal-hash-code` on them are structural -- which
;; is what makes the intern table below work.

;; node-children : Node -> (Listof Idx)
;; The Idxs this node points at, left to right.
(define (node-children n)
  (cond [(app? n) (list (app-fun n) (app-arg n))]
        [(lam? n) (list (lam-body n))]
        [else '()]))

(module+ test
  (test-case "node-children"
    (check-equal? (node-children (app 3 7)) '(3 7))
    (check-equal? (node-children (lam 5)) '(5))
    (check-equal? (node-children (prim 'cons)) '())
    (check-equal? (node-children (var 0)) '())))

;; ---------------------------------------------------------------------------
;; The corpus arena
;; ---------------------------------------------------------------------------

;; A Corpus is a (corpus GVector Hash (Listof Idx) Natural Hash Hash Hash Hash
;;                       (U #f Vector) (U #f Vector))
;; where
;;   nodes     is the arena, indexed by Idx
;;   intern    maps Node -> Idx, giving hash-consing
;;   roots     lists the program roots in program order (may repeat, if two
;;             programs in the corpus are identical)
;;   sealed-span is the arena length just after parsing, or #f while unsealed;
;;             read it through `corpus-span`, which insists on a sealed corpus
;;   *-table   are the analysis memo tables, keyed by Idx (or by (loc . path)
;;             for arg-table).  They are hash tables rather than vectors
;;             because the arena grows after parsing.
;;   num-paths-table / programs-with-table are whole-span computations, filled
;;             in once by seal-corpus!.
(struct corpus (nodes
                intern
                [roots #:mutable]
                [sealed-span #:mutable]
                cost-table
                free-vars-table
                free-ivars-table
                arg-table
                [num-paths-table #:mutable]
                [programs-with-table #:mutable]))

;; make-corpus : -> Corpus
;; A fresh empty corpus.
(define (make-corpus)
  (corpus (make-gvector)
          (make-hash)
          '()
          #f
          (make-hasheqv)
          (make-hasheqv)
          (make-hasheqv)
          (make-hash)
          #f
          #f))

;; corpus-node : Corpus Idx -> Node
;; The node stored at this index.
(define (corpus-node c idx)
  (gvector-ref (corpus-nodes c) idx))

;; corpus-size : Corpus -> Natural
;; How many nodes the arena currently holds (span plus any shifted copies).
(define (corpus-size c)
  (gvector-count (corpus-nodes c)))

;; in-corpus-span : Corpus -> Sequence
;; All Idxs that came from parsing programs, in child-first (bottom-up) order.
;; Every analysis defined only over the span iterates this.
(define (in-corpus-span c)
  (in-range (corpus-span c)))

;; corpus-span : Corpus -> Natural
;; The number of nodes the arena held when the corpus was sealed, i.e. one past
;; the largest Idx that names a real corpus subtree.  Everything at or above it
;; is a shifted copy manufactured by argument extraction.
(define (corpus-span c)
  (or (corpus-sealed-span c)
      (error 'corpus-span "corpus has not been sealed yet; call seal-corpus!")))

;; add-node! : Corpus Node -> Idx
;; Add a node to the arena, or return the Idx of an existing node equal to it.
;; The caller must already have added the children, which is what keeps the
;; arena child-first.  Mirrors `ExprSet::add` (lambdas expr.rs:135-165).
(define (add-node! c n)
  (hash-ref! (corpus-intern c) n
             (lambda ()
               (define idx (gvector-count (corpus-nodes c)))
               (gvector-add! (corpus-nodes c) n)
               idx)))

(module+ test
  (test-case "hash-consing in the arena"
    ;; Hash-consing: equal nodes are the same Idx, and children really do come
    ;; first.
    (define c (make-corpus))
    (define a (add-node! c (prim 'a)))
    (define aa (add-node! c (app a a)))
    (check-equal? a 0)
    (check-equal? aa 1)
    (check-equal? (add-node! c (prim 'a)) a)
    (check-equal? (add-node! c (app a a)) aa)
    (check-equal? (corpus-size c) 2)
    (check-true (< (app-fun (corpus-node c aa)) aa))))

;; ---------------------------------------------------------------------------
;; Parsing
;; ---------------------------------------------------------------------------
;;
;; The surface syntax is stitch's, which is DreamCoder's:
;;
;;   (a b c)          curried application, i.e. ((a b) c)
;;   (lam e)          lambda; `lambda` is accepted as a synonym and normalized
;;   $3               de Bruijn variable
;;   #1               abstraction variable
;;   anything else    a primitive, including numerals and names like `is_nil`
;;
;; Two things are worth pointing out, because they surprise people reading the
;; corpora in stitch/data:
;;
;;   * `app` is NOT a keyword.  Several corpora are written in the fully
;;     explicit style `(app (app cons x) y)`, but stitch's parser has no case
;;     for it (lambdas parse_expr.rs:189-207), so that text denotes the
;;     primitive named `app` applied -- curried -- to two arguments.  We
;;     reproduce that, deliberately: it is what the real system compresses.
;;   * a top-level juxtaposition needs no parentheses: "foo bar baz" parses as
;;     (foo bar baz), and "(f x) (f x)" as an application of one to the other.
;;
;; stitch's parser scans right to left; ours scans left to right.  The
;; resulting trees agree, since both build a left-associated spine out of the
;; items of a parenthesized group.

;; A Token is one of 'lparen, 'rparen, or a String (a maximal run of
;; characters that are neither whitespace nor a parenthesis).

;; tokenize : String -> (Listof Token)
;; Split program text into parentheses and atoms.
(define (tokenize s)
  (let loop ([i 0] [acc '()])
    (cond
      [(= i (string-length s)) (reverse acc)]
      [else
       (define ch (string-ref s i))
       (cond
         [(char-whitespace? ch) (loop (add1 i) acc)]
         [(char=? ch #\() (loop (add1 i) (cons 'lparen acc))]
         [(char=? ch #\)) (loop (add1 i) (cons 'rparen acc))]
         [else
          ;; scan to the end of the atom
          (define end
            (let scan ([j i])
              (cond [(= j (string-length s)) j]
                    [(let ([d (string-ref s j)])
                       (or (char-whitespace? d) (char=? d #\() (char=? d #\))))
                     j]
                    [else (scan (add1 j))])))
          (loop end (cons (substring s i end) acc))])])))

(module+ test
  (test-case "tokenize"
    (check-equal? (tokenize "(a b)") '(lparen "a" "b" rparen))
    (check-equal? (tokenize "  $0 #1  ") '("$0" "#1"))
    ;; atoms end at a parenthesis even with no space, as in stitch's scanner
    (check-equal? (tokenize "(a(b))") '(lparen "a" lparen "b" rparen rparen))))

;; An Item is either an Idx (a parsed subterm) or the symbol 'lam-keyword.

;; atom->item : Corpus String -> Item
;; Turn one atom into a corpus node, or report that it is the `lam` keyword.
;; Raises an error on the tag syntax we do not model, and on a malformed
;; variable such as "$x", exactly where stitch's parser would fail.
(define (atom->item c a)
  (cond
    [(or (string=? a "lam") (string=? a "lambda")) 'lam-keyword]
    [(or (string-prefix? a "lam_") (string-prefix? a "lambda_"))
     (error 'parse-program! "fused-lambda tags are not supported: ~a" a)]
    [(string-prefix? a "$")
     (define rest (substring a 1))
     (cond
       [(regexp-match? #rx"^[0-9]+$" rest)
        (add-node! c (var (string->number rest)))]
       [(regexp-match? #rx"^[0-9]+_[0-9]+$" rest)
        (error 'parse-program! "variable tags are not supported: ~a" a)]
       [else (error 'parse-program! "malformed de Bruijn variable: ~a" a)])]
    [(string-prefix? a "#")
     (define rest (substring a 1))
     (unless (regexp-match? #rx"^[0-9]+$" rest)
       (error 'parse-program! "malformed abstraction variable: ~a" a))
     (add-node! c (ivar (string->number rest)))]
    [else (add-node! c (prim (string->symbol a)))]))

;; combine-items : Corpus (Listof Item) -> Idx
;; Fold the items of one juxtaposition group into a single node.  A group
;; headed by `lam` must have exactly one further item; any other group becomes
;; a left-associated chain of applications.  Both restrictions are stitch's
;; (lambdas parse_expr.rs:168-171 for lam, :103-108 for the chain).
(define (combine-items c items)
  (cond
    [(null? items) (error 'parse-program! "empty group ()")]
    [(eq? (car items) 'lam-keyword)
     (unless (and (pair? (cdr items)) (null? (cddr items)))
       (error 'parse-program!
              "`lam` must be applied to exactly one argument, as in (lam (f x))"))
     (add-node! c (lam (cadr items)))]
    [(memq 'lam-keyword items)
     (error 'parse-program!
            "`lam` must be the head of its group, as in (lam (f x))")]
    [else
     (for/fold ([f (car items)]) ([x (in-list (cdr items))])
       (add-node! c (app f x)))]))

;; parse-group : Corpus (Listof Token) Boolean -> (values Idx (Listof Token))
;; Parse one juxtaposition group and return it together with the tokens left
;; over.  `in-parens?` says whether a closing paren is expected to end us.
(define (parse-group c toks in-parens?)
  (let loop ([toks toks] [items '()])
    (cond
      [(null? toks)
       (when in-parens? (error 'parse-program! "mismatched parentheses"))
       (values (combine-items c (reverse items)) '())]
      [(eq? (car toks) 'rparen)
       (unless in-parens? (error 'parse-program! "unexpected `)`"))
       (values (combine-items c (reverse items)) (cdr toks))]
      [(eq? (car toks) 'lparen)
       (define-values (idx rest) (parse-group c (cdr toks) #t))
       (loop rest (cons idx items))]
      [else
       (loop (cdr toks) (cons (atom->item c (car toks)) items))])))

;; parse-program! : Corpus String -> Idx
;; Parse one program into the corpus, interning every subtree, and return the
;; Idx of its root.  Does not register the program as a root; see add-program!.
(define (parse-program! c s)
  (define toks (tokenize s))
  (when (null? toks) (error 'parse-program! "empty program text"))
  (define-values (idx rest) (parse-group c toks #f))
  (unless (null? rest) (error 'parse-program! "mismatched parentheses in: ~a" s))
  idx)

;; add-program! : Corpus String -> Idx
;; Parse a program and register its root.  Program indices (what
;; `programs-with` reports) are positions in the order of these calls.
(define (add-program! c s)
  (define idx (parse-program! c s))
  (set-corpus-roots! c (append (corpus-roots c) (list idx)))
  idx)

;; seal-corpus! : Corpus -> Void
;; Freeze the span at the current arena length and precompute the two
;; whole-corpus analyses.  Call once, after all programs are added and before
;; any argument extraction (which appends shifted copies past the span).
(define (seal-corpus! c)
  (when (corpus-sealed-span c) (error 'seal-corpus! "corpus is already sealed"))
  (set-corpus-sealed-span! c (corpus-size c))
  (set-corpus-num-paths-table! c (compute-num-paths c))
  (set-corpus-programs-with-table! c (compute-programs-with c)))

;; corpus-from-programs : (Listof String) -> Corpus
;; Build and seal a corpus from program texts.  This is the normal entry point.
(define (corpus-from-programs programs)
  (define c (make-corpus))
  (for ([p (in-list programs)]) (add-program! c p))
  (seal-corpus! c)
  c)

;; ---------------------------------------------------------------------------
;; Printing
;; ---------------------------------------------------------------------------

;; expr->string : Corpus Idx -> String
;; Print the subtree at idx in stitch's format: application spines flattened,
;; lambdas as (lam ...), variables as $i, abstraction variables as #i.  Mirrors
;; `impl Display for Expr` (lambdas parse_expr.rs:40-70), including the trick
;; that an application on the left of an application needs no parentheses --
;; which is what turns ((a b) c) back into "(a b c)".
(define (expr->string c idx)
  (define out (open-output-string))
  ;; emit : Idx Boolean -> Void ; left-of-app? suppresses our own parentheses
  (define (emit idx left-of-app?)
    (define n (corpus-node c idx))
    (cond
      [(var? n) (fprintf out "$~a" (var-i n))]
      [(ivar? n) (fprintf out "#~a" (ivar-i n))]
      [(prim? n) (fprintf out "~a" (prim-name n))]
      [(app? n)
       (unless left-of-app? (write-string "(" out))
       (emit (app-fun n) #t)
       (write-string " " out)
       (emit (app-arg n) #f)
       (unless left-of-app? (write-string ")" out))]
      [(lam? n)
       (write-string "(lam " out)
       (emit (lam-body n) #f)
       (write-string ")" out)]))
  (emit idx #f)
  (get-output-string out))

(module+ test
  (test-case "printing round-trips"
    ;; round-trip : String -> String
    (define (round-trip s)
      (define c (make-corpus))
      (expr->string c (parse-program! c s)))

    ;; strings lifted from stitch/data/basic
    (check-equal? (round-trip "(a a a)") "(a a a)")                   ; simple1
    (check-equal? (round-trip "(a (lam (a a)))") "(a (lam (a a)))")   ; simple2
    (check-equal? (round-trip "(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))")
                  "(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))")    ; ctx_thread_1
    (check-equal?
     (round-trip
      "(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))")
     "(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))")
    (check-equal?
     (round-trip
      (string-append
       "(app Y (lam (lam (app (app (app if (app is_nil $0)) nil)"
       " (app (app cons (app (app + (app car $0)) (app car $0)))"
       " (app $1 (app cdr $0)))))))"))
     (string-append
      "(app Y (lam (lam (app (app (app if (app is_nil $0)) nil)"
      " (app (app cons (app (app + (app car $0)) (app car $0)))"
      " (app $1 (app cdr $0)))))))"))

    ;; normalizations the printer performs
    (check-equal? (round-trip "((foo bar) baz)") "(foo bar baz)")
    (check-equal? (round-trip "foo bar baz") "(foo bar baz)")
    (check-equal? (round-trip "(lambda (+ $0 b))") "(lam (+ $0 b))")
    (check-equal? (round-trip "(foo (bar baz))") "(foo (bar baz))")
    (check-equal? (round-trip "3") "3")
    (check-equal? (round-trip "(lam (+ #0 b))") "(lam (+ #0 b))")
    ;; an application in argument position keeps its parentheses
    (check-equal? (round-trip "(f (g x) (h y))") "(f (g x) (h y))")))

(module+ test
  (test-case "hash-consing across programs"
    ;; Hash-consing across programs: the shared subtree (g x) is one node, and
    ;; the two occurrences within one program are the same Idx too.
    (define c (corpus-from-programs (list "(f (g x) (g x))" "(h (g x))")))
    (define p0 (car (corpus-roots c)))
    (define spine (app-fun (corpus-node c p0)))          ; (f (g x))
    (check-equal? (app-arg (corpus-node c spine))
                  (app-arg (corpus-node c p0)))
    (define p1 (cadr (corpus-roots c)))
    (check-equal? (app-arg (corpus-node c p1))
                  (app-arg (corpus-node c p0)))
    ;; parsing the same text twice yields the same root
    (check-equal? (parse-program! c "(g x)") (app-arg (corpus-node c p0)))))

(module+ test
  (test-case "parse errors"
    ;; Parse errors we inherit from stitch, plus the tag deviation.
    (check-exn #rx"exactly one argument" (lambda () (parse-program! (make-corpus) "(lam a b)")))
    (check-exn #rx"head of its group" (lambda () (parse-program! (make-corpus) "(f lam b)")))
    (check-exn #rx"mismatched" (lambda () (parse-program! (make-corpus) "(f b")))
    (check-exn #rx"fused-lambda tags" (lambda () (parse-program! (make-corpus) "(lam_1 a)")))
    (check-exn #rx"variable tags" (lambda () (parse-program! (make-corpus) "(f $0_1)")))
    (check-exn #rx"malformed de Bruijn" (lambda () (parse-program! (make-corpus) "(f $x)")))))

;; ---------------------------------------------------------------------------
;; Analyses
;; ---------------------------------------------------------------------------
;;
;; stitch computes these once, bottom-up, into vectors indexed by Idx (the
;; `AnalyzedExpr` machinery, lambdas analysis.rs).  We memoize into hash tables
;; instead, because our arena keeps growing: argument extraction adds shifted
;; copies of subtrees after parsing, and those need cost/free-vars too.

;; cost : Corpus Idx -> Natural
;; The cost model's size of the subtree at idx: 1 per app and lam, 100 per
;; leaf.  Note this is the cost of *one* occurrence; multiplicity comes in
;; separately, via num-paths.  Mirrors `ExprCost` / `cost_rec` (lambdas
;; expr.rs:272-284).
(define (cost c idx)
  (hash-ref! (corpus-cost-table c) idx
             (lambda ()
               (define n (corpus-node c idx))
               (cond
                 [(var? n) COST-VAR]
                 ;; Ivars in this arena are capture sentinels inside shifted
                 ;; argument copies, and nothing ever prices a sentinel-bearing
                 ;; copy: the multiuse bonus prices the unshifted argument, and
                 ;; body sizes are accumulated incrementally (with abstraction
                 ;; variables at 0) rather than through this function.
                 ;; (Sentinel-free shifted copies may be priced -- one test
                 ;; does -- and never reach this branch.)  Raising keeps the
                 ;; function total and the claim checked.
                 [(ivar? n) (error 'cost "asked to price an abstraction variable (Idx ~a); nothing in the pipeline should ever do this" idx)]
                 [(prim? n) COST-PRIM]
                 [(app? n) (+ COST-APP
                              (cost c (app-fun n))
                              (cost c (app-arg n)))]
                 [(lam? n) (+ COST-LAM (cost c (lam-body n)))]))))

(module+ test
  (test-case "cost"
    ;; (a a a) = ((a a) a): two apps and three leaf occurrences.
    (define c (corpus-from-programs (list "(a a a)" "(b b b)")))
    (check-equal? (cost c (car (corpus-roots c))) (+ 2 300))
    ;; real stitch reports original_cost = 604 for data/basic/simple1.json
    (check-equal? (for/sum ([r (in-list (corpus-roots c))]) (cost c r)) 604)
    ;; (a (lam (a a))) = one app, a lam, another app, three leaves
    (define c2 (corpus-from-programs (list "(a (lam (a a)))")))
    (check-equal? (cost c2 (car (corpus-roots c2))) (+ 1 1 1 300))))

;; free-vars : Corpus Idx -> (Setof Natural)
;; The de Bruijn indices that escape the subtree at idx, expressed relative to
;; idx: `i` is in the set when some $i inside idx refers to a binder above idx.
;; Crossing a lam drops 0 and decrements the rest.  Abstraction variables are
;; not de Bruijn variables and contribute nothing.  Mirrors `FreeVarAnalysis`
;; (lambdas analysis.rs:122-146).
(define (free-vars c idx)
  (hash-ref! (corpus-free-vars-table c) idx
             (lambda ()
               (define n (corpus-node c idx))
               (cond
                 [(var? n) (seteqv (var-i n))]
                 [(ivar? n) (seteqv)]
                 [(prim? n) (seteqv)]
                 [(app? n) (set-union (free-vars c (app-fun n))
                                      (free-vars c (app-arg n)))]
                 [(lam? n)
                  (for/seteqv ([i (in-set (free-vars c (lam-body n)))]
                               #:when (> i 0))
                    (sub1 i))]))))

;; free-ivars? : Corpus Idx -> Boolean
;; Does any abstraction variable #i occur in the subtree at idx?  For an
;; extracted argument this is exactly "does it contain a sentinel", which is
;; what makes a match location unusable.  Mirrors `IVarAnalysis` (lambdas
;; analysis.rs:149-170) as used by `has_free_ivars` (pattern_args.rs:108-121).
(define (free-ivars? c idx)
  (hash-ref! (corpus-free-ivars-table c) idx
             (lambda ()
               (define n (corpus-node c idx))
               (cond
                 [(ivar? n) #t]
                 [(app? n) (or (free-ivars? c (app-fun n))
                               (free-ivars? c (app-arg n)))]
                 [(lam? n) (free-ivars? c (lam-body n))]
                 [else #f]))))

(module+ test
  (test-case "free-vars and free-ivars?"
    ;; the example from the lambdas test suite: free vars {0}, ivars {0}
    (define c (make-corpus))
    (define e (parse-program! c "(lam (lam ($1 #0 $2)))"))
    (check-equal? (free-vars c e) (seteqv 0))
    (check-true (free-ivars? c e))
    ;; a closed term
    (define closed (parse-program! c "(lam (f $0))"))
    (check-equal? (free-vars c closed) (seteqv))
    (check-false (free-ivars? c closed))
    ;; inside that lambda, $0 is free relative to the application
    (check-equal? (free-vars c (lam-body (corpus-node c closed))) (seteqv 0))))

;; compute-num-paths : Corpus -> (Vectorof Natural)
;; num-paths for every Idx in the span, in one downward sweep.
;;
;; stitch does this by literally walking every path from every root and
;; incrementing a counter per node visited (`num_paths_to_node`,
;; util.rs:106-135).  We get the same numbers in linear time by exploiting the
;; child-first invariant: a node's parents all have larger Idxs, so if we visit
;; Idxs in decreasing order every node's count is final by the time we push it
;; down to its children.
(define (compute-num-paths c)
  (define span (corpus-span c))
  (define counts (make-vector span 0))
  ;; each program contributes one path to its own root; duplicate programs
  ;; contribute twice, matching stitch's per-root loop
  (for ([r (in-list (corpus-roots c))])
    (vector-set! counts r (add1 (vector-ref counts r))))
  (for ([idx (in-range (sub1 span) -1 -1)])
    (define k (vector-ref counts idx))
    (unless (zero? k)
      (for ([ch (in-list (node-children (corpus-node c idx)))])
        (vector-set! counts ch (+ k (vector-ref counts ch))))))
  counts)

;; num-paths : Corpus Idx -> Natural
;; How many times this unique subtree occurs across the whole corpus, counting
;; the sharing that hash-consing folded away.  Defined only on the span.  This
;; is how multiplicity re-enters utility and the upper bound after the search
;; has collapsed all occurrences of a subtree into one Idx.
(define (num-paths c idx)
  (define t (or (corpus-num-paths-table c)
                (error 'num-paths "corpus has not been sealed yet")))
  (unless (< idx (vector-length t))
    (error 'num-paths "~a is outside the corpus span" idx))
  (vector-ref t idx))

;; compute-programs-with : Corpus -> (Vectorof (Setof Natural))
;; Same downward sweep, carrying sets of program indices instead of counts.
;; This is stitch's `associate_tasks` (egraphs.rs:23-47) under the default
;; task labelling, where each program is its own task (compression.rs:1813).
(define (compute-programs-with c)
  (define span (corpus-span c))
  (define sets (make-vector span (seteqv)))
  (for ([r (in-list (corpus-roots c))] [i (in-naturals)])
    (vector-set! sets r (set-add (vector-ref sets r) i)))
  (for ([idx (in-range (sub1 span) -1 -1)])
    (define s (vector-ref sets idx))
    (unless (set-empty? s)
      (for ([ch (in-list (node-children (corpus-node c idx)))])
        (vector-set! sets ch (set-union s (vector-ref sets ch))))))
  sets)

;; programs-with : Corpus Idx -> (Setof Natural)
;; The indices of the programs whose tree contains this subtree.  The search
;; uses its size for single-task pruning: an abstraction that appears in only
;; one program is rejected, which is stitch's default behaviour
;; (compression.rs:1150-1155).
(define (programs-with c idx)
  (define t (or (corpus-programs-with-table c)
                (error 'programs-with "corpus has not been sealed yet")))
  (unless (< idx (vector-length t))
    (error 'programs-with "~a is outside the corpus span" idx))
  (vector-ref t idx))

(module+ test
  (test-case "num-paths and programs-with by hand"
    ;; Corpus: "(a a a)" and "(b b b)".  Worked out by hand:
    ;;   node       num-paths   programs-with
    ;;   a              3           {0}
    ;;   (a a)          1           {0}
    ;;   (a a a)        1           {0}
    ;;   ... likewise for b in program 1
    (define c (corpus-from-programs (list "(a a a)" "(b b b)")))
    (define r0 (car (corpus-roots c)))
    (define aa (app-fun (corpus-node c r0)))
    (define a (app-fun (corpus-node c aa)))
    (check-equal? (num-paths c a) 3)
    (check-equal? (num-paths c aa) 1)
    (check-equal? (num-paths c r0) 1)
    (check-equal? (programs-with c a) (seteqv 0))
    (check-equal? (programs-with c (cadr (corpus-roots c))) (seteqv 1))))

(module+ test
  (test-case "sharing across programs"
    ;; Sharing across programs, and a subtree used twice in one program.
    ;;   "(f (g x) (g x))"  contributes 2 occurrences of (g x)
    ;;   "(h (g x))"        contributes 1
    (define c (corpus-from-programs (list "(f (g x) (g x))" "(h (g x))")))
    (define r0 (car (corpus-roots c)))
    (define gx (app-arg (corpus-node c r0)))
    (check-equal? (expr->string c gx) "(g x)")
    (check-equal? (num-paths c gx) 3)
    (check-equal? (programs-with c gx) (seteqv 0 1))
    ;; g itself occurs once per occurrence of (g x)
    (check-equal? (num-paths c (app-fun (corpus-node c gx))) 3)
    ;; f occurs once, only in program 0
    (define f (app-fun (corpus-node c (app-fun (corpus-node c r0)))))
    (check-equal? (expr->string c f) "f")
    (check-equal? (num-paths c f) 1)
    (check-equal? (programs-with c f) (seteqv 0))))

(module+ test
  (test-case "a duplicated program"
    ;; A duplicated program: stitch loops over roots, so the shared root counts
    ;; twice, but it belongs to two distinct programs.
    (define c (corpus-from-programs (list "(f x)" "(f x)")))
    (define r (car (corpus-roots c)))
    (check-equal? (cadr (corpus-roots c)) r)
    (check-equal? (num-paths c r) 2)
    (check-equal? (programs-with c r) (seteqv 0 1))))

;; expands-to : Corpus Idx -> ExpandsTo
;; The root constructor of this subtree: what a hole must expand into to match
;; here.  App and lam collapse to symbols because the children become fresh
;; holes; leaves keep their payload, because the search needs the variable
;; index (to reject variables that would be free in the abstraction body) and
;; the primitive name (to price it).  Mirrors `expands_to_of_node`
;; (expansion.rs:149-160).
(define (expands-to c idx)
  (define n (corpus-node c idx))
  (cond [(app? n) 'app]
        [(lam? n) 'lam]
        [else n]))            ; (var i), (prim s) or (ivar i) -- already erased

(module+ test
  (test-case "expands-to"
    (define c (make-corpus))
    (check-equal? (expands-to c (parse-program! c "(f x)")) 'app)
    (check-equal? (expands-to c (parse-program! c "(lam x)")) 'lam)
    (check-equal? (expands-to c (parse-program! c "$2")) (var 2))
    (check-equal? (expands-to c (parse-program! c "cons")) (prim 'cons))
    (check-equal? (expands-to c (parse-program! c "#1")) (ivar 1))))

;; ---------------------------------------------------------------------------
;; Argument extraction
;; ---------------------------------------------------------------------------
;;
;; When a partial abstraction has a hole at some Path below a match location,
;; the subtree sitting at that position is what the abstraction would receive
;; as an argument.  Lifting it out of the body changes its de Bruijn indices,
;; because the lambdas on the Path are *inside* the body but *outside* the
;; argument's original position.
;;
;; An Arg records both views of the subtree plus the bookkeeping:
;;
;;   unshifted   the original corpus subtree.  This is what the rewriter walks
;;               (nested matches inside arguments still get rewritten), and
;;               what determines expands-to.
;;   shifted     the same subtree as seen from the match root.  Variables that
;;               referred to a lambda on the Path have become sentinel ivars;
;;               variables that referred to something above the match root have
;;               been downshifted.  Two holes see "the same argument" exactly
;;               when their shifted Idxs are equal -- so hash-consing turns the
;;               abstraction-variable equality constraint into integer =.  This
;;               is stitch's `shifted_id` pointer equality.
;;   shift       the (non-positive) total downshift actually applied; the
;;               rewriter replays it as a shift rule (rewriting.rs:50-59).
;;   captures?   whether any sentinel appears, i.e. whether this argument would
;;               have to capture a binder that lives inside the abstraction
;;               body.  Such an argument cannot be passed in, so the location is
;;               matched but never used: its utility is forced to zero
;;               (`has_free_ivars`, pattern_args.rs:108-121).  This is stitch's
;;               stand-in for the paper's &i indices.
;;   expands-to  the head constructor the search groups locations by.
;;
;; --- The sentinel representation, and why one pass suffices ----------------
;;
;; stitch never extracts downward.  It builds arguments bottom-up: a zipper
;; from node n to a descendant is "bubbled" up to n's parent, and when that
;; parent is a lam the argument is rewritten (`get_zippers`,
;; compression.rs:1297-1332).  Crossing one lambda does two things, in order:
;;
;;   1. every variable referring to *that* lambda -- i.e. every free $0 of the
;;      argument as it currently stands -- becomes the sentinel #k, where k is
;;      the number of Body steps below the lambda being crossed
;;      (`insert_arg_ivars`, egraphs.rs:51-73, whose Var case at egraphs.rs:61
;;      is `if i == init_depth { add(IVar(set_to)) }`; called from
;;      compression.rs:1326 with set_to = depth_root_to_arg - 1; the comment there says "point past all
;;      lambdas except the newly added one");
;;   2. all remaining free variables are downshifted by one (`shift(-1, 0, ..)`,
;;      lambdas expr.rs:476-498).
;;
;; Fix a match root and a Path with m lambdas on it: L_1 (outermost, nearest
;; the root) through L_m (innermost, nearest the argument).  Let F be the
;; free-variable set of the argument subtree as it sits in the corpus.
;;
;; Because *every* binder between the argument and the match root lies on the
;; Path, the binders enclosing the argument are exactly L_m, L_{m-1}, ..., L_1
;; and then whatever encloses the match root.  So a free $d of the argument
;; refers to L_{m-d} when d < m, and to something above the match root when
;; d >= m.
;;
;; Bubbling visits the lambdas innermost first.  Claim: just before step d
;; (d = 0 .. m-1, the step that crosses L_{m-d}) the argument's free-variable
;; set is {f - d | f in F, f >= d}.  Induction: true at d = 0; step d turns the
;; f - d = 0 members into sentinels and decrements the rest, giving
;; {f - d - 1 | f in F, f > d} = {f - (d+1) | f in F, f >= d+1}.  Hence
;;
;;   * step d replaces exactly the original $d occurrences, and it uses
;;     set_to = d, because the zipper from L_{m-d} down to the argument has
;;     d + 1 Body steps and set_to = (d+1) - 1.  So the sentinel index counts
;;     crossed lambdas from the *inside*: #0 is the innermost crossed lambda.
;;   * an original free $d with d >= m survives all m steps, losing one per
;;     step, ending as $(d - m).
;;   * a variable bound by a lambda *inside* the argument is never free, so no
;;     step ever touches it.
;;   * sentinels, once introduced, are ignored by both insert_arg_ivars and
;;     shift, so they never move again.
;;
;; That is exactly the single downward pass `shift-arg` implements: relative to
;; the argument's own root, $d becomes #d when d < m and $(d-m) otherwise.
;;
;; --- Why `shift` is not simply -m -----------------------------------------
;;
;; The downshift is only performed, and only counted, at a lambda where the
;; argument still has free variables: the whole block at
;; compression.rs:1314-1330 sits under `if !free_vars(shifted_id).is_empty()`,
;; and `arg.shift -= 1` (compression.rs:1329) lives inside it.  By the claim above, at step d the argument has a free variable iff
;; max(F) >= d, so the number of counted downshifts is
;; |{d in [0,m) : max(F) >= d}| = min(m, max(F) + 1).  Therefore
;;
;;   shift = 0                      when F is empty
;;   shift = -min(m, max(F) + 1)    otherwise.
;;
;; The sentinel-only case really does stop early: extracting $0 from under two
;; lambdas yields shifted #0 and shift = -1, not -2, because after the first
;; crossing the argument is closed.
;;
;; --- What expands-to does with a sentinel ---------------------------------
;;
;; Nothing.  `expands_to` is computed once, from the *unshifted* node, when the
;; empty zipper is seeded (compression.rs:1253-1254), and every bubbling step
;; clones the Arg without touching that field.  So an argument that is $0
;; pointing at a crossed lambda still reports Var(0), not IVar(_), and the hole
;; can indeed be expanded syntactically -- into $0, which is well formed
;; because the pattern's own lam binds it (the free-variable prune at
;; compression.rs:1017 only fires when the index reaches past the Body steps of
;; the hole's zipper).  Sentinels are visible only through
;; `shifted_id`, where they act as ordinary ivars for equality, and through
;; `has_free_ivars`, which zeroes the location's utility.  Hence the accessor
;; below reads the unshifted node, and `captures?` is the separate flag.

;; An Arg is a (arg Idx Idx Integer Boolean ExpandsTo).
(struct arg (unshifted shifted shift captures? expands-to) #:transparent)

;; follow-path : Corpus Idx Path -> (values Idx Natural)
;; Walk from idx down the path, returning the subtree reached and the number of
;; lambdas crossed on the way (the count of 'body steps).
(define (follow-path c idx path)
  (let loop ([idx idx] [path path] [lams 0])
    (cond
      [(null? path) (values idx lams)]
      [else
       (define n (corpus-node c idx))
       (case (car path)
         [(fun) (unless (app? n) (error 'follow-path "'fun step into ~a" n))
                (loop (app-fun n) (cdr path) lams)]
         [(arg) (unless (app? n) (error 'follow-path "'arg step into ~a" n))
                (loop (app-arg n) (cdr path) lams)]
         [(body) (unless (lam? n) (error 'follow-path "'body step into ~a" n))
                 (loop (lam-body n) (cdr path) (add1 lams))]
         [else (error 'follow-path "bad path step: ~a" (car path))])])))

(module+ test
  (test-case "follow-path"
    (define c (make-corpus))
    (define e (parse-program! c "(lam (f (g x)))"))
    (define-values (gx lams) (follow-path c e '(body arg)))
    (check-equal? (expr->string c gx) "(g x)")
    (check-equal? lams 1)
    (define-values (root no-lams) (follow-path c e '()))
    (check-equal? root e)
    (check-equal? no-lams 0)
    (check-exn #rx"'fun step" (lambda () (follow-path c e '(fun))))))

;; shift-arg : Corpus Idx Natural -> Idx
;; Rewrite the subtree at idx as it would be seen from a match root with `m`
;; lambdas between the root and idx: free $d becomes the sentinel #d when
;; d < m, and $(d-m) otherwise; variables bound inside the subtree are left
;; alone.  See the derivation above for why this single pass equals stitch's
;; per-lambda bubbling.
(define (shift-arg c idx m)
  ;; walk : Idx Natural -> Idx
  ;; `depth` is the number of lambdas of the argument itself that enclose this
  ;; subtree, so a variable $i here is bound inside the argument iff i < depth.
  (define (walk idx depth)
    (cond
      ;; Nothing in this subtree escapes past the argument's own binders, so it
      ;; is unchanged.  stitch short-circuits the same way, on the same test
      ;; (`max(free_vars) < init_depth`, lambdas expr.rs:478-482).
      [(for/and ([f (in-set (free-vars c idx))]) (< f depth)) idx]
      [else
       (define n (corpus-node c idx))
       (cond
         [(var? n)
          (define i (var-i n))
          (define d (- i depth))       ; index relative to the argument's root
          (cond
            [(< i depth) idx]                          ; bound inside the arg
            [(< d m) (add-node! c (ivar d))]           ; points at crossed lam
            [else (add-node! c (var (- i m)))])]        ; points above the root
         [(ivar? n) idx]
         [(prim? n) idx]
         [(app? n) (add-node! c (app (walk (app-fun n) depth)
                                     (walk (app-arg n) depth)))]
         [(lam? n) (add-node! c (lam (walk (lam-body n) (add1 depth))))])]))
  (if (zero? m) idx (walk idx 0)))

;; arg-shift-amount : Corpus Idx Natural -> Integer
;; The `shift` stitch would record for this argument under `m` crossed
;; lambdas: zero if the subtree is closed, otherwise -min(m, max(free)+1).
(define (arg-shift-amount c idx m)
  (define fv (free-vars c idx))
  (if (set-empty? fv)
      0
      (- (min m (add1 (apply max (set->list fv)))))))

;; extract-arg : Corpus Idx Path -> Arg
;; The argument a hole at `path` below match location `loc` would capture.
;; Memoized on (loc, path): the search asks this repeatedly, once per location
;; per hole, and the shifting work is proportional to the subtree size.
;; (stitch precomputes the whole (zipper, node) table up front in get_zippers;
;; we compute the same entries on demand.)
(define (extract-arg c loc path)
  (hash-ref!
   (corpus-arg-table c) (cons loc path)
   (lambda ()
     (define-values (unshifted m) (follow-path c loc path))
     (define shifted (shift-arg c unshifted m))
     (arg unshifted
          shifted
          (arg-shift-amount c unshifted m)
          (free-ivars? c shifted)
          (expands-to c unshifted)))))

(module+ test
  (test-case "extract-arg with no lambdas crossed"
    ;; No lambdas crossed: the argument is the subtree, untouched.
    (define c (corpus-from-programs (list "(f (g x))" "(h (g x))")))
    (define a (extract-arg c (car (corpus-roots c)) '(arg)))
    (check-equal? (expr->string c (arg-unshifted a)) "(g x)")
    (check-equal? (arg-shifted a) (arg-unshifted a))
    (check-equal? (arg-shift a) 0)
    (check-false (arg-captures? a))
    (check-equal? (arg-expands-to a) 'app)
    ;; the empty path makes a location its own argument (stitch's EMPTY_ZID)
    (define self (extract-arg c (car (corpus-roots c)) '()))
    (check-equal? (arg-shifted self) (car (corpus-roots c)))
    (check-equal? (arg-shift self) 0)
    ;; memoized: the same query returns the very same struct
    (check-eq? (extract-arg c (car (corpus-roots c)) '(arg)) a)))

(module+ test
  (test-case "free variables downshifted across lambdas"
    ;; A free variable downshifted across one lambda, then across two.
    ;; "(lam (f $3))": $3 points three binders up, one of which is the lambda we
    ;; cross, so from the match root it is $2.
    (define c (corpus-from-programs (list "(lam (f $3))" "(lam (lam (f $3)))")))
    (define one (extract-arg c (car (corpus-roots c)) '(body arg)))
    (check-equal? (expr->string c (arg-unshifted one)) "$3")
    (check-equal? (expr->string c (arg-shifted one)) "$2")
    (check-equal? (arg-shift one) -1)
    (check-false (arg-captures? one))
    (check-equal? (arg-expands-to one) (var 3))

    (define two (extract-arg c (cadr (corpus-roots c)) '(body body arg)))
    (check-equal? (expr->string c (arg-shifted two)) "$1")
    (check-equal? (arg-shift two) -2)
    (check-false (arg-captures? two))

    ;; The two shifted arguments differ, so a single abstraction variable cannot
    ;; serve both holes -- and hash-consing says so with one integer comparison.
    (check-not-equal? (arg-shifted one) (arg-shifted two))))

(module+ test
  (test-case "sentinel creation"
    ;; Sentinel creation: the argument refers to a lambda we crossed, so it would
    ;; have to capture a binder inside the abstraction body.
    ;; "(lam (f $0))": $0 is the crossed lambda -> #0, and the argument is then
    ;; closed, so only one downshift is counted.
    (define c (corpus-from-programs (list "(lam (f $0))" "(lam (lam (f $0)))"
                                          "(lam (lam (f $1)))")))
    (define-values (r0 r1 r2) (apply values (corpus-roots c)))

    (define a0 (extract-arg c r0 '(body arg)))
    (check-equal? (expr->string c (arg-shifted a0)) "#0")
    (check-equal? (arg-shift a0) -1)
    (check-true (arg-captures? a0))
    ;; PARITY: expands-to still reports the unshifted Var(0), not an ivar, so the
    ;; hole can be expanded syntactically into $0 (bound by the pattern's lam).
    (check-equal? (arg-expands-to a0) (var 0))

    ;; Two lambdas crossed, argument points at the inner one: sentinel #0 again,
    ;; and still only one counted downshift.
    (define a1 (extract-arg c r1 '(body body arg)))
    (check-equal? (expr->string c (arg-shifted a1)) "#0")
    (check-equal? (arg-shift a1) -1)
    (check-true (arg-captures? a1))
    ;; ... and it is the same shifted node as the one-lambda case
    (check-equal? (arg-shifted a1) (arg-shifted a0))

    ;; Two lambdas crossed, argument points at the *outer* one: sentinel index
    ;; counts crossed lambdas from the inside, so this is #1, and two downshifts
    ;; are counted ($1 is still free after the first crossing).
    (define a2 (extract-arg c r2 '(body body arg)))
    (check-equal? (expr->string c (arg-shifted a2)) "#1")
    (check-equal? (arg-shift a2) -2)
    (check-true (arg-captures? a2))
    (check-equal? (arg-expands-to a2) (var 1))))

(module+ test
  (test-case "variables bound inside the argument"
    ;; A variable bound *within* the argument is untouched, even though the
    ;; extraction crosses a lambda.
    (define c (corpus-from-programs (list "(lam (f (lam $0)))"
                                          "(lam (f (lam $1)))"
                                          "(lam (f (lam $2)))")))
    (define-values (r0 r1 r2) (apply values (corpus-roots c)))

    ;; (lam $0) is closed: nothing to shift, nothing to capture, same Idx.
    (define a0 (extract-arg c r0 '(body arg)))
    (check-equal? (expr->string c (arg-shifted a0)) "(lam $0)")
    (check-equal? (arg-shifted a0) (arg-unshifted a0))
    (check-equal? (arg-shift a0) 0)
    (check-false (arg-captures? a0))
    (check-equal? (arg-expands-to a0) 'lam)

    ;; (lam $1): the inner $1 escapes its own lambda and lands on the crossed
    ;; one, so it becomes the sentinel -- but the depth counter is what tells us
    ;; that, and $0 in the same position would not have.
    (define a1 (extract-arg c r1 '(body arg)))
    (check-equal? (expr->string c (arg-shifted a1)) "(lam #0)")
    (check-equal? (arg-shift a1) -1)
    (check-true (arg-captures? a1))

    ;; (lam $2): escapes past the crossed lambda too, so it just downshifts.
    (define a2 (extract-arg c r2 '(body arg)))
    (check-equal? (expr->string c (arg-shifted a2)) "(lam $1)")
    (check-equal? (arg-shift a2) -1)
    (check-false (arg-captures? a2))))

(module+ test
  (test-case "a mixed argument"
    ;; A mixed argument: one variable bound inside it, one pointing at the
    ;; crossed lambda, one pointing above the match root.  m = 1 here, so the
    ;; free indices 0 and 1 of "(lam ($0 $1 $2))" behave differently:
    ;;   $0 -> bound by the argument's own lam, untouched
    ;;   $1 -> free index 0 relative to the argument's root, 0 < m -> #0
    ;;   $2 -> free index 1, 1 >= m -> downshift to $1
    (define c (corpus-from-programs (list "(lam (f (lam ($0 $1 $2))))"
                                          "(lam (f (lam ($0 $1 $2))))")))
    (define a (extract-arg c (car (corpus-roots c)) '(body arg)))
    (check-equal? (expr->string c (arg-unshifted a)) "(lam ($0 $1 $2))")
    (check-equal? (expr->string c (arg-shifted a)) "(lam ($0 #0 $1))")
    ;; max free index of the argument is 1 and m is 1, so min(1, 2) = 1
    (check-equal? (arg-shift a) -1)
    (check-true (arg-captures? a))))

(module+ test
  (test-case "the min() in the shift arithmetic"
    ;; The min() in the shift arithmetic: a deeply free variable under one
    ;; lambda still only counts one downshift, and a shallowly free one under
    ;; many lambdas stops counting once the argument closes up.
    (define c (corpus-from-programs (list "(lam (f $5))"
                                          "(lam (lam (lam (f $5))))"
                                          "(lam (lam (lam (f $1))))")))
    (define-values (r0 r1 r2) (apply values (corpus-roots c)))
    ;; m = 1, max free = 5 -> min(1, 6) = 1
    (check-equal? (arg-shift (extract-arg c r0 '(body arg))) -1)
    (check-equal? (expr->string c (arg-shifted (extract-arg c r0 '(body arg)))) "$4")
    ;; m = 3, max free = 5 -> min(3, 6) = 3
    (check-equal? (arg-shift (extract-arg c r1 '(body body body arg))) -3)
    (check-equal? (expr->string c (arg-shifted (extract-arg c r1 '(body body body arg))))
                  "$2")
    ;; m = 3, max free = 1 -> min(3, 2) = 2; the argument becomes #1 after two
    ;; crossings and is closed for the third
    (define a2 (extract-arg c r2 '(body body body arg)))
    (check-equal? (expr->string c (arg-shifted a2)) "#1")
    (check-equal? (arg-shift a2) -2)
    (check-true (arg-captures? a2))))

(module+ test
  (test-case "shifted copies live past the span"
    ;; Shifted copies live past the span, and the analyses still work on them.
    (define c (corpus-from-programs (list "(lam (f $3))")))
    (define span (corpus-span c))
    (define a (extract-arg c (car (corpus-roots c)) '(body arg)))
    (check-true (>= (arg-shifted a) span))
    (check-equal? (cost c (arg-shifted a)) COST-VAR)
    (check-equal? (free-vars c (arg-shifted a)) (seteqv 2))
    ;; num-paths is a corpus-span notion only
    (check-exn #rx"outside the corpus span"
               (lambda () (num-paths c (arg-shifted a))))))

;; ---------------------------------------------------------------------------
;; A worked example, kept as a test: stitch's data/basic/hof.json.  The real
;; binary reports original_cost 1717 for the third program and finds the
;; arity-2 abstraction
;;   (app (app cons (app #1 #0)) (app (app cons (app #1 #0)) empty))
;; whose two holes sit at paths that cross the program's lambda, taking $0 and
;; (app plus $0) as arguments.  Here we only check the pieces this module
;; owns: the corpus, the costs, and the arguments at those two paths.
;; ---------------------------------------------------------------------------

(module+ test
  (test-case "hof.json, the pieces expr.rkt owns"
    (define hof
      (list
       "(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))"
       "(lam (app (app cons (app dec $0)) (app (app cons (app dec $0)) empty)))"
       "(lam (app (app cons (app (app plus $0) $0)) (app (app cons (app (app plus $0) $0)) empty)))"))
    (define c (corpus-from-programs hof))
    ;; matches stitch's reported max program cost
    (check-equal? (apply max (for/list ([r (in-list (corpus-roots c))]) (cost c r)))
                  1717)

    ;; The abstraction's body is the lambda's body; #0 lands on the innermost
    ;; argument of `(app inc $0)`, i.e. path (body arg fun arg arg) from the
    ;; program root -- one lambda crossed.
    (define r0 (car (corpus-roots c)))
    (define x (extract-arg c r0 '(body fun arg arg arg)))
    (check-equal? (expr->string c (arg-unshifted x)) "$0")
    ;; $0 refers to the crossed lambda, so as an argument it is a sentinel and
    ;; this location can be matched but never rewritten...
    (check-equal? (expr->string c (arg-shifted x)) "#0")
    (check-true (arg-captures? x))
    ;; ... which is exactly why the abstraction stitch actually finds keeps the
    ;; lambda *outside* itself: its match locations are the bodies, not the
    ;; whole programs.  Extracting from the body crosses no lambda:
    (define body (lam-body (corpus-node c r0)))
    (define y (extract-arg c body '(fun arg arg arg)))
    (check-equal? (expr->string c (arg-shifted y)) "$0")
    (check-equal? (arg-shift y) 0)
    (check-false (arg-captures? y))
    ;; and the other hole sees `inc` there, `dec` in program 1, and (app plus $0)
    ;; in program 2 -- three different shifted Idxs, hence a second variable.
    (define f0 (extract-arg c body '(fun arg arg fun arg)))
    (check-equal? (expr->string c (arg-shifted f0)) "inc")
    (define body2 (lam-body (corpus-node c (caddr (corpus-roots c)))))
    (define f2 (extract-arg c body2 '(fun arg arg fun arg)))
    (check-equal? (expr->string c (arg-shifted f2)) "(app plus $0)")
    (check-equal? (arg-shift f2) 0)
    (check-false (arg-captures? f2))
    (check-not-equal? (arg-shifted f0) (arg-shifted f2))))
