#lang racket

;; ---------------------------------------------------------------------------
;; tests/macro-fuzz.rkt --- a deterministic fuzzer for src/macro-micro.rkt
;; ---------------------------------------------------------------------------
;;
;; Two seeded fuzz properties, in the style of tests/fuzz.rkt (same
;; make-rng/random-seed trick, same "print a tally, assert an invariant"
;; shape), aimed at macro-micro.rkt's hygienic-macro learner instead of
;; micro.rkt's lambda-calculus one.
;;
;; PROPERTY 1 -- corpus fuzz.  Drive random small corpora through
;; `macro-compress`, which already asserts its own two big invariants inside
;; `rewrite-corpus` (predicted cost = real cost; every rewrite still expands
;; to something alpha-equivalent to the original).  This harness's job is
;; only to generate enough corpora, with enough deliberate sharing that a
;; macro is usually there to find, to give those asserts a real workout, and
;; to add two invariants of its own: every learned step has strictly positive
;; utility, and recomputing the first step's utility from scratch via
;; `macro-utility` reproduces what `macro-compress` recorded for it.
;;
;; PROPERTY 2 -- the inverse property.  Corpus fuzzing can only ever exercise
;; templates the SEARCH happens to propose; it says nothing about whether the
;; skeleton matcher can find every site a hand-built template legitimately
;; matches.  So here a finished template is built directly (using the pvar/
;; tvar structs macro-micro.rkt exports), a call to it is expanded to
;; manufacture a genuine "site", and the property is that `valid-sites`
;; recognizes the SAME template at the root of that site.  This is a
;; different fuzzer entirely: no corpus, no search, no cost model -- just
;; "does un-transcription invert transcription" -- and that is only true
;; because of two things this generator does on purpose: an argument may
;; reference a binder pvar only where that binder's own scope reaches
;; (`pscope`), never outside it, and `build-args` draws binder-position
;; names WITHOUT replacement.
;; Drop either one and the property goes false in general -- e.g. transcribing
;; `(lambda (#0) (lambda (#1) (f #0)))` with args `a a` produces a site whose
;; inner binder captures what the template aimed the outer one at, and no
;; un-transcription recovers that.  A fraction of generated templates carry
;; the one allowed (ellip sub) as a plain form's last element, with a
;; random-length (0-3, zero included) sequence of closed arguments for its
;; (svar), so the same inverse property is exercised across ellipsis
;; templates, not just flat ones (notes/2026-08-18-1324-ellipses-design.md,
;; section 5).
;;
;;   raco test tests/macro-fuzz.rkt
;;   racket tests/macro-fuzz.rkt --trials 500 --property both [--seed 20260818]
;; ---------------------------------------------------------------------------

(require rackunit racket/list
         (only-in "../src/macro-micro.rkt"
                  pvar pvar? pvar-i tvar tvar? tvar-j mdef mdef-template
                  ellip ellip? ellip-sub svar svar?
                  learned-macro learned-utility
                  template-arity expand-under valid-sites
                  macro-utility macro-compress))

;; The seed everything defaults to.  Changing it changes every corpus and
;; template this module generates, so don't, casually.
(define DEFAULT-SEED 20260818)

;; ---------------------------------------------------------------------------
;; Shared plumbing
;; ---------------------------------------------------------------------------

;; make-rng : Natural -> Pseudo-Random-Generator
;; A generator seeded so the same seed gives the same draws forever.
(define (make-rng seed)
  (define rng (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator rng]) (random-seed seed))
  rng)

;; rnd-choice : Pseudo-Random-Generator (Listof X) -> X
(define (rnd-choice rng lst) (list-ref lst (random (length lst) rng)))

(define GLOBALS '(f g h p))
(define LITERALS '(1 2 #t))
(define BINDER-NAMES '(a b c x y))

;; walk-path : Sexpr Path -> Sexpr
;; The subterm at `path`, by repeated list-ref -- the same traversal
;; macro-micro.rkt's own (unexported) subterm-at uses.
(define (walk-path t path)
  (if (null? path) t (walk-path (list-ref t (car path)) (cdr path))))

;; ---------------------------------------------------------------------------
;; PROPERTY 1 -- corpus fuzz
;; ---------------------------------------------------------------------------

(define CORPUS-DEPTH 4)

;; macro-search enumerates EVERY candidate template the shared skeleton
;; admits -- deliberately unoptimized (its docstring says so) -- so its cost
;; is steep in the corpus's total size once a shape is shared across all
;; three derived programs, as ours deliberately is.  A quick probe: three
;; near-identical ~14-node programs (42 nodes total) cost ~130ms; ~17 nodes
;; each (51 total) already cost ~2s; ~20 nodes each (60 total) cost ~26s.  So
;; the depth-4 cap alone is not enough -- a wide-but-shallow tree can still
;; have plenty of nodes -- and random-corpus below also rejects any shape
;; whose total size (all 3 copies) would exceed MAX-CORPUS-NODES.
(define MAX-CORPUS-NODES 30)

;; A binder introduced by random-expr draws from GLOBALS instead of
;; BINDER-NAMES with this probability (H2): the binder then genuinely
;; shadows a global inside its own body, which is exactly the case the old
;; disjoint vocabularies made unreachable.
(define SHADOW-DENOM 5) ; 1-in-5 = 20%

;; expr-node-count : Sexpr -> Natural
;; A rough size measure for the rejection sampler above: every list
;; contributes 1 plus its elements' counts, every atom contributes 1.
(define (expr-node-count t)
  (cond [(list? t) (+ 1 (for/sum ([e (in-list t)]) (expr-node-count e)))]
        [else 1]))

;; random-binder-name : Pseudo-Random-Generator -> Symbol
;; Ordinarily a fresh BINDER-NAMES symbol; with probability 1/SHADOW-DENOM a
;; GLOBALS symbol instead, so the binder shadows that global within its own
;; body (H2).  Either way the result is just a name handed to `random-expr`'s
;; own binder cases below -- nothing here needs to know what's in scope.
(define (random-binder-name rng)
  (if (zero? (random SHADOW-DENOM rng)) (rnd-choice rng GLOBALS) (rnd-choice rng BINDER-NAMES)))

;; random-expr : Pseudo-Random-Generator Natural (Listof Symbol) -> Sexpr
;; A random program over GLOBALS/LITERALS, with lambda/let binding forms and
;; plain forms of length 2-3.  `env` is the binder names currently in scope,
;; so a "variable" leaf is always a genuine reference to an enclosing binder
;; -- the leaf case draws from `env` itself, never independently guesses a
;; spelling, so this stays correct even though a binder's own name (see
;; random-binder-name) may now be drawn from GLOBALS: a var-leaf that
;; happens to be spelled like a global is still a real bound reference, and
;; a global leaf drawn straight from GLOBALS in the 'global case is still a
;; real free reference, because each case only ever draws from the
;; vocabulary its OWN case name says it should.  Leaves are weighted heavily
;; so the depth-4 cap is a true maximum, not the typical case -- matching
;; how macro-search's cost above requires it.
(define (random-expr rng depth env)
  (define (leaf)
    (define choices (append '(global literal) (if (pair? env) '(var) '())))
    (case (rnd-choice rng choices)
      [(global) (rnd-choice rng GLOBALS)]
      [(literal) (rnd-choice rng LITERALS)]
      [(var) (rnd-choice rng env)]))
  (cond
    [(<= depth 0) (leaf)]
    [else
     (case (rnd-choice rng '(leaf leaf leaf plain lambda let))
       [(leaf) (leaf)]
       [(plain)
        (define n (+ 2 (random 2 rng)))
        (for/list ([_ (in-range n)]) (random-expr rng (sub1 depth) env))]
       [(lambda)
        (define x (random-binder-name rng))
        `(lambda (,x) ,(random-expr rng (sub1 depth) (cons x env)))]
       [(let)
        (define x (random-binder-name rng))
        ;; the right-hand side does not see the let's own binder, matching
        ;; both the object language's real semantics and the template
        ;; hole-scope rule macro-micro.rkt documents for the same reason
        (define rhs (random-expr rng (sub1 depth) env))
        (define body (random-expr rng (sub1 depth) (cons x env)))
        `(let ([,x ,rhs]) ,body)])]))

;; A binder is alpha-renamed (see maybe-rename below) with this probability.
(define RENAME-DENOM 5) ; 1-in-5 = 20%

;; maybe-rename : Pseudo-Random-Generator Symbol Sexpr -> (values Symbol Sexpr)
;; With probability 1/RENAME-DENOM, replace this binder's name (and the
;; body's own references to it) with a fresh BINDER-NAMES symbol chosen to
;; occur NOWHERE in the body already -- so the new spelling cannot capture
;; an existing reference in body, and cannot itself be captured by some
;; inner binder that reuses it.  If no BINDER-NAMES symbol is that free (or
;; the coin misses), the binder is left exactly as it was.
(define (maybe-rename rng x body)
  (define candidates
    (for/list ([n (in-list BINDER-NAMES)] #:unless (memq n (flatten body))) n))
  (cond
    [(and (pair? candidates) (zero? (random RENAME-DENOM rng)))
     (define x^ (rnd-choice rng candidates))
     (values x^ (rename-bound x x^ body))]
    [else (values x body)]))

;; rename-bound : Symbol Symbol Sexpr -> Sexpr
;; Substitute x -> x^ everywhere in body EXCEPT beneath an inner lambda/let
;; that rebinds x -- there, the old spelling still names that inner binder
;; (ordinary lexical shadowing) and must be left exactly alone, so a rename
;; can never change which binder some deeply-nested reference resolves to.
(define (rename-bound x x^ body)
  (define (walk t shadowed?)
    (match t
      [`(lambda (,(? symbol? y)) ,b) `(lambda (,y) ,(walk b (or shadowed? (eq? y x))))]
      [`(let ([,(? symbol? y) ,rhs]) ,b)
       `(let ([,y ,(walk rhs shadowed?)]) ,(walk b (or shadowed? (eq? y x))))]
      [(? list?) (map (lambda (e) (walk e shadowed?)) t)]
      [(? symbol?) (if (and (eq? t x) (not shadowed?)) x^ t)]
      [_ t]))
  (walk body #f))

;; perturb : Pseudo-Random-Generator Sexpr [(Listof Symbol)] -> Sexpr
;; A copy of `shape` with (a) some global and literal leaves randomly
;; replaced by another member of their own vocabulary, and (b) some
;; lambda/let binders alpha-renamed (see maybe-rename) to a different
;; BINDER-NAMES spelling.  `env` tracks binder names currently in scope,
;; mirroring random-expr, because (a) and (b) now both need it: since
;; random-binder-name above can spell a binder like a GLOBALS symbol, a leaf
;; occurrence of (say) `f` may be a bound reference to a local shadowing
;; binder rather than the free global -- only `env` (not mere membership in
;; GLOBALS) can tell those apart, so a bound reference is always left
;; untouched by (a) regardless of its spelling.  This, together with (b), is
;; what lets a perturbed corpus exhibit H2 (shadowing) and H3 (differently-
;; spelled-but-corresponding binders across the three derived programs) --
;; both unreachable when BINDER-NAMES and GLOBALS were disjoint and every
;; derived program kept the shape's exact binder spelling.
(define (perturb rng shape [env '()])
  (match shape
    [`(lambda (,(? symbol? x)) ,body)
     (define-values (x^ body^) (maybe-rename rng x body))
     `(lambda (,x^) ,(perturb rng body^ (cons x^ env)))]
    [`(let ([,(? symbol? x) ,rhs]) ,body)
     (define-values (x^ body^) (maybe-rename rng x body))
     `(let ([,x^ ,(perturb rng rhs env)]) ,(perturb rng body^ (cons x^ env)))]
    [(? list?) (map (lambda (e) (perturb rng e env)) shape)]
    [_ (perturb-leaf rng shape env)]))

;; perturb-leaf : Pseudo-Random-Generator Any (Listof Symbol) -> Any
(define (perturb-leaf rng atom env)
  (cond
    [(memq atom env) atom] ; a genuine bound reference (H2: maybe spelled like a global) -- untouched
    [(and (symbol? atom) (memq atom GLOBALS)) (if (zero? (random 2 rng)) (rnd-choice rng GLOBALS) atom)]
    [(member atom LITERALS) (if (zero? (random 2 rng)) (rnd-choice rng LITERALS) atom)]
    [else atom]))

;; random-corpus : Pseudo-Random-Generator -> (Listof Sexpr)
;; One random shape expression, perturbed into exactly 3 programs, redrawn
;; until the (shared) skeleton is small enough for macro-search to chew
;; through quickly -- see MAX-CORPUS-NODES above.
(define (random-corpus rng)
  (let draw ()
    (define shape (random-expr rng CORPUS-DEPTH '()))
    (if (> (* 3 (expr-node-count shape)) MAX-CORPUS-NODES)
        (draw)
        (for/list ([_ (in-range 3)]) (perturb rng shape)))))

;; check-corpus-invariants! : (Listof Sexpr) -> (Listof Learned)
;; Run macro-compress and its internal asserts, plus the two extra invariants
;; this fuzzer adds: every learned step is strictly compressive, and
;; recomputing the first step's utility from scratch agrees with what
;; macro-compress recorded.  Any failure -- macro-compress's own asserts
;; included -- is re-raised with the corpus attached so a failing check
;; prints something a person can reproduce by hand.  Returns the steps
;; macro-compress found, so a caller that also wants to tally how many
;; corpora had something to learn doesn't have to run macro-compress again.
(define (check-corpus-invariants! programs)
  (define steps-box (box '()))
  (check-not-exn
   (lambda ()
     (with-handlers ([exn:fail?
                      (lambda (e)
                        (error 'macro-fuzz "corpus ~s: ~a" programs (exn-message e)))])
       (define steps (macro-compress programs 2 2))
       (set-box! steps-box steps)
       (for ([step (in-list steps)])
         (unless (positive? (learned-utility step))
           (error 'macro-fuzz
                  "corpus ~s: step for macro ~s has non-positive utility ~a"
                  programs (learned-macro step) (learned-utility step))))
       (when (pair? steps)
         (define step0 (car steps))
         (define recomputed
           (macro-utility '() (mdef-template (learned-macro step0)) programs))
         (unless (= recomputed (learned-utility step0))
           (error 'macro-fuzz
                  (string-append
                   "corpus ~s: first step utility mismatch -- macro-compress said ~a, "
                   "recomputing via macro-utility on template ~s said ~a")
                  programs (learned-utility step0)
                  (mdef-template (learned-macro step0)) recomputed))))))
  (unbox steps-box))

;; fuzz-corpora : Natural Natural -> Natural
;; Runs `trials` random corpora through check-corpus-invariants!, and returns
;; how many of them macro-compress actually found something to learn on (a
;; sanity count: a generator that stopped sharing structure would make this
;; property vacuous without ever failing).
(define (fuzz-corpora trials seed)
  (define rng (make-rng seed))
  (for/sum ([_ (in-range trials)])
    (define programs (random-corpus rng))
    (define steps (check-corpus-invariants! programs))
    (if (pair? steps) 1 0)))

;; ---------------------------------------------------------------------------
;; PROPERTY 2 -- the inverse property (un-transcription inverts transcription)
;; ---------------------------------------------------------------------------

(define TPL-DEPTH 4)
(define TPL-MAX-ARITY 2)
(define ARG-DEPTH 2)

;; mint-pvar! : Box Hash (U 'binder 'expr) (Listof Natural) -> Pvar
;; A brand-new pattern-variable index, recorded in `origin` under
;; (cons 'binder #f), for a binder-position mint, or (cons 'expr pscope),
;; for an expression-position mint, where `pscope` is the CURRENT pscope at
;; the moment of minting -- the binder-pvar indices in whose scope this
;; occurrence sits.  Every reuse of this index anywhere in the template
;; refers back to this same origin entry, which is exactly what decides how
;; build-args will fill it in (and, for 'expr, which names it may legally
;; reference -- see gen-expr-pvar and build-args below) and whether a LATER
;; occurrence may reuse it at all (see gen-expr-pvar's reuse rule).
(define (mint-pvar! pv-box origin kind pscope)
  (define n (unbox pv-box))
  (set-box! pv-box (add1 n))
  (hash-set! origin n (if (eq? kind 'expr) (cons 'expr pscope) (cons 'binder #f)))
  (pvar n))

;; mint-tvar! : Box -> Tvar
(define (mint-tvar! tv-box)
  (define j (unbox tv-box))
  (set-box! tv-box (add1 j))
  (tvar j))

;; pscope-subset? : (Listof Natural) (Listof Natural) -> Boolean
(define (pscope-subset? sub super)
  (andmap (lambda (i) (memv i super)) sub))

;; gen-expr-pvar : ... (Listof Natural) -> Sexpr
;; A pattern variable in EXPRESSION position: reuse an already-introduced
;; index or mint a fresh one if the arity cap allows.
;;   * An EXPR-origin index i is reusable here only if its own mint-time
;;     pscope is empty (a closed argument, safe to splice anywhere: it
;;     cannot depend on where it lands) OR that mint-time pscope is a
;;     SUBSET of the current pscope (build-args will let #i's argument
;;     reference the names of binder-pvars in its mint-time pscope -- see
;;     F6 in build-args below -- so reusing #i somewhere those binders are
;;     NOT in scope would splice a reference to a name that isn't bound
;;     there at all).  (An earlier version of this generator called EXPR-
;;     origin reuse "always safe" -- true only before arguments could
;;     reference binder names; it no longer is, hence this check.)
;;   * A BINDER-origin index i is reusable here only where `pscope` says
;;     that binder's own reference-scope reaches -- exactly mirroring a
;;     tvar reference, since a binder-position pvar denotes "the name this
;;     binder introduces" and referencing it outside the binder's own body
;;     (a let's own right-hand side, a sibling subtree, ...) is not a
;;     reference to that binder at all, just a same-spelled but unrelated
;;     occurrence; H4 would require its argument to agree with the
;;     binder's, which nothing forces once it is out of scope.  (This was
;;     caught by the fuzzer itself: an earlier version of this generator
;;     allowed exactly that reuse and produced templates the oracle
;;     correctly refused -- see the note below run-template-trial!.)
;; If the cap is reached and no in-scope reuse exists, fall back to a
;; global rather than manufacture either hazard.
(define (gen-expr-pvar rng pv-box max-arity origin pscope)
  (define count (unbox pv-box))
  (define reusable
    (for/list ([i (in-range count)]
               #:when (let ([entry (hash-ref origin i)])
                        (if (eq? (car entry) 'expr)
                            (or (null? (cdr entry)) (pscope-subset? (cdr entry) pscope))
                            (memv i pscope))))
      i))
  (cond
    [(and (< count max-arity) (or (zero? count) (zero? (random 2 rng))))
     (mint-pvar! pv-box origin 'expr pscope)]
    [(pair? reusable) (pvar (rnd-choice rng reusable))]
    [(< count max-arity) (mint-pvar! pv-box origin 'expr pscope)]
    [else (rnd-choice rng GLOBALS)]))

;; gen-binder : ... -> (U Tvar Pvar)
;; A binder position's occupant: a fresh template binder, or (V2) a pattern
;; variable.  Reuse is restricted to pvars whose FIRST occurrence was ITSELF
;; a binder position: those are guaranteed to receive a bare symbol argument
;; (see build-args), so splicing that same argument into another binder
;; position stays syntactically a `(lambda (symbol) ...)`.  Reusing a pvar
;; whose first occurrence was an expression position would instead force
;; that binder's argument to be a compound expression the site's other
;; occurrence already fixed -- an illegitimate template (this is exactly the
;; generator hazard the task's write-up warns about), not something the real
;; search ever needs to produce to reach every legitimate site.
(define (gen-binder rng pv-box tv-box max-arity origin)
  (define count (unbox pv-box))
  (define binder-reusable
    (for/list ([i (in-range count)] #:when (eq? (car (hash-ref origin i)) 'binder)) i))
  (define can-mint (< count max-arity))
  (define want-pvar? (and (or can-mint (pair? binder-reusable)) (zero? (random 2 rng))))
  (cond
    [(not want-pvar?) (mint-tvar! tv-box)]
    [(and can-mint (or (null? binder-reusable) (zero? (random 2 rng))))
     (mint-pvar! pv-box origin 'binder '())]
    [(pair? binder-reusable) (pvar (rnd-choice rng binder-reusable))]
    [else (mint-tvar! tv-box)]))

;; With this probability, a freshly-generated plain form becomes the
;; template's one ellip -- see `gen-template`'s 'plain case below.
;; ~25%, so most templates stay ellip-free while a healthy minority
;; exercise the ellipsis machinery.
(define ELLIP-DENOM 4) ; 1-in-4 = 25%

;; contains-svar? : Template -> Boolean
;; A local stand-in for macro-micro.rkt's (unexported) template-has-svar?,
;; used only by force-svar below.
(define (contains-svar? t)
  (cond [(svar? t) #t]
        [(ellip? t) (contains-svar? (ellip-sub t))]
        [(list? t) (ormap contains-svar? t)]
        [else #f]))

;; force-svar : Template -> Template
;; If `t` already contains an (svar) anywhere, return it unchanged (the
;; common case, given gen-ellip-sub's own per-leaf svar production below);
;; otherwise force one in by replacing t's own first leaf -- structurally,
;; recurse into a list's first element until a non-list is reached, and
;; replace THAT with a bare (svar) -- with a bare (svar) itself if t was
;; already a leaf (the depth-0 sub case, where there is nothing to recurse
;; into).  A bare (svar) is itself a perfectly legal sub (macro-micro.rkt's
;; own `(f (ellip (g (svar))))` benchmark has a one-node sub), so this
;; always terminates in a legal result without ever retrying generation.
;; Whatever leaf this discards -- a global, a literal, or a pvar/tvar
;; reference -- simply never occurs in the FINISHED template:
;; template-arity and renumber-template both walk the tree actually
;; returned, never pv-box's own mint count, so a discarded pvar reference
;; is invisible and harmless, exactly as an ordinary retry-until-lucky
;; would also discard it.
(define (force-svar t)
  (cond [(contains-svar? t) t]
        [(list? t) (cons (force-svar (car t)) (cdr t))]
        [else (svar)]))

;; gen-ellip-sub : Pseudo-Random-Generator Natural (Listof Natural)
;;                 (Listof Natural) Box Natural Hash -> Template
;; The restricted recursion for an ellip's sub (design note section 2 /
;; module header): leaves and plain forms only -- no lambda/let (no binder
;; forms to abstract inside a single iteration, per the note: "lambda/let
;; have fixed shapes ... nothing variadic to abstract there") and no nested
;; ellip (at most one per template, and this IS that one's own sub) -- plus
;; one extra leaf production, (svar), that ordinary gen-template does not
;; have.  `scope`/`pscope` are exactly the ones already in effect where the
;; ellip sits: an ellip introduces no binder of its own (macro-micro.rkt's
;; own hole-ellip-scope treats it the same way, passing scope through
;; unchanged into sub), so both are simply threaded in as-is, never
;; extended here.  A depth-0 (pvar) inside sub reuses the very same
;; gen-expr-pvar as everywhere else in the template, on equal footing:
;; nothing about being inside a sub changes its reasoning (the sub itself
;; carries no pscope of its own to add), so an already-minted pvar may be
;; reused here subject to its usual pscope-subset rule, and a pvar first
;; minted HERE may just as well be reused outside sub later.
(define (gen-ellip-sub rng depth scope pscope pv-box max-arity origin)
  (define (leaf)
    (define options (append '(global literal pvar svar) (if (pair? scope) '(tvar-ref) '())))
    (case (rnd-choice rng options)
      [(global) (rnd-choice rng GLOBALS)]
      [(literal) (rnd-choice rng LITERALS)]
      [(pvar) (gen-expr-pvar rng pv-box max-arity origin pscope)]
      [(tvar-ref) (tvar (rnd-choice rng scope))]
      [(svar) (svar)]))
  (cond
    [(<= depth 0) (leaf)]
    [else
     (case (rnd-choice rng '(leaf leaf plain))
       [(leaf) (leaf)]
       [(plain)
        (define n (+ 2 (random 2 rng)))
        (for/list ([_ (in-range n)])
          (gen-ellip-sub rng (sub1 depth) scope pscope pv-box max-arity origin))])]))

;; gen-ellip-sub! : Pseudo-Random-Generator Natural (Listof Natural)
;;                  (Listof Natural) Box Natural Hash -> Template
;; gen-ellip-sub, then force-svar -- guarantees the result contains at
;; least one (svar), which is what macro-micro.rkt's finished?
;; (template-ellipses-ok?) requires of every ellip's sub and what actually
;; controls the splice's iteration count; nothing else could.
(define (gen-ellip-sub! rng depth scope pscope pv-box max-arity origin)
  (force-svar (gen-ellip-sub rng depth scope pscope pv-box max-arity origin)))

;; gen-template : ... Natural (Listof Natural) (Listof Natural) Box Box
;;                Natural Hash Box -> Template
;; A random finished template: expression positions hold globals, literals,
;; pattern variables, a reference to a template binder in `scope`, or (V2) a
;; reference to a binder-position pvar in `pscope`; plain forms have length
;; 2-3; lambda/let binder positions hold a fresh tvar or a (fresh-or-reused)
;; pvar, per gen-binder above.  Both `scope` and `pscope` mirror
;; macro-micro.rkt's hole-scope exactly, including for pvar binders: a let's
;; right-hand side does not see the let's own binder, tvar or pvar alike.
;; `ellip-box`, a shared (Box Boolean) starting #f, is threaded into every
;; recursive call so that at most one (ellip sub) is ever generated across
;; the WHOLE template (one ellip per template, not merely per form) -- see
;; the 'plain case, the only place that ever sets it.  When a plain form
;; under construction takes
;; that branch, the ellip's own mint-time pscope is recorded in `origin`
;; under the reserved key 'ellip-pscope (raw pvar indices, exactly like an
;; expr-pvar's own mint-time pscope -- see mint-pvar! -- so build-args can
;; later decide, via the identical F6a logic, which binder-pvar names a
;; sequence argument may reference).
(define (gen-template rng depth scope pscope pv-box tv-box max-arity origin ellip-box)
  (define (leaf)
    (define options (append '(global literal pvar) (if (pair? scope) '(tvar-ref) '())))
    (case (rnd-choice rng options)
      [(global) (rnd-choice rng GLOBALS)]
      [(literal) (rnd-choice rng LITERALS)]
      [(pvar) (gen-expr-pvar rng pv-box max-arity origin pscope)]
      [(tvar-ref) (tvar (rnd-choice rng scope))]))
  (cond
    [(<= depth 0) (leaf)]
    [else
     (case (rnd-choice rng '(leaf plain lambda let))
       [(leaf) (leaf)]
       [(plain)
        (define n (+ 2 (random 2 rng)))
        (define want-ellip?
          (and (not (unbox ellip-box)) (zero? (random ELLIP-DENOM rng))))
        (cond
          [want-ellip?
           (set-box! ellip-box #t)
           (hash-set! origin 'ellip-pscope pscope)
           (define prefix
             (for/list ([_ (in-range (sub1 n))])
               (gen-template rng (sub1 depth) scope pscope pv-box tv-box max-arity origin ellip-box)))
           (define sub (gen-ellip-sub! rng (sub1 depth) scope pscope pv-box max-arity origin))
           (append prefix (list (ellip sub)))]
          [else
           (for/list ([_ (in-range n)])
             (gen-template rng (sub1 depth) scope pscope pv-box tv-box max-arity origin ellip-box))])]
       [(lambda)
        (define binder (gen-binder rng pv-box tv-box max-arity origin))
        (define scope^ (if (tvar? binder) (cons (tvar-j binder) scope) scope))
        (define pscope^ (if (pvar? binder) (cons (pvar-i binder) pscope) pscope))
        `(lambda (,binder)
           ,(gen-template rng (sub1 depth) scope^ pscope^ pv-box tv-box max-arity origin ellip-box))]
       [(let)
        (define binder (gen-binder rng pv-box tv-box max-arity origin))
        (define rhs (gen-template rng (sub1 depth) scope pscope pv-box tv-box max-arity origin ellip-box))
        (define scope^ (if (tvar? binder) (cons (tvar-j binder) scope) scope))
        (define pscope^ (if (pvar? binder) (cons (pvar-i binder) pscope) pscope))
        (define body (gen-template rng (sub1 depth) scope^ pscope^ pv-box tv-box max-arity origin ellip-box))
        `(let ([,binder ,rhs]) ,body)])]))

;; renumber-template : Template Hash -> (values Template Hash)
;; Pvars and tvars are renumbered by first occurrence (a plain left-to-right
;; preorder walk of the template's list structure -- which always visits a
;; binder before its body, and a let's binder before its own right-hand
;; side) so both are contiguous from 0, as template-arity assumes.  The
;; `origin` hash (raw index -> (cons 'binder #f) or (cons 'expr pscope)) is
;; carried along, remapped to the new indices, since minting is what
;; actually decided each index's origin (and, for 'expr, its mint-time
;; pscope) and that decision must survive renumbering.  A pscope list is
;; itself a list of raw pvar indices, so remapping an 'expr entry recurses
;; remap-pvar over it too -- safe (no cycle) because a pvar can never be a
;; member of its own pscope.  `walk` also recurses into an ellip's sub (an
;; ellip struct is not itself a list, so the plain `list?` case does not
;; see inside it on its own); and if `origin` carries the
;; reserved 'ellip-pscope key (the ellip's own mint-time pscope, set by
;; gen-template), it is remapped too, AFTER the walk -- every raw index it
;; names is a binder-pvar that necessarily occurs as an actual binder node
;; somewhere structurally enclosing the ellip, hence already visited (and
;; so already in pvar-map) by the time the walk itself is done.
(define (renumber-template tpl origin)
  (define pvar-map (make-hash))
  (define tvar-map (make-hash))
  (define next-pvar (box 0))
  (define next-tvar (box 0))
  (define new-origin (make-hash))
  (define (remap-pvar old)
    (hash-ref! pvar-map old
               (lambda ()
                 (define n (unbox next-pvar))
                 (set-box! next-pvar (add1 n))
                 (define entry (hash-ref origin old))
                 (hash-set! new-origin n
                            (if (eq? (car entry) 'expr)
                                (cons 'expr (map remap-pvar (cdr entry)))
                                (cons 'binder #f)))
                 n)))
  (define (remap-tvar old)
    (hash-ref! tvar-map old
               (lambda () (define n (unbox next-tvar)) (set-box! next-tvar (add1 n)) n)))
  (define (walk t)
    (cond
      [(pvar? t) (pvar (remap-pvar (pvar-i t)))]
      [(tvar? t) (tvar (remap-tvar (tvar-j t)))]
      [(ellip? t) (ellip (walk (ellip-sub t)))]
      [(list? t) (map walk t)]
      [else t]))
  (define result (walk tpl))
  (when (hash-has-key? origin 'ellip-pscope)
    (hash-set! new-origin 'ellip-pscope (map remap-pvar (hash-ref origin 'ellip-pscope))))
  (values result new-origin))

;; random-finished-template : Pseudo-Random-Generator -> (values Template Hash)
;; Retries until the result is not a bare pattern variable (the identity
;; macro, which template-arity and the real search both refuse to consider).
;; `ellip-box` starts fresh #f on every attempt, exactly like
;; pv-box/tv-box/origin -- a retry must not carry over "this template
;; already used its one ellip" from a discarded attempt.
(define (random-finished-template rng)
  (let loop ()
    (define origin (make-hash))
    (define pv-box (box 0))
    (define tv-box (box 0))
    (define ellip-box (box #f))
    (define raw (gen-template rng TPL-DEPTH '() '() pv-box tv-box TPL-MAX-ARITY origin ellip-box))
    (define-values (tpl new-origin) (renumber-template raw origin))
    (if (pvar? tpl) (loop) (values tpl new-origin))))

;; A separate binder-name pool for the little lambdas random-closed-expr can
;; introduce (F6b below): disjoint from build-args' own '(a b c q) pool so a
;; V2 use-site-capture reference (drawn from that pool) can never collide
;; with one of these.
(define LAMBDA-BINDER-NAMES '(u w))

;; random-closed-expr : Pseudo-Random-Generator Natural (Listof Symbol) -> Sexpr
;; A random argument for a pattern variable: globals, literals, small plain
;; forms over them, and two deliberate departures from "closed" that build-
;; args' comment below explains the point of:
;;   * F6a -- `names` is the spelling build-args already assigned to the
;;     binder-pvars in scope at this argument's pvar's first occurrence
;;     (empty if none); a leaf may reference one of them with probability
;;     1/2, which is exactly the legitimate use-site capture V2 exists for.
;;   * F6b -- at any non-leaf depth, with probability 1/4, emit a
;;     `(lambda (v) ...)` with v drawn from LAMBDA-BINDER-NAMES (disjoint
;;     from every name `names` could contain), whose body may in turn
;;     reference v.  This is what exercises alpha-comparison (H4) across
;;     two hygienically-renamed copies of the same argument, since a reused
;;     pvar's single argument value is spliced at every one of its
;;     occurrences and only alpha=?, not equal?, can relate them afterward.
(define (random-closed-expr rng depth names)
  (define (gen d lenv)
    (define (leaf)
      (cond
        [(and (pair? lenv) (zero? (random 2 rng))) (rnd-choice rng lenv)]
        [(and (pair? names) (zero? (random 2 rng))) (rnd-choice rng names)]
        [(zero? (random 2 rng)) (rnd-choice rng GLOBALS)]
        [else (rnd-choice rng LITERALS)]))
    (cond
      [(<= d 0) (leaf)]
      [(zero? (random 4 rng))
       (define v (rnd-choice rng LAMBDA-BINDER-NAMES))
       `(lambda (,v) ,(gen (sub1 d) (cons v lenv)))]
      [(zero? (random 2 rng)) (leaf)]
      [else
       (define n (+ 2 (random 2 rng)))
       (for/list ([_ (in-range n)]) (gen (sub1 d) lenv))]))
  (gen depth '()))

;; binder-pvar-counts : Template -> (HashOf Natural Natural)
;; How many times each binder-origin pvar index occurs AS A BINDER anywhere
;; in the finished template (a pvar occurring only in expression position,
;; or not at all, simply doesn't show up here).  What this is for: an index
;; occurring exactly once as a binder has an unambiguous "recovered name" --
;; skeleton-match's first-occurrence rule and the site's actual (unique)
;; binder for that index necessarily agree.  An index occurring MORE than
;; once as a binder does not: skeleton-match still reports only the FIRST
;; occurrence's site-name, but real lexical scoping resolves any reference
;; to the CLOSEST enclosing occurrence, which need not be the first one --
;; see build-args below for where this bites.
(define (binder-pvar-counts tpl)
  (define counts (make-hash))
  (define (bump! b) (when (pvar? b) (hash-update! counts (pvar-i b) add1 0)))
  (let walk ([t tpl])
    (match t
      [`(lambda (,b) ,body) (bump! b) (walk body)]
      [`(let ([,b ,rhs]) ,body) (bump! b) (walk rhs) (walk body)]
      [(? list?) (for-each walk t)]
      [_ (void)]))
  counts)

;; pvars-outside-ellip : Template -> (Listof Natural)
;; Pattern-variable indices occurring somewhere in `t` OUTSIDE every ellip's
;; sub (duplicates allowed -- callers only care about membership).  Exists
;; for exactly one reason (see build-args's "needs-iteration?" below): a
;; depth-0 pvar whose ONLY occurrence in the whole template is inside an
;; ellip's sub is never bound by skeleton-match when that ellip matches
;; ZERO elements at a site -- sub is simply never walked against anything
;; then, so that index never enters the matcher's `binds` hash at all (see
;; macro-micro.rkt's skeleton-match docstring/comment on this exact point,
;; and its own "no zero-th occurrence to fall back on" remark) -- and
;; skeleton-match soundly treats that as NO MATCH rather than guess.  A
;; pvar that ALSO occurs outside sub is never at risk regardless of
;; iteration count: skeleton-match's global first-occurrence rule binds it
;; from whichever occurrence walk actually reaches first, prefix or
;; sibling, so zero sub iterations just means that outside occurrence
;; becomes the (only) one visited.
(define (pvars-outside-ellip t)
  (cond [(pvar? t) (list (pvar-i t))]
        [(ellip? t) '()] ; do not look inside sub
        [(list? t) (append-map pvars-outside-ellip t)]
        [else '()]))

;; build-args : Pseudo-Random-Generator Natural Hash Template -> (Listof Sexpr)
;; One argument per pattern-variable index, in order.  A pvar whose first
;; occurrence is a binder position gets a bare symbol (so every binder
;; position it fills stays syntactically a binder); an expression-position
;; pvar gets a random argument via random-closed-expr, which (F6a) may
;; reference names assigned to the binder-pvars recorded in its mint-time
;; pscope.  Those binder pvars always have a SMALLER index than this one
;; (they are structural ancestors in the template, so renumber-template's
;; preorder pass necessarily visited them first), so a single left-to-right
;; pass over 0..arity-1, threading which names have been assigned so far,
;; always has every name an expr-pvar might want already in hand.
;;
;; F6a is further restricted to binder pvars `binder-pvar-counts` reports as
;; occurring EXACTLY ONCE as a binder.  (gen-binder can reuse a binder-pvar
;; at another binder position anywhere -- an earlier, unrelated one, or even
;; a self-shadowing one nested inside its own scope -- and both were caught
;; by this fuzzer, hand-traced: skeleton-match always reports index i's
;; recovered name from its FIRST binder occurrence, but a real reference at
;; an expression position resolves to whichever occurrence of i is
;; LEXICALLY CLOSEST, which need not be the first; re-splicing the
;; first-occurrence name at every occurrence during un-transcription then
;; reproduces a different binding than the site actually had, and the
;; oracle correctly refuses it.  An index occurring exactly once as a
;; binder has no such ambiguity: its one occurrence is necessarily both the
;; first AND the closest.  Note this restriction is about being a BINDER
;; more than once -- reusing an index directly as an expression-position
;; pvar leaf, pre-F6's original V2 mechanism, is unaffected: that reuse
;; creates no separate argument slot at all, so it always resplices
;; whatever single value the index's one binder got, faithfully
;; reproducing the site's own resolution regardless of nesting.)
;;
;; Binder-name choices are drawn WITHOUT replacement across the whole arg
;; list: two binder-position pvars that happen to nest (one's scope inside
;; the other's) and share a name would make ordinary lexical shadowing
;; capture a reference the template aimed at the outer one -- a hygiene
;; accident manufactured purely by this generator's naming, not by anything
;; macro-micro.rkt does (caught by an earlier version of this generator,
;; which drew names independently).
;;
;; When `tpl` contains an ellip (recorded by gen-template as the
;; 'ellip-pscope key in `origin`), a random-length sequence of TRAILING
;; arguments is appended after the fixed pvar arguments -- these are the
;; (mfz e1 .. earity s1 .. sn) call's s1..sn, i.e. the %xs VALUES
;; themselves that svar receives each iteration, NOT the transcribed (sub
;; with svar := si) elements the expanded site will actually contain (the
;; expander builds those, one per si, when it expands the call).  Each si
;; is an ordinary closed expression (random-closed-expr again), built with
;; the SAME F6a treatment as an expr-pvar's own argument just above and for
;; the identical reason: it may reference a binder-pvar name recorded in
;; the ellip's own mint-time pscope, restricted to names occurring EXACTLY
;; ONCE as a binder (binder-pvar-counts) -- the ellip's pscope plays
;; exactly the role a single expr-pvar's own mint-time pscope plays above,
;; just shared across every si instead of being scoped per-pvar.
;;
;; The length is 0-3 -- zero deliberately included, since syntax-rules and
;; the expander both treat zero iterations as perfectly legal -- EXCEPT
;; when `pvars-outside-ellip` reports some pvar index in 0..arity-1 as
;; occurring ONLY inside this ellip's sub: zero iterations would then leave
;; skeleton-match unable to bind that index at all (see that function's
;; docstring), which is a real, DOCUMENTED limitation of skeleton-match
;; itself, not a bug -- so length is instead drawn from 1-3 whenever that
;; situation applies, guaranteeing sub gets walked at least once.
(define (build-args rng arity origin tpl)
  (define binder-names (shuffle-by rng '(a b c q)))
  (define reused (binder-pvar-counts tpl))
  (define-values (out _pool assigned)
    (for/fold ([out '()] [pool binder-names] [assigned (hash)])
              ([i (in-range arity)])
      (define entry (hash-ref origin i))
      (case (car entry)
        [(binder)
         (define nm (car pool))
         (values (cons nm out) (cdr pool) (hash-set assigned i nm))]
        [(expr)
         (define in-scope
           (filter-map (lambda (j) (and (= (hash-ref reused j 0) 1) (hash-ref assigned j #f)))
                       (cdr entry)))
         (values (cons (random-closed-expr rng ARG-DEPTH in-scope) out) pool assigned)])))
  (define pvar-args (reverse out))
  (define seq-args
    (if (hash-has-key? origin 'ellip-pscope)
        (let* ([ellip-in-scope
                (filter-map (lambda (j) (and (= (hash-ref reused j 0) 1) (hash-ref assigned j #f)))
                            (hash-ref origin 'ellip-pscope))]
               [outside (pvars-outside-ellip tpl)]
               [needs-iteration? (for/or ([i (in-range arity)]) (not (memv i outside)))]
               [n (if needs-iteration? (add1 (random 3 rng)) (random 4 rng))]) ; see docstring
          (for/list ([_ (in-range n)]) (random-closed-expr rng ARG-DEPTH ellip-in-scope)))
        '()))
  (append pvar-args seq-args))

;; shuffle-by : Pseudo-Random-Generator (Listof X) -> (Listof X)
(define (shuffle-by rng lst)
  (define v (list->vector lst))
  (for ([i (in-range (sub1 (vector-length v)) 0 -1)])
    (define j (random (add1 i) rng))
    (define tmp (vector-ref v i))
    (vector-set! v i (vector-ref v j))
    (vector-set! v j tmp))
  (vector->list v))

;; run-template-trial! : Pseudo-Random-Generator -> Void
;; Build a random finished template and a random argument list, expand the
;; call to manufacture a genuine site, and check that the SAME template
;; matches back at that site's root -- and (F16c) that what comes back is
;; not just SOME argument but the RIGHT one:
;;   * count, when tpl has an ellip: valid-sites must recover exactly
;;     arity + n entries, n being the sequence length build-args generated
;;     (the zero-length case included -- an ellip matching zero elements is
;;     just as much a legal match as any other, per the design note and
;;     macro-micro.rkt's own skeleton-match docstring).
;;   * path-consistency, always, for EVERY recovered entry (fixed pvar args
;;     and trailing sequence args alike): each recovered
;;     (path . arg) pair must actually be what walking `site` by that path
;;     finds there -- i.e. valid-sites's internal skeleton-match is
;;     reporting the site's own structure back at us, not something else.
;;   * for a binder-origin pvar, the recovered value must be a symbol (a
;;     binder position's argument is always the site's binder NAME).
;;   * for an expr-origin pvar whose built argument is CLOSED -- empty
;;     mint-time pscope (F6a made no reference), and no lambda anywhere in
;;     it (F6b introduced none) -- expansion cannot have changed it at all,
;;     so the recovered value must be equal? to the one build-args built.
;;     (An argument that DOES reference a binder name or contain a lambda
;;     gets hygienically renamed by expansion, so no such direct comparison
;;     is available for it; path-consistency above is what covers it.)
;;   * for a sequence argument whose si was built with an EMPTY
;;     in-scope name list (the ellip's own mint-time pscope was empty, so
;;     F6a could not have referenced anything) and no lambda anywhere in it
;;     (F6b introduced none), the identical equal? argument applies: si is
;;     closed, so expansion cannot have changed it, exactly mirroring the
;;     closed expr-pvar case just above -- the ellip's pscope plays the
;;     role a single pvar's own mint-time pscope plays there, just shared
;;     across every si rather than being per-argument.
;; Any exception (a malformed site, a crash inside valid-sites) is
;; re-raised with the template/args/site attached so a failing check prints
;; a reproducer.
(define (run-template-trial! rng)
  (check-not-exn
   (lambda ()
     (define-values (tpl origin) (random-finished-template rng))
     (define arity (template-arity tpl))
     (define args (build-args rng arity origin tpl))
     (define n (- (length args) arity)) ; sequence-arg count build-args generated (0 if no ellip)
     (with-handlers ([exn:fail?
                      (lambda (e)
                        (error 'macro-fuzz
                               "template ~s args ~s raised: ~a" tpl args (exn-message e)))])
       (define site (expand-under (list (mdef 'mfz arity tpl)) (cons 'mfz args)))
       (define expanded-site (expand-under '() site))
       (define result (hash-ref (valid-sites '() 'm9 tpl site expanded-site) '() #f))
       (unless result
         (error 'macro-fuzz
                (string-append "inverse property failed: the template did not match back "
                               "at the root of its own expansion\n"
                               "  template: ~s\n  args: ~s\n  site: ~s\n  expanded-site: ~s")
                tpl args site expanded-site))
       (unless (= (length result) (+ arity n))
         (error 'macro-fuzz
                (string-append "sequence-count mismatch: build-args generated ~a sequence "
                               "argument(s), but valid-sites recovered ~a entries total for "
                               "arity ~a\n  template: ~s\n  args: ~s\n  site: ~s")
                n (length result) arity tpl args site))
       (for ([i (in-range (length result))])
         (define pr (list-ref result i))
         (define path (car pr))
         (define recovered (cdr pr))
         (unless (equal? (walk-path site path) recovered)
           (error 'macro-fuzz
                  (string-append "path-consistency failed at result index ~a: path ~s in site "
                                 "~s is ~s, but valid-sites recovered ~s\n  template: ~s\n  args: ~s")
                  i path site (walk-path site path) recovered tpl args))
         (cond
           [(< i arity)
            (define entry (hash-ref origin i))
            (case (car entry)
              [(binder)
               (unless (symbol? recovered)
                 (error 'macro-fuzz
                        "binder-origin pvar ~a recovered non-symbol ~s\n  template: ~s\n  args: ~s"
                        i recovered tpl args))]
              [(expr)
               (define built (list-ref args i))
               (when (and (null? (cdr entry)) (not (memq 'lambda (flatten built))))
                 (unless (equal? recovered built)
                   (error 'macro-fuzz
                          (string-append "closed expr-origin pvar ~a: recovered ~s does not "
                                         "match the built argument ~s\n  template: ~s\n  args: ~s")
                          i recovered built tpl args)))])]
           [else
            ;; a sequence (svar) argument -- (- i arity) is which one, in order
            (define si (list-ref args i))
            (define ellip-pscope (hash-ref origin 'ellip-pscope '()))
            (when (and (null? ellip-pscope) (not (memq 'lambda (flatten si))))
              (unless (equal? recovered si)
                (error 'macro-fuzz
                       (string-append "closed sequence arg ~a: recovered ~s does not match the "
                                      "built argument ~s\n  template: ~s\n  args: ~s")
                       (- i arity) recovered si tpl args)))]))))))

;; fuzz-templates : Natural Natural -> Void
(define (fuzz-templates trials seed)
  (define rng (make-rng seed))
  (for ([_ (in-range trials)]) (run-template-trial! rng)))

;; ---------------------------------------------------------------------------
;; The tests
;; ---------------------------------------------------------------------------

;; Trial counts, chosen so the whole file runs in well under the ~2-minute
;; budget with a comfortable margin: property 1 pays for a macro-compress run
;; (up to two full search iterations) per corpus -- measured at ~3ms/corpus
;; average with MAX-CORPUS-NODES's cap, so even 400 trials is ~1-2s, not the
;; minutes an unbounded corpus size would cost (see MAX-CORPUS-NODES above).
;; Property 2 pays only for one expand and one valid-sites call per
;; template, so its trial count can be generous for free.
(define CORPUS-TRIALS 400)
(define TEMPLATE-TRIALS 2000)

(module+ test
  (test-case "property 1: corpus fuzz -- macro-compress's invariants hold, and match by hand"
    (define found (fuzz-corpora CORPUS-TRIALS DEFAULT-SEED))
    (printf "corpus fuzz: ~a corpora, ~a found something to learn\n" CORPUS-TRIALS found)
    ;; a generator that stopped sharing structure would make every assertion
    ;; above vacuous without ever failing; the observed rate across seeds is
    ;; 17%-36%, so 10% is a comfortable floor rather than a tight one
    (check-true (> found (quotient CORPUS-TRIALS 10))
                "too few corpora had anything to learn -- check the generator's sharing"))

  (test-case "property 2: the inverse property -- un-transcription inverts transcription"
    (fuzz-templates TEMPLATE-TRIALS DEFAULT-SEED)
    (printf "inverse property: ~a templates, all matched back\n" TEMPLATE-TRIALS)))

;; ---------------------------------------------------------------------------
;; Command line
;; ---------------------------------------------------------------------------
;;
;;   racket tests/macro-fuzz.rkt --trials 5000 --property both [--seed 20260818]
;;
;; for runs bigger than the test suite should sit through.

(module+ main
  (define trials 1000)
  (define property 'both)
  (define seed DEFAULT-SEED)
  (command-line
   #:program "macro-fuzz"
   #:once-each
   [("--trials") n "how many trials per property" (set! trials (string->number n))]
   [("--property") p "corpus, inverse, or both" (set! property (string->symbol p))]
   [("--seed") s "PRNG seed" (set! seed (string->number s))])
  (unless (memq property '(corpus inverse both))
    (error 'macro-fuzz "--property must be corpus, inverse or both, not ~a" property))
  (when (memq property '(corpus both))
    (define found (fuzz-corpora trials seed))
    (printf "corpus fuzz: ~a corpora, ~a found something to learn\n" trials found))
  (when (memq property '(inverse both))
    (fuzz-templates trials seed)
    (printf "inverse property: ~a templates, all matched back\n" trials)))
