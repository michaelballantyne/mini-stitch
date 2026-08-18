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
;; "does un-transcription invert transcription".
;;
;;   raco test tests/macro-fuzz.rkt
;;   racket tests/macro-fuzz.rkt --trials 500 --property both [--seed 20260818]
;; ---------------------------------------------------------------------------

(require rackunit
         (only-in "../src/macro-micro.rkt"
                  pvar pvar? pvar-i tvar tvar? tvar-j mdef mdef-template
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

;; expr-node-count : Sexpr -> Natural
;; A rough size measure for the rejection sampler above: every list
;; contributes 1 plus its elements' counts, every atom contributes 1.
(define (expr-node-count t)
  (cond [(list? t) (+ 1 (for/sum ([e (in-list t)]) (expr-node-count e)))]
        [else 1]))

;; random-expr : Pseudo-Random-Generator Natural (Listof Symbol) -> Sexpr
;; A random program over GLOBALS/LITERALS, with lambda/let binding forms
;; (binder names from BINDER-NAMES) and plain forms of length 2-3.  `env` is
;; the binder names currently in scope, so a "variable" leaf is always a
;; genuine reference to an enclosing binder -- never an accidental global
;; masquerading as one, since BINDER-NAMES and GLOBALS are disjoint.  Leaves
;; are weighted heavily so the depth-4 cap is a true maximum, not the
;; typical case -- matching how macro-search's cost above requires it.
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
        (define x (rnd-choice rng BINDER-NAMES))
        `(lambda (,x) ,(random-expr rng (sub1 depth) (cons x env)))]
       [(let)
        (define x (rnd-choice rng BINDER-NAMES))
        ;; the right-hand side does not see the let's own binder, matching
        ;; both the object language's real semantics and the template
        ;; hole-scope rule macro-micro.rkt documents for the same reason
        (define rhs (random-expr rng (sub1 depth) env))
        (define body (random-expr rng (sub1 depth) (cons x env)))
        `(let ([,x ,rhs]) ,body)])]))

;; perturb : Pseudo-Random-Generator Sexpr -> Sexpr
;; A copy of `shape` with some global and literal leaves randomly replaced by
;; another member of their own vocabulary.  Bound-variable references (any
;; symbol not in GLOBALS/LITERALS, i.e. a BINDER-NAMES symbol placed only via
;; `env` above) are left untouched.  This is what manufactures the
;; "deliberate sharing" the corpus fuzz needs: derived programs keep the
;; shape's exact lambda/let/plain-form skeleton and its exact binder names,
;; differing only in some leaf content -- exactly the situation a macro can
;; abstract over.
(define (perturb rng shape)
  (cond
    [(list? shape) (map (lambda (e) (perturb rng e)) shape)]
    [(memq shape GLOBALS) (if (zero? (random 2 rng)) (rnd-choice rng GLOBALS) shape)]
    [(member shape LITERALS) (if (zero? (random 2 rng)) (rnd-choice rng LITERALS) shape)]
    [else shape]))

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

;; check-corpus-invariants! : (Listof Sexpr) -> Void
;; Run macro-compress and its internal asserts, plus the two extra invariants
;; this fuzzer adds: every learned step is strictly compressive, and
;; recomputing the first step's utility from scratch agrees with what
;; macro-compress recorded.  Any failure -- macro-compress's own asserts
;; included -- is re-raised with the corpus attached so a failing check
;; prints something a person can reproduce by hand.
(define (check-corpus-invariants! programs)
  (check-not-exn
   (lambda ()
     (with-handlers ([exn:fail?
                      (lambda (e)
                        (error 'macro-fuzz "corpus ~s: ~a" programs (exn-message e)))])
       (define steps (macro-compress programs 2 2))
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
                  (mdef-template (learned-macro step0)) recomputed)))))))

;; fuzz-corpora : Natural Natural -> Natural
;; Runs `trials` random corpora through check-corpus-invariants!, and returns
;; how many of them macro-compress actually found something to learn on (a
;; sanity count: a generator that stopped sharing structure would make this
;; property vacuous without ever failing).
(define (fuzz-corpora trials seed)
  (define rng (make-rng seed))
  (for/sum ([_ (in-range trials)])
    (define programs (random-corpus rng))
    (check-corpus-invariants! programs)
    (if (pair? (macro-compress programs 2 2)) 1 0)))

;; ---------------------------------------------------------------------------
;; PROPERTY 2 -- the inverse property (un-transcription inverts transcription)
;; ---------------------------------------------------------------------------

(define TPL-DEPTH 4)
(define TPL-MAX-ARITY 2)
(define ARG-DEPTH 2)

;; mint-pvar! : Box Hash Symbol -> Pvar
;; A brand-new pattern-variable index, recorded in `origin` under whichever
;; of 'binder or 'expr it was minted at.  Every reuse of this index anywhere
;; in the template refers back to this same origin, which is exactly what
;; decides how build-args will fill it in below.
(define (mint-pvar! pv-box origin context)
  (define n (unbox pv-box))
  (set-box! pv-box (add1 n))
  (hash-set! origin n context)
  (pvar n))

;; mint-tvar! : Box -> Tvar
(define (mint-tvar! tv-box)
  (define j (unbox tv-box))
  (set-box! tv-box (add1 j))
  (tvar j))

;; gen-expr-pvar : ... (Listof Natural) -> Sexpr
;; A pattern variable in EXPRESSION position: reuse an already-introduced
;; index or mint a fresh one if the arity cap allows.  Reuse of an
;; EXPR-origin index is always safe (its argument is a closed expression --
;; splicing that same value at a second expression position anywhere in the
;; template cannot go wrong, since it does not depend on where it is
;; spliced).  Reuse of a BINDER-origin index is safe only where `pscope`
;; says that binder's own reference-scope reaches -- exactly mirroring a
;; tvar reference, since a binder-position pvar denotes "the name this
;; binder introduces" and referencing it outside the binder's own body (a
;; let's own right-hand side, a sibling subtree, ...) is not a reference to
;; that binder at all, just a same-spelled but unrelated occurrence; H4
;; would require its argument to agree with the binder's, which nothing
;; forces once it is out of scope.  (This was caught by the fuzzer itself:
;; an earlier version of this generator allowed exactly that reuse and
;; produced templates the oracle correctly refused -- see the note below
;; run-template-trial!.)  If the cap is reached and no in-scope reuse
;; exists, fall back to a global rather than manufacture that hazard.
(define (gen-expr-pvar rng pv-box max-arity origin pscope)
  (define count (unbox pv-box))
  (define reusable
    (for/list ([i (in-range count)]
               #:when (or (eq? (hash-ref origin i) 'expr) (memv i pscope)))
      i))
  (cond
    [(and (< count max-arity) (or (zero? count) (zero? (random 2 rng))))
     (mint-pvar! pv-box origin 'expr)]
    [(pair? reusable) (pvar (rnd-choice rng reusable))]
    [(< count max-arity) (mint-pvar! pv-box origin 'expr)]
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
    (for/list ([i (in-range count)] #:when (eq? (hash-ref origin i) 'binder)) i))
  (define can-mint (< count max-arity))
  (define want-pvar? (and (or can-mint (pair? binder-reusable)) (zero? (random 2 rng))))
  (cond
    [(not want-pvar?) (mint-tvar! tv-box)]
    [(and can-mint (or (null? binder-reusable) (zero? (random 2 rng))))
     (mint-pvar! pv-box origin 'binder)]
    [(pair? binder-reusable) (pvar (rnd-choice rng binder-reusable))]
    [else (mint-tvar! tv-box)]))

;; gen-template : ... Natural (Listof Natural) (Listof Natural) Box Box
;;                Natural Hash -> Template
;; A random finished template: expression positions hold globals, literals,
;; pattern variables, a reference to a template binder in `scope`, or (V2) a
;; reference to a binder-position pvar in `pscope`; plain forms have length
;; 2-3; lambda/let binder positions hold a fresh tvar or a (fresh-or-reused)
;; pvar, per gen-binder above.  Both `scope` and `pscope` mirror
;; macro-micro.rkt's hole-scope exactly, including for pvar binders: a let's
;; right-hand side does not see the let's own binder, tvar or pvar alike.
(define (gen-template rng depth scope pscope pv-box tv-box max-arity origin)
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
        (for/list ([_ (in-range n)])
          (gen-template rng (sub1 depth) scope pscope pv-box tv-box max-arity origin))]
       [(lambda)
        (define binder (gen-binder rng pv-box tv-box max-arity origin))
        (define scope^ (if (tvar? binder) (cons (tvar-j binder) scope) scope))
        (define pscope^ (if (pvar? binder) (cons (pvar-i binder) pscope) pscope))
        `(lambda (,binder)
           ,(gen-template rng (sub1 depth) scope^ pscope^ pv-box tv-box max-arity origin))]
       [(let)
        (define binder (gen-binder rng pv-box tv-box max-arity origin))
        (define rhs (gen-template rng (sub1 depth) scope pscope pv-box tv-box max-arity origin))
        (define scope^ (if (tvar? binder) (cons (tvar-j binder) scope) scope))
        (define pscope^ (if (pvar? binder) (cons (pvar-i binder) pscope) pscope))
        (define body (gen-template rng (sub1 depth) scope^ pscope^ pv-box tv-box max-arity origin))
        `(let ([,binder ,rhs]) ,body)])]))

;; renumber-template : Template Hash -> (values Template Hash)
;; Pvars and tvars are renumbered by first occurrence (a plain left-to-right
;; preorder walk of the template's list structure -- which always visits a
;; binder before its body, and a let's binder before its own right-hand
;; side) so both are contiguous from 0, as template-arity assumes.  The
;; `origin` hash (raw index -> 'binder or 'expr) is carried along, remapped
;; to the new indices, since minting is what actually decided each index's
;; origin and that decision must survive renumbering.
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
                 (hash-set! new-origin n (hash-ref origin old))
                 n)))
  (define (remap-tvar old)
    (hash-ref! tvar-map old
               (lambda () (define n (unbox next-tvar)) (set-box! next-tvar (add1 n)) n)))
  (define (walk t)
    (cond
      [(pvar? t) (pvar (remap-pvar (pvar-i t)))]
      [(tvar? t) (tvar (remap-tvar (tvar-j t)))]
      [(list? t) (map walk t)]
      [else t]))
  (values (walk tpl) new-origin))

;; random-finished-template : Pseudo-Random-Generator -> (values Template Hash)
;; Retries until the result is not a bare pattern variable (the identity
;; macro, which template-arity and the real search both refuse to consider).
(define (random-finished-template rng)
  (let loop ()
    (define origin (make-hash))
    (define pv-box (box 0))
    (define tv-box (box 0))
    (define raw (gen-template rng TPL-DEPTH '() '() pv-box tv-box TPL-MAX-ARITY origin))
    (define-values (tpl new-origin) (renumber-template raw origin))
    (if (pvar? tpl) (loop) (values tpl new-origin))))

;; random-closed-expr : Pseudo-Random-Generator Natural -> Sexpr
;; A random argument for an expression-position pattern variable: globals,
;; literals, and small plain forms over them.  No lambdas needed -- these
;; arguments are checked only for whether the template's skeleton can read
;; them back off the expanded site, never asked to bind anything themselves.
(define (random-closed-expr rng depth)
  (define (leaf) (if (zero? (random 2 rng)) (rnd-choice rng GLOBALS) (rnd-choice rng LITERALS)))
  (cond
    [(or (<= depth 0) (zero? (random 2 rng))) (leaf)]
    [else
     (define n (+ 2 (random 2 rng)))
     (for/list ([_ (in-range n)]) (random-closed-expr rng (sub1 depth)))]))

;; build-args : Pseudo-Random-Generator Natural Hash -> (Listof Sexpr)
;; One argument per pattern-variable index, in order.  A pvar whose first
;; occurrence is a binder position gets a bare symbol (so every binder
;; position it fills stays syntactically a binder); an expression-position
;; pvar gets a random closed expression.  Binder-name choices are drawn
;; WITHOUT replacement across the whole arg list: two binder-position pvars
;; that happen to nest (one's scope inside the other's) and share a name
;; would make ordinary lexical shadowing capture a reference the template
;; aimed at the outer one -- a hygiene accident manufactured purely by this
;; generator's naming, not by anything macro-micro.rkt does (caught by an
;; earlier version of this generator, which drew names independently).
(define (build-args rng arity origin)
  (define binder-names (shuffle-by rng '(a b c q)))
  (for/fold ([out '()] [pool binder-names] #:result (reverse out))
            ([i (in-range arity)])
    (case (hash-ref origin i)
      [(binder) (values (cons (car pool) out) (cdr pool))]
      [(expr) (values (cons (random-closed-expr rng ARG-DEPTH) out) pool)])))

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
;; matches back at that site's root.  Any exception (a malformed site, a
;; crash inside valid-sites) is re-raised with the template/args/site
;; attached so a failing check prints a reproducer.
(define (run-template-trial! rng)
  (check-not-exn
   (lambda ()
     (define-values (tpl origin) (random-finished-template rng))
     (define arity (template-arity tpl))
     (define args (build-args rng arity origin))
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
                tpl args site expanded-site))))))

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
