# Session log: V2, the for/set north-star, and the macro fuzzer

Autonomous session (Claude, 2026-08-18, ~05:20-06:00 UTC). Implementation
and testing were dispatched to sonnet subagents; this session directed,
specified, and reviewed. Everything below is committed on
claude/syntax-rules-macro-learning-xsysex.

## What landed

1. **Expander boundary tests** (src/expander.rkt). The pearl's appendix
   B.1 (a use-site `define` binding capturing a macro-introduced
   reference) and B.2 (a transcribed free identifier whose referent is
   determined only after transcription) now run as checked tests against
   the model expander, reproducing the paper's answers. They are executable
   documentation of where the alpha-style H1-H4 story stops, and the
   ready-made adversarial tests for a future learner that admits
   definition contexts. Verified before writing any V2 code that the
   oracle already handles binder-position pattern variables, mixed
   binders, and still refuses H1 violations -- so V2 needed no oracle
   changes, as the design note predicted.

2. **V2: pattern variables in binder positions** (src/macro-micro.rkt).
   Three semantic touch points, exactly as scoped in the design note:
   hole-scope (a pvar binder extends no tvar scope), skeleton-match (a
   pvar binder takes the site's binder NAME as its argument, by the same
   first-occurrence rule as expression positions; binder paths (1 0) for
   lambda, (1 0 0) for let, matched before the let's right-hand side so
   first-occurrence order agrees with leftmost-first enumeration), and
   expansions (each binding shape now offered with a tvar and with every
   allowed pvar in the binder position). The V1 tests all stand; new
   tests cover the V2 rescue of H1-blocked sites, an end-to-end search
   with hand-derived utility (403), and the mixed tvar-over-pvar shape.

3. **The north-star benchmark passes** (tests/for-set-test.rkt). Four
   hand-expanded curried folds; every body mentions its own iteration
   variable, so no V1 template matches anywhere -- the binder-position
   pvar is load-bearing, not decorative. macro-search at arity 3 recovers

       (sequence-fold (lambda (t0) (lambda (#0) (set-add t0 #1))) (set) #2)

   exactly, in ~4 minutes of naive enumerate-and-oracle work (25
   candidates survive the >=2-program skeleton filter). Utility 1111,
   hand-derived and machine-confirmed; the runner-up (1009) generalizes
   set-add itself to a pattern variable. The fourth program locally
   shadows set-add and is refused outright by the oracle (H2): it
   survives rewriting byte-for-byte, asserted both at the valid-sites
   level and through the rewrite. Every mechanism in the design note is
   exercised by one benchmark, as its addendum F hoped.

4. **Deterministic fuzzer** (tests/macro-fuzz.rkt). Two properties:
   - corpus fuzz: random shared-shape corpora driven through
     macro-compress, whose internal asserts (DP cost = real cost; every
     rewrite expands back alpha-equivalent) do the heavy lifting; plus
     positive-utility and utility-recomputation checks. 400 corpora in
     the suite (~27% learn something), 6000 in a stress run.
   - the inverse property: un-transcription inverts transcription. A
     random finished template's call is expanded to manufacture a site;
     valid-sites must recognize the same template at that site's root.
     This is the property corpus fuzzing cannot see (a skeleton matcher
     that silently MISSED legitimate sites would only ever cost utility,
     never fail an assert). 2000 templates in the suite, 3000 x 6 seeds
     in stress runs.
   No learner bugs found. The two counterexamples that did appear were
   generator artifacts, and both are informative about the semantics:
   reusing a binder-position pvar OUTSIDE its binder's scope is a
   hygiene violation the oracle correctly refuses (the reuse is a
   same-spelled but unrelated occurrence); and two nested binder-position
   pvars handed the SAME name argument let ordinary shadowing capture a
   reference aimed at the outer one -- also correctly refused. Both are
   documented where they live, in the generator's comments.

5. **Related-work survey** (notes/2026-08-18-0533). Headline: nothing
   found occupies "search-driven discovery of hygienic syntactic
   abstractions." Resugaring inverts KNOWN sugar; Macrofication (ESOP
   2016) reverse-matches ONE known macro; stitch/babble/DreamCoder invent
   only functions and so never check hygiene of what they invent. Nominal
   anti-unification (Baumgartner & Kutsia) is the most promising formal
   vocabulary for grounding un-transcription. Close reads recommended:
   Pombrio & Krishnamurthi ICFP 2015; the nominal anti-unification line.

6. **Three long-term directions analyzed** (notes/2026-08-18-0539), from
   Michael: Racket's own expander as the outermost differential oracle;
   real Racket corpora (both framings gated on ellipses); and
   functions-AND-macros learning -- including the observation that in the
   current setting macros strictly dominate functions, so compression
   alone will never emit a function, and the "function-shaped template"
   criterion that fixes it, plus the for/list-over-map layering benchmark.

## State of the test suite

raco test over src/expander.rkt, src/macro-micro.rkt, tests/macro-fuzz.rkt,
tests/micro-test.rkt: 29 tests pass in seconds. tests/for-set-test.rkt is
the deliberate outlier (~4 minutes, the naive search doing naive search);
run it knowingly. tests/differential.rkt and tests/fuzz.rkt (the
lambda-calculus side) are unchanged.

## What did NOT happen, and is next

- **Adversarial review of V2 + the new tests** -- cut when the session was
  wrapped early; it is the top of the stack now. Reviewer bait I already
  see: the enumeration's binder-pvar productions may propose templates
  whose binder-pvar is never referenced (junk arity spent re-binding a
  name nothing uses -- e.g. (lambda (#0) #1) as a lambda re-constructor
  saving 2 per site; legitimate under the cost model, but is it wanted?);
  the constant-argument and duplicate-argument filters from the design
  note's section 7 are still not implemented in macro-micro (deliberate
  so far, worth a reviewer's judgment); fuzz property 1 runs
  macro-compress twice per corpus (harmless, sloppy).
- Ellipses (the big rung), function-shaped classification (cheap, high
  story-value), define/letrec + the layering benchmark, the Racket
  expander as outer oracle -- per the directions note.
