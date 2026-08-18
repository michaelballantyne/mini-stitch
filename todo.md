# Plan

Design spec: notes/2026-08-17-1900-mini-stitch-design.md
Algorithm background: notes/2026-08-17-1840-paper-digest.md
Real implementation map: notes/2026-08-17-1844-rust-implementation-map.md

## Current status

COMPLETE. All modules implemented, documented, and differentially validated
against the real binary (87 runs: 85 MATCH / 2 TIE / 0 FAIL; nuts-bolts full
match). Micro-stitch oracle agrees everywhere feasible and uncovered a genuine
utility over-count bug in real stitch (see notes/2026-08-17-2030). Possible
future work: report the stitch bug upstream (Michael's call); optionally add
fused-lambda tags for simple3/4/5 coverage; more cogsci domains.

## Steps

- [x] Read paper; digest core algorithm (notes/2026-08-17-1840)
- [x] Map real Rust implementation; essential vs incidental (notes/2026-08-17-1844)
- [x] Settle design with Michael: Racket, implementation parity, simple
      architecture (no zipper tables), basic + nuts-bolts scale, HtDP style
- [x] Build real stitch binary for differential testing (stitch/target/release)
- [x] src/expr.rkt — corpus arena, hash-consing, parse/print, analyses,
      argument extraction with shift/sentinel. Parity verified vs Rust:
      parser quirks, sentinel/shift semantics, expands-to from unshifted
      node; corpus costs match real binary on all of data/basic + nuts-bolts.
      Fused-lambda tags unsupported (simple3/4/5 out of scope).
- [x] src/pattern.rkt — patterns as trees with holes, match machinery,
      self-overlap detection (replaces ziptrie with ordinary unification)
- [x] src/search.rkt — branch-and-bound. (Interim figure at this stage was
      27/28 basic corpus/arity combos at iterations=1, plus nuts-bolts/
      wheels/dials spot checks; the final reproducible figures are the
      differential suite's, below. wheels/dials are now in the checked-in
      suite at arity 2.)
- [x] src/rewrite.rkt — greedy top-down rewrite + mismatch assert
- [x] src/compress.rkt — iteration loop, JSON I/O, CLI
- [x] tests/differential.rkt — compare against real binary on data/basic
- [x] Differential pass: 21 basic corpora x {arity 2,3} x {iters 1,3} plus
      nuts-bolts/wheels/dials = 87 runs: 85 MATCH / 2 TIE (verified genuine) /
      0 FAIL. Ties excuse only themselves; unexpected ties fail the suite.
- [x] Differential pass on nuts-bolts: full match incl. all 250 rewritten
      programs; mini ~1s of work per run
- [x] src/micro.rkt — unoptimized executable spec (241 loc + extensive
      comments/tests): naive enumeration, matching from scratch, utility by
      rewriting (bottom-up DP). Agrees with mini AND the real binary on all
      tested corpora. Fuzzing micro-vs-mini uncovered a genuine utility
      over-count bug in REAL stitch (multiuse x nested matches; stitch
      panics on its own assert) — see
      notes/2026-08-17-2030-stitch-utility-overcount-bug.md.
- [x] walkthrough.md — the paper's Section 2 running example traced through
      micro then mini, with real measured numbers; anti-unification lens; coda
      on known divergences
- [x] Final review pass; README
- [x] Micro-first restructure (Michael's direction, 2026-08-18): micro made
      fully standalone — new src/ast.rkt (shared AST + cost model), micro
      scrubbed of mini references and of parsing/printing, examples as AST
      values, comparisons moved to tests/micro-test.rkt + tests/support.rkt,
      paper relationship stated precisely (implements the paper's OBJECTIVE
      via its discarded "naive approach", NOT Algorithm 1). See
      notes/2026-08-18-0246-micro-first-restructure.md.
- [x] Second adversarial review (Opus) of the restructure —
      notes/2026-08-18-0300-adversarial-review-2.md. All findings fixed:
      micro's paper framing corrected (Algorithm 1 is Appendix A; the
      capture-locations-count-as-matches rule is stitch's, diverging from the
      paper's discard-from-Matches, now signposted as a second deviation; the
      >=2-programs rule attributed to the paper's own Section 6; corpus-prims
      and zero-match honesty; the cost_{alpha=0} deviation noted as
      load-bearing — literal Eq. 8 flips the paper's own example); micro
      header regains the over-count pointer; delta-section errors in
      search.rkt/expr.rkt fixed; ast.rkt arena forward-ref removed;
      support.rkt term->string guarded; stale counts/notes updated.
      Also: micro-search's for*/fold simplified to append-map + partition +
      two-accumulator fold (Michael's question).
- [x] Adversarial review (Fable subagent) — notes/2026-08-17-2110; all
      findings fixed: walkthrough section 6 lgg claim corrected, penalty
      divergence signposted, README overclaim fixed, tie enforcement made
      real (unexpected ties and pre-tie mismatches now FAIL), wheels/dials
      added to the suite, deterministic fuzzer checked in (tests/fuzz.rkt),
      stale notes corrected

## New direction (2026-08-18): learning hygienic syntax-rules macros

Design: notes/2026-08-18-0323-syntax-rules-learning-design.md (plus its
addendum connecting to the "Hygienic macro expansion explained" pearl).
The stitch objective, asked about syntactic abstractions: which single
syntax-rules macro compresses an s-expression corpus most, where using it
means replacing a subexpression by a call that hygienically expands back.

- [x] src/expander.rkt — the pearl's appendix model expander (marks + scope
      graphs + syntax-rules), verbatim except three additions it needs to
      serve as the semantic oracle: lambda, applications, unbound
      identifiers as globals (+ boolean literals). Its own Fig. 12 test kept.
- [x] src/macro-micro.rkt — micro.rkt's structure for macros, smallest
      version: expressions only (lambda/let bind; if and primitive calls are
      plain forms), one rule, flat patterns, template binders only (the
      note's V1), no optimizations. Matching = a hygiene-blind skeleton
      matcher + check-by-expansion against the model expander per site, so
      the note's H1-H4 conditions are enforced without being implemented.
      Utility by rewriting (micro's DP), with a whole-program
      expand-and-alpha-compare assert after every rewrite. Iteration works
      over corpora containing earlier macros' calls; learned names are
      withheld from templates (no macros expanding to macro calls).
- [x] The note's V2: pattern variables in binder positions (my-lambda-style
      capture, hygienically) — enumeration + skeleton only; the oracle
      already understood them, verified empirically before implementing.
- [x] North-star benchmark: learn for/set from expanded folds —
      tests/for-set-test.rkt PASSES: exact recovery at arity 3 (~4 min of
      naive search), H2-shadowed program refused byte-for-byte, utility
      1111 hand-derived. Session log: notes/2026-08-18-0557.
- [x] Fuzz: tests/macro-fuzz.rkt — corpus fuzz through macro-compress's
      internal asserts, plus the inverse property (un-transcription
      inverts transcription: a template must match back at the root of
      its own call's expansion — catches silently LOST matches, which
      corpus fuzzing can't see). No learner bugs; two generator-side
      hygiene hazards found and documented in place.
- [x] Pearl appendix B.1/B.2 checked in as expander tests (the boundary
      where alpha-style hygiene accounts stop; future adversarial tests
      for definition contexts).
- [x] Related-work survey (notes/2026-08-18-0533): the intersection
      "search-driven discovery of hygienic syntactic abstractions"
      appears unoccupied; nearest are Macrofication (known-macro reverse
      matching) and resugaring (known sugar); nominal anti-unification is
      the formal vocabulary to borrow.
- [x] Adversarial review of V2 + new tests (Opus reviewer; all findings
      applied — notes/2026-08-18-1430. Headline: narrowing the oracle's
      error handler surfaced a real expander bug (unguarded binder
      positions) the blanket handler had been hiding. Also: DP memoized,
      skeleton shape-judgment tightened, check-corpus made a real
      well-formedness pass, fuzzer coverage gaps (H2/H3/V2-capture/
      lambda-args) closed, two proposed filters refuted by measurement.)
- [x] Ellipses, both stages (design notes/2026-08-18-1324 + amendment;
      expander: depth-1 trailing ellipses, hygiene-under-iteration
      tests, spot-checked against Racket's syntax-rules; learner: one
      (ellip sub) per template with (svar) as its own node — sequence
      args are ordinary trailing call args, oracle/rewriter/DP
      unchanged. Learns (m x ...) => (f (g x) ...) across three
      arities. Finding: zero-iteration matches satisfy structural
      pruning vacuously and explode the search; pre-filter now requires
      an iterating witness — see skeleton-programs.)
- [x] Fuzzer stage 3: ellip templates in the inverse property (~33% of
      trials; its counterexample became N4 of the non-injectivity
      catalogue, notes/2026-08-18-1541).
- [x] The binder mask (review finding 5): expr-children/expr-positions/
      corpus-facts/reject?/rewrite-program now take the library and walk
      a learned macro's calls correctly -- the head is not an
      expression, binder-position arguments are excluded like lambda's
      binder. Mask derived from the template (template-binder-mask), no
      mdef change.
- [ ] Function-shaped classification (cheap): macros strictly dominate
      functions under the compression objective, so report WHY each
      learned template needed to be a macro; later, learn functions AND
      macros with define/letrec + the for/list-over-map layering
      benchmark. Analysis: notes/2026-08-18-0539.
- [ ] Combined benchmark: a variadic binder-ful corpus (my-when/begin
      style bodies under a lambda) exercising V2 and ellipses together.
- [ ] Later rungs per the notes: literals lists, non-trailing/multiple
      ellipses (will meet the zero-iteration pruning interaction again),
      Racket's own expander as the outermost differential oracle,
      core-Racket then surface-Racket corpora, definition contexts
      (B.1/B.2 as adversarial tests), recursive macros.
