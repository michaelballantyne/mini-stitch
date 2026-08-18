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
- [ ] The note's V2: pattern variables in binder positions (my-lambda-style
      capture, hygienically) — enumeration + skeleton only; the oracle
      already understands them.
- [ ] North-star benchmark: learn for/set from expanded folds (needs V2).
- [ ] Adversarial review + fuzz (skeleton/oracle agreement invariants,
      e.g. hand-built matcher vs oracle once one exists).
- [ ] Later rungs per the note: ellipses, literals lists, definition
      contexts (where the alpha-style reasoning provably stops working —
      pearl appendix B.1/B.2 as adversarial tests).
