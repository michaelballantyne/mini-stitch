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
- [ ] Second adversarial review (Opus) of the restructure, focused on the
      micro/paper relationship framing
- [x] Adversarial review (Fable subagent) — notes/2026-08-17-2110; all
      findings fixed: walkthrough section 6 lgg claim corrected, penalty
      divergence signposted, README overclaim fixed, tie enforcement made
      real (unexpected ties and pre-tie mismatches now FAIL), wheels/dials
      added to the suite, deterministic fuzzer checked in (tests/fuzz.rkt),
      stale notes corrected
