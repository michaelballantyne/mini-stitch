# Plan

Design spec: notes/2026-08-17-1900-mini-stitch-design.md
Algorithm background: notes/2026-08-17-1840-paper-digest.md
Real implementation map: notes/2026-08-17-1844-rust-implementation-map.md

## Current status

Design settled; implementation in progress.

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
- [x] src/search.rkt — branch-and-bound. Matches real binary exactly on
      27/28 basic corpus/arity combos (one verified utility tie) and on
      nuts-bolts/wheels/dials. Caveat for rewrite stage: num_uses counts
      ALL match locations; used/unused split untested by iteration-1 diffs.
- [ ] src/rewrite.rkt — greedy top-down rewrite + mismatch assert (in progress)
- [ ] src/compress.rkt — iteration loop, JSON I/O, CLI (in progress)
- [ ] tests/differential.rkt — compare against real binary on data/basic
      (in progress)
- [ ] Differential pass on all of stitch/data/basic (arity 2 and 3, iterations 1-3)
- [ ] Differential pass on nuts-bolts (realistic scale)
- [ ] src/micro.rkt (in progress) — unoptimized executable spec (~200-300 lines): naive
      worklist enumeration, matching from scratch, utility by actually
      rewriting (bottom-up DP). Keeps only the semantic filters: zero-match
      termination, >=2-programs, free-var ban, capture rejection, argument
      capture (semantic per paper footnote 2). Differential-test micro vs mini
      on tiny corpora as a second oracle.
- [ ] walkthrough.md — end-to-end trace of a small example; present micro
      first, then mini as "the same thing, made fast"
- [ ] Final review pass; README
