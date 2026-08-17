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
- [ ] src/expr.rkt — corpus arena, hash-consing, parse/print, analyses,
      argument extraction with shift/sentinel (verify parity details vs Rust)
- [ ] src/pattern.rkt — patterns as trees with holes, match machinery,
      self-overlap detection
- [ ] src/search.rkt — cost model, utility, upper bound, prunings, arity-zero
      priming, branch-and-bound loop
- [ ] src/rewrite.rkt — greedy top-down rewrite + mismatch assert
- [ ] src/compress.rkt — iteration loop, JSON I/O, CLI
- [ ] tests/differential.rkt — compare against real binary on data/basic
- [ ] Differential pass on all of stitch/data/basic (arity 2 and 3, iterations 1-3)
- [ ] Differential pass on nuts-bolts (realistic scale)
- [ ] walkthrough.md — end-to-end trace of a small example
- [ ] Final review pass; README
