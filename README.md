# mini-stitch

> [!WARNING]
> 100% AI slop! Was helpful to me for understanding stitch though.

A miniature replication, in Racket, of **[stitch](https://github.com/mlb2251/stitch)** —
the library-learning system of Bowers et al., *[Top-Down Synthesis for Library
Learning](https://arxiv.org/abs/2211.16605)* (POPL 2023). Given a
corpus of lambda-calculus programs, it finds the abstraction that compresses the
corpus most, rewrites the corpus to use it, and repeats.

The goal is to exhibit the core algorithm and the optimizations that are
actually load-bearing, and to strip away everything else. Parallelism and
constant-factor engineering are deliberately out of scope; the de Bruijn
machinery, the branch-and-bound, and stitch's exact utility accounting are not.

The code was written by Claude Code and is **differentially tested against
the real stitch binary**: 87 runs over stitch's own corpora, comparing
abstraction bodies, arities, utilities, use counts, costs and rewritten programs.

**Start with [`walkthrough.md`](walkthrough.md)**, which traces the paper's own
Section 2 running example end to end through both implementations.

## Layout

```
src/ast.rkt         the shared language: the lambda-calculus AST structs and
                    stitch's cost model. Read this first (one minute).
src/micro.rkt       micro-stitch: the executable SPECIFICATION, standalone.
                    Naive enumeration, matching from scratch, utility computed
                    by actually rewriting the corpus. Slow on purpose,
                    readable. Read this second.

src/expr.rkt        mini-stitch begins here: the hash-consed corpus arena,
                    parser/printer, the bottom-up analyses (cost, free vars,
                    occurrence counts, program sets), and argument extraction
                    with de Bruijn shifting and capture sentinels
src/pattern.rkt     partial abstractions: trees with holes, hole paths,
                    expansion, self-overlap detection
src/search.rkt      branch and bound: the upper bound, the prunings, the
                    analytic utility, arity-zero priming, the worklist
src/rewrite.rkt     greedy top-down rewriting with de Bruijn shift rules, plus
                    the cost-mismatch oracle
src/compress.rkt    the iteration loop, JSON I/O, command-line entry point

tests/support.rkt   string<->AST bridges and helpers for the test files
tests/micro-test.rkt     holds micro and mini to the same answers, and both
                    to the real binary
tests/differential.rkt   runs mini-stitch and the real binary on the same
                    corpora and compares; unit tests live in `module+ test`
                    blocks beside the code they test
tests/fuzz.rkt      deterministic seeded fuzzer: mini's claimed utility
                    checked against micro's by-rewriting measurement on
                    random corpora (how the stitch bug was found)
notes/              design notes, a digest of the paper, a map of the Rust
                    implementation, and the write-up of a bug found in stitch
stitch/             git submodule: the real stitch implementation
walkthrough.md      the worked example: micro first, then mini
todo.md             the plan
```

micro and mini are two implementations of the same specification, sharing only
the AST and cost model (`src/ast.rkt`). micro is written to be read on its own,
with no reference to mini; it says what the answer *is*. mini computes the same
answer fast (held to micro's answers by `tests/micro-test.rkt`), matching real
stitch answer for answer — same abstractions, utilities, costs, and rewritten
programs on the default configuration — though not step for step: the
worklists differ, which is visible exactly once, as a documented equal-utility
tie.

## Quickstart

A corpus is a JSON array of program strings — stitch's `programs-list` format,
which is what everything in `stitch/data/basic` is.

```
racket src/compress.rkt stitch/data/basic/hof.json --max-arity 2 --iterations 3
```

Run the whole test suite (unit tests plus the differential comparison):

```
raco test src/ tests/
```

The differential tests need the real binary. If the submodule is not checked out
yet, `git submodule update --init`, then:

```
cd stitch && cargo build --release
```

## Results

`raco test src/ tests/` — 83 test cases, all passing, including:

* **87 differential runs**: 21 corpora of `stitch/data/basic` × {max-arity 2, 3}
  × {1, 3 iterations}, plus `cogsci/nuts-bolts.json` (250 programs, arity 2, 3
  iterations) and `cogsci/wheels.json` / `cogsci/dials.json` (arity 2, 1
  iteration). **85 MATCH, 2 TIE, 0 FAIL.** A tie excuses only itself: any
  other mismatch in the same run, or a tie not on the known-ties list, fails
  the suite.
* **a deterministic fuzzer** (`tests/fuzz.rkt`, seeded): mini's claimed utility
  checked against micro's by-rewriting measurement on hundreds of random
  corpora per run — zero disagreements on unbiased corpora, and on
  self-similar corpora the known stitch over-count reproduces, always as an
  over-count, never an under-count.
* `nuts-bolts` matches in full: every abstraction, every utility, every one of
  the 250 rewritten programs, at ~3 s for three iterations.
* micro-stitch agrees with mini-stitch, and with the real binary, on every
  corpus small enough for it to finish — the sole exception being the corpus
  family where real stitch's own utility accounting is wrong (below), which is
  itself a passing test.

## Known deviations and limitations

* **Fused-lambda tags.** stitch's parser accepts `lam_1` / `$0_1`, which make
  tagged variables distinct nodes even though the tags are inert by default.
  mini-stitch has no tag field and raises a clear error instead of silently
  conflating them, so `simple3`, `simple4` and `simple5` are out of scope.
* **One genuine tie.** On `ctx_thread_twice` at max-arity 3, two abstractions
  have exactly equal utility (1213) and the two systems reach them in different
  orders. The harness reports a differing body at equal utility as TIE, never as
  a pass — see `known-ties` in `tests/differential.rkt`.
* **A bug in real stitch.** Fuzzing micro against mini found a corpus family
  where stitch's analytic utility over-counts, and stitch aborts on its own
  cost-mismatch assertion. mini-stitch reproduces the arithmetic faithfully and
  therefore fails there too, via its own oracle; micro-stitch gets it right.
  See `notes/2026-08-17-2030-stitch-utility-overcount-bug.md`.
* **Scale.** Targeted at `data/basic` for correctness and `nuts-bolts` for
  realistic scale — seconds to minutes, not the real system's milliseconds.
  Single-threaded, with no interned zipper tables and no ziptrie.
* **Configuration.** Only `--max-arity` and `--iterations` are exposed;
  everything else is fixed at stitch's defaults (one candidate per iteration,
  depth-first hole choice, structure penalty 1, each program its own task).

## License

MIT — see [`LICENSE`](LICENSE). The vendored `stitch/` submodule is separately
licensed (MIT, © 2021 Matthew Bowers) and is not covered by this repository's
license.

Most of this code was generated by Claude, and under current US Copyright Office
guidance machine-generated material without substantial human authorship may not
be copyrightable at all. The license is offered to remove doubt about what you
may do with the code, not to assert a strong claim over it: use it freely, and
there is no warranty either way.

## Style

The code follows the *How to Design Programs* conventions: every function has a
signature line and a purpose statement, examples live in `module+ test` blocks
next to the function they exercise, and each module opens with a comment
explaining its role and its data definitions. Comments citing `file.rs:NN` point
into the stitch submodule and record where a decision came from — those parity
notes are how the replication was kept honest.
