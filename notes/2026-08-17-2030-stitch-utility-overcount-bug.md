# Discovered: a utility over-count bug in real stitch (multiuse × nested matches)

Found by fuzzing micro-stitch (utility-by-rewriting, the executable spec) against
mini-stitch (which replicates stitch's analytic utility). Verified against the
real binary at submodule rev 0ef5ec7.

## Reproducer

```
corpus: ["(((a a) (a a)) ((a a) (a a)))", "((a f) (a f))"]
flags:  --max-arity=1 --iterations=1
```

Real stitch panics on its own internal assert (rewriting.rs:145):

```
assertion `left == right` failed:  left: 705  right: 604
```

`left` (705) is the cost its rewriter actually produced; `right` (604) is what
the analytic utility promised. Mini-stitch reproduces the same numbers and
fails its own mismatch oracle with a clear message. Micro-stitch computes the
correct answer: compressive 505, utility 504, rewriting to
`(fn_0 (fn_0 (a a)))` / `(fn_0 (a f))` — matching what stitch's own rewriter
produces (the rewriter is right; the utility formula is wrong).

## Cause

Let `X = (Y Y)`, `Y = (Z Z)`, `Z = (a a)`. The pattern `(#0 #0)` (a multiuse
variable) matches at X, both Ys, and all four Zs. The search credits each
match location's marginal utility once per `num_paths` occurrence. But
rewriting X to `(fn_0 Y)` passes ONE copy of Y as the argument — the multiuse
compression deletes the duplicate Y, and with it the nested matches inside the
deleted copy that were already credited.

Stitch's self-overlap correction (`can_self_unify`, utility-phase marginal
subtraction) does not catch this because it deliberately excludes variable
positions: normally that is correct, since the rewriter descends into
arguments and nested matches there survive. It is wrong exactly when the
variable is used more than once, so only one copy of its argument survives.

## Scope

Fuzz statistics (micro vs mini, ~10k random corpora): zero disagreements on
corpora without duplicated-children self-similarity (~3,400 runs); on corpora
biased toward duplicated children, mini/stitch over-counted in 2,003 of 3,831
cases — always an over-count, never an under-count, and never a case where the
true-optimal abstraction differed from stitch's pick in a way stitch's filters
would have excluded. The bug requires a multiuse variable whose argument
contains further matches of the same pattern; none of stitch's own test
corpora (data/basic, cogsci domains) trigger it.

Note stitch's `--utility-by-rewrite` debug flag (rewriting.rs:144) embodies
micro's definition but stack-overflows on the reproducer, so it cannot serve
as an oracle here.

## Decision for mini-stitch

Mini-stitch keeps implementation parity: it reproduces stitch's accounting
faithfully, so it fails on these corpora too — but through its cost-mismatch
oracle with an explanatory error message pointing here (src/rewrite.rkt,
check-cost-mismatch). Micro-stitch documents the divergence as a passing test
("where micro and stitch genuinely disagree, and why"). Fixing the correction
for real (crediting nested matches inside deleted argument copies) is possible
but departs from replication; left as noted future work. Worth reporting
upstream to mlb2251/stitch — Michael's call.
