# Anti-unification feasibility for stitch-style abstraction search

**Question.** Is a BOTTOM-UP, anti-unification-based formulation of stitch's
abstraction search feasible — i.e. (A) is the space of pairwise
anti-unifications (Plotkin lggs) of corpus subtrees small enough to
materialize, and (B) does stitch's actual winning abstraction lie in / above
that space? This grounds an analysis of whether datalog-style engines fit
library learning.

All code is Python 3 stdlib only (Racket is not installed in this
environment). Parser, de Bruijn shifting, and argument-capture semantics
mirror `/home/user/mini-stitch/src/expr.rkt` (see the smoke tests replicated
from its test suite in the module docstrings / this README's "sanity" note).

## Files

- `au_core.py` — hash-consed arena, stitch-syntax parser, de Bruijn-aware
  `shift`, anti-unification `au` (pairwise and fold-over-set), canonical
  variable renaming, and de Bruijn-aware pattern matching with
  consistent-shifted-argument binding.
- `part_a.py` — per-corpus: corpus stats + the full pairwise-lgg space over
  unique subtrees. Appends one JSON object per run to `results_a.jsonl`.
- `part_b.py` — per-corpus: runs the real stitch binary
  (`stitch/target/release/compress`, `--max-arity=2 --iterations=1`), takes
  the winning abstraction, computes its match set, and checks SEED / CLOSED /
  fv-regeneralized variants / whether the winner generalizes the set-lgg.
  Also scrapes `worklist_steps` from stitch's Stats printout (Part C).
  Appends to `results_b.jsonl`.
- `gen_tables.py` — renders the markdown tables in `results.md` from the two
  jsonl files.
- `results.md` — the tables + observations. `results_a.jsonl` /
  `results_b.jsonl` are the raw per-run records.

## How to run

```sh
# build the stitch binary once (needed for part B only)
cd /home/user/mini-stitch/stitch && cargo build --release

cd /home/user/mini-stitch/experiments/2026-08-18-0337Z-au-feasibility

# Part A, one corpus per invocation (appends to results_a.jsonl):
python3 part_a.py /home/user/mini-stitch/stitch/data/basic/hof.json --name hof
python3 part_a.py .../cogsci/nuts-bolts.json --name nuts-bolts --prefix 50 --budget 500

# Part B (+ worklist_steps for Part C), appends to results_b.jsonl:
python3 part_b.py /home/user/mini-stitch/stitch/data/basic/hof.json --name hof

# regenerate the tables:
python3 gen_tables.py
```

Corpora with stitch's fused-lambda tags (`lam_1`, `$0_1`: simple3/4/5 in
data/basic) are detected at parse time and recorded as skipped.

## Definitions used

- **Unique subtrees S**: arena size after hash-consed parsing (identical
  subtrees anywhere in the corpus are one id).
- **Pairwise lgg**: `au(a, b)` over unordered pairs of distinct unique
  subtrees, de Bruijn-aware: mismatches become variables KEYED by the pair
  `(shift(a, d), shift(b, d))` of shifted subtrees, where `shift(t, m)`
  renames a var free at depth d relative to t's root to sentinel `#d` if
  `d < m` (would capture) else `$(d-m)`. Repeated keys within one lgg share a
  variable — that is what produces multiuse bodies like `(#0 #0 #0)`.
  Variables are canonically renamed by first occurrence afterwards.
  Pairs whose top constructors are incompatible (not app/app or lam/lam)
  anti-unify to a bare variable and are counted as **trivial** without being
  computed.
- **au subproblems**: distinct memoized `au(a,b,depth)` entries + one root
  call per pair — the analogue of a datalog join's intermediate relation.
- **SEED**: winner equals (modulo variable renaming) the pairwise lgg of some
  pair of its match locations. **CLOSED**: winner equals the lgg (au-fold) of
  its entire match set. **+fv**: same after re-generalizing free de Bruijn
  vars in the lgg (stitch bans free vars in bodies, so its winner is forced
  to be more general there). **winner ⊇ set-lgg**: the winner matches the
  set-lgg with the lgg's variables frozen as opaque constants, i.e. the
  winner is at-or-above the lgg in the subsumption lattice.
- **Match set**: unique corpus subtrees the winner's body matches with
  consistent shifted-argument bindings; occurrences (num-paths) reported
  separately. Capturing locations (some bound argument contains a sentinel)
  are counted; checks are run both over all matches and over non-capturing
  ones.
