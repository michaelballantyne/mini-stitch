# Search-order experiment: does branch-and-bound exploration order matter?

**Question.** mini-stitch's branch-and-bound (`src/search.rkt`) uses a
best-first worklist (max-heap on the utility upper bound) plus a global
best-so-far cutoff. A Datalog/relational reformulation could only run the
search level-synchronously — FIFO/BFS-ish order, cutoff updated between
strata. Does exploration order actually change how many patterns get
explored?

**Method.** `src-instr/` is a copy of `/home/user/mini-stitch/src/*.rkt` with
`search.rkt` instrumented (the only file modified):

- counters: `pops-expanded` (patterns popped that survive the cutoff
  re-check and get expanded), `pushed` (patterns added to the worklist,
  initial pattern included), `considered` (calls to `consider!`),
  `finished` (hole-free patterns scored via `finish`); read them with
  `(search-stats)` after a `search` call;
- a `#:mode` keyword on `search`: `'best` (original max-heap), `'fifo`
  (two-list queue — approximates level-synchronous order, since children
  are pushed as generated), `'lifo` (stack — DFS). All pruning logic,
  including the cutoff re-check at pop and the bound<=cutoff check at push,
  is identical in every mode; only the pop order differs.

`'best` mode is behaviorally identical to the original: `raco test
src-instr/search.rkt src-instr/compress.rkt src-instr/expr.rkt
src-instr/pattern.rkt` passes (52 tests).

**Corpora.** All of `stitch/data/basic/*.json` except simple3/4/5 (fused
lambda tags — mini-stitch's parser rejects them by design), plus
`stitch/data/cogsci/{nuts-bolts,wheels,dials}.json`. One `search` call per
(corpus, mode) at max-arity 2; the basic corpora additionally at max-arity 3.

**To rerun:**

```
raco make run-one.rkt          # optional, speeds up subprocess startup
rm -f results.csv
ARITY3=1 bash sweep.sh         # ARITY3=0 to skip the arity-3 basic sweep
racket aggregate.rkt           # prints the markdown tables in results.md
```

Each (corpus, mode) runs as its own subprocess under `timeout 180`, appending
one row to `results.csv` as it completes (the sweep resumes where it left off
if interrupted; delete results.csv to start fresh).

**Files.**

- `src-instr/` — instrumented copy of the sources (only `search.rkt` differs)
- `run-one.rkt` — one (corpus, mode, arity) run, prints one CSV row
- `sweep.sh` — the full sweep, incremental, per-run timeout
- `aggregate.rkt` — results.csv -> markdown tables + parity checks
- `results.csv` — raw rows
- `results.md` — tables, ratios, observations
