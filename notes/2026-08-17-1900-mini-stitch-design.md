# Mini-stitch design

Decisions settled with Michael on 2026-08-17, plus module-level design. This is the
working spec for implementation. Companion notes: `2026-08-17-1840-paper-digest.md`
(the algorithm) and `2026-08-17-1844-rust-implementation-map.md` (the real system;
cited below as "map §N").

## Decisions

1. **Language**: Racket (plain `#lang racket`, not typed), small focused modules.
2. **Fidelity**: *implementation parity* — match real stitch's semantics and outputs
   exactly on its default configuration, so we can differentially test against the
   submodule binary (`stitch/target/release/compress`, already built) on stitch's
   own corpora. Where paper and implementation diverge (rewrite strategy, &i vs
   sentinel capture handling, LambdaUnify vs incremental matching), follow the
   implementation. Write code in the paper's vocabulary where possible.
3. **Architecture**: skip stitch's interned zipper tables. Keep: one hash-consed
   corpus arena, explicit incremental match-location lists, patterns as actual
   trees with holes. Argument-at-location computed by walking the subtree along the
   hole's path, memoized on (location, path).
4. **Scale target**: all of `stitch/data/basic` for correctness + `nuts-bolts`
   (cogsci) at realistic scale. Minutes acceptable there.
5. **Style**: How To Design Programs. Every function gets a signature line, a
   purpose statement, and (where helpful, not huge) examples as a `module+ test`
   block immediately after the function. Each module opens with an explanatory
   comment describing its role and data definitions. A separate walkthrough file
   traces a small example end-to-end in the implementation's own language.

## Simplifications relative to real stitch (beyond map §7)

- Hardcode default config: `max-arity` (default 2) and `iterations` are the only
  knobs. Single candidate per iteration (best-so-far, no donelist). Depth-first
  hole choice (last-added hole). Uniform integer cost model as named constants
  (app = lam = 1, var = ivar = prim = 100; new abstraction symbol costs 100).
  `structure_penalty` fixed at 1 → utility = compressive − body-size, all integers.
- No task/weight machinery: utility is a plain sum over locations weighted by
  occurrence counts (exact parity for unlabeled corpora, which is all we accept).
  KEEP single-task pruning's default shadow: an abstraction must match in ≥ 2
  distinct programs (per-node "which programs contain this subtree" sets).
- No ziptrie: with tree-shaped patterns, self-overlap detection is ordinary
  pattern-vs-own-proper-subtree matching with variables/holes as wildcards.
- I/O: corpus = JSON array of program strings, parsed as s-expressions. Output:
  abstraction body/arity/utility, final cost, rewritten programs. One entry point
  (compress); no follow-mode, no separate rewrite binary.

Must NOT be cut (tempting but load-bearing): arity-zero priming + single-use
pruning; the de Bruijn shift machinery for arguments (downshift on extraction,
sentinel capture marking, shift fixup during rewrite); self-overlap utility
correction; the two runtime asserts (rewrite cost-mismatch check and upper-bound
monotonicity).

## Module layout

```
src/expr.rkt      corpus representation: nodes, hash-consing, parse/print,
                  analyses (cost, free vars, occurrence counts, program sets),
                  argument extraction (shift + sentinel)
src/pattern.rkt   patterns (trees with holes), paths, match-location machinery,
                  self-overlap detection
src/search.rkt    cost model constants, utility + upper bound, the two dominance
                  prunings, arity-zero priming, branch-and-bound loop
src/rewrite.rkt   greedy top-down rewrite with shift rules + mismatch assert
src/compress.rkt  iteration loop, JSON I/O, CLI entry point
tests/            rackunit unit tests live in module+ test blocks in src/;
tests/differential.rkt   runs mini-stitch and the real binary on the same
                  corpora and compares results
walkthrough.md    end-to-end trace of a small example (repo root)
```

## Data definitions

### Corpus (expr.rkt)

A *Node* is one of:
- `(prim symbol)` — a DSL primitive
- `(var i)` — de Bruijn variable `$i`, i ≥ 0
- `(ivar i)` — abstraction variable `#i` (only in abstraction bodies/args-with-
  capture, never in parsed programs)
- `(app fun arg)` — application; `fun`, `arg` are Idx
- `(lam body)` — lambda; `body` is an Idx

An *Idx* is a natural number indexing the corpus arena. The arena is append-only
and child-first: children always have smaller indices. `add-node!` interns: adding
a node equal to an existing one returns the existing Idx. Identical subtrees
anywhere in the corpus are therefore the same Idx, and subtree equality is `=`.

*corpus-span*: the range of Idxs created by parsing the programs (before any
shifted argument copies are added). Only these can be match locations. Analyses:
- `cost : Corpus Idx -> Natural` (memoized recursive)
- `free-vars : Corpus Idx -> (Setof Natural)` (memoized)
- `num-paths : Corpus Idx -> Natural` — occurrences of this unique subtree across
  the corpus counting DAG sharing (map §1); defined on corpus-span
- `programs-with : Corpus Idx -> (Setof Natural)` — which program roots contain it

### Argument extraction (expr.rkt)

A *Path* is a list of `'fun`/`'arg`/`'body` steps from a match root down into it.

`(extract-arg corpus loc path) -> Arg` where Arg has:
- `unshifted` — Idx of the original subtree at that position
- `shifted` — Idx of the subtree as seen from the match root: variables bound by
  lambdas crossed on `path` are replaced by *sentinel* ivars, and remaining free
  variables are downshifted by the number of crossed lambdas
- `shift` — the (non-positive) downshift amount
- `captures?` — whether any sentinel appears (argument would capture a body binder)

PARITY NOTE: mirror the exact sentinel representation and shift arithmetic of
`insert_arg_ivars` (stitch `egraphs.rs:50-73`) and the Lam case of `get_zippers`
(`compression.rs:1297-1334`), including how `expands_to` treats a sentinel-rooted
argument (check `expansion.rs`). Verify against the Rust before implementing.

### Patterns (pattern.rkt)

A *PatternTree* is one of: `'hole`, `(pivar i)`, and the Node shapes with
PatternTree children (patterns are small; no interning needed).

A *Pattern* bundles:
- `tree` — the PatternTree body
- `holes` — list of Paths, most recently created first (depth-first hole choice =
  take the head)
- `ivar-uses` — for each ivar, the list of Paths where it occurs (first path is
  the canonical one)
- `matches` — sorted list of Idx (match locations, unique subtrees)
- `body-utility` — summed local cost of the concrete constructors in `tree`
- `upper-bound` — see search.rkt

The initial pattern is a single hole matching every node in corpus-span.

### Search (search.rkt)

Cost model: `COST-APP = COST-LAM = 1`, `COST-VAR = COST-IVAR = COST-PRIM = 100`,
`COST-NEW-PRIM = 100`.

Priority queue (`data/heap`) keyed by upper-bound, max first. Loop = Algorithm 1
of the paper with stitch's pruning set (map §2, §6):
1. pop; skip if upper-bound ≤ best utility so far
2. choose hole = head of `holes`
3. group matches by the head constructor of the (shifted) argument at that hole;
   each group is a syntactic expansion (lam adds 1 hole, app adds 2, var/prim 0)
   — expansion to a var free at pattern top level is pruned (map §4)
4. ivar expansions: reuse `#i` (keep locations where this hole's shifted arg =
   `#i`'s canonical shifted arg), or fresh ivar if arity < max-arity
5. prune each candidate: zero matches (implicit in groupby); single-use (single
   unique location, no free vars — arity-0 dominates); single-task (matches in
   < 2 distinct programs); argument capture (some ivar sees the same no-free-vars
   shifted arg at every location); redundant argument (two ivars see identical
   shifted args at every location); upper bound ≤ best
6. no holes left → exact utility; update best

Utility (map §3): per location,
`util-once = body-utility − (COST-NEW-PRIM + COST-APP·arity) + Σ_ivars (uses−1)·cost(arg)`,
autorejected to 0 if any arg at that location `captures?`. Then self-overlap
correction (bottom-up over locations, subtracting corrected child-match marginals
reachable at internal non-variable positions where the pattern can match inside
itself, clamped at 0; locations ending ≤ 0 are *unused*). Compressive utility =
Σ util-once(loc)·num-paths(loc) over used locations; total utility = compressive −
body-utility. Upper bound = Σ max(0, (cost(loc) − COST-NEW-PRIM)·num-paths(loc)).

Arity-zero priming: before search, every corpus-span node with no free vars
matching in ≥ 2 programs scores `num-paths·(cost − COST-NEW-PRIM) − cost`; the
best positive one seeds best-so-far. (Arity-0 can be the final answer.)

Asserts: child upper-bound ≤ parent upper-bound; finished utility ≤ its pattern's
upper-bound.

### Rewrite (rewrite.rkt)

Greedy top-down per program over the ORIGINAL corpus (map §5): at node n, if n is
a used match location, emit `(fn_k arg1 ... argk)` (curried apps), recursing into
each argument's `unshifted` subtree while pushing a shift rule when `shift ≠ 0`:
any var whose binder lies at/above the rule's depth cutoff gets shifted. Assert:
cost(rewritten corpus) = cost(original) − compressive utility, exactly.

### Iteration (compress.rkt)

For iteration k: build corpus, search, rewrite with `fn_k` (a new prim), feed
rewritten programs into a fresh corpus for iteration k+1. Stop after `iterations`
or when no abstraction has positive utility. Report per-iteration: body (printed
in stitch's format, e.g. `(#0 #0 #0)`, curried apps flattened, `(lam ...)`),
arity, utility, corpus cost before/after.

## Differential testing

`tests/differential.rkt`: for each corpus in `stitch/data/basic/*.json` (and
`nuts-bolts` at the end), run the real binary
(`stitch/target/release/compress FILE --max-arity=A --iterations=N`) and
mini-stitch with the same settings; parse stitch's `out.json`; compare
per-iteration abstraction body string, arity, and rewritten corpus cost, plus
final total cost. Utility ties could make body strings differ while costs agree —
if observed, compare costs strictly and report body mismatches for review.

Open parity details to verify against the Rust during implementation:
1. sentinel ivar representation and its interaction with `expands_to` and
   ivar-equality
2. exact tie-breaking (does stitch keep first-found or last-found on equal
   utility?) — affects body-level comparison only
3. stitch's printed body format and out.json field names
4. whether `num-paths` for the upper bound uses `cost_of_node_all` before or
   after shifted copies are added (map §1 says before; verify)

## Addendum (settled later on 2026-08-17): micro-stitch

Also build `src/micro.rkt`: a semantically-equivalent, unoptimized executable
spec (~200-300 lines) for the smallest corpora only. Design:
- Utility BY REWRITING: utility = cost(P) - cost(Rewrite(P,A)) - cost(A), with
  the paper's bottom-up accept/reject DP as the rewriter. This eliminates the
  analytic utility formula, multiuse accounting, overlap correction, and
  unused-locations bookkeeping.
- The paper's naive enumeration: FIFO worklist from ??, all hole productions,
  match locations recomputed from scratch with a LambdaUnify-style matcher.
  Plain trees + equal?; no hash-consing, no incremental match lists, no
  priority queue, no upper bound.
- Retained because they are SEMANTIC, not speed: zero-match pruning (finiteness/
  termination), >=2-distinct-programs filter, free-var-in-body ban, capture
  rejection of match locations, de Bruijn shift machinery, and ARGUMENT CAPTURE
  pruning (paper footnote 2: stitch optimizes subject to all argument captures
  applied, so dropping it could yield a different, slightly better abstraction
  than real stitch).
- Dropped as genuinely dominance-safe: single-use pruning, arity-zero priming
  (arity-0 candidates arise naturally). [Update, post-implementation: the plan
  also listed redundant-argument elimination here, but micro.rkt KEEPS it — it
  is dominance-safe so dropping it would not change the optimum, but keeping
  it costs a few lines and makes micro's tie-breaking agree with mini more
  often. See micro.rkt's header.]
- Role: second differential oracle (micro vs mini on tiny corpora) alongside
  mini vs real binary; pedagogical baseline. Walkthrough presents micro first,
  then mini as "the same thing, made fast". Shares parser/printer with mini
  (import from expr.rkt).
