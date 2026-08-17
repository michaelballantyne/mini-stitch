# Map of the real stitch Rust implementation

Produced by a subagent that read all of `stitch/src/` plus the pinned `lambdas`
dependency (rev 2c9bfd0, which supplies `ExprSet`/`Node`/cost/analysis machinery).
Purpose: identify the essential algorithm vs incidental complexity, to design the
miniature reimplementation. Paths relative to `stitch/src/` unless marked `[lambdas]`.

## 1. Core data structures

### Corpus representation: one hash-consed arena
- `Node`: `Prim(Symbol)`, `Var(i32, Tag)` (de Bruijn `$i`), `IVar(i32)` (abstraction
  variable `#i`), `App(Idx, Idx)`, `Lam(Idx, Tag)` — `[lambdas] expr.rs:22-30`.
  Tags are a fused-lambda extension; a mini version can drop them.
- `ExprSet` is a flat arena `Vec<Node>` with structural hashing:
  `struct_hash: Option<FxHashMap<Node, Idx>>` — `[lambdas] expr.rs:33-39`. `add()`
  returns an existing `Idx` when the node is already present. Order is `ChildFirst`,
  so `Idx` is a bottom-up topological index.
- The whole corpus goes into **one** struct-hashed `ExprSet`
  (`compression.rs:1900-1902`, `construct_shared`). `roots: Vec<Idx>` are program
  roots; `corpus_span = 0..set.len()` is the set of all unique subtrees. Identical
  subtrees anywhere are the same `Idx` — foundation of everything else.
- Multiplicity via `num_paths_to_node` (`util.rs:106-135`): occurrences of each
  unique subtree, counting DAG sharing; also per-root variants for task accounting.
- Bottom-up analyses (`[lambdas] analysis.rs`): `ExprCost`, `FreeVarAnalysis`,
  `IVarAnalysis`, computed once, indexed by `Idx`.
- `cost_of_node_all[node] = subtree_cost(node) * num_paths_to_node[node]`
  (`compression.rs:1945`).

### Patterns (partial abstractions)
```rust
pub struct Pattern {                       // compression.rs:295-304
    pub holes: Vec<ZId>,                   // zippers from match root to each ??
    pub pattern_args: PatternArgs,         // where the #i variables are
    pub match_locations: Vec<Idx>,         // sorted unique-subtree Idxs
    pub utility_upper_bound: Cost,
    pub body_utility: Cost,                // cost of the concrete part of the body
    pub tracked: bool,                     // debugging only
}
```
A pattern is *not* stored as a tree: it is hole positions (zipper ids), argument
positions (`PatternArgs`), and match locations. The concrete body is reconstructed
from any match location by cutting at hole/ivar zippers (`Pattern::to_expr`,
`compression.rs:513-552`) — valid because all match locations share the same shape
at non-hole positions.

`PatternArgs` (`pattern_args.rs:36-40`): `arg_choices: Vec<LabelledZId>` — one
entry per *use* of an ivar — plus `variables` giving one canonical zid per ivar.

### Zippers (ZPath / ZId)
- A zipper is a path from a subtree root down into it: `Vec<ZNode>`,
  `ZNode ∈ {Func, Body, Arg}` (`[lambdas] zipper.rs:5-11`). Every distinct path in
  the corpus is interned to a `ZId`; `EMPTY_ZID = 0`.
- `get_zippers` (`compression.rs:1226-1357`) is the key precomputation: for every
  node `n` and every zipper `z` from `n` to any descendant, an `Arg` record:
```rust
pub struct Arg {                 // compression.rs:572-580
    pub shifted_id: Idx,         // argument as extracted (de Bruijn-adjusted)
    pub unshifted_id: Idx,       // original corpus subtree
    pub shift: i32,
    pub cost: Cost,
    pub expands_to: ExpandsTo,   // root constructor of the subtree
}
```
  stored as `arg_of_zid_node: Vec<FxHashMap<Idx, Arg>>` indexed `[zid][node]`.
  Built by bubbling zippers upward through parents (`compression.rs:1259-1334`).
  This makes matching during search a pure table lookup.
- `extensions_of_zid` (`compression.rs:1338-1350`): zids of `zip+Body/Arg/Func`
  for O(1) hole extension.
- `ziptrie.rs` is used **only** by the self-overlap analysis (see §5).

### Match location tracking
Maintained explicitly and incrementally: the single-hole pattern matches every node
in `corpus_span` (`Pattern::single_hole`, `compression.rs:437-512`); every expansion
subsets the parent's `match_locations`. No unification at search time — matching an
expansion at a location is the lookup `arg_of_zid_node[hole_zid][loc].expands_to`.

## 2. The search loop

- `stitch_search` (`compression.rs:943-1138`); worklist management in
  `get_worklist_item` (`compression.rs:866-941`) with a `BinaryHeap<HeapItem>`
  (mutex-shared; collapses to a plain local heap single-threaded).
- **Priority key**: `utility_upper_bound` (max-heap, best-first)
  (`compression.rs:598-608`).
- `utility_pruning_cutoff` = utility of best finished abstraction so far; items
  pruned both on push and pop (`compression.rs:898, 929-938`).

One step (`compression.rs:965-1135`):
1. Choose hole (`HoleChoice`, default **depth-first** = last-added,
   `compression.rs:814-852`).
2. `arg_of_loc = arg_of_zid_node[hole_zid]`.
3. Sort `match_locations` by `(expands_to, loc)`.
4. **Syntactic expansions** (`expansion.rs:162-168`): group_by on
   `arg_of_loc[loc].expands_to`; each group is one child pattern with exactly those
   locations. `Lam` adds one hole, `App` two, `Var`/`Prim` none
   (`expansion.rs:85-97`).
5. **Ivar expansions** (`get_ivars_expansions`, `expansion.rs:176-211`):
   - *Reuse* `#i`: keep locations where
     `arg_of_loc_1[loc].shifted_id == arg_of_loc_2[loc].shifted_id`
     (`pattern_args.rs:238-249`) — hash-consing makes this a pointer comparison.
   - *Fresh* `#(arity)` if `arity < max_arity`: all current locations.
6. No holes left → `FinishedPattern::new` (exact utility) → donelist; else worklist.

**Structural-hashing trick**: match locations are unique subtrees, so one groupby
entry advances the pattern at every occurrence simultaneously; multiplicity
re-enters only via `num_paths_to_node` in utility/bounds.

## 3. Utility and bounds

### Cost model
`cost_app = cost_lam = 1`, `cost_var = cost_ivar = cost_prim_default = 100`
(`compression.rs:367-430`). New primitive costs `cost_prim_default` (100).

### Exact utility of a finished pattern
- `body_utility` accumulated during search: each syntactic expansion adds the local
  cost of the added constructor (`expansion.rs:71-82`; ivars add 0).
- Per-location utility (`get_utility_of_loc_once`, `compression.rs:1619-1660`):
  - `app_penalty = −(cost_new_prim + cost_app · arity)`;
  - **multiuse**: for each ivar used `k > 1` times, `+(k−1) · cost(arg at loc)`
    (`pattern_args.rs:102-106`);
  - `util_once(loc) = body_utility + app_penalty + multiuse`; forced to 0
    (location autorejected) if any argument at that location contains sentinel
    ivars, i.e. would capture a body-lambda variable (`pattern_args.rs:108-121`).
- Overlap correction (§5), then `compressive_utility_from_marginals`
  (`compression.rs:1553-1580`): with default task/weight settings this degenerates
  to `Σ_locs util_once(loc) · num_paths_to_node(loc)`.
- `noncompressive_utility = −body_utility · structure_penalty` (default 1.0)
  (`compression.rs:1507-1516`).
- Total = compressive + noncompressive (`compression.rs:1173-1200`), with an assert
  it never exceeds the parent's upper bound (`compression.rs:1181`).

### Upper bound
`compressive_ub = Σ_{loc} max(0, cost_of_node_all[loc] − num_paths_to_node[loc] ·
cost_new_prim)` (`compression.rs:1521-1534`); `noncompressive_ub = 0`. Monotone
under expansion (asserted, `compression.rs:1028`).

### The two strict-dominance prunings
Checked on **every** expansion (location subsetting can newly trigger them):
- **Argument capture / useless abstraction** (`pattern_args.rs:123-142`, called at
  `compression.rs:1050-1052`): some ivar receives the same `shifted_id` at every
  location and it has no free vars → prune (inlined version dominates).
- **Redundant argument / force multiuse** (`pattern_args.rs:144-172`, called at
  `compression.rs:1054-1057`): two ivars with identical `shifted_id` args at every
  location → prune (reusing one ivar dominates).

(`inverse_argument_capture` (`compression.rs:1669-1780`) is gated behind
`--inv-arg-cap`, off by default — skip.)

## 4. Variables, lambdas, de Bruijn indices

- **No LambdaUnify at search time.** All shift reasoning happens once, in
  `get_zippers`, when a zipper bubbles up through a `Lam`
  (`compression.rs:1297-1334`):
  - Argument has no free vars → unchanged.
  - Free vars → downshifted by 1 (`shift(-1)`, `[lambdas] expr.rs:476-498`, adding
    shifted copies to the same arena); `arg.shift -= 1` recorded. So `shifted_id`
    is the argument as seen from the match root; free variables pointing above the
    match root are allowed in arguments.
  - Argument refers to the lambda being crossed (the paper's `&i` case):
    `insert_arg_ivars` (`egraphs.rs:50-73`) replaces those `$0`s with a **sentinel
    IVar** before shifting; `has_free_ivars` later zeroes the utility of any
    location whose argument contains sentinels, so those locations are matched but
    never used (they land in `unused_locations`). This replaces the paper's `&i`
    machinery: arguments may not capture body-lambda binders — the location is
    rejected for rewriting instead.
- **Free variables in the body are forbidden**: expanding a hole to `Var(i)` is
  pruned if `i ≥` number of `Body` steps in the hole's zipper
  (`compression.rs:1015-1021`, `expansion.rs:57-63`).
- Ivar-equality on `shifted_id` means two uses of the same argument under different
  lambda depths still unify correctly (both root-relative).
- Bodies **may** contain or be lambdas; no top-lambda ban in default mode. Finished
  invention bodies are stored with `#i` ivars, not wrapped in lambdas
  (`Invention`, `compression.rs:723-729`).

## 5. Rewriting

`rewrite_fast` (`rewriting.rs:15-155`) is a **single greedy top-down pass per
program**, not the paper's bottom-up accept/reject DP:
- At node `n`: if `match_locations.binary_search(&n)` hits and
  `n ∉ unused_locations`, emit `(inv a₁ … aₖ)`, recursing into each argument's
  `unshifted_id` (nested matches inside arguments still rewritten).
- **De Bruijn fixup**: argument with `shift ≠ 0` pushes a
  `ShiftRule {depth_cutoff, shift}` (`rewriting.rs:50-59`); any `Var(i)` whose
  binder lies at/above the cutoff gets `i += shift` (`rewriting.rs:106-119`).
- **Overlap handling** precomputed in the utility phase:
  - `can_self_unify` (`pattern_args.rs:344-359`): can the pattern match a proper
    subtree of itself at a non-variable internal position? Uses `ZipTrie` +
    structural `unifies` check (`pattern_args.rs:251-341`) at one example location;
    returns internal zids where self-overlap is possible.
  - `compressive_utility` (`compression.rs:1583-1616`) walks locations bottom-up,
    subtracting the corrected marginal utility of child matches reachable via
    self-overlap zids, clamping at 0. This is the paper's accept/reject DP
    specialized to self-overlap chains.
  - Locations with corrected marginal utility ≤ 0 go into `unused_locations`
    (`compression.rs:1561-1563`), skipped by the rewriter.
- Multiuse constraints need no rewrite-time check (enforced during search by
  location subsetting).
- **Mismatch assert** (`rewriting.rs:144-152`): rewritten cost ==
  init_cost − compressive_utility, exactly. Main correctness oracle — keep in the
  mini version, along with the bound-monotonicity asserts.
- `rewrite_with_inventions` (`rewriting.rs:159-204`) re-runs search in follow-mode;
  incidental.

## 6. Arity-zero init, single-use pruning, invariants

- **Arity-zero priming** (`compression.rs:2002-2087`): before search, every corpus
  node with no free vars (used in ≥2 tasks) scored as an arity-0 abstraction:
  `compressive = num_paths · (subtree_cost − cost_new_prim)`,
  `utility = compressive − structure_penalty·subtree_cost`. Positive ones seed the
  donelist, priming the pruning cutoff.
- **Single-use pruning** (`compression.rs:1140-1148`): discard candidates whose
  location set is a single unique subtree with no free vars (arity-0 dominates).
- **Single-task pruning** (`compression.rs:1150-1155`; arity-0 at `2019-2023`):
  **on by default**; with no task labels each program is its own task, so an
  abstraction must appear in ≥2 programs. A semantic default, not just speed.
- Other invariants (default mode): body has no free `$i`; bodies may be/contain
  lambdas; args may have free vars referring above the match root; args may not
  capture body binders (location rejected); ivars numbered `#0, #1, …` by first
  use; `match_locations` always sorted; trivial `#0` dies by autoreject (if every
  location's `util_once ≤ 0`, utility is 0; only utility > cutoff ≥ 0 finishes).
- Eta-long mode is off by default — skip entirely.

## 7. Incidental complexity to strip

| Feature | Where | Note |
|---|---|---|
| Parallelism | `compression.rs:611-661, 866-941, 2203-2222` | plain loop + local heap |
| TDFA | `tdfa.rs` | optional, off by default |
| Symvars | `symvar.rs` + threading | off unless `--symvar-prefix` |
| Tasks + weights | `util.rs:7-20`, `egraphs.rs:23-48`, `*_weighted` fields | collapse to plain sum; but keep single-task-pruning semantics |
| DreamCoder compat | `formats.rs`, `util.rs:42-100` | skip |
| Follow/tracking | `follow*` flags, `Tracking` | debug machinery |
| Search-based rewrite | `rewriting.rs:159-204` | keep only `rewrite_fast` |
| Fused lambda tags | `Tag` fields | drop |
| `inverse_argument_capture` | `compression.rs:1669-1780` | off by default |
| Non-default hole choices | `compression.rs:799-852` | keep depth-first only |
| Stats/verbosity, extra bins | various | skip |
| Eta-long / curried restrictions | `eta_long` etc. | off by default |

Keep despite looking incidental: the mismatch assert and bound-monotonicity asserts
— the implementation's main correctness oracles.

## 8. Config defaults (core-relevant)

- `iterations = 3`, `max_arity = 2`, `inv_candidates = 1`, `threads = 1`,
  `hole_choice = depth-first`.
- Costs: `cost_app = cost_lam = 1`, `cost_var = cost_ivar = cost_prim_default = 100`.
- `structure_penalty = 1.0`; utility = compression − 1.0·abstraction-size.
- All optimization flags enabled by default; `allow_single_task = false` (single-
  task pruning ON — changes results).
- Mismatch check on. Search ends when worklist empties; multistep stops early when
  an iteration finds no positive-utility abstraction.

## Minimal-reimplementation sketch implied by the above

One hash-consed arena for the corpus + `num_paths` counts; precomputed
`(path, node) → (shifted arg, shift, expands_to, cost)`; best-first heap keyed by
the upper bound; expansion = sort+groupby on `expands_to` plus ivar reuse/fresh via
`shifted_id` equality; the two dominance prunings + free-var prune +
single-use/single-task prunes; arity-0 priming; exact utility with app penalty,
multiuse bonus, free-ivar autoreject, self-overlap correction; greedy top-down
rewrite with shift rules and the cost-equality assert.
