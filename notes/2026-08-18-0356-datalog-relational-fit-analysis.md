# Would a Datalog/relational substrate fit stitch-like library learning?

An analysis in the style of the sibling project,
`bottom-up-synth-datalog`, which asked the same question for bottom-up
enumerative program synthesis: where is the set-at-a-time work, what would a
relational engine actually buy, what is the right host-language/Datalog
split, and which engine (Ascent, egglog, Slog) fits. That project's measured
results are the calibration baseline here; they are cited as
[BUSD:&lt;entry&gt;] for `notebook/&lt;entry&gt;.md` in that repo. Its headline,
for orientation: expressibility and single-threaded time parity on Ascent
confirmed (OE dedup as a keyed lattice aggregation, 0.98–1.06x vs
handwritten Rust), memory failed (~4–8x per tuple), parallelism capped
(~2x on 4 cores by level barriers), and the engine gaps identified were
cost-stratified scheduling, goal-directed halt, additive-cost joins, and
interning [BUSD:2026-07-02-1720Z third reflection; 2026-07-01-2150Z].

Two measurements were run for this note, both in `experiments/`
(new directory; neither touches `src/`):

- **[AU]** `experiments/2026-08-18-0337Z-au-feasibility/` — the size of the
  pairwise anti-unification space on stitch's own corpora, and whether the
  real stitch binary's winning abstraction is reachable by anti-unification
  (Python; builds the submodule binary for ground truth).
- **[BB]** `experiments/2026-08-18-0341Z-search-order/` — whether stitch's
  best-first worklist order matters, i.e. whether branch-and-bound survives
  the level-synchronous schedule a Datalog engine would impose (instrumented
  copy of mini-stitch's search; Racket).

A pleasant cross-validation fell out: mini-stitch's instrumented
pops-expanded equals the real binary's reported `worklist_steps` exactly on
all three cogsci corpora (nuts-bolts 2520, wheels 23896, dials 12368) —
the two experiments were built independently and only compared afterwards.

## tl;dr

1. **Top-down stitch, encoded as-is, is a faithful but advantage-free fit**
   (inference — untested as an actual Ascent program, but bounded by the
   sibling project's parity-at-best results). The match-location machinery
   — the part that looks most relational — is literally two Datalog rules,
   but every derived fact has exactly one derivation, so the engine's core
   services (set-semantics dedup, semi-naive rederivation avoidance) sit
   idle. The essential optimizations are aggregation over match sets plus a
   non-monotone global cutoff — exactly the features Datalog lacks.
2. **The order objection to a relational schedule is dead (measured).**
   Replacing the best-first heap with FIFO — the order a stratified engine
   imposes — costs only 1.08x exploration in aggregate at arity 2 (worst
   corpus 1.75x, nuts-bolts; 1.01x at arity 3), with identical winner
   utilities everywhere. Branch-and-bound's power lives in the cutoff
   (heavily seeded by arity-zero priming) and the prunings, not the order.
3. **The genuinely Datalog-shaped formulation is bottom-up: anti-unification
   over the hash-consed corpus, with keep-best-per-match-set as the lattice
   aggregation.** This is where the rendezvous/contraction that Datalog pays
   for actually exists: 31–127x of generated pairwise lggs are duplicates
   (measured), the analogue of the sibling project's 8–20x OE collapse.
4. **The bottom-up space is small and it reaches stitch's answers
   (measured).** Full pairwise anti-unification over every stitch corpus
   costs at most 10.9 s of single-core stdlib Python (wheels: 1.2M pairs →
   9,538 distinct patterns); the deduplicated space is the same order of
   magnitude as the pruned top-down search's step count. Stitch's winner
   subsumes the lgg of its match set in 13/13 eligible runs and equals it
   (up to free-var re-generalization) in 7/13; every gap is an *upward*
   merge (3 exact utility ties, 2 arity-cap artifacts, 1 genuinely better
   merge), never a specialization.
5. **Reasons it may still not be a winner:** real stitch has little
   performance pain to relieve on the corpora mini-stitch targets (paper
   §6.1: tens of milliseconds on the DreamCoder-trace corpora; Table 2:
   0.24–2.8 s on the technical-drawing domains) — though see the
   correction in §6: the paper's tower domains run 17–77 s at up to
   ~0.7 GB, so a modest real-runtime regime does exist inside stitch's own
   benchmarks. Utility scoring, de Bruijn shifting, and the upward-merge
   phase all live in host code, so the Datalog fraction shrinks toward
   "the joins"; and the sibling project already measured where that road
   ends (parity, a memory tax, and engine feature gaps). The distinctive
   upside is elsewhere: legibility, the all-patterns-at-once bank,
   incremental maintenance across compression iterations, and the
   babble-style equational variant where matching really is e-matching.

## 1. What stitch computes, seen relationally

(Algorithm background: `notes/2026-08-17-1840-paper-digest.md`. One-line
recap: branch-and-bound over partial abstraction bodies ("patterns"), grown
one hole at a time; each pattern carries its set of match locations in a
hash-consed corpus arena; a utility upper bound per pattern plus a global
best-so-far cutoff prunes the search; the winner rewrites the corpus and
the loop repeats.)

The inventory, piece by piece:

| computation | shape | relational fit |
|---|---|---|
| corpus arena (hash-consing) | interning | this *is* the EDB: `node(id, ctor, child1, child2)`. Note most engines don't provide interning (Ascent has none; Slog's content-hash IDs do [BUSD:2026-07-02-0306Z]) — stitch's single most load-bearing property must be supplied by the host or the content-hash trick |
| analyses: cost, free-vars, num-paths, programs-with | bottom-up / top-down sweeps | recursive aggregation; expressible, linear-time either way, nothing to win |
| match-location maintenance | selection + group-by per expansion | **literally a Datalog rule** — see §2 |
| ivar-reuse expansion | equijoin on shifted-argument equality | ditto |
| zero-match pruning | — | free in the relational form: derivation is location-driven |
| free-var ban, arity cap | per-tuple guards | trivial |
| single-task, single-use prunes | aggregates over a pattern's match set | need per-pattern aggregation, i.e. stratification by pattern size |
| utility upper bound | SUM over the match set, compared to a global cutoff | aggregate + **non-monotone** read of evolving global state |
| dominance prunes (argument capture, redundant argument) | ∀-quantified over the match set | negation/aggregation; stratify or host |
| exact utility (multiuse, capture-zeroing) | aggregates over match set | host or stratified aggregate |
| self-overlap correction | *ordered* bottom-up scan with subtraction and clamping | sequential DP; hostile to Datalog; host code |
| rewriting | accept/reject DP + greedy top-down pass | linear host code, not worth relationalizing |
| best-so-far cutoff | global max, read anti-monotonically | the one genuinely sequential piece — but see §3 |

So the joins and group-bys exist, but each expansion step is wrapped in
aggregation, and the driver state (cutoff) is non-monotone. That is the
same list of engine gaps the sibling project ended with —
cost-stratified scheduling (here: pattern-size-stratified), goal-directed
halt (here worse: a continually *shrinking* frontier as the cutoff rises),
aggregation coupled to recursion — with one mercy: there are no
additive-cost joins (expansion is unary in the pattern; nothing like
`cost(a)+cost(b)+1 = k` ever appears).

## 2. The matching step, and the rendezvous test

The piece that looks most relational — checking which expression positions
match a newly grown pattern — is genuinely a two-rule Datalog program.
Stitch never re-matches a pattern against the corpus; it maintains a
relation `match(P, L)` and refines it:

```
match(expand(P, e),  L) :- match(P, L), arg_head(L, hole(P)) = e.
match(expand(P, #i), L) :- match(P, L), shifted(L, hole(P)) = shifted(L, canonical(P, i)).
```

mini-stitch's `syntactic-expansions` group-by is exactly what the first
rule's join-plus-term-constructing-head does implicitly, and the variable
reuse rule is an honest equijoin on the precomputed `(location, path) →
shifted-arg` table — which is itself exactly the index a Datalog engine
would maintain. Expressibility: clean yes, and arguably *more* legible
than zipper machinery.

But apply the sibling project's core lens — is there **rendezvous**,
i.e. do independently derived facts collide so that set-at-a-time dedup
does real work [BUSD:2026-06-30-2059Z §1.4]? In bottom-up synthesis, yes:
OE dedup collapses 8–20x of what generation produces (collapse ratios
0.05–0.13, measured [BUSD:2026-06-30-2121Z; 2026-07-02-1458Z]), and that
keyed aggregation was the substrate's cleanest win. In stitch's top-down
search, **no**: the hole-expansion order is deterministic, so every
pattern is reached by exactly one expansion sequence — the search tree is
a tree, and every `match(P, L)` fact has exactly one derivation.
Locations get *partitioned* down the tree, never merged. Set semantics,
semi-naive evaluation, index maintenance: all idle (the worklist already
*is* the semi-naive delta, maintained by hand; hash-consing already makes
every per-tuple step O(1)). The ceiling for a faithful relational encoding
is therefore parity, and the sibling project measured what parity costs on
Ascent: ~1x time, ~4–8x memory per tuple [BUSD:2026-07-02-1524Z]
(inference — the encoding itself was not built; the bound is the
transferred measurement).

There is one subtlety worth recording: distinct patterns can have
identical match sets and dominated futures — that is what the two
dominance prunings exploit. That is *semantic* subsumption, invisible to
Datalog's syntactic set semantics, but it is precisely what a lattice
keyed on the match set can see. Pulling that thread leads to §4.

## 3. Order: branch-and-bound survives a stratified schedule (measured)

A relational encoding cannot pop a max-heap; it expands a stratum at a
time. Two worries: (a) losing best-first order weakens the cutoff, so
more patterns get explored; (b) the paper's ablations say bounds pruning
is worth 12–208x, so any weakening might be fatal.

[BB] measures (a) directly: mini-stitch's search with the heap replaced by
a FIFO queue (≈ level-synchronous) or a LIFO stack (DFS), all pruning
identical, on 24 corpora at arities 2 and 3.

- **fifo/best on patterns expanded: 1.079 aggregate at arity 2** (49,273 →
  53,158), 1.153 excluding wheels, **1.011 at arity 3**. Fifteen of 24
  corpora are exactly 1.00. Worst case: nuts-bolts at 1.75 (2,520 → 4,404).
  LIFO is 1.031 / 1.016. (measured)
- Winner utilities identical across modes on every corpus, both arities;
  bodies identical except one known equal-utility tie (ctx_thread_twice,
  arity 3 — the same tie the differential suite documents). (measured)
- Mechanism: **arity-zero priming usually sets the final or near-final
  cutoff before the search starts**, and with a static cutoff the explored
  set is provably order-independent. Extreme case wheels: the largest run
  (23,896 pops) has bit-identical counts in all three modes because its
  winner *is* the primed arity-zero abstraction. Order matters only where
  the winner is found mid-search and far exceeds the primed cutoff
  (nuts-bolts). (measured + mechanism)
- Caveat: a true stratified run would update the cutoff only *between*
  strata, slightly weaker than our FIFO (which scores finished patterns
  immediately); treat 1.08x/1.75x as a lower bound on the stratified cost.
  Still small. Also all corpora here are ≤24k pops; order-sensitivity
  could grow where the primed cutoff is weak relative to a late winner.
  (inference)

So the sequential-control objection reduces to: keep the cutoff as a
host-side scalar, re-seed it into each stratum (the sibling project's
stratified-driver architecture, strata = pattern size instead of candidate
cost [BUSD:2026-06-30-2253Z]), and lose almost nothing. What remains true
is that the *driver* — strata, cutoff, aggregation between levels, utility
scoring — is host code, and the Datalog fraction of a top-down encoding is
two selection rules that were never the expensive part.

## 4. The bottom-up reformulation: anti-unification and closed patterns

The interesting question is the one the sibling project's title asks:
is there a *bottom-up* formulation? For library learning there is, and
stitch's own prunings point at it. Both dominance prunings are moves
toward the least general generalization (lgg) of the match set:

- **argument capture** discards a pattern whose variable takes the same
  closed argument everywhere — i.e. *inline it*: specialize toward the lgg;
- **redundant argument** discards a pattern where two variables always
  agree — i.e. *identify them*: exactly Plotkin lgg variable identification.

A pattern surviving both is (nearly) the lgg of its own match set — a
**closed pattern** in the formal-concept-analysis sense: extent = match
set, intent = lgg. The top-down search wades through many generalizations
of each closed pattern and prunes them; a bottom-up search would construct
each closed pattern once, by anti-unifying corpus subtrees, and score it
once. Relationally:

- `subtree(t)` is the EDB (the hash-consed arena);
- pairwise anti-unification is a join over subtree pairs — the
  product/tree-automata-intersection construction, with recursive structure
  `au(app(f1,x1), app(f2,x2)) = app(au(f1,f2), au(x1,x2))` and variables
  keyed by *shifted* subtree pairs (the same de Bruijn-aware equality stitch
  uses for variable reuse; this keying is what produces multiuse bodies like
  `(#0 #0 #0)`);
- **keep-best-per-extent is a keyed lattice aggregation** — the exact
  analogue of the sibling project's bank keyed by behavior, with the match
  set playing the role of the behavior vector and a content-hash of the
  extent as the key (Slog-on-Ascent's `calc_id` trick transfers verbatim
  [BUSD:2026-07-02-0306Z]);
- computing extents (matching the whole pattern bank against the corpus)
  is itself a joint bottom-up pass in which hash-consed subpatterns share
  their match facts across all superpatterns — here set semantics finally
  *pays*, because the pattern bank is a DAG, not a tree.

This is recognizably babble's territory (Cao et al., POPL 2023: library
learning via e-graph anti-unification, built on the egg library); the
corpus-as-DFTA product construction is the same idea with the e-graph
degenerate (no equational theory, so hash-consing suffices).

### Is it feasible? (measured)

[AU] computed the *entire* pairwise de Bruijn-aware lgg space for every
corpus, in stdlib Python, single core:

| corpus | programs | tree nodes | unique subtrees S | compatible pairs | distinct lggs | wall |
|---|---:|---:|---:|---:|---:|---:|
| nuts-bolts | 250 | 37,766 | 455 | 92,235 | 3,019 | 1.08 s |
| dials | 250 | 71,174 | 1,225 | 689,725 | 22,087 | 7.7 s |
| wheels | 250 | 70,602 | 1,663 | 1,206,681 | 9,538 | 10.9 s |

(all 21 basic corpora are ≤0.07 s; nothing timed out.)

- **Hash-consing absorbs the corpus.** 250 programs / 70k tree nodes
  collapse to ~0.5–1.7k unique subtrees; growing nuts-bolts 10x in programs
  grows S only 2.2x. The pair space is quadratic in S, not in corpus size.
- **The contraction is real: 31–127x of computed pairwise lggs are
  duplicates** on the cogsci corpora. This is the rendezvous top-down
  search lacks — the thing a Datalog engine's set semantics is *for*.
- **The deduplicated bottom-up space is the same order of magnitude as the
  pruned top-down step count**: 3,019 distinct lggs vs 2,520 worklist steps
  (nuts-bolts), 9,538 vs 23,896 (wheels), 22,087 vs 12,368 (dials).
  Structural dedup buys roughly what branch-and-bound buys on this data —
  without a cutoff, without ordering, without the dominance machinery.
  (Caveats: the pair space is only the first closure level; units are
  patterns touched, not time.)
- The memoized `au` subproblem table — the join's intermediate relation —
  peaks at 1.8M tuples (wheels): tiny by the sibling project's standards
  (its banks hit 8.9M *surviving* tuples), so Ascent's 4–8x per-tuple
  memory tax would not bind here. (inference from measured sizes)
- 59–76% of distinct lggs on cogsci corpora contain a repeated variable —
  the de Bruijn-aware shifted-pair keying is load-bearing, not a nicety.

### Does it reach stitch's answers? (measured)

[AU] Part B checks the real binary's winner (arity 2, iteration 1) against
the anti-unification lattice, per corpus:

- **The winner subsumes the lgg of its match set in 13/13 runs** with ≥2
  unique match locations, and **equals it in 7/13** (exactly, or after
  re-generalizing free de Bruijn variables — stitch bans free `$i` in
  bodies, so its winner is forced one step more general than the true lgg
  at such positions; hof is the confirmed instance).
- The six gaps classify cleanly, probed with stitch's own `--follow`
  utility: **3 exact utility ties** (the ctx_thread family — the lgg is
  co-optimal at 1011/910/1213); **2 arity-cap artifacts** (map2,
  map_minimal: the lgg has arity 3–4; at `--max-arity=3` stitch's winner
  *is* the set-lgg); **1 genuine case** (simple_hof: merging a repeated
  subpattern into one variable, `(#0 #1 (#0 #1))` → `(#0 #0)`, beats the
  lgg 201 vs 199).
- **Every gap is an upward move only** — replace a subpattern by a single
  variable. No winner is ever more specific than its lgg. So a bottom-up
  system reaches a lower bound of the winner in the subsumption lattice
  and needs a bounded *upward-merge-and-rescore* phase (empirically: one
  merge step sufficed in every observed gap) — it never needs to
  specialize, i.e. never needs the top-down hole-expansion machinery.
- Degenerate cases to handle: arity-0 winners (5 corpora + wheels) are
  repeated concrete subtrees — reachable trivially (they are arena nodes),
  but the formulation must score plain subtrees, not just proper lggs; and
  single-program corpora need the same ≥2-programs filter stitch applies
  (their AU spaces are sizable but stitch prunes them instantly).

What was *not* measured: the cost of the extent-computation pass (match
sets were computed only for winners), the closure above pairwise (folds
over match sets were spot-checked via the winners, not enumerated), and
utility scoring throughput. Utility is a function of (intent, extent)
plus corpus statistics — aggregates over the extent plus the sequential
self-overlap correction — and would be host code per surviving pattern.

## 5. Engine choice

- **Ascent** is the default, for the sibling project's measured reasons:
  compiled joins 30–3000x faster than egglog on synthesis-shaped workloads
  [BUSD:2026-07-02-0448Z], arbitrary Rust UDFs (the de Bruijn
  shift/extract machinery must be host functions in any engine), lattice
  relations for keep-best-per-extent, and the already-proven stratified
  driver architecture. Its known deficits — no interning (use content-hash
  IDs), ~4–8x per-tuple memory — are respectively solvable and non-binding
  at this workload's measured sizes.
- **egglog** as plain Datalog is disqualified by the same measurements.
  Its genuine role is the *equational* variant — babble-style library
  learning modulo a rewrite theory, where the corpus is a real e-graph,
  match sets are over e-classes, and matching is e-matching. Notably,
  library learning has no observational equivalence (there are no
  examples/behaviors!), so the sibling project's "OE is not e-graphs"
  argument [BUSD:2026-07-01-2150Z] cuts the *other* way here: equality is
  syntactic (hash-consing = the degenerate e-graph, sufficient for stitch
  parity) or equational (a real e-graph, and then egglog's machinery
  earns its keep). If "stitch modulo theories" ever becomes a goal,
  egglog is the natural vehicle despite the constants. Precedent exists:
  babble itself is built on egg (not egglog), but a 2026 preprint
  co-authored by stitch's Maddy Bowers ("Library Learning with E-Graphs
  on Jazz Harmony", Ren/Bowers/Guan/Rohrmeier, arXiv:2605.04622)
  reimplements babble in egglog and integrates it with deductive parsing
  — evidence the AU-as-datalog-rules encoding is workable in egglog's
  language, though that paper reports no performance comparison against
  the Rust implementations.
- **Slog / slog3-clone**: first-class facts fit patterns-as-terms and give
  native interning, but the useful trick (content-hash IDs) is already
  extracted into the lab's Ascent fork, and nothing here needs
  distribution. Idea source, not substrate.

Host/Datalog split, concretely: corpus arena, parser, de Bruijn
shift/extract, utility scoring (incl. self-overlap DP), rewriting, the
per-stratum driver and cutoff — host. AU closure rules, extent
computation/matching, keep-best-per-extent lattice, the corpus analyses if
one likes — Datalog. That split gives the engine the two computations
with genuine join-plus-contraction structure and keeps everything
sequential or arithmetic in Rust.

## 6. Reasons Datalog may not be a winner here

1. **The performance pain is modest — but not zero.** CORRECTION
   (2026-08-18, same day, after the project lead pointed back at the
   paper): an earlier draft of this note claimed "milliseconds on every
   published corpus," which conflated two very different scales.
   The paper's §6.1 corpora (DreamCoder traces) do run in tens of
   milliseconds, and the small Wong-et-al. domains — the ones mini-stitch
   targets, nuts&bolts at 0.24 s / 11 MB — in single-digit seconds. But
   Table 2's tower domains run **bridges ~17.6 s, cities ~50.7 s, castles
   ~77.3 s at up to ~684 MB peak** (means over 50 seeded runs), and the
   ablations show the search sits near a tractability cliff there: with
   any essential pruning disabled, no Wong domain finishes within 90
   minutes and 50 GB at arity 3. So stitch's own benchmarks do contain a
   real-runtime regime (tens of seconds to minutes), it just isn't the
   part mini-stitch replicated (bridge/city/house/castle are checked in
   at `stitch/data/cogsci/` and unmeasured here so far — being measured
   now, see `results-large.md` in the AU experiment folder). Still: the
   prior art (DreamCoder's version-space compressor) is orders of
   magnitude worse than stitch on all of these, so the top-down algorithm
   remains the efficiency solution; the open question is only whether the
   heavy tail is where a bottom-up formulation's different scaling could
   show an advantage.
2. **A faithful top-down encoding is advantage-free** (§2): no rendezvous,
   so the engine's differentiating services are idle, and the sibling
   project's measured endpoint for that situation is parity at a memory
   tax.
3. **The datalog fraction shrinks under your hands.** Every pruning and
   score is an aggregate over a match set; the cutoff and strata live in
   the host; the shift machinery is UDFs. The sibling project named this
   endpoint precisely — "an engine-research project wearing a synthesis
   costume" [BUSD:reflection 2026-07-02-0218Z] — and library learning
   would re-derive the same missing-feature list (size-stratified
   scheduling, goal-directed frontier shrinking) without adding a new
   workload character.
4. **The bottom-up route has unproven edges**: the upward-merge phase
   (needed for 6/13 winners, though always one step in the data), extent
   computation cost (unmeasured), the closure above pairwise (unmeasured),
   and utility-under-arity-caps making "best" not extent-determined. None
   looks fatal; none is confirmed cheap.
5. **Iteration compounds in the host anyway**: compress iterations rewrite
   the corpus and re-run; the relational bank must be rebuilt or
   incrementally maintained per iteration.

## 7. What it could win, and next bets

Genuine upside, in descending confidence:

- **A teaching-quality executable specification.** The AU-closure +
  keep-best-per-extent formulation is arguably the clearest statement of
  "library learning = mining closed patterns under a utility" that could
  exist as running code — two joins and a lattice. That aligns with this
  repo's actual purpose (exhibit the algorithm) and with the sibling
  project's one unmeasured-but-standing claim (concision).
- **All-patterns-at-once.** Bottom-up produces the whole scored bank, not
  just the argmax — useful for k-best abstraction selection (which real
  stitch approximates by greedy iteration) and for downstream selection
  objectives à la babble's beam search over partial libraries.
- **Incrementality** (speculative): compression iterations, and outer
  wake-sleep loops à la DreamCoder, re-learn over corpora that change
  locally; maintaining `match(P, L)` and the AU bank under corpus deltas is
  differential-dataflow-shaped. Needs a scale story before it matters.
- **A hybrid cheap win, testable in mini-stitch today**: prime the
  top-down cutoff with the best pairwise-lgg score instead of only
  arity-zero. [BB] showed order-insensitivity comes from strong priming;
  [AU] showed pairwise lggs contain or nearly contain the winner; together
  they suggest near-total pruning of the top-down search for the cost of
  a ~1 s AU pass. (inference — untested.)

Falsifiable next bets, if this direction is pursued:

1. **Build the Ascent encoding of pairwise-AU + keep-best-per-extent +
   host-side scoring**, and run it on data/basic + cogsci. Claim to test:
   it finds an abstraction with utility ≥ stitch's winner on every corpus
   (given the one-step upward-merge phase), within ~10x of mini-stitch's
   wall time. The [AU] Python numbers (≤11 s worst-case interpreted,
   single-core) make the time budget plausible.
2. **Measure the extent pass and the closure**: match the full lgg bank
   against the corpus (the DAG-shared matching pass of §4) and enumerate
   one closure level above pairwise; check nothing blows up and no new
   winner-reachability gaps appear.
3. **The hybrid priming experiment** in mini-stitch (one-line change to
   `arity-zero-best` seeding): measure pops-expanded with AU-primed
   cutoffs.
4. Only after 1–3: the equational variant on egglog at toy scale, as the
   "stitch modulo theories" probe.

My overall read: **library learning is a worse fit than bottom-up
synthesis for the substrate's performance story, but a better fit for its
expressiveness story.** The sibling project found the relational win where
enormous generate-and-collapse volume met a keyed aggregation; stitch's
top-down search deliberately has no such volume — that is its genius — and
the corpora are too small for a substrate to pay rent on speed. But the
bottom-up reformulation the relational lens forces you into (closed
patterns, extent-keyed lattices, AU-as-join) is a real and apparently
viable alternative algorithm (measured: small space, winners reachable),
is genuinely set-at-a-time, and is the version of the algorithm that
generalizes — to equational matching, to k-best libraries, to incremental
corpora. If the goal is a faster stitch on the corpora measured above,
skip it. Whether the heavy end of stitch's own benchmarks (the tower
domains, 17–77 s at arity 3 — see the correction in §6) leaves room for a
speed story is an open measurement, in progress. Independent of that: if
the goal is understanding what library learning *is* as a set-at-a-time
computation — this project's kind of goal — the AU formulation is worth
building.
