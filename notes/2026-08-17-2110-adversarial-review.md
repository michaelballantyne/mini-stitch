# Adversarial review of mini-stitch

Reviewer role: attack the replication, its documentation, and its
fidelity-vs-simplification decisions. Everything below that could be checked by
running code was run (Racket 8.10, submodule rev 0ef5ec7, real binary at
stitch/target/release/compress); scratch scripts lived in the session
scratchpad and are not part of the repo.

## Verdict on the three owner questions

**1. Are micro/mini faithful to the paper and the Rust?** Yes, to an unusual
degree, and the divergences from the paper (sentinels for &i, greedy rewrite
instead of the DP, no LambdaUnify at search time, the implementation's tighter
upper bound) are correctly attributed to the Rust and signposted. I
re-derived every parity-critical code path named in the brief against the
Rust source and found no discrepancy (details in "what I tried to break").
Two prose-level exceptions: the walkthrough's anti-unification section makes
one claim about the search space that is provably false (finding 1), and one
paper-vs-implementation divergence — the abstraction-size penalty term — is
papered over rather than signposted (finding 4).

**2. Is the documentation correct?** The numerical content is essentially
flawless: I recomputed roughly thirty worked numbers, counter tables, and
instrumented measurements from the walkthrough and the bug note by running
the code, and every one reproduced exactly (including the 828/622/87/17/1/0
micro filter table, the 59-pop search trace, and the 1311-vs-14956 nuts-bolts
pop counts). ~40 `file.rs:NN` citations spot-checked; all land within a line
or two. The errors that remain are conceptual or stale-doc, not numeric:
findings 1, 3, 4, 5.

**3. Were the fidelity-vs-simplification decisions right?** Mostly yes, and —
unusually — their costs are documented where they bite. The one decision with
an undisclosed weakness is the differential harness's tie handling: an
*unexpected* tie cannot fail the test suite, and the TIE verdict can mask
per-field mismatches noted before the tie point (finding 2).

---

## Findings, by severity

### 1. The walkthrough's central anti-unification claim is false (moderate)

**Claimed** (walkthrough.md §6): "The two dominance prunings are what keep the
survivors *least* general for their match set … Modulo the arity cap, what
survives to be scored is exactly the anti-unifier of its own match set."

**Actually true**: the two prunings enforce only two necessary conditions of
lgg-ness — no constant argument column, no duplicate argument column. A
pattern with a variable where the lgg has concrete structure is never pruned;
it reaches scoring and merely loses on utility.

**Evidence**: instrumenting `search` on the corpus
`["(f (g (h a)) x)", "(f (g (h b)) x)"]`, the finished patterns that reach
`finish` include `(#0 x)`, `(f #0 x)`, `(f (g #0) x)`, `(#1 #0 x)`,
`(#1 (g #0) x)` — five candidates sharing one match set whose lgg is
`(f (g (h #0)) x)`. None is pruned by `useless-abstract-prune?` (the
arguments differ across the two locations) or `redundant-argument-prune?`
(no duplicate column). Scored-candidate list from the run:

```
(#0 x) (f #0 x) (#1 #0 x) (f (g #0) x) (#1 (g #0) x)
(f (g (h #0)) x) (#1 (g (h #0)) x) ...
```

**Why it matters**: §6 is the walkthrough's most conceptual section and the
one a PL reader is most likely to quote. The true statement is weaker and
worth stating precisely: the *winner* is (generically) the lgg of its match
set, because refining a variable into shared concrete structure gains
`(Σ num-paths − 1) × cost(structure) > 0` whenever the ≥2-programs rule
holds; but "what survives to be scored" is the whole cone of generalizations
above the lgg minus the two pruned dimensions.

### 2. Unexpected ties cannot fail the differential suite, and TIE can mask earlier mismatches (moderate)

**Claimed**: README — "The harness reports a differing body at equal utility
as TIE, never as a pass"; tests/differential.rkt — "Kept explicit so that a
new tie shows up as something to look at rather than as noise"; compare-run
comment — "A tie leaves exactly one note, its own; a failure keeps them all."

**Actually true**:

* The suite's only assertion is `(check-equal? (map outcome-corpus failures)
  '())` over verdicts equal to `'fail` (differential.rkt:232-236). A **new,
  unexpected** tie prints "UNEXPECTED … tie" in the summary table but `raco
  test` still passes. The known-ties list changes a printed label only.
* In `compare-run`, `tie?` is decided by the lockstep walk, and the final
  verdict is `(cond [tie? 'tie] [(null? notes) 'match] [else 'fail])`
  (differential.rkt:154-157). Notes accumulated *before* the tie — an
  `original_cost` mismatch (parser/cost-model drift), or an
  arity/utility/num_uses/final_cost mismatch on an earlier abstraction whose
  body *did* match — are silently subsumed under the TIE verdict. So "a tie
  leaves exactly one note" is false in exactly the case where it would
  matter, and a run that is simultaneously drifting and tying reports TIE,
  not FAIL.
* A TIE also (by design, and documented) stops all comparison downstream of
  the tie point, so "83 MATCH, 2 TIE, 0 FAIL" means 2 of 85 runs were only
  compared up to their first abstraction's utility.

**Mitigations that genuinely bound the risk** (checked): mini's own
`check-cost-mismatch` oracle runs inside `compress` on every iteration, so a
mini utility that its own rewriter cannot realize crashes the run rather than
tying; the known over-count family crashes both systems rather than tying.
The residual exposure is a correlated mini bug that reproduces a wrong
utility *and* a rewrite consistent with it, landing on the same number as
real stitch for a different body. Unlikely — but the suite's advertised
tie-discipline is enforcement-by-printf.

**Fixes are one-liners** (not applied, per review rules): fail on ties not in
`known-ties`; compute the verdict as `'fail` whenever non-tie notes exist.

### 3. README overclaims "matches real stitch step for step" (minor)

README line 51: "mini computes the same answer fast, and matches real stitch
step for step." The repo's own walkthrough §7.3 says the opposite about
steps: "mini's worklist is not the real one's (no threads, no batching, a
different heap)", and the ctx_thread_twice tie (verified: real picks
`(A (lam (lam (+ (#0 $0 $1 f) (#0 $0 $1 f)))))`, mini picks
`(A (lam (lam (+ (a b #0 $0 $1 f) (a b #0 $0 $1 f))))`, both utility 1213)
exists precisely because the two searches take different steps. What is true
and tested is answer-for-answer parity on the default configuration, modulo
documented ties. One phrase, but it is the README's headline claim about
what "replication" means here.

### 4. The abstraction-size penalty is a paper-vs-implementation divergence the docs assert away (minor)

**Claimed** (walkthrough §1; micro.rkt `term-cost` comment): abstraction
variables cost nothing in the abstraction's own cost; "That is the paper's
`cost_{α=0}`."

**Actually true**: `cost_{α=0}` is indeed the paper's function (defined after
Eq. 9), but the paper's utility (Eq. 8, carried unchanged through Eq. 11-12)
charges `−cost(A)` with `cost(α) = cost_α`, and §6.1 states the experimental
constants as `cost_$i = cost_α = cost_t = 100` (paper text line ~1110). Read
literally, Eq. 8 on simple1 gives 202 − 302 = **−100**; stitch (and mini,
and micro) compute **200**, because the implementation's penalty is
`−cost_{α=0}(A)` (`noncompressive_utility = −body_utility`,
compression.rs:1507-1516; ivar expansions add 0 to body_utility,
expansion.rs:79). So this is another place where mini follows the
implementation against the paper's letter — same category as sentinels-vs-&i
and greedy-vs-DP, both of which the docs signpost carefully. This one is
instead presented as if the paper said it. A learner reconciling Eq. 8
against the code with the paper's own constants will get a different number
and no warning. One sentence in walkthrough §1 would fix it.

### 5. Stale and unreproducible claims in the notes (minor)

* **Design note addendum** (notes/…-1900, "micro-stitch" section): "Dropped
  as genuinely dominance-safe: redundant-argument elimination, …". micro.rkt
  *keeps* it (`duplicate-argument?`, micro.rkt:647-651) and its header
  explains why. The addendum was the plan; the code diverged; the note was
  not updated. A reader using the notes as the spec will mispredict micro's
  behavior.
* **todo.md line 31**: "Matches real binary exactly on 27/28 basic
  corpus/arity combos" — stale; the final suite is 21 corpora × {2,3} ×
  {1,3} = 84 runs + nuts-bolts. Same file claims parity "on
  nuts-bolts/wheels/dials", but wheels and dials appear in no checked-in
  test. (I ran both at arity 2, 1 iteration: wheels utility 699628 /
  num_uses 3465 / final 2877846, dials utility 750733 / 127 / 2849869 — mini
  matches the binary on both, in ~1-2 s. The claim is true; it is just not
  reproducible from the repo.)
* **Bug note fuzz statistics** (notes/…-2030): the headline numbers check out
  against preserved scratchpad outputs — 3831 biased corpora-with-abstraction,
  2003 over-counts, 0 under-counts (fuzz5.out); 3400 = 400 + 3000 unbiased
  trials with zero disagreements (fuzz.out, fuzz4.out). But the "~10k random
  corpora" total includes ~2.6k runs (fuzz2, fuzz3) that fit neither stated
  bucket — fuzz3.out records 2 mismatches, consistent with the note only
  because those corpora do contain duplicated children — and the fuzz scripts
  live in an ephemeral scratchpad (fuzz3.rkt is already gone). The statistics
  cannot be audited from the repo. If the fuzz result is worth citing in the
  README, one fuzz script belongs in tests/.
* **Bug note citation nit**: "stitch's `--utility-by-rewrite` debug flag
  (rewriting.rs:144) embodies micro's definition" — rewriting.rs:144 is where
  the flag *disables the mismatch assert*; the utility-by-rewriting
  computation it enables lives in `FinishedPattern::new`
  (compression.rs:~1185-1196). The stack-overflow claim itself is true (I
  reproduced it: `--utility-by-rewrite` on the reproducer aborts with
  "thread 'main' has overflowed its stack").

### No other errors found

* **The bug note's causal diagnosis is correct.** Re-derived by hand and by
  machine: on the reproducer, `(#0 #0)` matches at Idx {Z, Y, X, V} with
  marginals {0, 101, 303, 101}; ×num-paths {4,2,1,1} gives compressive 606,
  utility 605 (mini reproduces both; real stitch's panic prints the same:
  "finished: utility=605, compressive_utility=606 … left: 705 right: 604").
  True rewrite: 1210 → 705 = compressive 505. The over-count is exactly one
  num-paths credit for the Y-copy deleted when X's multiuse argument is
  passed once (606 − 505 = 101 = Y's marginal). `can_self_unify` returns
  nothing because `find_self_unification_points` returns early at variable
  positions (pattern_args.rs:322-325, "variables do not count as
  self-unification points"), which is correct for single-use variables (the
  rewriter descends into arguments) and wrong exactly for multiuse — as the
  note says. "Always an over-count, never an under-count" is consistent with
  both the mechanism (only credited matches get deleted) and the preserved
  fuzz output (0 under-counts in 4239 scored corpora).
* **Walkthrough worked numbers**: every number I recomputed reproduced
  exactly; list in the final section.

---

## Defensible but debatable decisions (not errors)

* **Keeping parity with stitch's utility over-count instead of fixing it.**
  Right call for a replication whose test oracle is the real binary, and the
  costs are documented in four places (README, the note, micro.rkt's last
  test, rewrite.rkt's oracle comment) with a loud runtime error pointing at
  the note. The alternative — fix it behind a flag — would be nicer for
  downstream users but worse for the differential-testing story. The one
  thing missing is an upstream report; the note correctly leaves that as
  Michael's call.
* **Dropping the zipper tables (`arg_of_zid_node`) and ziptrie.** Consistent
  with CLAUDE.md's "constant-factor improvements out of scope", and the paper
  supports the framing: §6.4's ablations credit argument capture and
  upper-bound pruning; Appendix A credits structural hashing. But be aware
  the walkthrough's framing ("the same computation, made fast" via
  hash-consing + incremental match lists) understates one real architectural
  idea of the Rust: `get_zippers` computes every (zipper, node) argument
  record once, in O(1) per record, by extending the child's records, so
  search-time matching is a single hash lookup and shifted arguments are
  shared across all parents. mini's `extract-arg` recomputes each
  (location, path) entry by an O(|path| + |subtree|) walk, memoized. Same
  asymptotics in the match-list dimension, worse constants in the argument
  dimension. The README's Scale section does disclose the omission; a
  learner should just not come away thinking the zipper table was *only*
  interning.
* **TIE-at-equal-utility policy.** Comparing bodies at equal utility as TIE
  rather than FAIL is the correct semantics; the enforcement gap is finding
  2, not the policy.
* **micro's retained filter set.** Verified correct on both counts: argument
  capture is kept *for parity* (paper footnote 2 makes it non-dominance-safe:
  the delta is `−(cost(e)+cost_app)·|RewriteLocs| + (cost(e)−cost_α)·usages(α)`,
  positive when the argument is used more often than the abstraction), and
  redundant-argument really is dominance-safe under multiuse utility:
  replacing #j by a reuse of #i keeps the identical match set, saves
  COST-APP per location, and *gains* `(uses−1)·cost(arg)` multiuse bonus —
  strict domination. Keeping it in micro for tie-agreement is honest and
  cheap. (Nit: both files say the filter "is two lines"; it is six.)
* **Hardcoded costs, two CLI knobs, no tasks/weights, single candidate.**
  All are stitch defaults (verified: `inv_candidates` default 1,
  `hole_choice` default depth-first, `allow_single_task` off,
  dreamcoder cost model, structure_penalty 1.0) and the degenerate task/weight
  arithmetic in `compressive_utility_from_marginals` really does collapse to
  mini's plain sum for one-root-per-task, weight 1. Disclosed in README.
* **micro's utility-by-rewriting as the specification.** Good pedagogy, and
  the one place the two definitions provably differ is exactly where the
  docs spend their ink. The walkthrough's §3.8 equality claim ("the same
  numbers … by an arithmetic identity") is scoped to the example and §7
  retracts it in general. No change needed.

---

## What I tried to break and could not

* **The full test suite**: `raco test src/ tests/` — 77 test cases pass (76
  in src/, 1 differential); differential re-run reproduced **85 runs: 83
  MATCH, 2 TIE, 0 FAIL**, both ties on ctx_thread_twice at arity 3, exactly
  as README claims; nuts-bolts (250 programs, 3 iterations) matched in full
  in ~1.0 s here (README's "~3 s" is conservative).
* **Every instrumented number in the walkthrough**, by re-instrumenting the
  real modules: arena 30 nodes / num-paths sum 51 / corpus cost 2526;
  program costs 707/910/909; subterm counts 14+19+18; initial bound 10006;
  arity-zero table ((+2)→1, (+3)→203); the step table (locations
  30,18,7,7,7,7,3,3,3,3; bounds 7173/3737/1818; body-utility 304; final
  locations {10,17,26}); micro's 828 generated / 622 zero-match / 87
  single-program / 17 argument-capture / 1 identity / 0 redundant / 27
  finished / 74 queued; micro's site counts 51/22/11/6/4/3/3/3; micro's
  runner-up utilities (203, 202, 100, 100, 1, 0, −1, −102); mini's 59 pops
  with the bound and 59 without (0 bound-prunes), 159 children, 23 finished,
  58 queued; nuts-bolts prefixes 1311 pops/380 bound-prunes vs 14956, and
  2439/673 vs 81969, same answers both ways; the extract-arg table at locs
  17/18/21 (shifted `(+ 3 #0)`, shift −1, captures); iteration 2 = `(+ 2)`
  utility 1, cost 1718, 28-node corpus; iteration 3 finds nothing. All exact.
* **The real binary on the Section 2 corpus**: body `(+ 3 (* #1 #0))`,
  dreamcoder `#(lambda (lambda (+ 3 (* $0 $1))))`, utilities 302/1,
  num_uses 3/2, final cost 1718, and all three rewritten strings at both
  iterations — verbatim as the walkthrough prints them; micro's rewrite
  matches the paper's Eq. (3) argument order.
* **The bug reproducer end to end**: real binary panic (left 705, right
  604), stats line quoting utility 605/compressive 606; mini's search
  returning 605/606 and its oracle erroring with 705-vs-604; micro's 504/505
  and `(fn_0 (fn_0 (a a)))` / `(fn_0 (a f))`; `--utility-by-rewrite` stack
  overflow. The self-overlap-correction explanation re-derived from
  pattern_args.rs directly.
* **Rust parity, path by path** (read side-by-side, not trusted from
  comments): upper bound formula incl. `max(0, ·)` and num-paths weighting;
  `noncompressive_utility_upper_bound` ≡ 0; `get_utility_of_loc_once`
  (negative marginals preserved; autoreject only when none positive;
  capture-zeroing via canonical variable only; multiuse priced at the
  unshifted arg's cost); the self-overlap correction (ascending-Idx =
  bottom-up; child looked up unshifted; clamp at 0); `can_self_unify`'s
  candidate positions (non-root, variable strictly below, variables
  excluded, `overall_loc == partial_loc` shortcut — mini's justification for
  dropping it is sound: two generalizations of the same concrete tree always
  unify); `is_useless_abstract` over every *use* vs `is_redundant_argument`
  over canonical zids; both prunings on parent's variables against child's
  locations, after the bound, before pattern construction; single-use
  (unique-subtree, closed) and single-task (≥2 programs) semantics;
  free-variable prune against Body-step count; expansion ordering
  (Lam < App < Var < Prim < IVar by declaration order; string_cache Atom's
  Ord confirmed to be string comparison in the vendored source); hole order
  (Func pushed before Arg, depth-first takes last ⇒ argument first);
  arity-zero priming (span order, closed, ≥2 tasks, strict double cutoff,
  first-found wins ties); `finish`'s double cutoff test (and
  `inverse_argument_capture` confirmed a no-op without `--inv-arg-cap`);
  `usages` counting all match locations; the sentinel arithmetic
  (set_to = depth_root_to_arg − 1 ⇒ #i counts crossed lambdas from inside;
  shift = −min(m, max(F)+1) because the downshift block is guarded on
  remaining free vars; expands_to seeded from the unshifted node at
  EMPTY_ZID and never updated); the rewriter (binary-search on match
  locations minus unused; ShiftRule cutoff = current depth, recursion depth
  = total_depth − shift, rules stack; assert = init_cost − util);
  `invalid_metavar_location` inert by default (TDFA/fused-tags only), so
  mini's unfiltered fresh-ivar expansion is exact parity.
* **~40 file:line citations** across expr.rkt, pattern.rkt, search.rkt,
  rewrite.rkt, micro.rkt, and the two Rust-facing notes, against
  compression.rs / expansion.rs / pattern_args.rs / rewriting.rs /
  egraphs.rs / util.rs and the pinned lambdas crate (expr.rs, analysis.rs,
  parse_expr.rs). All accurate to within a couple of lines; none pointed at
  the wrong construct except the `--utility-by-rewrite` nit in finding 5.
* **Uncommitted parity claims**: wheels and dials (todo.md) — both match the
  real binary at arity 2, iteration 1.
* **Paper claims quoted in the docs**: Eq. 3 (rewritten corpus), Eq. 8/10/12
  (utility decomposition), Eq. 14 (the paper's bound is Σ cost(e) — looser
  than the implemented one; the digest describes the paper's, search.rkt
  describes the Rust's, correctly attributed on both sides), Eq. 15 (micro's
  DP, correctly rephrased in costs with the argmax-preserving constant
  noted), §4.3 and footnote 2, Lemma 2, the best-bound/A* framing and the
  paper's own report that ordering mattered mainly for anytime behavior
  (paper digest states this correctly; the walkthrough's §3.7 is consistent).

**Areas with no significant findings, in one line each**: expr.rkt (including
the long sentinel/shift derivation — correct, and its min() subtlety is real
and tested); pattern.rkt (self-overlap machinery matches the ziptrie
semantics on all four subtleties); rewrite.rkt (shift rules, unused
locations, argument order all verified against the Rust and the binary);
compress.rkt (iteration semantics and early stop match `multistep_compression`);
micro.rkt code (the DP, matcher, lift, and filters are correct, and its DP-vs-
greedy tie behavior genuinely coincides with stitch's used/unused semantics);
the paper digest note (accurate throughout); HtDP style (genuinely followed:
signatures, purpose statements, and examples are present and the examples are
real tests).

---

## Executive summary

1. The replication is real: 85/85 differential runs reproduce (83 MATCH, 2
   verified ties), every walkthrough number I recomputed is exact, and every
   Rust parity path I re-derived checks out.
2. The stitch over-count bug note is correct end to end: mechanism, numbers
   (705/604, 605/606, 504/505), the can_self_unify explanation, and the
   stack-overflow of `--utility-by-rewrite` all reproduce.
3. Worst prose error: walkthrough §6's claim that survivors of the dominance
   prunings are "exactly the anti-unifier of their match set" is false —
   demonstrated with a corpus where five non-lgg generalizations reach scoring.
4. Worst tooling gap: an UNEXPECTED tie cannot fail the differential suite
   (printf-only), and a TIE verdict silently absorbs mismatch notes recorded
   before the tie point.
5. README's "matches real stitch step for step" overclaims; the repo's own
   tie corpus proves the searches take different steps.
6. The abstraction-size penalty (−cost_{α=0}(A)) is an implementation-vs-paper
   divergence (Eq. 8 with the paper's cost_α=100 gives −100 on simple1, not
   200) that the docs assert is "the paper's" rather than signposting.
7. Notes are stale in places: the design addendum says micro drops
   redundant-argument (it keeps it); todo.md's "27/28" and wheels/dials claims
   are unreproducible from the repo (though I verified wheels/dials do match).
8. The fuzz statistics' headline numbers match preserved outputs, but the
   scripts live only in an ephemeral scratchpad; one belongs in tests/.
9. Decision audit: bug-parity, zipper-table omission, filter retention, and
   cost hardcoding are all defensible and mostly honestly costed; only the
   zipper table's one-lookup/shared-shift role is mildly understated.
10. No errors found in expr/pattern/rewrite/compress code or comments, the
    paper digest, or the HtDP claim — the numeric documentation is flawless.
