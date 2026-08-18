# Results: anti-unification feasibility for stitch's abstraction search

All numbers below are **measured** on this VM (Python 3.11.15, single core,
stdlib only; stitch built from the submodule with `cargo build --release`,
run single-threaded at `--max-arity=2 --iterations=1` unless noted).
Corpora: all of `stitch/data/basic/*.json` (simple3/4/5 skipped — fused-lambda
tags) plus cogsci `nuts-bolts.json`, `wheels.json`, `dials.json` (250 programs
each). Tables regenerable via `python3 gen_tables.py` from
`results_a.jsonl` / `results_b.jsonl`.

## Part A — corpus stats and the pairwise anti-unification space

Pairwise Plotkin lggs (de Bruijn-aware, variables keyed by shifted subtree
pairs, canonicalized by first occurrence) over all unordered pairs of distinct
unique subtrees with compatible top constructors (app/app or lam/lam; all
other pairs anti-unify to a bare variable = "trivial pairs", counted but not
computed). "au subproblems" = distinct memoized au(a,b,depth) entries + one
root call per pair — the analogue of a datalog join's intermediate relation.
"w/ repeated var" = distinct lggs in which some variable occurs more than
once (multiuse). All rows completed; nothing timed out (600 s budget).

| corpus | prefix | progs | tree nodes | unique subtrees S | compatible pairs | trivial pairs | distinct lggs | w/ repeated var | max vars | au subproblems | au wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| cex | full | 2 | 78 | 24 | 78 | 198 | 10 | 0 | 8 | 201 | 0.001 |
| ctx_thread_1 | full | 2 | 50 | 25 | 84 | 216 | 15 | 4 | 4 | 207 | 0.001 |
| ctx_thread_2 | full | 2 | 46 | 22 | 61 | 170 | 14 | 3 | 4 | 153 | 0.000 |
| ctx_thread_twice | full | 2 | 58 | 28 | 111 | 267 | 17 | 4 | 5 | 276 | 0.001 |
| hof | full | 3 | 86 | 31 | 213 | 252 | 19 | 2 | 4 | 427 | 0.001 |
| identical | full | 2 | 18 | 9 | 6 | 30 | 3 | 0 | 4 | 18 | 0.000 |
| issue108 | full | 1 | 22 | 18 | 42 | 111 | 11 | 0 | 2 | 124 | 0.000 |
| issue108_2 | full | 1 | 28 | 26 | 69 | 256 | 8 | 0 | 5 | 196 | 0.000 |
| lio_test1 | full | 6 | 1180 | 206 | 13041 | 8074 | 606 | 83 | 26 | 25332 | 0.068 |
| lio_test2 | full | 1 | 181 | 96 | 2278 | 2282 | 176 | 11 | 20 | 4858 | 0.011 |
| map | full | 2 | 106 | 50 | 534 | 691 | 36 | 0 | 6 | 1183 | 0.002 |
| map2 | full | 2 | 68 | 40 | 237 | 543 | 32 | 0 | 6 | 602 | 0.001 |
| map_minimal | full | 2 | 64 | 32 | 211 | 285 | 21 | 0 | 5 | 470 | 0.001 |
| safe_ctx_thread_bug | full | 2 | 30 | 21 | 51 | 159 | 10 | 0 | 3 | 124 | 0.000 |
| simple1 | full | 2 | 10 | 6 | 6 | 9 | 5 | 2 | 2 | 12 | 0.000 |
| simple2 | full | 2 | 12 | 8 | 7 | 21 | 6 | 3 | 2 | 15 | 0.000 |
| simple3 | - | 2 | (skipped: fused-lambda tags) |  |  |  |  |  |  |  |  |
| simple4 | - | 2 | (skipped: fused-lambda tags) |  |  |  |  |  |  |  |  |
| simple5 | - | 2 | (skipped: fused-lambda tags) |  |  |  |  |  |  |  |  |
| simple_hof | full | 2 | 20 | 11 | 16 | 39 | 5 | 3 | 2 | 42 | 0.000 |
| symbol_weighting_test_1 | full | 4 | 48 | 22 | 55 | 176 | 8 | 0 | 6 | 148 | 0.000 |
| symbol_weighting_test_2 | full | 4 | 56 | 26 | 78 | 247 | 7 | 0 | 7 | 213 | 0.000 |
| tmp_crash | full | 2 | 20 | 15 | 22 | 83 | 6 | 0 | 3 | 58 | 0.000 |
| tmp_minimal | full | 1 | 73 | 42 | 496 | 365 | 207 | 149 | 18 | 1043 | 0.004 |
| nuts-bolts | 25 | 25 | 3199 | 208 | 16653 | 4875 | 518 | 166 | 13 | 27658 | 0.108 |
| nuts-bolts | 50 | 50 | 7642 | 263 | 28203 | 6250 | 1031 | 514 | 16 | 43384 | 0.192 |
| nuts-bolts | 100 | 100 | 12264 | 300 | 37675 | 7175 | 1313 | 655 | 16 | 54272 | 0.289 |
| nuts-bolts | full | 250 | 37766 | 455 | 92235 | 11050 | 3019 | 1774 | 16 | 110623 | 1.081 |
| dials | full | 250 | 71174 | 1225 | 689725 | 59975 | 22087 | 16687 | 56 | 1058377 | 7.661 |
| wheels | full | 250 | 70602 | 1663 | 1206681 | 175272 | 9538 | 3339 | 39 | 1840734 | 10.860 |

Arena growth from shifted copies + interned patterns (measured, full runs):
nuts-bolts 455 → 105,504 nodes; dials 1,225 → 889,149; wheels 1,663 →
1,442,688.

**Scaling (nuts-bolts prefixes, measured):** programs 25→250 (10x) grows
tree nodes 3,199→37,766 (11.8x) but unique subtrees only 208→455 (2.2x),
compatible pairs 16,653→92,235 (5.5x), and wall time 0.11 s→1.08 s.
Hash-consing absorbs most of the corpus growth; the pair space grows
quadratically in S, not in corpus size.

## Part B — is stitch's winner reachable by anti-unification?

Winner = first abstraction from the real binary at `--max-arity=2
--iterations=1`. Match set computed over unique corpus subtrees with
de Bruijn-aware consistent-shifted-argument binding (occurrences via
num-paths shown separately; the ≥2 sanity holds on occurrences — arity-0
winners match exactly 1 unique subtree occurring ≥2 times). No corpus had
any capturing match location (cap = 0 everywhere), so the all/non-capturing
check variants coincide; the table shows the "all" variant.

- **SEED** — winner == pairwise lgg of some pair of its match locations.
- **CLOSED** — winner == lgg of the entire match set.
- **+fv** — same, after re-generalizing free de Bruijn vars in the lgg
  (stitch bans free vars in abstraction bodies).
- **winner ⊇ set-lgg** — winner subsumes the set-lgg (matches it with the
  lgg's variables frozen as opaque constants).

| corpus | winner body (a2 i1) | arity | utility | uniq matches | occurrences | SEED | SEED+fv | CLOSED | CLOSED+fv | winner ⊇ set-lgg | worklist steps |
|---|---|---|---|---|---|---|---|---|---|---|---|
| cex | `(a b c d e f g h (A B C) (A B C) (A B C) (A B C))` | 0 | 1819 | 1 | 2 | - | - | - | - | - | 48 |
| ctx_thread_1 | `(A (lam (lam (+ (#0 $0 f) (#0 $0 f)))))` | 1 | 1011 | 2 | 2 | no | no | no | no | yes | 346 |
| ctx_thread_2 | `(lam (lam (+ (#0 $0 f) (#0 $0 f))))` | 1 | 910 | 2 | 2 | no | no | no | no | yes | 233 |
| ctx_thread_twice | `(A (lam (lam (+ (#0 $0 $1 f) (#0 $0 $1 f)))))` | 1 | 1213 | 2 | 2 | no | no | no | no | yes | 410 |
| hof | `(app (app cons (app #1 #0)) (app (app cons (app #1 #0)) e...` | 2 | 2320 | 3 | 3 | no | yes | no | yes | yes | 305 |
| identical | `(a b c d e)` | 0 | 304 | 1 | 2 | - | - | - | - | - | 6 |
| issue108 | (no compressive abstraction) |  |  |  |  |  |  |  |  |  | 1 |
| issue108_2 | (no compressive abstraction) |  |  |  |  |  |  |  |  |  | 1 |
| lio_test1 | `(C (T (T (T (C (r_s 12 5) (T (repeat (T r (M 0.84375 0 0 ...` | 2 | 14745 | 2 | 4 | yes | yes | yes | yes | yes | 7335 |
| lio_test2 | (no compressive abstraction) |  |  |  |  |  |  |  |  |  | 1 |
| map | `(app (app (app if (app is_nil #0)) nil))` | 1 | 505 | 1 | 2 | - | - | - | - | - | 997 |
| map2 | `(if (nil? #0) nil (cons #1 (r (cdr #0))))` | 2 | 604 | 2 | 2 | no | no | no | no | yes | 373 |
| map_minimal | `(app (app cons #1) (app rec (app cdr #0)))` | 2 | 504 | 2 | 2 | no | no | no | no | yes | 192 |
| safe_ctx_thread_bug | `(Y (lam (lam (is_nil $0 nil (cons (#0 $0))))))` | 1 | 406 | 2 | 2 | yes | yes | yes | yes | yes | 133 |
| simple1 | `(#0 #0 #0)` | 1 | 200 | 2 | 2 | yes | yes | yes | yes | yes | 6 |
| simple2 | `(#0 (lam (#0 #0)))` | 1 | 201 | 2 | 2 | yes | yes | yes | yes | yes | 12 |
| simple3 | (skipped: fused-lambda tags) |  |  |  |  |  |  |  |  |  |  |
| simple4 | (skipped: fused-lambda tags) |  |  |  |  |  |  |  |  |  |  |
| simple5 | (skipped: fused-lambda tags) |  |  |  |  |  |  |  |  |  |  |
| simple_hof | `(#0 #0)` | 1 | 201 | 2 | 2 | no | no | no | no | yes | 34 |
| symbol_weighting_test_1 | `(+ (+ 1 2) (+ 3 4))` | 0 | 506 | 1 | 2 | - | - | - | - | - | 16 |
| symbol_weighting_test_2 | `(* (/ 5 6) (& L1 L2 L3))` | 0 | 607 | 1 | 2 | - | - | - | - | - | 16 |
| tmp_crash | (no compressive abstraction) |  |  |  |  |  |  |  |  |  | 23 |
| tmp_minimal | (no compressive abstraction) |  |  |  |  |  |  |  |  |  | 1 |
| nuts-bolts | `(T (repeat (T l (M 1 0 -0.5 (/ 0.5 (tan (/ pi #1))))) #1 ...` | 2 | 837792 | 8 | 320 | yes | yes | yes | yes | yes | 2520 |
| wheels | `(M 1 0)` | 0 | 699628 | 1 | 3465 | - | - | - | - | - | 23896 |
| dials | `(C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0...` | 1 | 750733 | 2 | 127 | yes | yes | yes | yes | yes | 12368 |

### The six non-CLOSED cases, classified with `--follow --follow-prune` probes

Each probe hands stitch the set-lgg (fv-regeneralized where it contains free
de Bruijn vars) as a followed pattern and reads off the utility stitch itself
assigns it (measured; the follow assertion then panics on ivar numbering,
which is harmless — the utility line prints first).

| corpus | set-lgg of the winner's match set | lgg arity | stitch utility of set-lgg | winner utility | verdict |
|---|---|---|---|---|---|
| ctx_thread_1 | `(A (lam (lam (+ (a b #0 $0 f) (a b #0 $0 f)))))` | 1 | 1011 | 1011 | **exact tie**; stitch happened to report the coarser merge |
| ctx_thread_2 | `(lam (lam (+ (a b #0 $0 f) (a b #0 $0 f))))` | 1 | 910 | 910 | **exact tie** |
| ctx_thread_twice | `(A (lam (lam (+ (a b #0 $0 $1 f) (a b #0 $0 $1 f)))))` | 1 | 1213 | 1213 | **exact tie** |
| simple_hof | `(#0 #1 (#0 #1))` | 2 | 199 | 201 | **winner strictly better**: merging the repeated subpattern `(#0 #1)` into one variable `(#0 #0)` beats the lgg by 2 |
| map2 | `(if (nil? #0) nil (cons (#1 #2 (car #0) #3) (r (cdr #0))))` | 4 | 904 (needs `-a4`) | 604 | **arity cap**: lgg exceeds max-arity 2. At `-a4` stitch's winner is one merge above the lgg (arity 3, util 905 vs 904) |
| map_minimal | `(app (app cons (app (app #0 (app car #1)) #2)) (app rec (app cdr #1)))` | 3 | 1108 (needs `-a3`) | 504 | **arity cap**: at `-a3` stitch's winner IS exactly this set-lgg (util 1108) |

## Part C — top-down search-space size vs the bottom-up pair space

`worklist_steps` scraped from stitch's end-of-step `Stats { ... }` printout
(single thread, default optimizations, a2 i1) = partial patterns actually
expanded by the pruned top-down search. Compared against the unpruned
bottom-up pair space from Part A (full corpora).

| corpus | top-down worklist steps (with pruning) | bottom-up compatible pairs (no pruning) | distinct pairwise lggs | ratio pairs/steps |
|---|---|---|---|---|
| cex | 48 | 78 | 10 | 1.6x |
| ctx_thread_1 | 346 | 84 | 15 | 0.2x |
| ctx_thread_2 | 233 | 61 | 14 | 0.3x |
| ctx_thread_twice | 410 | 111 | 17 | 0.3x |
| hof | 305 | 213 | 19 | 0.7x |
| identical | 6 | 6 | 3 | 1.0x |
| issue108 | 1 | 42 | 11 | 42.0x |
| issue108_2 | 1 | 69 | 8 | 69.0x |
| lio_test1 | 7335 | 13041 | 606 | 1.8x |
| lio_test2 | 1 | 2278 | 176 | 2278.0x |
| map | 997 | 534 | 36 | 0.5x |
| map2 | 373 | 237 | 32 | 0.6x |
| map_minimal | 192 | 211 | 21 | 1.1x |
| safe_ctx_thread_bug | 133 | 51 | 10 | 0.4x |
| simple1 | 6 | 6 | 5 | 1.0x |
| simple2 | 12 | 7 | 6 | 0.6x |
| simple_hof | 34 | 16 | 5 | 0.5x |
| symbol_weighting_test_1 | 16 | 55 | 8 | 3.4x |
| symbol_weighting_test_2 | 16 | 78 | 7 | 4.9x |
| tmp_crash | 23 | 22 | 6 | 1.0x |
| tmp_minimal | 1 | 496 | 207 | 496.0x |
| nuts-bolts | 2520 | 92235 | 3019 | 36.6x |
| wheels | 23896 | 1206681 | 9538 | 50.5x |
| dials | 12368 | 689725 | 22087 | 55.8x |

## Observations

1. **Feasibility (measured): the full pairwise-AU space is small and cheap on
   every corpus tried.** Worst case (wheels): 250 programs / 70,602 tree
   nodes collapse to 1,663 unique subtrees; the full 1.21M compatible pairs
   anti-unify in 10.9 s of pure single-core Python, producing 1.84M memoized
   au subproblems and only 9,538 distinct canonical lgg patterns. Nothing
   timed out; the planned prefix fallback for nuts-bolts was unnecessary
   (full corpus: 1.08 s).

2. **Hash-consing + shifted-pair variable keying are doing almost all of the
   work.** The pattern dedup ratio (compatible pairs → distinct lggs) is
   31x–127x on the cogsci corpora. The de Bruijn-aware keying matters for
   content, too: 59% of nuts-bolts' distinct lggs and 76% of dials' have a
   repeated variable (multiuse patterns like stitch's `(#0 #0 #0)` winners),
   which naive positional anti-unification would miss.

3. **Reachability (measured): stitch's winner subsumes the match-set lgg in
   all 13 runs that have ≥2 unique match locations; it EQUALS it (exactly or
   after free-var re-generalization) in 7 of 13.** The 6 exceptions split
   cleanly (probe table above): 3 exact utility ties where the lgg is
   co-optimal, 2 arity-cap effects where the lgg exceeds `--max-arity=2` (and
   at sufficient arity the lgg is the winner or within one merge of it), and
   1 case (simple_hof, util 201 vs 199) where a coarser merge is genuinely
   strictly better. In every winner-vs-lgg gap the winner is obtained from
   the lgg by "upward" moves only: replacing a subpattern (possibly
   containing variables) by a single variable. So pairwise AU + fold reaches
   a *lower bound* of the winner in the subsumption lattice; a bottom-up
   system needs an additional bounded upward-merge phase (merge subpatterns
   into variables, re-scoring utility) to close the gap — it never needs to
   *specialize* below an lgg.

4. **The free-var re-generalization is a real, mechanical discrepancy source
   (predicted, now measured):** hof's set-lgg keeps the shared free `$0`
   concrete; stitch's body ban on free de Bruijn vars forces `#1` there.
   After re-generalizing free-var positions the lgg equals the winner
   exactly. SEED and CLOSED verdicts agreed in every run (no case where a
   pair-lgg hits the winner but the set-lgg misses, or vice versa); hof's
   winner is already the +fv lgg of a single pair (inc/dec programs).

5. **Arity-0 winners are a degenerate case for AU:** cex, identical, map,
   symbol_weighting_*, wheels have winners matching exactly one unique
   subtree (2–3,465 occurrences). These are trivially "reachable bottom-up"
   — they are corpus subtrees, no anti-unification involved — but they mean
   a bottom-up formulation must also enumerate repeated concrete subtrees,
   not only nontrivial lggs. (map's arity-1 winner also matches a single
   unique subtree; its variable's argument is constant across occurrences.)

6. **Search-space comparison (measured, with caveats):** on the cogsci
   corpora, stitch's pruned top-down search expands 37x–56x FEWER partial
   patterns than the unpruned bottom-up pair count (nuts-bolts 2,520 steps vs
   92,235 pairs). But the *deduplicated* bottom-up space — distinct lggs — is
   the same order of magnitude as the top-down step count (3,019 vs 2,520;
   9,538 vs 23,896; 22,087 vs 12,368): structural dedup buys roughly what
   branch-and-bound buys on this data. The datalog-relevant number is the
   intermediate relation (au subproblems): 1.1M–1.8M tuples for the largest
   corpora, i.e. 20x–150x the distinct-lgg count but still tiny by datalog
   standards. Caveats: worklist steps are utility-pruned and would grow with
   weaker bounds; the pair space is only the FIRST level of a bottom-up
   closure (lggs of lggs were not enumerated, though Part B suggests folds
   over match sets suffice to reach winners); units are "patterns touched",
   not wall time.

7. **Surprises / anomalies:** (a) `worklist_steps=1` corpora (issue108,
   issue108_2, lio_test2, tmp_minimal) are single-program corpora where stitch's
   single-task prune kills everything immediately, yet their pairwise-AU
   spaces are sizable (up to 2,278 pairs) — a bottom-up system would need the
   same multi-program filter to avoid wasted work. (b) wheels' top-down
   search is oddly expensive (23,896 steps for an arity-0 winner `(M 1 0)`).
   (c) No capturing match location occurred for any winner on any corpus —
   the capture machinery is exercised by the checks but never fires on
   winners' match sets at a2 i1.
