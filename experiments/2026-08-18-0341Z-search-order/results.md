# Results: does branch-and-bound exploration order matter?

**Setup.** One `search` call per (corpus, mode); modes are `best` (max-heap
on utility upper bound — the original), `fifo` (plain queue, approximating
the level-synchronous order a Datalog stratum would impose), `lifo` (stack,
DFS). All pruning identical across modes, including the bound<=cutoff check
at push and the cutoff re-check at pop. Headline number is **pops-expanded**:
patterns popped that survived the cutoff re-check and were expanded.
Machine: the shared 4-core VM; wall-clock is per-search
`current-inexact-milliseconds`, single run, so treat ms as rough (a
concurrent agent was active on the machine — counts are exact and
deterministic, times are not).

Columns: pops-expanded per mode, ratios, `considered` (consider! calls) per
mode, wall ms per mode, winner utility.

## max-arity 2

| corpus | pops best | pops fifo | pops lifo | fifo/best | lifo/best | considered best | considered fifo | considered lifo | ms best | ms fifo | ms lifo | utility |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| cex | 48 | 48 | 48 | 1.00 | 1.00 | 148 | 148 | 148 | 0.8 | 0.5 | 0.6 | 1819 |
| ctx_thread_1 | 346 | 347 | 346 | 1.00 | 1.00 | 594 | 596 | 594 | 3.3 | 3 | 2.9 | 1011 |
| ctx_thread_2 | 233 | 234 | 233 | 1.00 | 1.00 | 413 | 415 | 413 | 2 | 2.1 | 2 | 910 |
| ctx_thread_twice | 410 | 412 | 411 | 1.00 | 1.00 | 683 | 686 | 684 | 3.9 | 3.7 | 3.6 | 1213 |
| hof | 305 | 328 | 328 | 1.08 | 1.08 | 513 | 550 | 550 | 3.6 | 3.5 | 3.6 | 2320 |
| identical | 6 | 6 | 6 | 1.00 | 1.00 | 23 | 23 | 23 | 0.2 | 0.1 | 0.2 | 304 |
| issue108 | 1 | 1 | 1 | 1.00 | 1.00 | 7 | 7 | 7 | 0.1 | 0.1 | 0.1 | - |
| issue108_2 | 1 | 1 | 1 | 1.00 | 1.00 | 14 | 14 | 14 | 0.1 | 0.1 | 0.1 | - |
| lio_test1 | 7335 | 8255 | 7855 | 1.13 | 1.07 | 10897 | 12417 | 11700 | 159.1 | 164.6 | 267.2 | 14745 |
| lio_test2 | 1 | 1 | 1 | 1.00 | 1.00 | 30 | 30 | 30 | 0.3 | 0.2 | 0.2 | - |
| map | 997 | 999 | 999 | 1.00 | 1.00 | 1520 | 1524 | 1524 | 10.3 | 10.5 | 9.5 | 505 |
| map2 | 373 | 375 | 375 | 1.01 | 1.01 | 668 | 672 | 672 | 3.8 | 3.2 | 3.7 | 604 |
| map_minimal | 192 | 193 | 193 | 1.01 | 1.01 | 365 | 367 | 367 | 2.2 | 1.9 | 2 | 504 |
| safe_ctx_thread_bug | 133 | 136 | 136 | 1.02 | 1.02 | 253 | 259 | 259 | 1.1 | 1.2 | 1 | 406 |
| simple1 | 6 | 6 | 6 | 1.00 | 1.00 | 24 | 24 | 24 | 0.1 | 0.1 | 0.1 | 200 |
| simple2 | 12 | 12 | 12 | 1.00 | 1.00 | 42 | 42 | 42 | 0.2 | 0.2 | 0.2 | 201 |
| simple_hof | 34 | 34 | 34 | 1.00 | 1.00 | 91 | 91 | 91 | 0.4 | 0.3 | 0.4 | 201 |
| symbol_weighting_test_1 | 16 | 16 | 16 | 1.00 | 1.00 | 64 | 64 | 64 | 0.3 | 0.3 | 0.3 | 506 |
| symbol_weighting_test_2 | 16 | 16 | 16 | 1.00 | 1.00 | 73 | 73 | 73 | 0.3 | 0.3 | 0.3 | 607 |
| tmp_crash | 23 | 23 | 23 | 1.00 | 1.00 | 63 | 63 | 63 | 0.4 | 0.3 | 0.3 | - |
| tmp_minimal | 1 | 1 | 1 | 1.00 | 1.00 | 12 | 12 | 12 | 0.1 | 0.1 | 0.2 | - |
| nuts-bolts | 2520 | 4404 | 3136 | 1.75 | 1.24 | 4076 | 6686 | 4803 | 463.7 | 694.5 | 511.3 | 837792 |
| wheels | 23896 | 23896 | 23896 | 1.00 | 1.00 | 31900 | 31900 | 31900 | 1936.6 | 1948 | 2004.4 | 699628 |
| dials | 12368 | 13414 | 12725 | 1.08 | 1.03 | 20723 | 22230 | 21181 | 1020.4 | 1165.4 | 1034.6 | 750733 |

TOTALS arity 2: best pops=49273 considered=73196 ms=3613;  fifo pops=53158 considered=78893 ms=4004;  lifo pops=50798 considered=75238 ms=3849;  

## max-arity 3

| corpus | pops best | pops fifo | pops lifo | fifo/best | lifo/best | considered best | considered fifo | considered lifo | ms best | ms fifo | ms lifo | utility |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| cex | 56 | 56 | 56 | 1.00 | 1.00 | 181 | 181 | 181 | 1 | 0.7 | 0.7 | 1819 |
| ctx_thread_1 | 418 | 419 | 418 | 1.00 | 1.00 | 844 | 846 | 844 | 4.5 | 4.2 | 7.4 | 1011 |
| ctx_thread_2 | 284 | 285 | 284 | 1.00 | 1.00 | 583 | 585 | 583 | 3.1 | 2.9 | 2.8 | 910 |
| ctx_thread_twice | 549 | 551 | 550 | 1.00 | 1.00 | 1061 | 1065 | 1063 | 6.3 | 5.9 | 5.7 | 1213 |
  (tie: bodies differ at ctx_thread_twice arity 3: ((A (lam (lam (+ (a b #0 $0 $1 f) (a b #0 $0 $1 f))))) (A (lam (lam (+ (#0 $0 $1 f) (#0 $0 $1 f))))) (A (lam (lam (+ (#0 $0 $1 f) (#0 $0 $1 f)))))))
| hof | 457 | 487 | 487 | 1.07 | 1.07 | 880 | 938 | 938 | 9.3 | 8.4 | 8.3 | 2320 |
| identical | 7 | 7 | 7 | 1.00 | 1.00 | 27 | 27 | 27 | 0.1 | 0.2 | 0.1 | 304 |
| issue108 | 1 | 1 | 1 | 1.00 | 1.00 | 7 | 7 | 7 | 0.1 | 0.1 | 0.1 | - |
| issue108_2 | 1 | 1 | 1 | 1.00 | 1.00 | 14 | 14 | 14 | 0.1 | 0.1 | 0.1 | - |
| lio_test1 | 15737 | 15856 | 15969 | 1.01 | 1.01 | 27362 | 27612 | 27827 | 362 | 345.7 | 354.3 | 15653 |
| lio_test2 | 1 | 1 | 1 | 1.00 | 1.00 | 30 | 30 | 30 | 0.4 | 0.3 | 0.4 | - |
| map | 1894 | 1946 | 1946 | 1.03 | 1.03 | 3143 | 3251 | 3251 | 24.7 | 22.6 | 22.3 | 1310 |
| map2 | 531 | 540 | 540 | 1.02 | 1.02 | 1055 | 1073 | 1073 | 6 | 5.6 | 5.7 | 905 |
| map_minimal | 343 | 352 | 352 | 1.03 | 1.03 | 656 | 674 | 674 | 4.7 | 4.4 | 4.4 | 1108 |
| safe_ctx_thread_bug | 136 | 139 | 139 | 1.02 | 1.02 | 300 | 306 | 306 | 1.4 | 1.3 | 1.5 | 406 |
| simple1 | 6 | 6 | 6 | 1.00 | 1.00 | 25 | 25 | 25 | 0.1 | 0.1 | 0.1 | 200 |
| simple2 | 12 | 12 | 12 | 1.00 | 1.00 | 43 | 43 | 43 | 0.2 | 0.2 | 0.2 | 201 |
| simple_hof | 40 | 40 | 40 | 1.00 | 1.00 | 121 | 121 | 121 | 0.5 | 0.4 | 0.6 | 201 |
| symbol_weighting_test_1 | 22 | 22 | 22 | 1.00 | 1.00 | 85 | 85 | 85 | 0.3 | 0.3 | 0.4 | 506 |
| symbol_weighting_test_2 | 24 | 24 | 24 | 1.00 | 1.00 | 97 | 97 | 97 | 0.4 | 0.4 | 0.4 | 607 |
| tmp_crash | 24 | 24 | 24 | 1.00 | 1.00 | 69 | 69 | 69 | 0.3 | 0.5 | 0.4 | - |
| tmp_minimal | 1 | 1 | 1 | 1.00 | 1.00 | 12 | 12 | 12 | 0.2 | 0.1 | 0.2 | - |

TOTALS arity 3: best pops=20544 considered=36595 ms=426;  fifo pops=20770 considered=37061 ms=404;  lifo pops=20880 considered=37270 ms=416;  

## Aggregate ratios (pops-expanded)

| sweep | best | fifo | fifo/best | lifo | lifo/best |
|---|---:|---:|---:|---:|---:|
| arity 2, all 24 corpora | 49273 | 53158 | 1.079 | 50798 | 1.031 |
| arity 2, excluding wheels | 25377 | 29262 | 1.153 | 26902 | 1.060 |
| arity 3, data/basic only | 20544 | 20770 | 1.011 | 20880 | 1.016 |

Total wall clock (sum over corpora): arity 2 — best 3613 ms, fifo 4004 ms,
lifo 3849 ms; arity 3 — best 426 ms, fifo 404 ms, lifo 416 ms.

## Observations

1. **Winner utilities are equal across modes on every corpus, both arities**
   (measured — `aggregate.rkt` asserts it; zero mismatches). Bodies are also
   identical everywhere except one equal-utility tie: `ctx_thread_twice` at
   max-arity 3, where best finds
   `(A (lam (lam (+ (a b #0 $0 $1 f) (a b #0 $0 $1 f)))))` and fifo/lifo find
   `(A (lam (lam (+ (#0 $0 $1 f) (#0 $0 $1 f)))))`, both at utility 1213 —
   the same corpus/arity as the repo's one documented mini-vs-stitch tie.

2. **Order barely matters for exploration volume.** fifo/best on
   pops-expanded is 1.00 on 15 of 24 corpora at arity 2, and never exceeds
   1.75. The grand totals put FIFO at +7.9% pops over best-first (+15.3%
   excluding wheels) and LIFO at +3.1%. At arity 3 on data/basic the effect
   nearly vanishes (+1.1% / +1.6%).

3. **Where order matters most: nuts-bolts** (arity 2), fifo/best = 1.75
   (2520 -> 4404 pops), lifo/best = 1.24. Next: lio_test1 at 1.13, dials at
   1.08, hof at 1.08. These are exactly the corpora where the winner is
   found mid-search and substantially beats the arity-zero primed cutoff, so
   reaching it early pays.

4. **Why so many corpora show ratio 1.00: the arity-zero priming often sets
   the final (or near-final) cutoff before the search starts** (inference
   from the mechanism, supported by the data). Extreme case: `wheels`, the
   largest run (23896 pops, ~2 s), has *identical* counts in all three modes
   and pushed == pops-expanded (the pop re-check never fires) — its winner
   `(M 1 0)` is the arity-zero abstraction found by priming, so the cutoff
   never moves during the search and order provably cannot change the
   explored set. When the cutoff is static, branch-and-bound explores
   exactly the set {patterns whose parent chain stays above cutoff},
   independent of order.

5. **Wall clock tracks pops.** FIFO's overhead is proportional to its extra
   pops (nuts-bolts: 464 -> 695 ms). No mode is asymptotically different
   here. One anomaly: lio_test1 arity-2 lifo took 267 ms vs best's 159 ms
   despite only 7% more pops — single-run noise/GC on a busy VM, not a
   pattern (the arity-3 run of the same corpus shows no such gap).

6. **No timeouts, no errors.** Every (corpus, mode) pair completed well
   under the 180 s guard; the longest single search was wheels at ~2 s.

## Implication for the Datalog/relational reformulation

On these corpora, giving up best-first order for level-synchronous (FIFO)
expansion costs at most ~1.75x exploration on the worst corpus and ~1.08x
overall — the branch-and-bound's power comes almost entirely from the
cutoff (heavily seeded by arity-zero priming) and the five prunings, not
from the exploration order. A stratum-synchronous cutoff that updates
between levels would if anything sit *between* our FIFO (cutoff updates
immediately, within the level) and a no-mid-level-update variant, so the
true stratified cost may be slightly above the FIFO numbers here — but the
FIFO numbers bound how much order-sensitivity there is to lose, and it is
small. Caveat: this is mini-stitch's single-threaded search on small-to-
medium corpora; the biggest run is ~24k pops. Order sensitivity could grow
on corpora where the best abstraction is found very late relative to a weak
primed cutoff.
