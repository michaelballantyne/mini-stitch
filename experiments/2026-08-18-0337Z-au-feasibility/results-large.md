# Results (extension): larger corpora — AU space vs top-down cost

Extends `results.md` to the larger corpora checked into the stitch submodule
(`stitch/data/logo`, `data/dc`, `data/python`, plus the start of the remaining
`data/cogsci` domains). All numbers **(measured)** on this VM (same setup as
`results.md`: Python 3.11 stdlib harness, single core; stitch binary from the
submodule, `--iterations=1`, single thread). Raw per-run records:
`results_large.jsonl` (one JSON object per row, `kind: "au" | "stitch"`).
Driver: `run_large.py` (subcommands `au` / `stitch`); DreamCoder-format
extraction: `extract_dc.py`.

**The run was cut short by a stop order (out of credits) partway through the
sweep** — see "NOT measured" at the bottom for the explicit gaps. In
particular the remaining cogsci domains (flagged mid-run as the highest-value
targets) got exactly one partial AU row (bridge) and no stitch runs.

## Corpus inventory and format notes

| file | format | disposition |
|---|---|---|
| `logo/train_{19,39,49,66,99,200}.json`, `test_111.json` | programs-list | measured (train_1/2/1_hard skipped: 1–2 programs, trivial). NOTE: the train_N files are independent samples, NOT prefixes of one another (checked: `train_200[:99] != train_99`). |
| `python/{10,100,1000}.json` | programs-list (s-expr Python ASTs) | NOT measured — AU on even `10.json` (319 KB, 10 programs) exceeded a 600 s wall before producing a record (see obs. 5). Also not prefixes of each other. Small python/*.json files (2–5 programs) skipped as trivial. |
| `dc/dc_logo_log.json` | DreamCoder (88 tasks / 802 programs, 0 inline inventions) | measured (extracted + dcfmt) |
| `dc/logo_iteration_1.json` | DreamCoder (80 tasks / 380 programs, 9 DSL inventions inlined as `#(lambda ...)`) | measured (extracted + dcfmt) |
| `dc/logo_iteration_1_stitchargs.json` | DreamCoder | skipped — extracted program list byte-identical to `logo_iteration_1.json` (only args metadata differs) |
| `dc/origami/iteration_{0_3,1_6,2_1,3_1}.json`, `nil_iteration_4.json` | DreamCoder (11–20 tasks, 49–100 programs, 0–11 inventions) | measured. `nil_iteration_5..9` skipped — md5-identical to `nil_iteration_4`. `info.json`/`types_origami.json` are metadata, not corpora. |
| `dc/origami/stitch_0_found0.json` | programs-list (49 programs) | measured |
| `logo/logo_dc.json` | DreamCoder (tiny) | skipped (trivial size) |
| `neurosym/*.json` | programs-list, 2 programs each, fused-lambda tags (`lam_1`) | skipped — trivial size AND fused tags (unsupported by the AU parser) |
| `expected_outputs/**` | stitch *outputs*, not corpora | out of scope |
| `cogsci/{bridge,city,castle,house,furniture}.json` | programs-list, 250 programs each | added to scope mid-run; only bridge AU (partial) completed before the stop order |

**DreamCoder extraction** (`extract_dc.py`, output in `tmp/*-extracted.json`):
replicates stitch's own loader (`stitch/src/formats.rs`) exactly — DSL
productions starting with `#` are sorted by increasing length, named
`dreamcoder_abstraction_i`, and textually substituted into every frontier
program longest-first; asserts no `#` remains. So the AU harness sees the
same token stream stitch compresses. What extraction does NOT preserve is
task grouping: in programs-list format stitch treats each program as its own
task, which changes its single-task pruning and utilities. For dreamcoder
corpora the stitch numbers are therefore reported BOTH ways: `flat` =
extracted programs-list, `dcfmt` = original file with `--fmt=dreamcoder`.
The AU numbers are task-agnostic (pairwise over unique subtrees) and apply
to both.

## Main table (measured)

AU columns as in `results.md` Part A (600 s budget). Stitch at
`--iterations=1`, wall = subprocess wall-clock, steps = `worklist_steps`
scraped from the Stats printout. For dreamcoder corpora the stitch cells
show `flat / dcfmt`.

| corpus | progs | tree nodes | S | compatible pairs | distinct lggs | w/ repeated var | au subproblems | AU wall (s) | stitch a2 steps | stitch a2 wall (s) | stitch a3 steps | stitch a3 wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| logo-train_19 | 19 | 772 | 239 | 14,581 | 205 | 12 | 28,243 | 0.07 | 597 | 0.007 | — | — |
| logo-train_39 | 39 | 2,043 | 348 | 32,001 | 444 | 19 | 61,465 | 0.17 | 816 | 0.011 | — | — |
| logo-train_49 | 49 | 2,825 | 399 | 42,606 | 623 | 48 | 81,382 | 0.22 | 1,642 | 0.014 | — | — |
| logo-train_66 | 66 | 4,259 | 489 | 65,571 | 908 | 118 | 124,400 | 0.38 | 3,105 | 0.021 | — | — |
| logo-train_99 | 99 | 7,256 | 715 | 139,601 | 1,678 | 329 | 268,813 | 0.85 | 3,253 | 0.032 | — | — |
| logo-train_200 | 200 | 20,370 | 1,497 | 604,515 | 7,799 | 2,913 | 1,162,962 | 5.22 | 3,705 | 0.096 | 14,091 | 0.156 |
| logo-test_111 | 111 | 12,796 | 1,124 | 345,036 | 5,959 | 1,917 | 647,581 | 2.53 | 5,874 | 0.070 | 23,958 | 0.126 |
| origami-stitch_0_found0 | 49 | 1,288 | 344 | 27,756 | 1,416 | 104 | 54,187 | 0.14 | 3,532 | 0.011 | — | — |
| origami-iteration_0_3 | 49 | 1,500 | 375 | 33,309 | 2,067 | 148 | 65,230 | 0.17 | 2,933 / 5,919 | 0.014 / 0.018 | — | — |
| origami-iteration_1_6 | 80 | 1,723 | 493 | 58,348 | 1,540 | 106 | 107,367 | 0.28 | 2,553 / 5,031 | 0.013 / 0.023 | — | — |
| origami-iteration_2_1 | 90 | 1,546 | 519 | 64,483 | 1,271 | 54 | 116,704 | 0.28 | 2,475 / 3,284 | 0.018 / 0.027 | — | — |
| origami-iteration_3_1 | 96 | 1,598 | 532 | 66,781 | 1,325 | 62 | 121,473 | 0.30 | 3,607 / 3,303 | 0.015 / 0.033 | — | — |
| origami-nil_iteration_4 | 100 | 1,621 | 555 | 72,136 | 1,522 | 79 | 131,853 | 0.32 | 3,279 / 3,505 | 0.014 / 0.031 | — | — |
| dc-logo_iteration_1 | 380 | 8,782 | 2,363 | 1,463,181 | 10,364 | 700 | 2,553,582 | 11.48 | 1,153 / 8,957 | 0.051 / 0.103 | — | — |
| dc-dc_logo_log | 802 | 17,077 | 3,391 | 3,069,506 | 23,274 | 3,624 | 4,940,073 | 26.78 | 878 / 8,030 | 0.087 / 0.137 | — | — |
| **cogsci bridge** | 250 | 68,264 | **6,901** | **23,540,091** | **≥3,952,896 (partial)** | 3,950,768 | 15,819,920 (partial) | **TIMED OUT: 8,152,713 / 23.5 M pairs done in 480 s** | not run | not run | not run | not run |

Bridge partial-row detail (measured): after 8.15 M of 23.5 M compatible pairs
(35 %), the distinct-lgg set already held 3,952,896 canonical patterns — a
dedup ratio of only **2.06x** (pairs-done : distinct lggs), vs 31–127x on
every earlier corpus. 99.95 % of those lggs contain a repeated variable, and
the largest pattern has **50 variables**. Max vars elsewhere in this table:
7–13.

## Nuts-bolts prefix scaling: top-down vs bottom-up (measured)

Stitch `--max-arity=2 --iterations=1` on prefix files (`tmp/nuts-bolts-pN.json`,
first N programs — same prefixes as the `results.md` Part A rows, whose AU
columns are repeated here for the comparison).

| prefix | AU: S | AU: compatible pairs | AU: distinct lggs | AU wall (s) | stitch worklist steps | stitch wall (s) |
|---|---|---|---|---|---|---|
| 25 | 208 | 16,653 | 518 | 0.108 | 2,333 | 0.011 |
| 50 | 263 | 28,203 | 1,031 | 0.192 | 2,770 | 0.018 |
| 100 | 300 | 37,675 | 1,313 | 0.289 | 1,855 | 0.020 |
| 250 | 455 | 92,235 | 3,019 | 1.081 | 2,520 | 0.048 |

(The p250 run reproduces the full-corpus row in `results.md`: 2,520 steps —
consistency check passed.)

**Top-down cost is nearly corpus-size-flat**: 10x more programs moves
worklist steps 2,333 → 2,520 (and non-monotonically — p100 is *lower* at
1,855 than p50's 2,770, i.e. bigger corpora can strengthen the utility bound
faster than they widen the space). Stitch wall grows 0.011 → 0.048 s,
roughly linear in corpus size (matching/rewriting work), not in search
space. Meanwhile the bottom-up side grows: pairs 5.5x, distinct lggs 5.8x,
AU wall 10x over the same prefixes.

## Observations

1. **S growth (measured): still sublinear in corpus size, but domain-
   dependent.** Nuts-bolts prefixes: 10x programs → 2.2x S (strong sharing;
   true prefixes). Logo train ladder: 10.5x programs → 6.3x S (239 → 1,497)
   — but these are independent samples, not prefixes, so part of that growth
   is distribution width, not accumulation. dc_logo_log reaches 802 programs
   with S = 3,391 (4.2 nodes of new structure per program). Bridge is the
   outlier: 250 programs → S = 6,901, 4–15x the S of the three cogsci domains
   already measured at the same program count (nuts-bolts 455, dials 1,225,
   wheels 1,663) — per-program structural diversity is much higher.

2. **AU space vs worklist steps (measured): same order of magnitude on every
   logo/origami/dc corpus — then diverges catastrophically on bridge.**
   Distinct lggs vs a2 steps: logo-train_200 7,799 vs 3,705 (2.1x);
   test_111 5,959 vs 5,874 (1.0x); origami 1.3–2.1k vs 2.5–5.9k (0.2–0.8x);
   dc_logo_log 23,274 vs 878/8,030 (2.9–27x). But on bridge the *partial*
   distinct-lgg count is already 3.95 M and growing ~linearly with pairs
   processed (dedup ratio 2.06x and falling slowly), so the full space is
   plausibly ~10 M+ distinct patterns. This is the first corpus in the whole
   experiment where structural dedup stops working: nearly every pair of
   bridge subtrees anti-unifies to a *distinct* multi-variable pattern (up
   to 50 variables). The unrestricted pairwise-AU space is NOT tractable
   there — a bottom-up formulation would need an arity/size cap on lggs
   (stitch caps arity at 2–3; an lgg with 50 variables is useless as an
   abstraction) or utility-style pruning *during* AU, not after.
   (inference — untested: capping variables per lgg at ≤3 during AU would
   collapse most of those 3.95 M patterns into a tiny quotient; the harness
   computes full lggs before canonicalization so this run can't tell.)

3. **Top-down scaling (measured): stitch's step count is set by domain
   structure + utility bounds, not corpus size or S.** Across everything run
   here at a2, steps stay in a 600–24,000 band while corpora span 19–802
   programs and S spans 239–3,391. Wall time never exceeded 0.16 s on any
   corpus stitch was run on (bridge and the other heavy cogsci domains were
   not run — the stitch paper reports those as its expensive cases, which is
   exactly the un-taken measurement that matters most).

4. **Arity 3 (measured, logo only): steps grow ~4x over a2** (train_200
   3,705 → 14,091; test_111 5,874 → 23,958), wall still ≤ 0.16 s. Winner
   utility unchanged (the a2 winner stays optimal at a3 on both).

5. **Python corpora: AU harness hits a wall immediately (measured only as a
   timeout).** `python/10.json` — just 10 programs, but huge ASTs with long
   leftward `/seq` spines and hundreds of distinct string prims — exceeded a
   600 s wall (parse + pair loop; killed before the budget checkpoint could
   record a partial row, a harness granularity bug worth noting: the budget
   check fires per outer row, too coarse when S is large). No AU or stitch
   numbers exist for python/*. (inference — untested: S here is likely in
   the tens of thousands, putting compatible pairs near 10^8–10^9; a
   quadratic-in-S enumeration is simply the wrong algorithm shape for this
   domain.)

6. **Task grouping matters to the top-down numbers (measured).** The same
   program set run as `--fmt=dreamcoder` (real tasks) vs flat programs-list
   (each program its own task) shifts worklist steps up to 9x
   (dc_logo_log: 878 flat vs 8,030 dcfmt; logo_iteration_1: 1,153 vs 8,957)
   and changes the winner and its utility (e.g. origami nil_iteration_4:
   util 1,930 flat vs 307 dcfmt). Flat mode lets many-programs-per-task
   duplicates count as separate "tasks", weakening single-task pruning's
   bite differently in each direction. Any bottom-up/top-down comparison
   must hold the task convention fixed.

## NOT measured (explicit gaps, cut off by the stop order)

- **cogsci bridge**: stitch a2 and a3 (steps + wall) — not run; AU row is
  partial (35 % of pairs, 480 s budget). No prefix-fallback rows run.
- **cogsci city, castle, house, furniture**: nothing measured (no AU, no
  stitch), despite being flagged mid-run as the highest-value targets (the
  stitch paper's own heavy end). This is the most important missing leg.
- **a3 stitch** on nuts-bolts/wheels/dials/origami/dc corpora (only the two
  big logo corpora got a3).
- **python/10, 100, 1000**: no completed measurements at all (see obs. 5);
  the planned program-count-prefix fallback (e.g. 2/5 programs) was not run.
- **AU on dreamcoder corpora at real task granularity** — AU here is
  task-agnostic; no per-task filtering variant was tried.
