# Adversarial review 2: the micro-first restructure

Scope: commit `f15fd82` ("Restructure micro as a standalone learning artifact")
against `b2259f9`. Three further commits landed on the branch while I was
working — `b3af41c` (gitignore), `428d089` ("Drop the inert COST-IVAR"),
`476c227` ("micro: correct the DP memo's story; extract surviving-children").
**Every line number and every claim below has been re-checked against
HEAD = `476c227`**, and `428d089`/`476c227` are reviewed too: between them they
resolve half of what was L9 and add one new drift (L12). Everything below was
run on this machine (Racket 8.10, `stitch/target/release/compress` at the
checked-out submodule rev). Paper citations are to the page-marked extraction
of `stitch.pdf`; page numbers are the article's own (41:N).

Prior review: `notes/2026-08-17-2110-adversarial-review.md`. Its five findings
were all addressed before this commit; none has regressed (checked: §6 lgg
prose, `known-ties` enforcement, README "step for step", the `cost_{α=0}`
signpost in walkthrough §1, `tests/fuzz.rkt` now checked in).

---

## Verdict

**1. The paper-relationship framing (the owner's worry).** Substantially sound,
and much better than what it replaced — the header is right on the three things
that matter most: it does not claim Algorithm 1, it names the naive-approach
paragraph correctly (the paragraph immediately before "Introducing Strict
Dominance Pruning", 41:10), and it is right that argument capture changes the
objective rather than only the speed (the paper says exactly that, 41:14, and
footnote 2 is real). But six specific defects, all fixable in single lines:
two citation errors (**L1**, **L2**), one section heading that contradicts two
of its own five bullets (**M2**), one silent substitution of the naive
approach's termination rule (**L5**), one *under*-claim — the ≥2-programs rule
**is** in the paper, §6 (41:18), two sentences after the cost constants micro
already cites (**L3**) — and one overstatement of micro's naivety, since
corpus-guidance and zero-usage pruning are both Algorithm 1 machinery that
micro does use (**L4**, **L5**).

Two structural questions the brief raised, answered:

* *Is "the paper's objective" a single well-defined thing?* No — Eq. 8 is
  `U_{P,R}` and is parameterized by the rewrite strategy R (41:9, "Rewrite
  Strategies"; 41:9, "Utility"). micro's header handles this correctly and
  explicitly: it pins R by taking §4.4's DP "as the *definition* of utility",
  and §4.4 says stitch's strategy is optimal (41:14). This is the right move
  and it is stated, not assumed.
* *Is the `cost_{α=0}` deviation load-bearing or cosmetic?* Load-bearing, and
  micro **under**states it. With Eq. 8 read literally and the paper's own §6
  constants (`cost_$i = cost_α = cost_t = 100`, 41:18), the optimum on the
  paper's own Section 2 running example flips from `(+ 3 (* #0 #1))` to the
  arity-zero `(+ 3)`:

  ```
  alpha=0   (stitch/micro):  (+ 3 (* #0 #1)) 302 > (+ 3) 203 > (+ 3 #0) 202
  alpha=100 (Eq. 8 literal): (+ 3) 203 > (+ 3 (* #0 #1)) 102 = (+ 3 #0) 102
  ```
  (scratchpad `alpha.rkt`, scoring all 27 finished candidates.) So the paper's
  own stated answer `fn0 = λα.λβ.(+ 3 (* α β))`, Eq. (2) at 41:3, is *not* the maximizer of
  Eq. 8 under its own constants. micro's header calls this "one deviation
  ... deliberate, and follows the real implementation"; it could say that
  without the deviation micro would not reproduce the paper's own example.

**2. micro's standalone-ness.** Clean. `src/micro.rkt` requires exactly
`"ast.rkt"` and `racket/set` (micro.rkt:98); zero tokens of `mini`,
`expr.rkt`, `search.rkt`, `pattern.rkt`, `rewrite.rkt`, `compress.rkt`,
`hash-cons`, `zipper`, `worklist`, `parse`, `->string`, `differential`,
`harness`, `json` appear anywhere in it (grep below). It loads and answers
correctly from a bare `racket -e` outside the repo with only `ast.rkt`
alongside. Two residual outward references remain, both to *real stitch* rather
than to mini (micro.rkt:144, :428), and one forward reference in `ast.rkt`
(**L9**). No test file is required by any `src/` module.

**3. Knowledge conservation and doc coherence.** No test coverage was lost:
at `f15fd82`, 104 `check-` forms before and 110 after (54 micro + 47
micro-test + 9 support), and micro's 16 `test-case`s became 10 + 6 + 2 new;
`476c227` adds a seventeenth (114 checks now, and one stale count — **L12**); the three evicted assertions
(parse/print round-trips) were replaced by five in `tests/support.rkt`. The
over-count story survives in three places with its exact numbers intact
(`tests/micro-test.rkt:152-197` asserting 1210/705/705/504/605,
`src/rewrite.rkt:170-182`, and the note). Timing claims re-measured and
accurate. The one real loss is that **micro.rkt itself no longer says its
answer can differ from real stitch's** (**M3**), and the four new
"WHAT WE DO DIFFERENTLY" sections contain two factual errors (**M1**, **L6**)
and one absolute that the codebase itself contradicts (**L8**).

Areas clean, one line each: `tests/differential.rkt` (byte-identical, tally
reproduced); `src/compress.rkt` (untouched, output byte-identical);
`tests/fuzz.rkt` (same seed, same tallies, only the `parse` import moved);
the `rewrite.rkt` delta section (every claim checked and true); `todo.md`.

---

## Findings by severity

No high-severity findings. Nothing in the restructure changes what any program
computes — verified below.

### M1. `search.rkt`'s new delta section is wrong about which of micro's prunings change the answer

`src/search.rkt:49-52`:

> `* micro keeps only the prunings that change the answer (zero matches, the
>    two-programs rule, the free-variable rule, and the two Section 4.3
>    filters).`

Two of those five do **not** change the answer, by micro.rkt's own header:

* zero matches — micro.rkt:54-56: "A candidate that matches nowhere can never
  grow into one that matches somewhere, so **nothing is lost by dropping it**".
* redundant argument elimination (one of "the two Section 4.3 filters") —
  micro.rkt:67-69: "Redundant argument elimination genuinely is dominance-safe
  and **could be dropped without changing what is optimal**".

The list also omits `identity-body?` (micro.rkt:642), micro's sixth filter,
which is a real filter and not a speed hack. So the sentence is wrong on 2 of
its 5 items and short by 1. `notes/2026-08-17-1900-...`:213 gets it right
("zero-match pruning (finiteness/termination)"); this new prose does not.

### M2. micro.rkt's section heading contradicts two of its own bullets

`src/micro.rkt:52`: `WHAT IS KEPT, BECAUSE DROPPING IT WOULD CHANGE THE ANSWER`
— followed by five bullets of which the first (zero-match pruning, :54-56) and
the last clause of the fifth (redundant argument elimination, :67-69) each say
in their own text that dropping them would *not* change the answer. The list is
really "what is kept, and why each is kept"; the heading asserts a single
reason that applies to three of the five. Same defect as M1, on the other side
of the split.

### M3. Standalone micro no longer tells its reader where it and real stitch disagree

Before the restructure, micro.rkt carried the over-count story as an in-file
test ("where micro and stitch genuinely disagree, and why", old micro.rkt:926, i.e. `b2259f9:src/micro.rkt`)
— the design note still records that as micro's job
(`notes/2026-08-17-2030-...`:70: "Micro-stitch documents the divergence as
a passing test"). It is now in `tests/micro-test.rkt:152`. What is left in
micro.rkt points the other way: micro.rkt:144-145 ("Real stitch reports
original_cost 604") and micro.rkt:428 ("which is what the real binary reports")
both assert agreement, and nothing in the file mentions a corpus family where
micro's answer is right and stitch's is wrong. A reader who takes micro.rkt as
the standalone artifact the restructure intends learns that micro reproduces
stitch, and never learns the most interesting thing this repo found. One
sentence in the header ("on one corpus family stitch's own utility accounting
disagrees with rewriting, and this file is the one that is right — see
tests/micro-test.rkt") would restore it without re-introducing a mini
reference.

### L1. `Section 3.1, Algorithm 1` conflates two places in the paper

`src/micro.rkt:17`. §3.1 is titled "Algorithm" and gives the narrative
(expansion → naive approach → dominance pruning → upper-bound pruning);
**Algorithm 1** is the pseudocode listing in **Appendix A** (41:33, "The full
algorithm is given in Algorithm 1"). §3.1 contains no Algorithm 1. The
walkthrough's version (`walkthrough.md:132`, "its Algorithm 1") is fine because
it gives no section number.

### L2. `the paper's &i indices (Appendix B)` — wrong appendix, and the rule described is stitch's, not the paper's

`src/micro.rkt:63`. Two separate problems.

* `&i` is introduced in **Section 3**, 41:7 ("a new syntactic form `&i` is used
  to represent a `$i` variable that has been downshifted further than
  traditional downshifting would permit"), with its shift rules in Fig. 4/5.
  **Appendix B is "PROOF OF CORRECTNESS OF LAMBDAUNIFY"** (extraction line
  2190); it discusses `&i` only through the well-formedness predicate used in
  that proof.
* micro describes the rule as "a location whose argument would have to capture
  a lambda *inside* the body **is matched but never rewritten**". The paper
  says the opposite about matching (41:9, "Match Locations"): "We **discard
  locations** where the mapping produced by LambdaUnify has `&i` indices in
  expressions bound by abstraction variables". Under the paper's definition
  such a location is not in `Matches` at all. micro keeps it as a match and
  refuses it only in the rewriter — which is what real stitch does, and which
  is observable through micro's own exported API: on
  `["(lam (f a $0))", "(lam (f a b))"]` the pattern `(lam (f a #0))` matches
  **both** programs, one of them with a capturing argument, so it counts as a
  2-program candidate for `too-few-programs?` even though only one location can
  ever be rewritten (scratchpad `cap4.rkt`, using only `match-pattern` and
  `rewrite-corpus`):

  ```
  program 0: matches=#t arg=&0
  program 1: matches=#t arg=b
  rewritten: ((lam (f a $0)) (fn_0 b))
  ```
  Under the paper's definition program 0 is not a match location, so the
  candidate would be single-program. The bullet sits under a "kept" list whose
  framing is the paper's; it belongs in the "follows the implementation"
  category, next to `cost_{α=0}`.

### L3. The ≥2-programs rule is attributed only to stitch; the paper states it

`src/micro.rkt:57-60` calls it "stitch's default single-task pruning".
`walkthrough.md:90` calls it one of "two of stitch's *semantic* defaults". The
paper states it directly, 41:18, in the same paragraph micro already cites for
the cost constants:

> For all experiments, we parameterize Stitch's cost(e) function ... costapp =
> costλ = 1, cost$i = costα = cost_t(t) = 100. **To avoid overfitting,
> DreamCoder prunes the abstractions that are only useful in programs from a
> single task. We add this to Stitch as well, treating each program as a
> separate task for datasets that don't divide programs into tasks.**

That second sentence also licenses micro's programs-as-tasks identification,
which micro currently presents as its own simplification. This is an
under-claim, and an odd one given that micro cites "the paper's Section 6
constants" one sentence earlier in its own header (micro.rkt:47). (Rust parity
confirmed: `compression.rs:1150-1155`, `allow_single_task` defaults false.)

### L4. "every production of the grammar" is not what `expansions` does

`src/micro.rkt:38`. The paper's `G_{A??}` is the DSL grammar extended with `??`
and `α` (41:7), so its productions include **every** primitive in `Gsym`.
micro's `expansions` (micro.rkt:542-553) offers only the primitives that occur
in the corpus (`corpus-prims`, micro.rkt:529), only `$i` below the hole's own
lambda depth, and only up to `max-arity` variables. On the walkthrough corpus
that is 7 prims rather than the DSL's; the restriction is documented at the
`corpus-prims` definition but the header sentence contradicts it. Also, the
`max-arity` cap (default 2) is a restriction of the objective and is not listed
among the deviations.

### L5. "None of that is here" overstates; zero-match pruning is Algorithm 1's own zero-usage pruning

`src/micro.rkt:16-19` says the paper's algorithm is "a corpus-guided top-down
search: a branch and bound with upper-bound pruning, dominance pruning, and a
best-first worklist ... **None of that is here.**" Two of those words are in
fact here:

* *corpus-guided*: `corpus-prims` restricts productions to the corpus, which is
  precisely the "strong corpus-guidance" of Appendix A (41:33).
* zero-match pruning is Algorithm 1's colour-coded **Zero-usage pruning**
  (listing lines 11-13, 41:34), justified there by Lemma 2 — not part of the naive
  approach. The paper's naive approach terminates differently: "the algorithm
  can stop expanding when all expansions would lead to abstractions larger than
  the largest program in the corpus" (41:10). micro substitutes a strictly
  stronger rule and says only that it "is also what makes the enumeration
  finite at all" (micro.rkt:56), with no note that the paper's paragraph
  terminates by a size bound instead. Both terminate and both are optimal, so
  nothing is wrong with the code; the *attribution* silently borrows from
  Algorithm 1 while the surrounding text says nothing of Algorithm 1 is used.

### L6. "every candidate that matches anywhere is expanded" is false

`src/search.rkt:34-35`. On the walkthrough corpus, of 828 children generated,
622 match nowhere and 206 match somewhere; of those 206, **105 are rejected
before expansion** (87 `too-few-programs?`, 17 `constant-argument?`, 1
`identity-body?`) and 27 are finished, leaving 74 expanded. Measured with an
instrumented copy of micro (scratchpad `count2.rkt`):

```
((constarg . 17) (fewprogs . 87) (identity . 1) (queued . 74) (scored . 27) (zero . 622))
total 828
```

The intended contrast (no *bound*-based pruning) is true; the sentence as
written is not, and it contradicts `walkthrough.md:196-206`, which tabulates
exactly these rejections.

### L7. walkthrough §1 still leans on two mini-only concepts

`walkthrough.md:79-82`: "this is one more place where we follow the
implementation against the paper's letter, in the same category as **sentinels
instead of `&i`** and **the greedy rewrite instead of the DP**." Both are
mini's (`expr.rkt` argument-extraction sentinels; `rewrite.rkt`'s greedy
top-down pass); neither is defined anywhere before §3, and micro uses neither —
it has an explicit `captured` struct *and* the DP. The document's own reading
order (`walkthrough.md:4-6`) sends the reader through §§1-2 before mini, so
these are two dangling forward references in the section that is supposed to be
resolvable. Everything else in §§1-2 checks out: no other `mini`/`expr.rkt`/
`search.rkt`/`hash-cons` token appears before the `## 3.` heading.

### L8. `expr.rkt`'s new opening claims exactness the repo contradicts

`src/expr.rkt:7-8`: "mini-stitch, which computes **exactly** what micro.rkt
computes". `src/search.rkt:54-55`, four files over, says "The one thing micro
does that we do not is get self-similar corpora right", and
`tests/micro-test.rkt:188-197` asserts the two differ by 101 on the reproducer.
The same absolute appears at `walkthrough.md:321` ("computes exactly what
micro computes"), but there §7 (`walkthrough.md:765`) supplies the caveat;
`expr.rkt` supplies none and points nowhere.

### L9. `ast.rkt`: one forward reference a first-time reader cannot resolve

`src/ast.rkt` is 78 lines, 55 of them comment — genuinely a one-minute read, and
free of mini vocabulary except **line 30**: a node's children hold "a nested
Node, or **an index into an arena of Nodes**". "Arena" is mini's
representation, introduced in `expr.rkt`; a reader following the stated order
(`ast.rkt` → `micro.rkt` → walkthrough §§1-2 → mini) meets the word here first
with no referent, in the one file whose job is to be readable cold.

*Resolved mid-review, and independently verified.* At `f15fd82` this finding had
a second half: `COST-IVAR = 100` sat in the shared cost model, was used only by
mini (then `expr.rkt:499`), was contradicted by micro's `term-cost` charging 0, and
the `α` split — the previous review's finding #4, the single most confusing
point in the cost model — went unmentioned in the file that defines both
constants. `428d089` deletes the constant, replaces it with an eleven-line
explanation (`ast.rkt:66-76`), and makes `expr.rkt`'s generic `cost` raise on an
ivar. I checked the load-bearing claim in that new comment — "Real stitch's
config does carry a `cost_ivar = 100` default ... the constant is inert there
too" — empirically rather than by reading:

```
$ compress data/basic/simple1.json --max-arity=2 --iterations=1 --cost-ivar=100000
Cost before: 604 ... utility: 200 | final_cost: 402 | body: (#0 #0 #0)
$ compress data/basic/hof.json --max-arity=2 --iterations=1 --cost-ivar=100000
Cost before: 4343 ... utility: 2320 | final_cost: 1111 | (identical to the default run)
```

`cost_ivar` is genuinely live in the `lambdas` crate (`expr.rs:547`,
`analysis.rs:71,88`) and genuinely never reaches a stitch number. The new
`error` in `expr.rkt:499-506` is also safe as written: the only `cost` call sites
that could see a sentinel are `search.rkt:494`, which prices
`arg-unshifted` (never shifted, hence never sentinelled), and
`arity-zero-best` (`search.rkt:707`) via `in-corpus-span`, which by construction stops at
`corpus-span` and so excludes every shifted copy (`expr.rkt:186-196`). Suite
green at `428d089`: 83 tests, 87 differential runs, 85/2/0.

### L10. `notes/2026-08-17-1900-mini-stitch-design.md:227` is now stale

"Shares parser/printer with mini (import from expr.rkt)." (line 227) — false since this
commit. That note's own convention for post-hoc corrections is an inline
`[Update, post-implementation: ...]` bracket (it has one at line 220-224, added
by the previous review's fix); this line did not get one.

### L11. `tests/support.rkt`'s `term->string` silently returns `""` for a non-Term

`tests/support.rkt:45-55` — the `intern` cond ends in `[else (add-node! ...)]`
with no guard, and `expr->string` renders an unrecognised struct as the empty
string:

```
$ racket -e '(require (file ".../tests/support.rkt"))
                 (println (term->string 42)) (println (term->string (list 1 2)))'
""
""
```

Since `micro-test.rkt` compares bodies through `canonical` → `term->string`,
two *differently* malformed values compare `equal?`. Carried verbatim from the
old `micro.rkt:143-153`, so not introduced here, but it is now in a file whose
whole purpose is comparison. (`add-node!` accepting a non-Node is the
underlying cause.)

---

## Defensible but debatable

* **`pattern.rkt:35-37`, "the paper's Lemma 2".** Lemma 2 (41:11) states that
  `Matches(P, A??)` upper-bounds the *rewrite* locations of any derived `A`.
  The property pattern.rkt actually relies on — child matches ⊆ parent matches
  — is the sentence justifying Lemma 2 ("as partial abstractions are expanded
  they become more precise and thus match at a subset of the locations"), not
  Lemma 2 itself. Close enough to be a fair citation; not exactly right.
* **`pattern.rkt:37`, "the corpus is never walked again after the first
  pass".** `search.rkt:707` (`arity-zero-best`) iterates `in-corpus-span`, i.e.
  every arena node, before the search proper. The sentence is about pattern
  expansion and is true of it; read literally it is not true of mini.
* **`ast.rkt` existing at all.** The brief's premise is that micro is
  standalone; sharing 20 lines of struct definitions is what keeps `equal?`
  comparable across the two systems and what lets `tests/support.rkt` bridge
  them. The alternative (duplicating the structs) would make micro literally
  self-contained at the cost of two divergent definitions of the same language.
  The current choice is right; it is worth knowing it is a choice.
* **"about 3 s" for nuts-bolts** (README:109, walkthrough:326). Re-measured:
  `racket src/compress.rkt stitch/data/cogsci/nuts-bolts.json --max-arity 2
  --iterations 3` → 2.07 s wall including Racket startup. "About 3 s" is
  conservative rather than wrong.
* **micro's `>` in `micro-search`** (micro.rkt:749) means an abstraction of
  utility exactly 0 is never returned, and `max-arity` defaults to 2. Both
  match real stitch; neither is listed as a restriction of "the paper's
  objective" in the header.
* **`expr.rkt`'s new `cost` error (`428d089`) vs its own test suite.** The
  comment justifies raising with "nothing ever prices" a shifted argument copy,
  but `expr.rkt:1061` does exactly that — `(check-equal? (cost c (arg-shifted
  a)) COST-VAR)` — and passes only because that particular shifted copy happens
  to carry no sentinel. The invariant the error encodes is really "nothing ever
  prices a *sentinel-bearing* copy", which is narrower than the comment says.
  Harmless today; a trap for whoever next prices a shifted argument.
* **walkthrough.md:196**, "each counted against the first filter that applies,
  in `reject?`'s own order" — the table then lists the filters in a different
  order than `reject?` applies them (`identity-body?` is first in the code,
  fourth in the table). The counts are unaffected because the one
  identity-rejected candidate also matches somewhere; the sentence is still
  slightly misleading.

---

## What I tried to break and could not

* **Behaviour preservation, mini.** `racket src/compress.rkt FILE --max-arity 2
  --iterations 3` on `hof`, `simple2`, `ctx_thread_1`, `map`, `map2` and
  `cogsci/nuts-bolts`, old worktree vs new: output identical on every line
  except line 1, which echoes the path I passed.
* **Behaviour preservation, micro.** `micro-search` + `micro-compress` (3
  iterations, arity as noted) on six corpora, `b2259f9` vs `f15fd82` vs
  `476c227`: byte-identical output at all three, including the self-similar
  reproducer.

  ```
  ((a a a) (b b b)) | best=(#0 #0 #0) util=200 | steps=(((#0 #0 #0) 200 402))
  ((a (lam (a a))) (b (lam (b b)))) | best=(#0 (lam (#0 #0))) util=201 | ...
  ((f (g a) (g a)) (f (g b) (g b)) (k (g a))) | best=(f #0 #0) util=302 | ...
  ((lam (g (f a b) $0)) ...) | best=(lam (g (f a #0) $0)) util=203 | ...
  ((m (lam (p $0 q)) r) (m (lam (p $0 s)) r)) | best=(m (lam (p $0 #0)) r) util=203
  ((((a a) (a a)) ((a a) (a a))) ((a f) (a f))) | best=(#0 #0) util=504 | ...
  ```
* **Suite, at `f15fd82`, `428d089` and `476c227`.** `raco test src/ tests/` →
  `83 tests passed`, `83`, then `84` (20.5 / 29.2 / 28.0 s); differential
  `87 runs: 85 match, 2 tie, 0 fail` with the two known ties; fuzz
  `unbiased: 300/79 → 79 AGREE, 0 OVER, 0 UNDER` and `biased: 300/259 → 187
  AGREE, 72 OVER, 0 UNDER` — tallies identical to a run of the *old* tree's
  `tests/fuzz.rkt` on the same seed.
* **Standalone load.** From `/tmp`, with only `src/ast.rkt` and `src/micro.rkt`
  on the path, `racket -e '(require (file ".../micro.rkt") (file
  ".../ast.rkt")) ... (micro-search ...)'` returns
  `#(struct:app #(struct:app #(struct:ivar 0) #(struct:ivar 0)) #(struct:ivar 0))`.
  `raco test src/micro.rkt` alone → `10 tests passed`.
* **Coupling greps.** In `src/micro.rkt`, `grep -nEi
  "mini|search\.rkt|expr\.rkt|pattern\.rkt|rewrite\.rkt|compress\.rkt|hash-cons|
  zipper|worklist|upper.bound|differential|harness|binary|parse|->string|
  canonical|support\.rkt|json"` returns exactly two lines: `:18` (describing the
  paper's algorithm) and `:428` (a real-binary cross-check). In `src/ast.rkt`,
  the same grep set returns only the "arena" line (L9). No `src/` module
  requires anything under `tests/`.
* **Every worked number in walkthrough §2, recomputed.** 51 subterms; 7 corpus
  primitives; 10 children of `??` and 11 under one lambda; 828 candidates;
  filter tallies 622 / 87 / 17 / 1 / 0; 27 scored; 74 queued (sum 828); the
  ranked utility list (`(+ 3 (* #0 #1))` 302, `(+ 3)` 203, `(+ 3 #0)` 202,
  ... `(lam (+ 3 (* #0 #1)))` -102) — all exact. The `(#0 #1) -1` row is one of
  four candidates tied at -1, so the displayed ordering is a valid selection.
* **§3's new timing table, re-measured** on nuts-bolts prefixes (fresh process,
  micro then mini):

  | programs | claimed micro | measured | claimed mini | measured |
  |---|---|---|---|---|
  | 2 | 0.6 s | 0.61 s | 14 ms | 13 ms |
  | 3 | 1.8 s | 1.74 s | 22 ms | 20 ms |
  | 4 | 3.3 s | 3.22 s | 22 ms | 22 ms |
  | 5 | 9.0 s | 8.71 s | 27 ms | 26 ms |

  Both implementations return the same body at every prefix.
* **Test-coverage accounting.** 104 `check-` forms before → 110 after; the
  per-test-case counts for the eight retained micro tests are unchanged
  (4/9/11/10/10 and three assertion-free rewrite cases whose `check-equal?`s on
  strings became `check-equal?`s on AST values — verified equivalent by hand,
  e.g. `'("(lam (f a $0))" "(fn_0 b)")` → `(list p0 (app (prim 'fn_0) (prim
  'b)))`).
* **`rewrite.rkt`'s delta section**, every claim: it does consult
  `abstraction-used` rather than re-deciding (`rewrite.rkt:110`, `:134`); the
  cost agreement is an assertion (`check-cost-mismatch`, `:183`); the shift is
  precomputed in `expr.rkt`'s argument extraction. Nothing to report.
* **The over-count regression's exact numbers**, re-derived: corpus cost 1210,
  rewritten 705 (= stitch's own `left: 705`), DP prediction 705, micro utility
  504, mini utility 605, difference 101. All asserted in
  `tests/micro-test.rkt:188-197`.
* **Real-binary cross-check** of the one number micro.rkt asserts about stitch:
  `compress stitch/data/basic/simple1.json --max-arity=2 --iterations=1` prints
  `Cost before: 604` and `utility: 200 | final_cost: 402 | body: (#0 #0 #0)`,
  matching micro.rkt:144-148 and `tests/micro-test.rkt:115-116`.

---

## Addendum: the two follow-up commits (`428d089`, `476c227`)

Both landed after the restructure and during this review; both are covered by
the re-runs above (suite green, differential 87/85/2/0, micro's answers
byte-identical to `b2259f9` on all six regression corpora).

**`428d089`** — reviewed inline as the resolved half of **L9**, with the
`--cost-ivar=100000` experiment that confirms its claim about real stitch, and
one nit in "Defensible but debatable" about `expr.rkt:1061`.

**`476c227`** — two changes.

*The memo comment.* The new text ("this table ... IS the dynamic program ...
without it the recursion is exponential on self-similar programs (accept
descends into the argument, reject into both children)") is correct, and I
verified the exponential claim rather than taking it: with `X_0 = a`,
`X_{k+1} = (X_k X_k)`, corpus `(list X_d)`, body `(#0 #0)`, comparing HEAD's
`rewrite-corpus` against a copy with only `hash-ref!` stripped (scratchpad
`blow2.rkt`, `micro-memo.rkt`, `micro-nomemo.rkt`):

| depth | with table | without |
|---|---|---|
| 10 | 1 ms | 24 ms |
| 12 | 2 ms | 247 ms |
| 14 | 10 ms | 1.9 s |
| 16 | 51 ms | 17.2 s |

Growth without the table is ~8× per +2 depth against ~5× with it — exactly the
extra `(3/2)^2 ≈ 2.25` the three-calls-per-level argument predicts. (An
intermediate working-tree version of this comment quoted "89 ms with the table,
61 s without" on the depth-16 term; I measured 51 ms / 17.2 s. Those numbers
were dropped before the commit, so nothing unreproducible is checked in.)

One residual overstatement: "it IS the dynamic program". What Eq. 15 specifies
is a bottom-up table; what micro writes is a top-down recursion that fills the
same table. The next sentence says precisely that, so the headline is a
teaching simplification rather than an error — but it is the one place in
micro.rkt where the file claims to *be* the paper rather than to agree with it.

*`surviving-children`.* Correct and behaviour-preserving: the extracted
`for*/list` applies `reject?` with `(pattern-arity p)` exactly as the inlined
version did, and `micro-search`'s fold now only distinguishes finished from
unfinished. Its new unit test's arithmetic checks out by hand — on
`["(f a x)", "(f b x)"]` the ten children of `??` reduce to three survivors
(`(?? ??)`, `f`, `x`); `a` and `b` are single-program, `(lam ??)` matches
nowhere, `#0` is the identity body. The docstring's "This is the same job the
paper gives its Expansions procedure" is fair — with the caveat already logged
as **L4**/**L5**, that the paper's `Expansions(A??, h, P)` is corpus-guided by
design while micro's header presents its own corpus-guidance as absent.

### L12. `476c227` leaves the advertised test count stale

`raco test src/ tests/` now reports **84 tests passed** (the new
`surviving-children` case). `README.md:95` still says "83 test cases", as does
`notes/2026-08-18-0246-micro-first-restructure.md:39`. The README number was
updated as part of the restructure precisely because it is load-bearing for the
"Results" section, so it is worth keeping in step.
