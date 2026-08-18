# Repo review: what we have learned, where quality stands, what comes next

Claude (Fable), 2026-08-18, asked for an independent judgment: reflect on the
work so far, assess the quality and simplicity of the current approach, and
propose next steps from my own reading rather than from the existing todo.
Method: read micro.rkt, macro-micro.rkt, ast.rkt in full; expander.rkt and
search.rkt in part; the design notes, session logs, and both benchmark tests.
Verified on a fresh container (Racket 8.10, no stitch binary, benchmarks and
differential suite skipped): micro 13/13, expander 17/17, macro-micro 23/23,
macro-fuzz 400 corpora + 2000 inverse trials, all green in under 10 seconds
total.

## 1. What we have actually learned (the durable lessons)

**The differential ladder is the project's real invention, and it works.**
The layering executable-spec (micro) / optimized replication (mini) / real
binary, with fuzzers between rungs, did the thing such a method exists to do:
it produced a new, checkable fact about the ORIGINAL system (the multiuse ×
nested-matches utility over-count, notes/2026-08-17-2030). A replication that
only matched would have been a success; a replication that found the original
wrong, and could prove which side is right because the spec computes utility
by definition rather than by formula, is the method paying for itself.

**Oracle-by-execution is the load-bearing move, and it has now paid off
twice.** Utility-by-rewriting (micro) and hygiene-by-expansion (macro-micro)
are one idea: refuse to implement the analytic side conditions, run the
semantics, compare. Both oracles caught things the analytic sides missed --
stitch's utility formula in act one; our own expander's unguarded binder
positions in act two, the moment the error handler was narrowed
(notes/2026-08-18-1430). The corollary discipline is worth stating as a rule
for everything that follows: *an oracle's errors must be separable into
verdicts and bugs, and only verdicts may be swallowed.*

**Search width and semantics must be kept visibly separate, and gates must
be measured.** The second act's healthiest habit: every pruning decision is
labeled as either part of WHAT is computed (the >=2-programs rule, argument
capture) or purely HOW MUCH is explored (the ellipsis family gate, the p>=1
prefix rule, the iterating-witness pre-filter), and the width choices come
with measurements (900k open candidates without the witness rule; 6x from
the coarse ellipsis gate; two proposed filters refuted by measurement, one
of which would have deleted the for/set answer). This is the discipline that
kept three fast-moving expressiveness rungs from silently changing the
objective.

**Zero-information matches poison structural pruning.** The genuine
algorithmic finding of act two so far: a match that succeeds vacuously (zero
ellipsis iterations) satisfies the >=2-programs prune while constraining
nothing, and the sub-grammar re-explodes per coincidental prefix. Any future
segment-matching rung meets this again; "the pre-filter counts only
witnesses that constrain the candidate" is the general fix.

**Un-transcription is only partially invertible, and we now know the
boundary.** The N1-N4 catalogue (notes/2026-08-18-1541) with its conjectured
linearity/freshness characterization is the most paper-shaped artifact in
the repo. Notably, all four cases were found by fuzzers being kept honest,
not by design foresight.

**Corpus design is a skill, and hand-built benchmarks are weak evidence.**
The my-when session's two surprises (a recurring head lets V1 bake the
reference in; a pvar splices a shadowed identifier through unrenamed) both
amount to: the corpus did not force the mechanism the benchmark claimed to
test. Our benchmarks were debugged until the learner won. That is fine for
existence proofs; it is not an evaluation. See next steps.

## 2. Quality and simplicity, honestly

**ast.rkt and micro.rkt are the standard the repo set for itself, met.**
micro.rkt reads top to bottom; every deviation from the paper is signposted
WITH an argument for why it is load-bearing (the cost_{alpha=0} note that
literal Eq. 8 would flip the paper's own example is exactly the right kind
of comment). The no-COST-IVAR decision in ast.rkt -- delete the constant and
explain why neither pipeline can price one -- is the taste the whole repo
should hold.

**mini (expr/pattern/search/rewrite) does its job.** Its correctness story
is the differential suite plus the micro pin, which is the right story; its
"what we do differently from micro" preamble in search.rkt is a model
delta-spec. I did not re-review it line by line; two prior adversarial
reviews did.

**macro-micro.rkt is well-tested and, as far as I can judge, correct -- but
it is drifting away from the repo's own readability standard.** Three
specific symptoms:

* *Comment archaeology.* The file increasingly narrates its own history:
  review-finding numbers (F1, F3, F9, F10, F15) that mean nothing without a
  note the reader has not read, "the session lead's amendment", measured-6x
  stories, before/after container timings (the worst case is in
  tests/for-set-test.rkt, which carries two machines' wall-clock numbers and
  a warning not to compare them). micro.rkt's comments say what things ARE;
  macro-micro's say what things WERE and which reviewer proposed otherwise.
  This is review residue, valuable in notes/, noise in the module. The
  measurements deserve to live in the notes they came from, referenced by
  one line.
* *Local complexity that earns nothing.* skeleton-match threads a
  parameter-holding-a-box for the per-element svar path -- mutable state
  inside an otherwise functional matcher -- and the `binds` hash mixes
  natural-number pvar keys with a reserved 'seq-args symbol key. Both work;
  both are the kind of cleverness micro.rkt refused. A return value that
  carries (binds, seq-args, first-svar-path) explicitly would be longer and
  plainer.
* *A free 2x-ish sitting in best-candidate.* `(expand-under library p)` for
  each program is recomputed inside the per-candidate loop, though it does
  not depend on the candidate. F15 removed one recomputation layer; this one
  is two lines. (It is dominated by valid-sites' per-position expansions, so
  it is a cleanup, not a rescue.)

None of this threatens correctness -- the test story is strong (deterministic
fuzzers, an inverse property, benchmarks with hand-derived utilities). It
threatens the repo's second purpose, being READ. The file is 1750 lines of
which a large fraction is justification; the equivalent of micro.rkt's
"somebody else's problem" line is overdue -- act two needs its micro/mini
split before it needs more features.

**expander.rkt is fine as code and weak as a trust anchor.** It is the
pearl's artifact, which is good; but we extended it four ways, and one of
our extensions already carried a bug that only surfaced when the oracle's
error handler was narrowed. The entire second act's headline claim
("hygienic syntax-rules macros, really") currently rests on an oracle the
same project modified. Spot-checks against Racket's syntax-rules exist for
four macros; that is not a differential story yet.

**Scale honesty.** for/set is four programs and ~5 minutes; my-when is
similar; the ellipsis benchmark is three programs. Everything act two
claims, it claims about toy corpora. That is the declared genre for micro --
but unlike act one, there is no mini behind it, so the genre currently has
no exit.

## 3. Next steps, in my order

1. **Consolidate before climbing.** One pass over macro-micro.rkt (+ the
   test files) that moves the measurement stories and F-numbers into
   notes/, de-clevers skeleton-match's box-parameter, hoists the
   best-candidate expansion, and -- most valuable -- writes the act-two
   walkthrough: for/set traced end to end the way walkthrough.md traces the
   paper's Section 2, including one H1 refusal, the H2 refusal, and the V2
   rescue, with the scope-graph two-coloring picture from the design note's
   addendum C. Act one is teachable because of walkthrough.md; act two's
   story is currently spread across five notes.

2. **Racket's expander as the outer differential oracle** (direction 1 of
   notes/2026-08-18-0539) -- promoted, in my judgment, above every
   expressiveness rung. It is the missing trust anchor for the second act's
   central claim; it is a contained piece of work (a core-form
   referent-aware alpha walker, ~50 lines, plus a namespace harness); and it
   is the precondition for real corpora either way. Divergences it finds are
   either bugs in our four extensions (likely at least one more exists) or
   genuine model-vs-Racket semantic boundaries -- both are wins.

3. **Round-trip recovery fuzzing: generate the macro, expand it, ask for it
   back.** The evaluation the repo does not yet have, and the cheapest big
   one available: sample a random (well-formed, N1-N4-avoiding) macro M and
   random call sites, EXPAND them with the model expander to manufacture the
   corpus, run the learner, and check M is recovered up to the catalogue's
   ambiguities. This kills three birds: it replaces debugged-until-green
   hand benchmarks with an unbiased distribution; it operationally tests the
   non-injectivity conjecture (an unexpected recovery failure is exactly an
   N5); and it produces the quantitative table (recovery rate by mechanism:
   V1/V2/ellipses/mixed) that any write-up needs. The fuzzer infrastructure
   is already most of the way there -- the inverse property checks
   transcription locally; this lifts it to whole-corpus, whole-search.

4. **Function-shaped classification** (the todo's next item) -- agree, and
   cheap. Reporting WHY each learned template needed to be a macro converts
   "macros strictly dominate functions under this objective" from a
   methodological embarrassment into the interesting output. Do it before
   define/letrec; the classifier is just the four eta-convertibility
   clauses over the winning template plus its sites.

5. **Start act two's mini.** The design note's M2 (the resolution-aware
   matcher with the rho bijection) differential-tested against the
   expansion oracle, then match-location indexing so scoring is not
   per-(candidate, site) whole-program expansion. This is where act one's
   experience says the next real findings live -- deriving the analytic
   account and having the oracle catch its corner cases is precisely how
   micro-vs-mini found stitch's bug -- and nothing on the real-corpora
   horizon (direction 2) is reachable without it. The naive learner at five
   minutes for four programs does not survive contact with any corpus that
   was not built for it.

6. **Two decisions for Michael, not for the code.** (a) Report the stitch
   utility bug upstream -- it is verified, reproducible, written up, and a
   day old; sitting on it has no upside. (b) Decide whether act two is
   heading at a write-up (the related-work note says the niche is open; the
   N-catalogue + hygiene-by-expansion + recovery-rate table is roughly a
   workshop paper). The answer reorders everything above: if yes, items 2
   and 3 are the evaluation section and jump the queue; if no, item 1's
   readability debt matters most, because the repo's product is then the
   explanation itself.

**Deliberately deprioritized:** literals lists, non-trailing/multiple
ellipses, recursive macros, definition contexts. Each adds expressiveness to
a learner whose evaluation, trust anchor, and fast implementation do not
exist yet. The design notes have kept these doors open cleanly; they will
still be open after 2, 3, and 5.

## 4. One process observation

The main-session-directs / subagents-implement / adversarial-review-by-a-
different-model loop has earned its keep: the reviews found real bugs (the
expander's unguarded binders, the phantom memo table) and -- rarer and more
valuable -- refuted two plausible cleanups by measurement before they were
implemented. The habit to protect as sessions accumulate: proposals get
measured, not adopted; and review findings get fixed in code but RECORDED in
notes, not in ever-growing module headers.
