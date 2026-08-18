# Session log 2: the third adversarial review, and ellipses end to end

Autonomous session (Claude, 2026-08-18, ~13:22-16:22 UTC), continuing the
morning session (notes/2026-08-18-0557). Direction and review here;
implementation in sonnet subagents; the adversarial reviewer was an Opus
subagent. Everything committed on claude/syntax-rules-macro-learning-xsysex.

## Adversarial review 3 (notes/2026-08-18-1430)

Findings and dispositions are in the review note. The headline earned its
own moral: narrowing the oracle's "errors count as no" handler to
user-level expansion errors immediately surfaced a REAL expander bug the
blanket handler had been silently absorbing -- lambda/let clauses called
identifier-symbol on binders unguarded, so a compound spliced into a
binder slot (reachable through a learned macro that reuses a pattern
variable as both argument and binder) crashed with a contract violation
instead of reporting an ordinary "this rewrite is invalid". Oracles must
be allowed to fail loudly; the errors that are verdicts and the errors
that are bugs must be distinguishable, and the distinction found a bug
within minutes of being enforced.

Also from the review: the rewrite DP got the memo table it claimed to
already have; skeleton-match now refuses compound-into-binder reuse as a
shape judgment; check-corpus became a real well-formedness pass; the
benchmark's V2-necessity claim was corrected to the true, narrower one;
the fuzzer now actually generates H2 shadowing, H3 renaming, V2 capture
references, and lambda arguments (it previously could not produce any of
the four); and two proposed "cleanups" were refuted with measurements --
the unreferenced-binder-pvar filter would have deleted the for/set answer
itself, and the constant/duplicate-argument filters are unnecessary (not
merely deferred) under this cost model, a real divergence from micro.rkt
now recorded at reject?.

## Ellipses: designed, then built in two stages (task was "the big rung")

Design note notes/2026-08-18-1324 (plus amendment): depth 1, one trailing
ellipsis, expander first. Stage 1 (expander.rkt): depth-tagged pattern
envs, deterministic segment matching, per-copy transcription with the
existing mark machinery -- no new hygiene mechanism, which is itself a
result (the plausible wrong guess, "each iteration freshens separately",
is tested against). 11 new tests including hygiene under iteration;
behavioral spot-checks against Racket's own syntax-rules agree on all
four compared macros. Stage 2 (macro-micro.rkt): the amendment's
one-ellip-per-template + (svar)-as-node design paid off exactly as hoped
-- sequence arguments are ordinary trailing call arguments, so the
oracle, rewriter, and DP changed not at all; the entire variadic
extension lives in the matcher, the renderer, and the enumerator.

The learner now recovers (define-syntax-rule (m x ...) (f (g x) ...))
from programs of three different arities -- abstraction over arity,
which stitch cannot express at all. Utility 607; the identity-splice
candidate measures at -201, so the suspected filter is unnecessary
(measured, not assumed).

The session's second genuine research finding came from stage 2: LEGAL
ZERO-ITERATION MATCHES ARE POISON TO STRUCTURAL PRUNING. An ellip
template matching some short subterm with zero splices never constrains
its sub-template, so the >=2-programs prune passes vacuously and the sub
grammar re-explodes per coincidental prefix (measured: 900k+ open
candidates on a 3-program corpus). The fix -- the pre-filter counts only
witnesses that actually iterate; scoring semantics untouched -- restores
tractability (670 finished candidates, sub-second). Any future
segment-matching rung (non-trailing ellipses, structured patterns) will
meet the same interaction; it is flagged at skeleton-programs.

## Suite state

46 tests green across expander (23), macro-micro (21 -- wait: 16 after
review + 5 ellipses test-cases; raco counts test-cases), macro-fuzz,
micro-test; fuzzer at 400 corpora + 2000 inverse trials with the new
coverage; for/set benchmark green post-review (~5.3 min) and re-run
after stage 2.

## Accumulating theme worth a future note of its own

Un-transcription's non-injectivity now has THREE catalogued sources (two
from the first fuzzer session, one from the review-driven fuzzer
extension: binder-pvar reuse out of scope; nested binder-pvars sharing a
spelling; a twice-bound binder-pvar pinning recovery to its first
occurrence against lexically-nearest resolution). Together they sketch
the conditions under which "the template that transcribed this site" is
well-defined -- the formal core a nominal-anti-unification treatment
(related-work note) would need. If a fourth source appears, consolidate.

## Next (unchanged from todo, minus what landed)

Fuzzer stage 3 (ellip templates in the inverse property); the mdef
binder mask (review finding 5, documented gap); function-shaped
classification; define/letrec + the layering benchmark; Racket as outer
oracle; ellipsis benchmark in a for/set-like setting (a variadic
my-when/begin corpus) as the two mechanisms' first combined test.

## Addendum: the session's final hour (written ~16:00 UTC)

- **Fuzz stage 3 landed**: the inverse property generates ellipsis
  templates (~33% of trials, zero-length sequences included). Its one
  counterexample was the FOURTH catalogued un-transcription boundary --
  a depth-0 pvar occurring only inside an ellip's sub is unrecoverable
  from a zero-iteration site (macro-micro's documented sound-but-
  incomplete corner) -- so the threshold for consolidating the
  non-injectivity catalogue into the design note (set at "a fourth
  source") has been met -- done: notes/2026-08-18-1541-untranscription-noninjectivity.md.
- **The ellipsis gate had to sharpen**: any-two-lengths opened on the
  for/set corpus and took its benchmark from ~5.3 to 30+ measured
  minutes for candidates that cannot win there. Now gated on a variadic
  FAMILY (same head, two lengths); blind spot recorded at corpus-facts.
- **my-when benchmark** (tests/my-when-test.rkt): V2 and ellipses in one
  learned macro, (m v e xs ...) => ((lambda (v) (seq xs ...)) e), H2
  program refused. Its two documented surprises are a small lesson in
  corpus design: a recurring head lets a V1-template bake the bound
  reference in beside a template copy of that head (H1 never fires),
  and a pvar over the shadowed identifier splices through unrenamed (H2
  never fires). What forces V2 is cross-program VARIABILITY, not
  binder-mentioning bodies alone.
- **Michael's renamed-temporaries question**, answered and tested: one
  anonymous template binder recovers per-element temporaries spelled
  differently from each other (the tvar-inside-ellipsis test), H1 still
  per copy. The recursive-macro case needs new SEARCH machinery (match
  a fixed point), but no new binder machinery -- anonymity + freshening
  + referent-aware alpha already generalize; the oracle criterion never
  mentions how many temporaries exist.
