# Consolidation pass over macro-micro.rkt (plan item 1)

Claude, 2026-08-18. macro-micro.rkt was rewritten to the standard micro.rkt
sets: comments say what things are; this note keeps what they used to say
about how they got that way. Everything below either moved here from code
comments or records a decision made during the rewrite. Test behavior is
unchanged: all module tests, both benchmarks, and the fuzzer pass before and
after (22 module tests + macro-fuzz 400 corpora / 2000 inverse trials;
my-when 5s, for/set 3m24s on this container).

## What was rewritten, beyond comments

Three code changes, none of which alters any answer:

1. **skeleton-match lost its mutable bookkeeping.** The old matcher threaded
   a parameter-holding-a-box to record, per matched sequence element, the
   first (svar) sighting's path and subterm, and smuggled the collected
   sequence arguments out of the walk under a reserved 'seq-args key in the
   binds hash. The rewrite observes that all of that is positional and
   template-determined: the ellipsis's form sits at the same path in the
   site as in the template (nothing above the one ellipsis can differ in
   length), and within each element the argument is the site's subterm at
   the sub-template's first (svar) path — a fact about the template, not
   the match. So the walk now threads a single binds hash, exactly as
   before ellipses existed, and a pure function (sequence-args, built on
   ellip-form-path and svar-path) reads the sequence arguments off the
   matched site afterward. Equivalence argument: the old walk visited sub's
   leaves left to right, so its "first svar sighting" was always the
   leftmost svar, at a template-determined relative path; paths and
   subterms therefore agree case for case. For a sub that has no (svar)
   yet — an unfinished template — the old code recorded #f per element and
   the new code records the element itself; only the count is ever
   consulted (skeleton-programs), so the difference is unobservable.

2. **hole-scope and hole-ellip-scope merged into hole-context.** Two walks
   retracing the same path to the same leftmost hole, returning a scope
   list and a (cons in-ellip? has-svar?) pair respectively. They were
   separate only because the second was added later without touching the
   first's contract. One walk, one three-field struct.

3. **The shared-sites plumbing was removed, and the per-program expansions
   hoisted.** Previously rewrite-corpus and macro-utility took an optional
   list of precomputed (expanded . sites) pairs, passed in by
   best-candidate so that a candidate surviving the two-valid-programs
   filter would not have its valid-sites recomputed when scored. That
   plumbing saved a measured ~11% on the for/set benchmark (5m58.6s
   without, 5m19.6s with, back to back on one container) and cost every
   signature an optional argument and every reader a paragraph. It is
   exactly the kind of optimization micro.rkt refuses on principle, so it
   is gone: the filter and the scorer each ask the oracle about the same
   sites, and the module computes a thing twice rather than carry plumbing
   to share it. In exchange, best-candidate now computes each program's own
   expansion once, before the candidate loop, instead of once per candidate
   (it never depended on the candidate). Net effect on this container:
   for/set at 3m24s, comfortably inside its budget.

Also: corpus-facts' five return values became a struct (grammar), and
expansions takes it whole instead of four positional lists plus a boolean.

## The review-finding numbers, decoded

Comments used to cite adversarial-review findings by number. The map, for
anyone reading old diffs or notes/2026-08-18-1430-adversarial-review-3.md:

- **F1** — match-binder and check-corpus made total: a raw symbol in a
  hand-built template's binder position is "no match", not a crash; an
  ill-formed corpus is rejected up front with a pointed error.
- **F3** — a pattern variable first recorded as a compound argument can
  never later be reused in binder position; skeleton-match fails that
  shape cleanly instead of letting transcription splice a compound term
  into a binder list.
- **F9** — a proposed "unreferenced binder pvar" filter was refuted by
  measurement: it would have deleted the for/set benchmark's own answer.
  The surviving explanation lives at reject?.
- **F10** — micro.rkt's constant-argument and duplicate-argument filters
  are unnecessary (not merely deferred) under the macro cost model; the
  dominance argument lives at reject?.
- **F15** — the shared-sites plumbing described above, now removed.

## Measurements the trimmed comments referred to

- **The zero-iteration guard in skeleton-programs.** Without requiring an
  ellipsis candidate to actually iterate somewhere, a 3-program benchmark
  exploded past 900,000 open candidates by enumeration level 7 (and
  climbing); with the guard, 670 finished candidates, sub-second. First
  recorded in notes/2026-08-18-1505-session-2-review-ellipses.md.
- **The variadic-family condition on ellipsis productions.** Offering
  ellipsis skeletons whenever the corpus has any two distinct form lengths
  (rather than one head at two lengths) took the for/set benchmark from
  ~5.3 measured minutes to 30+ for candidates that cannot win there. Also
  in notes/2026-08-18-1505-session-2-review-ellipses.md.
- **The rewrite DP's memo.** Without memoizing best-cost, every descendant
  is visited twice per node (once from accept-cost, once from
  reject-cost) — measured 4x per two nesting levels on self-similar
  programs, exponential in general.
- **for/set wall times across containers**, for calibration only (they are
  different machines; compare within a row, not across): original session
  ~245s; review session 358.6s → 319.6s (the ~11% from the now-removed
  plumbing); this session 204s without the plumbing but with the hoisted
  expansions.

## Review cycle 1 (Fable reviewer, same day)

What it verified, so later passes need not repeat the expensive parts:
every quantitative claim in walkthrough-macros.md and the two benchmark
headers regenerated from the code (including the 217,200 enumerated
candidates and exactly 25 oracle survivors, ~3.5 minutes); every expander
output in the walkthrough reproduced; both benchmarks' cost arithmetic
re-derived by hand and machine; and the rewrite's positional sequence-args
equivalence attacked with a walk-recording reference matcher on 14
hand-built adversarial cases plus 5,000 randomized transcribe-and-match
trials — zero disagreements (the argument: with at most one ellipsis,
every form inside the sub is fixed-length, so template and site paths
align positionally, and svar-path's leftmost order is the walk's visiting
order).

What it found, all fixed in the same session:

1. **The duplicate-svar withholding was mislabeled as dominance.** The
   comment said a second (svar) "can only score identically to its
   single-svar parent" — false.  On the corpus
   `((f (g 1 1) (g 2 2)) (f (g 3 3) (g 4 4) (g 5 5)))` the excluded
   template `(f (g %xs %xs) ...)` is oracle-valid at the root of both
   programs, rewrites the corpus to `((m0 1 2) (m0 3 4 5))`, and scores
   703, while the search returns `(g %x0 %x0)` at 399: a second svar adds
   no skeleton constraint, but the oracle can exploit per-element
   agreement, which no single-svar template reaches (a depth-0 pvar
   repeats one value across iterations).  The withholding is now
   documented as a search-width choice; macro-search's purpose statement
   and the module header no longer suggest the search is optimal over the
   whole template language.  Whether to lift the restriction (offer a
   second (svar) production) is future work: it widens the search on
   every variadic corpus and deserves its own measurement.
2. **check-corpus now rejects a binder named `lambda` or `let`** — the one
   way this object language can shadow them, and exactly the malformation
   the module header warns makes the position-walkers misread a program.
   Previously such a corpus passed the check and was walked wrongly in
   silence.
3. Smaller findings, all applied: the walkthrough gained an H4
   demonstration and a section on learning a second macro on top of the
   first (it had claimed to cover every mechanism while showing neither);
   its remaining development-history narration went; my-when's margin
   arithmetic was made exact (each site sheds 204 of fixed shape and pays
   101 for the call, netting 103); note references in code, README, and walkthrough spell full filenames
   everywhere; README's macro paragraphs and macro-fuzz's header stopped
   narrating development order.

## Vocabulary retired from the code

"V1"/"V2" (design-note shorthand for templates without/with binder-position
pattern variables) now appear only in the design notes; the code and tests
say "a template binder in the binder position" or "a binder-position
pattern variable". "Stage 1/2" (the two ellipsis implementation steps) is
gone the same way — the module describes the language it accepts, not the
order it was built in. The my-when test's header keeps its two
corpus-design lessons (a recurring identifier or a shared element shape
lets a template binder reach sites the design meant to reserve for a
binder-position pattern variable) but no longer narrates the scratch-script
process that found them; the fuller account is in notes/2026-08-18-1505-session-2-review-ellipses.md.
