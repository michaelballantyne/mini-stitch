# The plan: consolidate, anchor trust, evaluate — then widen

The work plan distilled from the independent repo review
(notes/2026-08-18-1700-repo-review-quality-next-steps.md, which carries the
arguments; this note carries the work items). Ordering principle: the macro
act currently has expressiveness (V1, V2, ellipses) without three things act
one had from the start — a readable single narrative, a trust anchor outside
the project, and an unbiased evaluation. Those come first; new expressiveness
rungs come after, and are listed at the end as deliberately deferred.

## 1. Consolidation pass (readability debt)

Goal: restore macro-micro.rkt and its tests to the standard micro.rkt set --
comments say what things ARE; notes say what happened.

- Move the comment archaeology out of macro-micro.rkt and
  tests/for-set-test.rkt into the notes it came from: review-finding numbers
  (F1, F3, F9, F10, F15), the 900k/6x/2x measurement stories, the
  cross-container timings. Each replaced by at most one line citing the note.
- De-clever skeleton-match: replace the parameter-holding-a-box for the
  per-element svar path, and the 'seq-args reserved hash key, with an
  explicit return shape (binds + sequence args carried openly). Longer and
  plainer; behavior identical, existing tests must pass unchanged.
- Hoist `(expand-under library p)` out of best-candidate's per-candidate
  loop -- it does not depend on the candidate. Two lines; re-time the
  for/set benchmark once, record the number here, not in the test file.
- Write walkthrough-macros.md: for/set traced end to end the way
  walkthrough.md traces the paper's Section 2 -- the corpus, one H1 refusal,
  the H2-shadowed program's refusal, the V2 rescue, the utility arithmetic,
  and the scope-graph two-coloring picture from the design note's addendum C.
  This is the deliverable that makes act two teachable; the design notes are
  not a substitute.

## 2. Racket's expander as the outer differential oracle

Goal: the second act's headline claim ("hygienic syntax-rules macros,
really") checked against the artifact the design claims to invert, not only
against our own extended model expander. Design sketch already exists:
notes/2026-08-18-0539 direction 1.

- A referent-aware alpha comparison over fully-expanded core Racket
  (#%plain-lambda, let-values, #%app, quote): walk two expansions in
  parallel, extend a binder correspondence at binding forms, compare locals
  through it and module/global references with free-identifier=?. Contained
  (~50 lines), independently testable.
- A harness: wrap corpus programs and the rendered define-syntax in a fresh
  namespace, `expand` both sides, compare expansions to expansions (never
  expansion to source -- #%app/#%datum wrapping lands on both sides).
- First rung, cheapest: replay the existing macro test corpora and both
  benchmarks' learned macros through it by hand before writing anything
  general.
- Then: model-vs-Racket agreement on every oracle query the learner makes on
  the checked-in corpora. A divergence is either a bug in our four model
  extensions (at least one more likely exists) or a genuine model/Racket
  semantic boundary -- both are findings; write either up.
- The model expander stays; Racket joins as the outermost layer of the
  ladder, exactly as the real binary sits above mini.

## 3. Round-trip recovery fuzzing (the missing evaluation)

Goal: replace debugged-until-green hand benchmarks with an unbiased
distribution, and make the N1-N4 conjecture operationally testable.

- Generator: sample a random well-formed macro M (respecting the
  N1-N4 avoidances already encoded in tests/macro-fuzz.rkt's generators)
  and random call sites; EXPAND the calls with the model expander to
  manufacture the corpus; optionally mix in distractor programs.
- Run macro-search / macro-compress on the manufactured corpus; check M is
  recovered up to the catalogue's documented ambiguities.
- An unexpected recovery failure is exactly an N5 for the non-injectivity
  catalogue -- hand-trace it, and either extend the catalogue (and the
  conjecture) or file the learner bug.
- Output: a recovery-rate table by mechanism (V1-only / V2 / ellipses /
  mixed), deterministic and seeded like the existing fuzzers. This is the
  quantitative result a write-up needs.

## 4. Function-shaped classification (cheap, high story-value)

As analyzed in notes/2026-08-18-0539 direction 3, the cheap policy only:
classify each learned template by the four eta-convertibility clauses (pvar
in binder position; pvar occurrence under a template binder; pvar used other
than exactly once; evaluation-order residue) and REPORT why it needed to be
a macro. No define/letrec yet, no function learning -- just the classifier
over the winning template and its sites, plus tests pinning each clause.
Converts "macros strictly dominate functions under this objective" from a
methodological bug into the interesting output.

## 5. Act two's mini (the fast analog)

Goal: an analytic implementation held to the oracle's answers, the
micro-vs-mini move one level up -- both because nothing on the real-corpora
horizon is reachable at five minutes per four programs, and because deriving
the analytic account and letting the oracle catch its corners is exactly how
act one found stitch's bug.

- M2 from the design note (notes/2026-08-18-0323 section 6): the
  resolution-aware matcher -- rho bijection for H3, per-pvar canonical
  arguments compared by alpha for H4, the ref-in-range(rho) check for H1,
  resolution comparison for H2 -- differential-tested against
  check-by-expansion on everything the fuzzers generate.
- Then match-location indexing so scoring stops being per-(candidate, site)
  whole-program expansion; then, if needed, the branch-and-bound analog.
- Expect findings: every place M2 and the oracle disagree is either an M2
  bug or a new boundary case for the catalogue.

## 6. Michael's decisions (blocking nothing, shaping everything)

- Report the stitch utility over-count upstream (mlb2251/stitch). Verified,
  reproducible, written up in notes/2026-08-17-2030; sitting on it has no
  upside.
- Decide whether act two aims at a write-up. The related-work survey says
  the niche is open; the N-catalogue + hygiene-by-expansion + item 3's
  recovery table is roughly a workshop paper. If yes: items 2 and 3 are the
  evaluation section and jump the queue. If no: item 1 matters most, because
  the repo's product is then the explanation itself.

## Deliberately deferred

Literals lists; non-trailing/multiple ellipses (will meet the
zero-iteration-pruning interaction again); define/letrec + the
map/for-list layering benchmark; core-Racket then surface-Racket corpora;
definition contexts (the pearl's B.1/B.2 as adversarial tests); recursive
macros. Each adds expressiveness to a learner whose evaluation (item 3),
trust anchor (item 2), and fast implementation (item 5) do not exist yet.
The design notes have kept these doors cleanly open; they stay open.
