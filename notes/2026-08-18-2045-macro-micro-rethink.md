# Rethinking macro-micro.rkt: simplifications that would also generalize

Claude, 2026-08-18. Michael's question, after the consolidation pass: is
there a different approach or architecture to some part of macro-micro.rkt
that does the same thing with less mechanism — ideally a simplification
that is also a generalization, easing the plan's next rungs? This note is
the assessment: an inventory of where the mechanism actually lives, two
proposals recommended (one now, one gated on the define/letrec rung), one
genuinely different architecture considered and declined with reasons, and
three smaller rethinks declined quickly.

## Where the mechanism actually lives

The parts one might expect to be complicated are not. The oracle is ten
lines (splice, expand, alpha-compare); the rewriter is micro.rkt's DP
verbatim; the cost model and the iteration loop are small and mirror
stitch. After the consolidation pass, the remaining mechanism concentrates
in three places:

1. **The matcher's argument-recovery protocol.** skeleton-match threads a
   binds hash through six walk cases; match-binder implements a
   first-occurrence protocol with a special later-occurrence-in-binder
   shape check (review finding F3); a completeness loop at the end rejects
   sites missing a pattern variable's argument (catalogue case N4).
   Meanwhile the SEQUENCE arguments are already recovered by a pure
   positional read-off after the walk (consolidation change #1) — so the
   matcher currently embodies two different theories of where arguments
   come from.

2. **The object language's shape, restated ten times.** lambda-form? /
   let-form? are cased in expr-children, template-binder-mask,
   hole-context, skeleton-match, ellip-form-path, svar-path,
   corpus-grammar, expansions, check-corpus — plus alpha=?'s own match
   patterns. Each walker re-derives the same three facts (where the binder
   is, where the subexpressions are, which subexpressions the binder
   scopes) with hand-written paths like (1 0 1). A fourth, newer case —
   walking a learned macro's call via template-binder-mask — restates the
   same facts a fourth way.

3. **The search-width heuristics** (grammar-variadic?, the iterating
   witness in skeleton-programs, the withheld productions). These carry
   measured justifications and are the honest price of naive enumeration;
   the plan already assigns their dissolution to M2's match-location
   indexing, so no rethink is proposed here.

## Proposal A (recommended now): finish the positional turn

The consolidation pass proved, for sequence arguments, that recovery is
positional and template-determined: the ellipsis's form sits at the same
path in site as in template, and within each element the argument sits at
the sub's first-(svar) path — a fact about the TEMPLATE, not the match.
The same is true of every pattern variable, and making that explicit
deletes the binds protocol entirely.

The claim: **a template statically determines where its arguments live in
any site it matches.** Pattern variable i's argument is the site's subterm
at the template path of i's first occurrence (walk order — binder slot
before subexpressions, a let's right-hand side before its body — which in
this syntax is plain textual left-to-right, the same order svar-path
already documents). Template and site paths coincide because matching is
positional and lengths agree everywhere except the one ellipsis form; for
a first occurrence inside the ellipsis's sub, the first matched element
sits at index `fixed` — which is also the ellip's own index in the
template, so even there the paths are literally equal.

skeleton-match then becomes three pure pieces:

- **shape-match?**, a boolean walk with no state: hole/pvar/svar match
  anything, a tvar in expression position needs a symbol, a binder
  position needs a tvar or pvar (totality kept), forms match positionally,
  the ellipsis form matches prefix-then-each-element. This is the whole
  walk; nothing is threaded.
- **pvar-paths : Template -> (Listof Path)**, one first-occurrence path per
  index — the same walk shape as svar-path and ellip-form-path, and the
  three collapse naturally into one parameterized find-first walker.
- **read-off + two post-hoc checks** on the recovered arguments:
  * every pattern variable's path must resolve in the site — this refuses
    exactly N4's zero-iteration erasure, replacing today's completeness
    loop with the same verdict;
  * every binder-masked pattern variable's argument must be a symbol,
    stated once via the existing template-binder-mask — this subsumes F3's
    first-vs-later-occurrence casing (binder-first arguments are symbols
    automatically; a compound recorded first and reused as a binder fails
    the mask check, exactly as match-binder refuses today).

match-binder, the binds hash, and the completeness loop all go. The
external interface is unchanged — same return value, same call sites
(valid-sites, skeleton-programs) — so this is a behavior-preserving
internal restructure, and the validation tooling already exists: review
cycle 1's reference-matcher harness (14 adversarial cases + 5,000
randomized transcribe-and-match trials) was built to attack exactly this
kind of positional-equivalence claim, plus macro-fuzz and both benchmarks.

Why it also generalizes:

- The invariant it states — arguments live at template-determined paths —
  is precisely what M2's match-location indexing is built on: the
  pvar-path table is the index's key set. Making the invariant a named
  function now means M2 refines an explicit artifact instead of
  re-deriving a buried one, and the micro/mini differential test gets a
  shared vocabulary.
- Pattern variables and the sequence variable become the SAME recovery
  mechanism, ending the matcher's two-theories split. The svar stops
  being special anywhere in the matcher; its remaining specialness
  (rendering, the one-per-template rule, the pattern's trailing `%xs ...`)
  is confined to the template layer where it belongs.
- The module-header story shortens to one sentence: the walk judges shape;
  the template says where arguments live; the oracle says whether they are
  acceptable.

## Proposal B (recommended when define/letrec work starts): one binding spec

The ten restatements of "where lambda and let put their binders and
subexpressions" should be one table. A FormSpec is a head, a shape check,
its binder slots (paths), and its expression slots (path plus does-this
-slot-see-the-binder). lambda: binder (1 0), exprs ((2) scoped). let:
binder (1 0 0), exprs ((1 0 1) unscoped, (2) scoped). Every walker in
inventory item 2 becomes generic code over the spec.

The pleasing inversion: the NEWEST mechanism already is this table for one
kind of form. A learned macro's call is walked from a spec derived from
its template — template-binder-mask says which argument slots are binders,
the rest are expressions. Rather than lambda/let being two hardcoded cases
and a macro call a third, lambda and let become entries of the same kind
the library already produces. Conceptually that is the right reading of
what this learner does: it learns new binding forms, so the library IS an
extension of the object language's binding spec — expr-children's comment
("this function IS the object language's binding spec") said so before
the code did.

Why gate it on define/letrec rather than do it now: micro-style prefers
concrete repetition over plumbing, and today the table would have exactly
two rows — the indirection would cost more readability than the
deduplication buys. The moment a third binding form arrives (define/letrec
is on the deferred list; core-Racket corpora and definition contexts sit
behind it, each bringing more forms), the trade flips hard: each new form
is one table row instead of ~10 function edits, and the multi-position
scoping that definition contexts need (a body that sees several binders)
is a spec-shape question rather than a rewrite of every walker. Two
boundaries to respect when it happens: alpha=? walks the expander's OUTPUT
language, which grows only if the expander's does, so it may keep its own
two patterns or share the table, whichever reads better; and templates
never contain macro calls, so template-side walkers need specs for core
forms only.

## Considered and declined: anti-unification as the generator

The genuinely different architecture the question invites: replace blind
top-down enumeration (grammar, expansions, hole-context, fill-hole,
reject?, skeleton-programs, and both width heuristics) with corpus-driven
generation — candidates as least general generalizations (lggs) of pairs
of corpus subterms, closed under pairwise lgg. Candidates would arrive
WITH their match sites; the two-programs rule would hold by construction;
the microkanren session's two corpus-poisoning lessons (shared spellings,
oversized shared shapes) would dissolve, since they are purely costs of
generating blind. Under this cost model the winner plausibly is the lgg of
its site set, by the same dominance arguments recorded at reject?
(specializing a template where all k sites agree pays 100 once and saves
100·k), so completeness would arguably improve too.

Declined, for a reason this repository has already documented from the
other direction: computing an lgg IN THE TEMPLATE LANGUAGE is
un-transcription, and notes/2026-08-18-1541 is the catalogue of exactly
where that inverse is ambiguous (N1–N3) or undefined (N4). The tvar/pvar
binder choice makes the generalization non-unique (the H1-blocked
template-binder variant versus the binder-pvar rescue is a semantic fork
invisible to the site text); generalizing across different-length forms is
sequence anti-unification, a substantially harder problem than the
syntactic lgg; and check-by-expansion is immune to all of it precisely
because it never inverts anything. The current architecture is not the
naive one awaiting the elegant replacement — it is the simple one, and the
catalogue is the evidence. Two things worth keeping from the idea: an
lgg-based PROPOSER that is allowed to be ambiguous and incomplete (emit
all readings; the oracle still judges) could someday replace the width
heuristics without touching the semantics; and if the nominal
anti-unification formal pass happens (already on the related-work thread),
its freshness/linearity side-conditions are the N-catalogue, so the two
work items are one.

## Smaller rethinks, declined quickly

- **svar as a depth-annotated pvar.** Unifying the node kinds looks like a
  simplification and would make a SECOND distinct sequence variable
  natural — but two distinct depth-1 variables force calls to pass
  per-element tuples, which kills "sequence arguments are ordinary
  trailing arguments," the property that keeps the oracle, rewriter, DP,
  and cost accounting ellipsis-free. The asymmetry is load-bearing; keep
  it until multiple/non-trailing ellipses force a wholesale redesign.
  (Distinguish this from lifting the duplicate-svar withholding — the SAME
  svar twice, as in the consolidation note's (f (g %xs %xs) ...) example —
  which needs no tuples, is compatible with everything, and is already
  recorded as a measure-it-first width toggle.)
- **Zipper/agenda enumeration** to avoid hole-context's re-walks:
  constant-factor, and "no zipper tables" is a standing design decision.
- **A compositional or local oracle** to avoid whole-program expansion per
  site: that is M2 itself (the resolution-aware matcher), already planned,
  and per-site whole-program expansion IS the micro semantics M2 will be
  differentially tested against. The micro file should keep it.

## Recommendation

Do Proposal A as its own small pass now: it deletes the matcher's last
piece of protocol machinery, is validated by harnesses that already exist,
and its named invariant is the foundation M2 builds on. Hold Proposal B
until the first new binding form is actually scheduled, then do it as the
opening move of that work. Record Proposal C's proposer idea alongside the
nominal-anti-unification thread and otherwise leave the architecture
alone: the oracle, the DP, and the cost model came through this rethink
without a finding, which is what the consolidation pass was for.
