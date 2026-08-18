# Ellipses: abstraction over arity, designed before it is built

The design note (2026-08-18-0323, section 9) called ellipses "the real
prize: abstraction over arity, something stitch cannot express at all" and
deferred them to their own note. This is that note. It designs the smallest
honest rung: **depth-1, one ellipsis per form, trailing position first**,
with the expander extended before the learner touches anything.

## 0. Why ellipses, and why now

Everything in the "three directions" note (2026-08-18-0539) that points at
real code — core-Racket corpora, surface corpora, rediscovering for/list —
stalls on the same fact: real code is variadic. Without abstraction over
arity, every arity of every shape is a separate macro, each too rare to be
worth learning; with it, one macro covers the family. In the current object
language the purchase is smaller but real: plain forms already come in
varying lengths, so families like

    (f (g 1) (g 2))          (f (g a) (g b) (g c))

are expressible corpora today, and no present template can cover both
programs with one macro.

What ellipses do NOT buy alone: recursion. A template `(cons e ...)` does
not exist — an ellipsis splices a sequence into ONE form level; folding a
sequence into nested conses needs a recursive macro, a different (harder)
rung. Non-recursive ellipses cover exactly the begin/when/list/application
-tail family: repeated elements at one level.

## 1. Semantics first: what the EXPANDER must learn

expander.rkt's match-pattern/transcribe "omits ellipses" (its own comment).
The learner's whole method is check-by-expansion, so nothing can be learned
that the oracle cannot expand: **the expander extension comes first**, and
is independently valuable (it moves the model expander toward full
syntax-rules; it can be differentially tested against Racket's own
syntax-rules on ellipsis programs, which connects to the "Racket as outer
oracle" direction).

The classic semantics, restricted to what this rung needs:

- **Patterns.** A list pattern may contain at most one element followed by
  `...`. Matching is deterministic: with p fixed elements before the
  ellipsis and s after (s = 0 in this rung), a target of length n matches
  iff n >= p + s, the middle n - p - s elements each match the ellipsis
  sub-pattern, and pattern variables inside it bind SEQUENCES (ellipsis
  depth 1).
- **Templates.** `sub ...` transcribes sub once per element of the
  controlling sequence. Every depth-1 variable inside sub must be
  controlled by exactly the ellipses around it (depth discipline); a
  depth-0 variable inside sub is repeated verbatim each iteration (legal
  in real syntax-rules, kept legal here).
- **Representation in the expander.** The pattern env currently maps pvar
  identifier -> syntax. It becomes pvar identifier -> (depth . value),
  where depth 0 carries syntax and depth 1 carries a list of syntax.
  match-pattern gains one case (the ellipsis element inside a list
  pattern); transcribe gains one case (an ellipsis element: look up the
  depth-1 variables inside sub, zip, transcribe per element, splice).
  Hygiene needs NO new mechanism: marks are applied to template
  identifiers exactly as before, once per transcribed copy; the marked
  copies share the def-mark, which is correct (they share the definition
  site) — this is worth an explicit test, since "each iteration freshens
  separately" is a plausible wrong guess (binder freshening happens later,
  at the binding form, per copy, which the existing machinery already
  does).
- **Errors kept honest:** a template ellipsis whose sub contains no
  depth-1 variable is a syntax error (nothing controls the iteration);
  depth mismatches (a depth-1 variable used outside any ellipsis) are
  errors. The learner's enumerator will be constructed to never produce
  either, but the expander should still refuse them — the oracle's
  "errors count as no" must not silently absorb malformed candidates the
  enumerator was never supposed to make (assert on the learner side, error
  on the expander side).

Deviation policy: expander.rkt is "the paper's code, kept intact"; the
ellipsis cases join lambda/applications/globals as clearly-marked
[extension] blocks, with tests including at least one hygiene-under-
ellipsis case (a template binder inside an ellipsis; an argument sequence
whose elements reference a use-site binder).

## 2. The learner's template language

One new template node:

    (ellip sub)     -- standing as an ELEMENT of a plain form, meaning
                       sub ... ; sub is a template; exactly one pattern
                       variable inside sub has depth 1

Restrictions for this rung, each with its reason:

- **Plain forms only.** lambda/let have fixed shapes in this object
  language; nothing variadic to abstract there.
- **At most one ellip per form, in TRAILING position.** Trailing covers
  the begin/when/list/apply-tail family that motivates the rung;
  prefix+suffix generality adds segment bookkeeping without adding a
  single interesting benchmark yet. With a fixed prefix and empty suffix,
  segment matching is deterministic (prefix consumes positionally, ellip
  consumes the rest), so matching stays a function, not a search.
- **Exactly one depth-1 pvar per ellip.** The learned PATTERN stays flat
  plus one trailing `xs ...`: (_ x1 .. xk-1 xk ...). Two depth-1 pvars in
  one ellip would need structured pattern elements ((y z) ...) — legal
  syntax-rules, deferred; it is a representation change on the pattern
  side, not the template side.
- **Depth-0 pvars and tvar references inside an ellip are allowed** (the
  expander repeats them per iteration; H4 generalizes pointwise, enforced
  by the oracle as always). Template BINDERS inside an ellip are allowed
  too — each transcribed copy freshens its own binder — but the enumerator
  may skip proposing them at first (a binder whose scope is one iteration
  of a splice abstracts nothing this corpus language can use).

Numbering: the depth-1 pvar is forced to be the LAST pattern variable
(highest index), so the call shape (m e1 .. ek-1 s1 s2 .. sn) splices the
sequence at the end and the flat-pattern renderer stays trivial. The
enumerator can maintain this invariant by construction (an ellip's depth-1
pvar is always minted fresh at the moment the ellip is proposed, never
reused); canonical-renumbering does the rest.

## 3. Matching and rewriting

skeleton-match, on a form template whose last element is (ellip sub)
against a site form: the k-1 fixed elements match positionally (site must
have length >= k-1); each remaining site element matches sub
independently; the depth-1 pvar's "argument" is the SEQUENCE of matched
subterms, recorded with the list of their paths. Zero iterations is a
legal match (site length exactly k-1) — syntax-rules says so — and the
oracle will confirm; whether the SEARCH wants to keep zero-iteration sites
is a utility question, not a semantics one.

Consequences downstream, all mechanical:

- **Arguments** are no longer one (path . subterm) per pvar: a depth-1
  pvar carries (paths . subterms) plural. The rewriter recurses into each
  element; the call it emits is (name e1 .. ek-1 s1 .. sn) — variable
  length per site. The DP's accept-cost sums over all spliced elements
  plus 1 + 100 as before.
- **The oracle is unchanged in shape**: build the call, expand under the
  candidate (whose pattern now ends in xs ...), alpha-compare. All the new
  semantics lives in the expander, where it belongs. H1-H4 need no
  restatement — the note's criterion ("expanding the rewritten corpus
  yields alpha-equivalent programs") never mentioned arity.
- **Cost model**: the `...` marker in a rendered template is an atom of
  the macro's source — charge it 100 like any atom, in the template only
  (calls contain no ellipsis, just the spliced elements at their own
  cost). The depth-1 pvar itself stays free (a parameter is not
  structure). No change to corpus costs.

## 4. Enumeration

New production at a hole that is the LAST element of a plain form under
construction... which is not how the current enumerator thinks: it
proposes whole form skeletons (make-list n 'hole) up front. The clean
extension: alongside each observed length n, ALSO propose, for each prefix
length p in 0..n-1 observed compatible, the skeleton

    (hole_1 .. hole_p (ellip hole))

but only when the corpus exhibits at least two DIFFERENT lengths >= p+1
for plain forms (corpus-facts gains "the set of lengths per nothing-in-
particular" — in this untyped setting, simply: at least two distinct
lengths overall, the coarsest useful gate). The gate matters: on a corpus
of uniformly 3-ary forms, every ellip candidate is either skeleton-
rejected late or degenerates into matching exactly one arity — wasted
oracle calls either way. The (ellip hole)'s hole is then filled by the
ordinary productions; the depth-1 pvar production is available only inside
an ellip that does not yet have one, and the ellip is not finished until
it has one (finished? learns this).

Junk-candidate pressure this creates, named for the reviewer: `(f (ellip
(pvar last)))` — "f applied to anything at any arity" — will match
enormously and compress genuinely (it absorbs every argument list of every
f-call). Whether that is signal (it IS the variadic-application
abstraction) or noise (it abstracts nothing but parentheses) is a filter
question; the constant/duplicate-argument filters from the design note
section 7 (still unimplemented) have an arity cousin here: an ellip whose
sub is a BARE depth-1 pvar saves only the head per site and should
probably be filtered as "identity splice", by analogy with the bare-pvar
identity template. Decide with measurements, not a priori.

## 5. Benchmarks and tests

- Micro benchmark: corpus `(f (g 1) (g 2))`, `(f (g a) (g b) (g c))`,
  `(f (g h) (g 1) (g 2) (g p))` — target `(f (ellip (g #0)))`, i.e.
  (define-syntax-rule (m x ...) (f (g x) ...)). Verifiable by hand.
- Hygiene benchmark: sequence elements referencing a use-site binder
  (must transcribe verbatim), template free identifier inside the ellip
  (H2 under iteration), a tvar inside an ellip (each copy freshened,
  all copies distinct from each other and from site binders).
- Expander-first tests: the extension is testable before any learner
  change, against hand-written syntax-rules programs, and (optional but
  cheap) differentially against Racket's syntax-rules via a script — the
  first concrete step of the "Racket as reference" direction.
- Fuzzer: property 2's template generator learns to emit ellips
  (trailing, one depth-1 pvar); args gain random-length sequences. The
  inverse property statement is unchanged and is exactly the right test:
  un-transcription of a splice must invert transcription of that splice.

## 6. Staging

1. expander.rkt: ellipsis matching + transcription + tests (own commit;
   no learner change). Differential spot-check against Racket syntax-rules.
2. macro-micro.rkt: (ellip sub) node, trailing-only; skeleton-match
   segments; sequence arguments through rewrite/DP; cost of `...`;
   enumerator productions with the two-distinct-lengths gate; finished?/
   hole-scope/renumbering updates. Tests incl. the micro benchmark.
3. Fuzz property 2 extension; then property-1 corpora with shared
   variadic families.
4. Filters conversation (identity-splice; the section-7 filters generally)
   informed by what junk actually wins on real runs.

Not this rung: nested ellipses (depth 2), structured pattern elements,
non-trailing ellipses, ellipses over binder lists (needs multi-arg lambda
in the object language first), recursive macros.
