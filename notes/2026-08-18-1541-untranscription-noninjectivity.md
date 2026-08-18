# When is un-transcription well-defined? The non-injectivity catalogue

Four boundary cases have now surfaced -- three from fuzzer generators being
corrected against the oracle, one from a review-driven extension -- where
"the template and arguments that transcribed this site" is NOT uniquely
recoverable, or not recoverable at all. Each was first met as a fuzzer
counterexample, hand-traced, and confirmed to be the SEMANTICS refusing,
not a learner bug. Consolidated here because they jointly sketch the
side-conditions a formal treatment of un-transcription (the nominal
anti-unification framing from the related-work note) would need as
freshness/linearity constraints. The learner itself needs none of this
machinery -- check-by-expansion is immune to non-injectivity, since it
only ever asks "does THIS candidate transcribe to THIS site", never "what
transcribed it" -- but the fuzzer's inverse property ("un-transcription
inverts transcription") is exactly a claim of injectivity, so its
generator must avoid each case, and the avoidances are the catalogue.

Notation: #i are pattern variables; binder-position #i (V2) receives the
site's binder NAME; sub ... is an ellipsis (one per template, trailing).

## N1. Binder-position pvar reused outside its binder's scope

Template fragment: (let ([#0 e]) body) with another #0 occurrence in a
position the let's binder does not scope (the let's own right-hand side, a
sibling subtree). Transcribing with #0 := x puts the SAME spelling x in
both places, but the out-of-scope occurrence refers to whatever x means
THERE -- an unrelated binder or a global. Un-transcribing the result as
"both occurrences are the one pattern variable" would require the argument
at the second occurrence to be the same name AND the same referent, which
H4 (referent-aware alpha on arguments) refuses unless the site
coincidentally arranges it. Not a template the search needs: the variant
with a fresh pvar at the second position matches strictly more sites.
(First fuzzer session; generator now threads a pscope.)

## N2. Two binder-position pvars assigned the same spelling

Template: (lambda (#0) (lambda (#1) (f #0))) with args x x. The inner
binder shadows the outer, so the transcribed body's f-reference resolves
to the INNER binder -- but the template said #0, the outer. Expansion is
perfectly well-defined; it just does not mean what the template's indices
suggest, and no un-transcription of the output recovers this template
(reading the output back, the reference belongs to #1). Ordinary lexical
shadowing, manufactured by argument choice. The macro USER made this
happen; syntax-rules semantics is fine with it; only inversion is lost.
(First fuzzer session; generator draws binder names without replacement.)

## N3. One binder-position pvar bound at two binder positions

Template: (lambda (#0) (lambda (#0) (f #0 #1))) -- legal, and transcribing
with #0 := x binds x twice, self-shadowing. Skeleton-match's
first-occurrence rule recovers #0's argument from the FIRST binder
occurrence; but a capture reference in argument #1 resolves to the
lexically NEAREST x, the second one. Both choices transcribe to the same
site text; the correspondence between "which occurrence supplied the name"
and "which binder captures" is lost in the output. Un-transcription is
ambiguous, and the ambiguity is invisible to text. (Review-driven fuzzer
extension; capture references generated only against once-bound
binder-pvars.)

## N4. A depth-0 pvar occurring only inside an ellipsis, at zero iterations

Template: (f #0 (g #1 (svar)) ...) called with zero sequence elements
transcribes to (f a) -- #1's argument appears NOWHERE in the output.
Un-transcription cannot recover it because the output does not contain
it: transcription genuinely discards information at zero iterations.
skeleton-match soundly refuses (a required binding is missing); the
learner loses nothing (the site is also matched by the ellipsis-free
prefix template, which is cheaper); but any claim that transcription is
invertible must except this case outright. This is the sharpest of the
four: N1-N3 are about AMBIGUITY, N4 is about ERASURE. (Fuzz stage 3;
generator forces >= 1 iteration when some pvar lives only in the sub.)

## What the four have in common

Each is a failure of LINEARITY or FRESHNESS, the two side-conditions
nominal anti-unification imposes on generalization variables: N1 and N3
are non-linear uses of one variable in scope-sensitive positions; N2 is a
freshness violation between two variables' instantiations; N4 is a
variable whose every occurrence sits under an iteration that may be
empty. Conjectured characterization, for a future formal pass:

> Un-transcription is well-defined (the template-and-arguments are
> recoverable up to alpha from the transcribed output) iff every
> binder-position pattern variable is bound exactly once and its
> spelling is fresh for every other binder its scope nests with, and
> every pattern variable has at least one occurrence outside every
> ellipsis, or the ellipsis is forced non-empty.

The fuzzer's generator restrictions are exactly an operational reading of
that conjecture; each catalogue entry cites where its restriction lives.
A proof (or refutation, i.e. an N5) belongs to the same future work item
as the nominal-anti-unification grounding. Note what the catalogue does
NOT threaten: the learner's soundness (the oracle never inverts anything)
and the two-sided benchmarks are untouched; this is about the THEORY of
inversion, and about keeping the inverse-property fuzzer honest about
what it can claim.
