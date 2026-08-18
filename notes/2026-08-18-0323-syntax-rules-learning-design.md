# Learning hygienic syntax-rules macros: a semantics-level design sketch

Status: design exploration, no code yet. The question (from Michael, 2026-08-18):
what would a stitch-like system look like that learns hygienic `syntax-rules`
macros — syntactic abstractions — instead of functions? This note works at the
level of micro.rkt: representations and the match operation, semantics first,
no optimizations. Where there are genuine design alternatives it sketches more
than one.

## 0. Standing simplifications

Adopted up front (Michael's list, plus consequences):

- no recursive macros, no macro-defining macros, no higher-order macros,
  no macros that expand to macro calls;
- single-rule macros with **flat patterns** `(m x1 ... xk)`: every pattern
  variable is a whole-form pattern, appearing once. No nested pattern
  structure, no ellipses, no literals list. (The pattern side is therefore
  trivial; all the interest is in the template and its inverse. Ellipses are
  the obvious next rung — see §9.)
- the macro is defined at the top level, so its definition context is the
  global scope: free identifiers in the template resolve globally;
- corpus programs are fully expanded core forms (no macro calls in the input),
  well-scoped, in one shared global scope.

Core language for the first cut, deliberately small:

    e ::= x                      identifier (reference)
        | (lambda (x) e)         one binder, one body form
        | (e1 e2 ... en)         application / any non-binding form
        | c                      literal constant

`if`, `cons`, etc. need no special treatment: a non-binding form is just a
list, and its head is an identifier like any other. The one thing the system
must know about the corpus language is **which positions bind** — a binding
spec. Everything below is parameterized by it, so adding `let` later is a
table entry, not a redesign.

## 1. The correctness criterion (what "un-transcribe" must mean)

stitch's rewrite is justified by beta: `(fn a1 .. ak)` reduces to the original
subterm. The macro analog is justified by **expansion**: we learn

    (define-syntax-rule (m x1 ... xk) template)

and rewrite matched sites to `(m e1 ... ek)`. The criterion:

> Hygienically expanding the rewritten corpus (with `m`'s definition in
> scope at top level) yields programs **alpha-equivalent to the originals,
> comparing referents** — every identifier occurrence resolves to "the same
> binder" under the alpha-correspondence, and free/global references resolve
> to the same global.

Two things to notice about this criterion before deriving anything from it:

1. It is *referent-aware*, not textual. Raw s-expression equality of the
   expanded output is both too strong (hygiene renames template binders, so
   the names will differ) and too weak (the same spelling can resolve
   differently — see H2 below). Alpha-equivalence over *resolved* syntax is
   the right notion, and this single choice drives the representation
   question in §4.

2. It is checkable by running the forward direction. We never need to trust
   a clever backwards analysis: rewrite, expand, compare. That is the same
   move micro.rkt makes with utility ("don't derive the formula, run the
   rewriter and weigh the result"), applied to hygiene. §6 builds a whole
   matcher design on it.

Vocabulary: matching a template against a site and reading off the arguments
is **un-transcription** — inverting the transcription step of the expander.

## 2. Orientation: what maps to what from micro.rkt

| micro.rkt                          | macro version                              |
|------------------------------------|--------------------------------------------|
| Term (de Bruijn)                   | resolved s-expression (§4)                 |
| Pattern (Term + hole + ivar)       | template (s-expr + hole + pvar) (§5)       |
| `lift` (renumber free vars)        | **nothing** — names are position-independent |
| `captured` / `captures?`           | hygiene condition H1 (§3)                  |
| `match-pattern` (LambdaUnify)      | un-transcription match (§6)                |
| "same arg judged after lifting"    | H4: alpha-equivalence of arguments (§3)    |
| free-var-at-top-of-body ban        | vacuous — templates *cannot* mention site binders (§3, end) |
| rewrite DP, utility by rewriting   | unchanged (§7)                             |
| filters (>=2 programs, const arg, dup arg, identity) | unchanged in spirit (§7) |

The headline: **de Bruijn arithmetic disappears, hygiene side conditions
appear.** micro's `lift` had two jobs — renumber a subterm's free indices for
its new position, and detect references to crossed binders (`&d`). Named
references don't need renumbering (an identifier means the same thing wherever
it sits, as long as its binder is still in scope), so the first job vanishes
outright: arguments are transcribed *verbatim*. The second job survives as
hygiene condition H1.

Conversely, de Bruijn gave stitch alpha-equivalence for free — equal terms
were `equal?`. With names we must rebuild alpha explicitly (H3, H4). The trade
is: no shift machinery, but an explicit notion of resolution and
alpha-comparison. Neither side gets scope for free; they pay in different
places.

## 3. The hygiene conditions

Derived by asking: in what ways could expanding `(m e1 ... ek)` fail to
reproduce the original site? Hygienic expansion treats the two provenances of
syntax differently:

- **use-site syntax** (the arguments `ei`) is transcribed verbatim — binders
  in it keep their names, references in it resolve as they did at the call
  site;
- **template syntax** gets the definition-site treatment: binders introduced
  by the template are renamed fresh at every expansion, and free identifiers
  in the template resolve in the macro's definition context.

Everything wholly use-site is therefore faithful *for free* — that is the
whole point of hygiene, run in reverse. Every condition below concerns the
template's own identifiers, and there are exactly four:

**H1 — arguments may not reference template binders.** If pattern variable
`#i` sits under a template-introduced binder `t`, and at some site the
corresponding subterm references the site binder that matched `t`, that site
cannot be un-transcribed: after expansion the template's binder is a fresh
name, so the argument's reference cannot reach it. This is precisely micro's
`captured`/`&d` situation, minus the arithmetic. Example: template
`(lambda (t) (f t #0))` at site `(lambda (x) (f x (g x)))` — the argument
`(g x)` mentions `x`, which matched `t`. Blocked. (V2 in §5 rescues exactly
these sites.)

**H2 — template free identifiers must resolve to their definition-site
meaning at every site.** The template's `f` will resolve, after expansion, in
the macro's definition context: globally. So a site identifier matches a
template free identifier only if it has the same name *and resolves
globally* — i.e. it is not shadowed at the match site. Example: template
`(f #0)` does not match the `(f x)` inside `(lambda (f) (f x))`; that `f`
means the local one, and the expanded macro's `f` would not. This condition
has no stitch analog at all — stitch's prims live in an unshadowable
namespace. It also applies, uniformly and pleasingly, to core form heads:
`lambda` in a template is a free identifier too, so a corpus that shadowed
`lambda` would block matches. (We assume the corpus never shadows core
names, but the machinery doesn't need the assumption to be stated —
resolution-comparison handles it.)

**H3 — template binder names are irrelevant.** The template's own binders are
renamed fresh at every expansion, so what they are called in the learned
macro's source is pure surface. Matching must therefore be modulo the site's
choice of name: template `(lambda (t) (cons t t))` matches both
`(lambda (x) (cons x x))` and `(lambda (y) (cons y y))`. Consequence for
representation: template binders are *semantically anonymous* — internally
they can be nameless tags, with names invented only when printing the learned
macro. The alpha-machinery stitch got from de Bruijn reappears here as a
binder-correspondence built during matching.

**H4 — multiple uses of one pattern variable must receive alpha-equivalent
arguments.** A pattern variable can appear several times in the template
(that is stitch's multiuse, and it's where compression comes from). After
expansion both copies are the *same* syntax; the original site had two
subterms. Faithfulness up to referent-aware alpha therefore requires the two
subterms to be alpha-equivalent with **identical external referents**: their
internal binding structure may differ in spelling, but any reference escaping
them must resolve to the very same binder/global. `(cons (lambda (a) a)
(lambda (b) b))` is a legitimate match for `(cons #0 #0)`. This is micro's
"the same argument is judged after lifting", with lifting replaced by alpha.

One micro rule becomes vacuous rather than translated: micro bans bodies with
free de Bruijn variables ("an abstraction with a free variable is not a
function"). A template simply *has no way* to reference a site binder above
the match root — its identifiers are either template-bound or resolve at the
definition site. The expressible templates are exactly the hygienically
learnable ones. (Site-binder-dependent behavior comes back, hygienically, via
V2 binder-position pattern variables — §5.)

## 4. Representing syntax: three options

### R1: raw s-expressions, resolve on demand

Terms are plain s-exprs. The matcher threads a scope environment (name ->
binder identity) as it walks the site, consulting the binding spec at each
form, and computes resolutions when it needs them (H1/H2 checks,
alpha-comparison).

Cheapest to start; closest to "the corpus is just sexprs". But scope
information is recomputed constantly, alpha-comparison is entangled with the
match walk, and — worse — the *rewritten* corpus stops being resolvable this
way: in `(m x (g x))` produced by a V2 match, the `x` in `(g x)` refers to a
binder whose binding occurrence sits in a *sibling argument*. Raw-sexpr
resolution can't see that without knowing `m`'s binding spec. Workable for a
single iteration, awkward after.

### R2: resolved s-expressions (recommended)

Parse once into s-expressions whose identifier occurrences carry their
resolution, micro-style data definitions:

    ;; An RSexpr is one of
    ;;   (ref binder)        reference; binder is a Binder or (global sym)
    ;;   (bind binder)       binding occurrence (only in binder positions)
    ;;   (form (Listof RSexpr))   a parenthesized form
    ;;   (lit datum)         literal constant
    ;;
    ;; A Binder is an opaque tag with a name attached: (binder sym uid).
    ;; Two occurrences relate iff their Binder tags are eq — names are
    ;; only for printing.

The parser (given the binding spec) assigns Binder tags; after that, *no
function in the system ever consults a scope environment again*. Resolution
is a field read. Alpha-equivalence is structural equality plus a bijection on
Binder tags encountered at corresponding `bind` positions, with `ref`s to
tags outside the bijection compared by `eq` — a ~15-line function, and it is
referent-aware by construction. H1 is "does the argument contain a `ref`
whose tag is in the match's template-binder range". H2 is "is the site
identifier's resolution `(global f)`".

This also survives rewriting: argument syntax keeps its Binder tags verbatim
when moved into a macro call, so the sibling-argument reference problem above
just… isn't one. The tags don't care where the binding occurrence sits. The
rewritten corpus remains a well-defined RSexpr corpus, which is what iteration
needs (§7, end).

The honest caveat: R2 *bakes in* the substance of hygiene (identifiers as
name+identity rather than name) instead of demonstrating it with marks or
scope sets. §6's M1′ variant addresses that.

### R3: core AST with named binders

micro's `Term` with a name field on `lam` — the minimal diff from existing
code. Rejected as the primary representation: it hard-codes the core forms
into the node types (every new form is a new struct and new cases
everywhere), can't represent non-core surface shapes, and closes the door on
ellipses, which are the whole reason to prefer s-expressions. Worth keeping
in mind only as "what a straight port of micro would look like".

### Sub-choice: lists as variadic forms vs cons pairs

Two ways to see `(f a b)`:

- **variadic forms** (recommended): a `form` node with n children.
  Enumeration and matching group by (head, length), the way a human reads a
  form. Fixed-arity everything; dotted tails don't exist.
- **binary cons pairs**: s-exprs as `(?? . ??)` trees. Regains micro's
  binary enumeration verbatim, and dotted patterns/templates (`(f a . #0)` —
  legal syntax-rules!) fall out. But partial-form matches and improper-list
  templates are a swamp of little decisions, and splicing tails are
  ellipsis-lite without ellipsis's guardrails. Note it, don't do it.

## 5. Representing templates

A Template is an RSexpr extended with `'hole` (unfilled, during enumeration)
and `(pvar i)` (pattern variable `#i`), plus template-binder tags:

    ;; A Template is one of
    ;;   'hole | (pvar i)
    ;;   (tref tbinder)            reference to a template binder
    ;;   (ref (global sym))        free identifier (definition-site)
    ;;   (tbind tbinder)           template binding occurrence
    ;;   (form (Listof Template))
    ;;   (lit datum)

Design points:

- **Template binders are anonymous** (H3): `tbinder` is a bare tag. The
  printer invents `t0, t1, ...` when rendering the learned
  `define-syntax-rule`. The alternative — carrying a concrete name chosen
  from one of the matched sites — records information the semantics ignores
  and invites spurious inequality; rejected.

- **Grammar-directed holes.** A hole can't be filled blindly: whether a
  position is a binder, a body, or an element is only known once the
  enclosing form's shape is chosen. So enumeration fills holes with whole
  *productions* — `(lambda (<fresh tbind>) hole)`, `(form hole ... hole)` at
  each (head-compatible) length observed in the corpus, a global identifier
  of the corpus, a `tref` to a template binder in scope at the hole, a pvar
  (reuse or fresh, under max-arity), a literal of the corpus. Structurally
  identical to micro's `expansions`, one production richer. Templates are
  s-expressions in representation but grammatical in discipline; pvars and
  holes appear only in expression positions (V1).

- **V1 vs V2: pattern variables in binder positions.** V1 (start here):
  binder positions hold template binders only. V2 (the genuinely new
  expressive rung): allow `(pvar i)` in binder position —

      (define-syntax-rule (m v b) (lambda (v) (f v b)))

  The macro user supplies the binder *name*; hygiene lets use-site binders
  capture use-site references, so the argument for `b` may legitimately
  mention `v`. This is the hygienic replacement for higher-order
  abstractions, and it rescues exactly the sites H1 blocks: `(lambda (x)
  (f x (g x)))` fails V1's `(lambda (t) (f t #0))` but matches V2's
  `(lambda (#0) (f #0 #1))` with arguments `x` and `(g x)`. stitch has no
  analog — its `&d` sites are matched-but-unrewritable, full stop; here one
  extra argument of arity buys the site back. (Search-wise that's a
  candidate-vs-candidate tradeoff the utility function already arbitrates.)
  H1 refines in V2 to: arguments may not reference *template* binders, but
  may reference binders matched by *binder-position pvars* — those are
  use-site syntax on both ends. In V1 an un-transcribed site reproduces the
  original up to renaming of template-binder names; in V2 with the binder
  name passed through, it reproduces it literally.

## 6. The match operation: two designs

### M1: skeleton match + check-by-expansion (the micro move — recommended first)

Split matching into a dumb candidate-decomposition and a semantic oracle:

1. **Skeleton matcher.** Walk template and site together, purely
   structurally: forms match forms of the same shape; `(ref (global f))`
   matches an identifier spelled `f` (name only — no resolution check);
   `tbind`/`tref` match any identifier, recording nothing; the *first*
   occurrence of `(pvar i)` grabs the site subterm as argument `ei`;
   subsequent occurrences of `(pvar i)` match anything at all. No H
   conditions, no consistency checks. Deliberately over-approximate.

2. **Oracle.** Build the rewritten site `(m e1 ... ek)`, expand it with the
   one-step hygienic transcriber, and test referent-aware alpha-equivalence
   against the original site. The site matches iff the check passes.

   Under §0's assumptions the transcriber is small and *is* the semantics of
   `syntax-rules` for this class: substitute the (resolved, tag-carrying)
   argument syntax into the template verbatim; mint a fresh Binder for each
   tbinder; template `(ref (global f))` becomes a reference resolved at the
   definition site. One step, no recursion — "no macros expand to macro
   calls" means transcription and expansion coincide.

Every hygiene condition — H1, H2, H3, H4 — is *enforced by the oracle without
ever being written down*. H2 in particular is easy to get subtly wrong by
hand (it's a negative condition about the site's context, not the site's
text); here it falls out of comparing resolutions. This is utility-by-
rewriting's twin: **hygiene-by-expansion**. micro refuses to predict what the
rewriter will save and instead runs it; M1 refuses to predict what the
expander will do and instead runs it. The skeleton matcher can be sloppy
because it is never trusted — even pvar-consistency (H4) can be omitted,
since choosing the first occurrence's subterm as the argument makes any
disagreement show up as an alpha-mismatch at the other occurrences.

Cost: one expansion + alpha-comparison per (candidate, site) pair.
Outrageous, and exactly as outrageous as micro re-matching every candidate
against every subtree from scratch. That's the genre.

Signatures:

    ;; skeleton-match : Template RSexpr -> (U #f (Listof RSexpr))   args by pvar index
    ;; transcribe     : Template (Listof RSexpr) -> RSexpr          fresh tbinders
    ;; alpha=?        : RSexpr RSexpr -> Boolean                    referent-aware
    ;; match-site     : Template RSexpr -> (U #f (Listof RSexpr))
    ;;   (define (match-site tpl site)
    ;;     (define args (skeleton-match tpl site))
    ;;     (and args (alpha=? (transcribe tpl args) site) args))

### M1′: the same, with a real expander (optional, more faithful oracle)

R2's transcriber is hygiene *by fiat* — identity tags do what marks/scope
sets exist to compute. A more faithful (and more expensive) oracle: keep the
rewritten program as a **raw** s-expression, run a miniature scope-sets (or
Dybvig marks) expander over the whole program with `m` defined, resolve, and
alpha-compare whole programs. Then hygiene is demonstrated, not assumed —
and the R2 transcriber becomes a *claim* that the little expander can
differentially test, exactly the micro-vs-mini pattern one level down.
Probably a later checkpoint, not the first cut; it is also the piece that
becomes load-bearing the moment corpora contain macro calls (§9).

### M2: resolution-aware matcher (the mini move — the fast analog, and LambdaUnify's true heir)

Hand-implement the H conditions in a single walk, for when expansion-per-site
is too slow. Threads:

- `rho` — a bijection tbinder -> site Binder, extended at binding forms
  (H3's alpha-correspondence, and micro's `depth` reborn as a map);
- per-pvar canonical arguments, compared with `alpha=?` on later uses (H4).

Identifier matching is a clean four-way case analysis on (template kind, site
resolution):

    template            site identifier resolves to        match?
    ------------------  ---------------------------------  -------------------
    (ref (global f))    (global f)                          yes   (H2)
    (ref (global f))    anything else                       no
    (tref t)            site Binder b with (rho t) = b      yes
    (tref t)            anything else                       no
    (pvar i) [expr pos] any subterm s                       H1: no ref in s to range(rho); then H4
    (pvar i) [V2, binder pos] the site's (bind b)           bind b becomes the argument

Note what is *absent*: no depth counter, no index renumbering, no `lift` —
the H1 check ("does the argument mention any rho-image") is the entire
residue of micro's shift machinery. M2 should agree with M1 exactly; fuzzing
M2 against M1 (and M1 against M1′) is the differential story this repo
already knows how to run, one level down from micro-vs-mini.

### Matched-but-unrewritable?

micro keeps H1-style sites as "matched but never rewritten" only for parity
with stitch's not-dominance-safe argument-capture filter (paper footnote 2).
Here there is no binary to agree with, so the simple rule wins: **a site that
fails the oracle is not a match**. If we later want the capture-adjacent
filters, revisit; note the asymmetry rather than inheriting it.

## 7. What carries over from micro unchanged

- **Rewrite** — the bottom-up accept/reject DP, verbatim: accept = emit
  `(m e1 ... ek)` and recurse into arguments, reject = recurse into
  children, take the cheaper. Arguments are spliced verbatim (no lift on the
  way out either). Only *expression positions* are candidate sites — a macro
  call is an expression, so binder lists and binding occurrences are never
  match roots.
- **Utility by rewriting** — `utility(m) = cost(corpus) − cost(rewrite(corpus, m))
  − cost(m)`, where `cost(m)` is the TEMPLATE's cost only, pvars free.
  [Corrected 2026-08-18, after Michael flagged it and the stitch source
  settled it: this note originally also charged the flat pattern
  `(m x1 ... xk)`, calling it "stitch's arity cost, made syntactic" — but
  stitch charges an invention nothing per parameter anywhere in the library:
  its structure penalty is the body at cost_{alpha=0} (`local_expansion_utility`
  hardcodes IVar to 0; the `cost_ivar = 100` config is inert), and neither
  the binder prefix nor the library entry is charged. The pattern is the
  binder prefix's analog, so it is free too; arity is paid only per use, in
  the call. Charging it distorted the search toward eta-reduced templates.]
  Cost model: keep micro's constants over RSexpr — 100 per
  identifier/literal, 1 per form-child edge, pvars cost 0 wherever they
  stand (parameters, not structure), 100 for the new macro name.
- **Filters** — >= 2 distinct programs; zero-match pruning (finiteness);
  constant-argument (a pvar receiving the same *closed* argument everywhere
  isn't a parameter — "closed" now means "no refs to binders outside
  itself"); duplicate-argument (up to `alpha=?`); identity template (a bare
  pvar).
- **Enumeration** — FIFO worklist from `'hole`, fill the leftmost hole with
  §5's productions, keep whatever still matches somewhere. Identical
  skeleton to micro-search.
- **Iteration** — with one addition: a learned macro extends the *grammar*.
  Iteration 2's corpus contains `(m1 e ...)` forms, so `m1` needs an entry
  in the binding spec (in V2, which argument positions were binders). Under
  §0's "no macros expand to macro calls", later templates must not contain
  `m1` — so learned-macro heads are excluded from the enumeration's
  identifier productions. First relaxation to consider once V1 works,
  since macro-calling-macro templates are where library structure appears.

## 8. Worked micro-examples (by hand)

1. **Alpha across sites** (H3): corpus `(lambda (x) (f x 1))`,
   `(lambda (y) (f y 2))`. Learn `(define-syntax-rule (m a) (lambda (t) (f t a)))`;
   rewrite to `(m 1)`, `(m 2)`. De-Bruijn stitch gets this via indices;
   names+hygiene recover it via H3. A system matching raw sexprs literally
   would not.
2. **Capture rejection** (H1): site `(lambda (x) (f x (g x)))` vs template
   `(lambda (t) (f t #0))` — argument `(g x)` references `rho(t)`; oracle:
   expansion gives `(lambda (t̂) (f t̂ (g x)))` with `x` unbound/other —
   alpha-mismatch. No match.
3. **The V2 rescue**: same site, template `(lambda (#0) (f #0 #1))`, call
   `(m x (g x))` — expansion reproduces the site literally. Match, arity 2.
4. **Referential transparency** (H2): template `(f #0)` vs the inner `(f x)`
   of `(lambda (f) (f x))`. Skeleton matches; oracle compares a
   global-`f` reference against a bound one — alpha-mismatch. No match.
5. **Multiuse alpha** (H4): template `(cons #0 #0)` vs
   `(cons (lambda (a) a) (lambda (b) b))`. Argument := `(lambda (a) a)`;
   expansion yields `(cons (lambda (a) a) (lambda (a) a))`, alpha-equal to
   the site. Match — the skeleton matcher never even compared the copies.

## 9. Doors deliberately left open (and how the design keeps them openable)

- **Ellipses** — the distinctive power of syntax-rules, and the real prize:
  they are *abstraction over arity*, something stitch cannot express at all.
  S-expression templates (R2) and variadic `form` nodes are chosen so that
  `(pvar i)`+`...` can slot in as a new template node later; patterns stop
  being flat at the same moment. Matching becomes segment-matching;
  un-transcription of `...` is anti-unification across siblings. Big rung,
  own note when we get there.
- **Structured patterns and literals lists** — flat patterns are a search
  restriction, not a representation one.
- **Macros in the corpus / macros expanding to macro calls** — needs the M1′
  real expander in the loop, since resolution of a macro call's arguments
  depends on expansion. This is where M1′ stops being a luxury.
- **Multiple rules per macro** — disjoint template alternatives sharing a
  name; utility already knows how to score a set of rewrites.
- **Other definition contexts** — H2 currently means "resolves globally";
  generalizing means carrying the definition context's resolution function.

## 10. Open questions

- Cost model details: is 1-per-form-child right, or should a form cost like
  micro's curried apps (n−1 per n-ary form) for continuity of numbers?
  Doesn't affect the semantics sketch; affects comparability of utilities.
- Should the enumerator propose literals (`(lit 1)`) as productions?
  Corpus-observed literals only, presumably, like corpus-prims.
- V2 binder-position pvars: same pvar in binder position *and* expression
  position is meaningful (`(lambda (#0) (cons #0 #1))`) — allowed from the
  start, or a separate rung?
- Tie-breaking / canonical form of learned templates for differential
  comparison between M1 and M2 (canonicalize tbinder order and pvar
  numbering, as micro's `canonical` does for ivars).
- Is there a syntax-rules analog of stitch's rewrite cost-mismatch assert
  worth keeping? Candidate: after every corpus rewrite, run the oracle's
  whole-program check (expand + alpha-compare) — the rewriter asserting its
  own faithfulness, not just its cost.

## Addendum (2026-08-18, after reading "Hygienic macro expansion explained")

Michael shared the tex source of his and Gregory Rosenblatt's pearl
(scope graphs / marked scope graphs / disjoin nodes) together with the
appendix's model expander (`expandersimpler.rkt`: marks, a scope-graph
`resolve`, syntax-rules matching and transcription, definition contexts,
macro-defining macros — ~300 lines). Several ideas transfer directly; one
corrects this note, and one puts a warning label on it.

### A. The appendix model *is* M1′, ready-made — flip the build order

§6 treated "a real marks/scope-sets expander as the oracle" (M1′) as a later
luxury and the R2 transcriber as the first oracle. The model expander already
exists, is small, and covers far more than §0's assumptions require (it
handles even the Fig. 12 macro-defining-macro example). So invert the plan:

- **The oracle comes first and is the model expander** (trimmed or near
  verbatim). Check a rewrite by expanding both programs and comparing:

      expand( (block defs... original) )
      expand( (block (define-syntax m (syntax-rules () [(_ x1 ... xk) tmpl]))
                     defs... rewritten) )

  The model's output is *fully resolved* — every binder renamed to a unique
  identity `x.n` — so "referent-aware alpha-equivalence" degenerates to
  structural equality up to a bijection on identities (numbering depends on
  counter order). One `expand` call per program per check; gloriously slow;
  exactly the genre.
- The R2 resolved-syntax transcriber becomes the thing that gets
  differential-tested *against* the model, not the trusted base.
- The corpus language question in §0 gets a concrete answer: adopt the
  model's input language (numbers, vars, `let`, `block`/`define`,
  `let-syntax`/`define-syntax`), possibly plus `lambda` (a small addition to
  the model). Learned macros are then *emitted as programs in the model's
  language* and checked end-to-end.

### B. H2 is the model's `literal-match?`, stated properly

The model matches syntax-rules literals by: both resolve to the same
binding, OR both are unbound with the same symbol. That is H2, generalized
and made precise. This note's phrasing "resolves globally / not shadowed" is
the special case where the macro's definition context is the top level; the
principled statement is *free-identifier=?*: the site identifier and the
template identifier resolve the same way relative to the macro's definition
site. Template free identifiers are pattern literals run in reverse — and
future literals-list support (§9) uses the identical relation, already
implemented in `make-literal-match?`.

### C. Un-transcription = choosing a marking (inventing a disjoin)

The paper's central picture: one macro expansion has *two* scoping-structure
extensions — definition-site (marked) and use-site (unmarked) — sharing the
template's shape, represented as one marked subgraph under a disjoin node
whose projection edges point at the definition site and the use site. Run
backwards, this is the crispest statement yet of what our matcher does:

> Matching a template at a site = choosing which identifiers in the site
> subtree receive the def-mark (template-origin) and which stay unmarked
> (argument-origin), such that resolving every identifier through the
> invented disjoin node reproduces the original program's resolutions.

M2's rho bijection (§6) is exactly the correspondence between site scope
nodes and the def-site extension; the template is the def-marked projection
of the site, the arguments are the unmarked residue. Bonus: the fact that
one template `lambda` contributes a scope node to *both* extensions cleanly
explains V1 vs V2 (§5) — V1 templates bind only in the def-site copy, V2's
binder-position pvars bind in the use-site copy — and shows a single binding
list can mix the two, since `for/set` itself binds one def-site name (`v`)
and one use-site name (`elem`) in the same lambda. That settles §10's
open question about mixing: it's the normal case, not a rung.

Also the visualization: the two-colored graph-extension figures are exactly
what a walkthrough of the learner should draw — the learner reverse-engineers
the coloring.

### D. A warning label with an expiration date on H1–H4

Appendix B.1 of the paper: when a macro is *used in the same definition
context where it is defined*, a use-site `define` binding CAN capture a
macro-introduced reference — real Scheme implementations do this, and
alpha-renaming-style hygiene accounts (Herman & Wand's transparency
side-condition; towards-essence's equivariance) forbid it. Appendix B.2:
with mutually-recursive definition contexts, the referent of a transcribed
free identifier may not even be *determined* at transcription time.

H1–H4 are precisely an alpha-renaming-style account. They are right for
§0's expression-only fragment, but they are the wrong *kind* of account the
moment the corpus language includes definition contexts (`block`/`define`)
or macros whose templates contribute definitions. The expand-and-compare
criterion (§1) survives all of this untouched — which is the strongest
argument yet for M1-as-specification: the oracle stays correct exactly where
hand conditions become subtle. And it marks the boundary where M2 must trade
the rho-bijection for genuine graph reasoning (scope separate from binding).
B.1 and B.2's programs go straight into the future adversarial test set.

### E. Marked graphs answer the rewritten-corpus representation question

§4 noted R2's binder tags survive rewriting even when a reference's binding
occurrence lands in a sibling argument. The principled version of that
observation is the marked scope graph itself: the rewritten corpus's scoping
structure is a graph with disjoin nodes, and resolution stays well-defined
without re-expansion. For iteration (learning m2 over a corpus containing m1
calls), "a learned macro extends the binding spec" (§7) is more honestly
"a learned macro's calls carry marked-subgraph structure".

### F. North-star benchmark: learn `for/set`

The paper's running example is a perfect end-to-end target: generate a
corpus of expanded `for/set`-style folds (varying iteration variable names,
body expressions, sequences, surrounding scopes — including a program that
locally shadows `set-add`, to exercise H2) and ask whether the system
recovers the macro. It exercises a template binder (`v`), a binder-position
pvar (`elem`), definition-site references (`sequence-fold`, `set-add`,
`set`, `lambda`), and a body pvar under both binders — every mechanism in
this note in one benchmark.
