# Three long-term directions (Michael's, 2026-08-18) with first analysis

Michael floated three ideas mid-session, flagged as possibly not
well-formed. This note takes each seriously enough to find its load-bearing
questions and a cheapest-first experiment. None of this is scheduled work
yet; the immediate ladder (V2, for/set, review, fuzz) is unchanged.

## 1. The Racket expander itself as the reference oracle

Today the oracle is the pearl's model expander. Could `expand` from Racket
itself play that role -- either instead, or as one more rung on the
differential ladder (micro's matcher vs. model expander vs. Racket)?

What it buys:
- Trust. The model expander is ~400 lines we (mostly) imported; Racket's
  expander is the artifact the whole design claims to invert. "The learned
  macro, pasted into Racket, really expands back" is the headline claim,
  and only Racket can check it.
- It is the gateway to direction 2: any ambition to run on real Racket
  code needs the real expander in the loop anyway.

The design questions, in the order they bite:
- **Output comparison.** `expand` yields core forms (#%plain-lambda,
  let-values, #%app, quote, ...) as syntax objects. Our alpha=? becomes: walk
  two fully-expanded syntax objects in parallel, extend a binder
  correspondence at each binding core form, compare references with
  free-identifier=? (module/global refs) or the correspondence (locals).
  That is a referent-aware alpha over core Racket -- a contained piece of
  work, maybe 50 lines, and independently testable.
- **Harness shape.** Each check is: two `expand` calls inside a fresh
  namespace (make-base-namespace), programs wrapped as modules or
  top-level begin blocks with the candidate define-syntax prepended.
  Slower than the model expander but the same genre of gloriously slow;
  memoization or a persistent namespace if it hurts.
- **Language gap.** Our object language (one-binder lambda, one-binding
  let, plain forms) embeds trivially into Racket. The subtlety is
  what expansion ADDS: #%app insertion, #%datum wrapping of literals --
  handled by comparing expansions to expansions (both sides get the same
  wrapping), never expansion to source.
- **What it does NOT replace.** The model expander stays: it is small
  enough to read, it is the paper's artifact, and scope graphs are the
  vocabulary the design notes think in. Racket joins as the outermost
  differential layer: model-vs-Racket agreement on every oracle query the
  learner makes. Divergence either finds a bug in our extensions to the
  model, or (more interesting) a place where the model's semantics and
  Racket's genuinely part ways (definition contexts, B.1/B.2 territory).

Cheapest first experiment: take the existing macro-micro test corpora,
render each learned macro via mdef-syntax-rules, run original and rewritten
programs through Racket `expand` in a namespace, and hand-check the core
alpha comparison on those few cases before writing the general walker.

## 2. Real Racket corpora: learning surprising abstractions from the wild

The dream: point the learner at significant chunks of Racket code and have
it propose syntactic abstractions nobody wrote down. Two very different
framings hide inside it:

- **(a) Learn over fully-expanded core Racket.** Expand real modules first
  (kernel syntax only, ~20 forms, fixed and documented binding structure),
  then learn macros over the core language. Attractive because the object
  language stops being ours to invent: the binding spec is Racket's, known
  and finite. Un-attractive because expanded code is verbose and
  homogenized -- the abstractions sitting there may be the ones the
  original macros already expressed (we would partly be re-discovering
  for/list from its own expansions, which is exactly the north-star
  benchmark scaled up, and a fine validation) plus optimization artifacts.
  "Surprising" discoveries here mean: patterns that RECUR ACROSS different
  surface macros' expansions -- abstraction the macro ecosystem re-invents
  repeatedly without naming.
- **(b) Learn over surface syntax.** Corpus programs still contain macro
  calls; matching a template against surface code whose meaning depends on
  expansion forces the M1-prime move globally (the design note section 9
  anticipated this: resolution of arguments depends on expansion). Much
  harder; also where the treasure is -- abstractions over the code people
  actually write, e.g. recurring (send ... (lambda ...)) callback shapes,
  test-suite boilerplate, contract patterns.

Both framings meet the same scaling wall: real code is variadic
(multi-argument lambdas, many-clause lets, n-ary applications), so
**ellipses stop being optional** -- without abstraction over arity, every
arity of every shape is a separate macro and the utility of each is
diluted. Ellipses are the prerequisite rung, before either framing.
And both need direction 1 first (the real expander as oracle), plus the
"mini" optimizations (the naive enumerate-and-oracle loop will not survive
corpora bigger than toys; stitch's match-location indexing and
branch-and-bound have macro analogs the design note already gestures at).

Dependency order that falls out: ellipses -> Racket-expander oracle ->
core-Racket corpora (framing a) -> surface corpora (framing b, research
question in its own right).

## 3. Functions AND macros; learn each only where it earns its keep

The observation behind the question: in our current setting macros strictly
dominate functions. Any function abstraction (fn a1 .. ak) is expressible
as a macro whose template is the function body with pvars for parameters --
same call shape, same cost, and the macro also reaches abstractions no
function can (binder-position pvars, code under template binders,
identifier capture). A compression objective alone will therefore never
prefer a function, and will happily present a macro where a function is the
honest artifact. That is a real methodological bug in the eventual story:
the interesting output of a MACRO learner is the macros that are macros for
a reason.

What "needed a macro" means, concretely, in our vocabulary: a template
requires a macro iff it is not eta-convertible to a function application,
i.e. iff any of
  - a pvar stands in binder position (use-site capture; V2's whole point),
  - a pvar occurrence sits under a template-introduced binder (the
    argument is evaluated in an extended scope -- as syntax, it MOVES
    under a binder),
  - a pvar is used other than exactly once (duplication/omission of
    argument syntax; a function evaluates its argument exactly once),
  - argument evaluation order/conditionality differs from call order
    (in our pure-syntax criterion this reduces to the clause above plus
    position under binders; in a real language with effects it is the
    evaluation-order story).
Call a template FUNCTION-SHAPED when none of these hold. Function-shaped
templates are exactly the stitch inventions, reachable by micro.rkt.

Two design levels:
- **Cheap policy (worth doing early):** keep one search, classify the
  winning template, and EMIT it as a function when function-shaped, as a
  macro otherwise. Tie-break rationale: prefer the weakest abstraction
  that suffices (functions are first-class, separately compilable,
  semantically tame). The learner's output then self-documents which
  learned abstractions are syntactic for a reason. Nearly free to
  implement; needs define/letrec in the object language so a learned
  function has somewhere to live, plus beta as a second rewrite
  justification next to expansion (micro.rkt's criterion imported into
  the macro setting -- in a corpus-as-syntax world "justified by beta"
  is itself checkable by a little evaluator, or taken as definitional the
  way micro takes it).
- **The layering question (the deep one):** for/list syntactically
  abstracts over map, which functionally abstracts over a loop. In
  iterated learning this is: iteration k learns function map (function-
  shaped template over the recursion skeleton); the corpus rewrites to
  (map (lambda (x) body) lst) calls; iteration k+1 learns the macro
  (for/list ([x lst]) body) whose template is exactly that call shape --
  a macro OVER the learned function, macro-ness earned by the
  binder-position pvar alone. Neither layer alone tells the story: the
  function removes the recursion boilerplate, the macro removes the
  lambda boilerplate and binds the iteration variable. This suggests the
  learner should ALTERNATE (or jointly search) function and macro
  candidates and let utility pick per iteration; the library becomes
  stratified the way real Racket libraries are (racket/list under
  for/list). A lovely benchmark exists here: corpora of hand-written
  recursive list loops, target library {map, for/list-analog}, two
  iterations. That is "north-star 2" once define/letrec lands.

Blockers named honestly: the object language has no way to define a
function today (no define, no recursion), so function learning cannot even
be expressed in macro-micro's corpus; and the function/macro tie-breaking
above assumes the pure-syntax criterion -- a corpus language with effects
would need the evaluation-order clause done properly.

## Where this leaves the ladder

Near rungs (this repo, current session horizon): V2 (done), for/set
benchmark, review, fuzz. Middle rungs, now partially reordered by these
ideas: ellipses; function-shaped classification (cheap, high
story-value); define/letrec + the map/for-list layering benchmark. Far
rungs: Racket expander as outer oracle; core-Racket corpora; surface
corpora. The three ideas are not orthogonal: 3's layering benchmark is the
best small-scale rehearsal of 2's "rediscover the standard library"
ambition, and 1 is the precondition for 2 either way.
