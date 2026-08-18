# Rediscovering miniKanren's macros from microKanren

Claude, 2026-08-18. Michael's question: could the macro learner discover
the macro abstractions on top of microKanren that make miniKanren? Source
examined: jasonhemann/microKanren (microKanren.scm, the ~50-line functional
core; miniKanren-wrappers.scm, the macro layer). Result: yes for the two
macros the system's current template language can express — and they are
the two the wrappers file defines first. macro-compress, given hand-expanded
uses of the core, learns Zzz and then single-variable fresh, in that order,
and stops. Checked in as tests/microkanren-test.rkt (a few seconds).

## What the wrappers file contains, and what is in scope

miniKanren-wrappers.scm defines six macros over the core:

| macro | shape | in scope for the current learner? |
|---|---|---|
| `Zzz` | single rule, arity 1 | yes |
| `conj+`, `disj+` | recursive, two rules, right-nested expansion | no — needs recursive macros; the nesting is not a trailing ellipsis |
| `fresh` | recursive over the binder list, two rules | the one-variable slice yes; the general form no |
| `conde` | ellipses at depth 2, expands to macro calls | no — needs nested ellipses and macro-calling templates |
| `run`, `run*` | fixed plumbing around fresh | fixed-arity slices yes in principle; not exercised |

So the recursive/variadic spine is out of reach, matching the deferred
rungs already on the plan (recursive macros; non-trailing/multiple
ellipses; macros expanding to macro calls). What is in reach is exactly the
semantically interesting pair: Zzz, whose argument moves under binders
(delay — the canonical must-be-a-macro), and fresh, whose binder is named
by the user (the binder-position pattern variable).

## The corpus and its translation

Corpus programs are hand-expanded uses — goals written as one would write
them if the macros did not exist — translated into the object language.
One rule beyond notation: the object language has no nullary lambdas, so
microKanren's thunk `(lambda () e)` becomes a unary lambda with an unused
binder; Zzz g is `(lambda (s) (lambda (d) (g s)))`. Everything else is
direct (plain forms are n-ary; `call/fresh`, `conj`, `disj`, `==` are
ordinary globals).

The checked-in corpus is three programs: the expansions of
`(fresh (x) (== x 1) (eats x))`, `(conde ((likes 2)) ((== 3 4)))`, and
`(fresh (q) (halts q))` — five delayed goals, two freshes, one disj.

## What the learner does

Iteration 1 (3.3 s of search): learns

    (syntax-rules () [(_ %x0) (lambda (%t0) (lambda (%t1) (%x0 %t0)))])

— Zzz, verbatim modulo the thunk translation, utility 1515, and rewrites
the corpus to

    (call/fresh (lambda (x) (conj (m0 (== x 1)) (m0 (eats x)))))
    (disj (m0 (likes 2)) (m0 (== 3 4)))
    (call/fresh (lambda (q) (m0 (halts q))))

— which is the code a miniKanren author writes with Zzz in hand.

Iteration 2: over that corpus (m0 now in the library, its calls walked as
calls, its name off limits to templates), learns

    (syntax-rules () [(_ %x0 %x1) (call/fresh (lambda (%x0) %x1))])

— single-variable fresh, with the binder-position pattern variable, at
utility 1. Both fresh bodies mention their own variable (through an m0
call's argument), so the template-binder variant has zero valid sites
anywhere — H1 working through the library. Iteration 3 finds nothing.

The discovery order matches the definition order of the wrappers file, and
for a reason visible in the arithmetic below: the fine-grained delay pays
at every delayed goal, the binder macro barely pays at all.

## The arithmetic, and a finding about fresh

On a richer three-program corpus (two two-goal freshes and a two-clause
conde with its nested double delays — eight Zzz sites), utilities measured
directly with macro-utility:

| template | utility |
|---|---:|
| Zzz | 2727 |
| fresh over two goals, delays inlined (the full `(fresh (x) g0 g1)` expansion) | 1112 |
| conj+ at two goals, delays inlined | 909 |
| bare single-variable fresh | 1 |

Two observations worth keeping:

- **Zzz dominates every fused alternative** because it is paid at every
  delayed goal, including the nested double delays a conde clause produces
  — the rewriter turns those into `(m0 (m0 (== 5 6)))` with no special
  handling, the accept/reject DP recursing into arguments as always.
- **Bare fresh is almost worthless under this cost model**: a call/fresh
  site's scaffolding (call/fresh, lambda, the binder's atom, three forms)
  costs 303, and the replacing call costs 201 plus 100 to pass the
  binder's name — 102 saved per site against a 203 template, so it needs
  two sites just to reach utility 1. Passing the name eats the saving.
  This is a compression-eye view of why the real fresh is variadic and
  fused with conj+: the binder plumbing only pays when it amortizes over
  bundled structure. The learner takes the +1 and learns it anyway, which
  is the correct reading of the objective, but the margin is the thinnest
  in the repository.

## Two search-width lessons, learned the expensive way

Both first attempts at a corpus made the enumeration diverge (not the
oracle — candidates never stopped being generated):

1. **Shared binder spellings are poison.** Real microKanren output would
   spell every state variable `s/c` and every fresh variable per its
   source. A corpus doing that (every delay binding `s`/`d`) lets every
   partial template that bakes the spelling in survive the two-programs
   skeleton rule — the spelling matches in every program — so the width
   control the rule provides is lost. H2 would kill those templates at the
   oracle, but the oracle only sees finished candidates; the enumeration
   drowned first. Per-site spellings restore the pruning (and for/set's
   corpus, in hindsight, had this property by construction).
2. **The largest shape shared by two programs bounds the lattice.** A
   corpus whose two fresh programs shared their entire ~20-node expansion
   made every sub-template of that shape a survivor; enumeration ran past
   fifteen minutes before being stopped (the shared-spellings attempt was
   stopped past ten). The checked-in corpus keeps the largest
   cross-program shape at the 7-node Zzz skeleton, and the whole
   two-iteration run takes seconds.

Both are the my-when lesson again — the corpus, not the learner, decides
what the two-programs rule can prune — and both would be dissolved by the
planned mini-scale matcher (match-location indexing), since they are
purely costs of the naive enumeration.

## What recursive macros would unlock

With recursive templates (a rung already on the deferred list), conj+ and
disj+ become expressible — their expansions are right-nested folds of the
already-learned conj/disj over Zzz'd goals — and fresh generalizes from
one variable by the same recursion over the binder list. conde needs
depth-2 ellipses plus templates that call learned macros (conj+/disj+),
which is the "macros expanding to macro calls" simplification. miniKanren
is thus a natural end-to-end target for exactly the next expressiveness
rungs the plan defers: each wrapper macro sits one rung up from the ones
this experiment already recovers.
