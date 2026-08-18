# Learning a hygienic macro, end to end

This is the worked example for `src/macro-micro.rkt`, the way
`walkthrough.md` is the worked example for micro- and mini-stitch. It traces
the learner's main benchmark — recovering the `for/set` comprehension from
its own expansions (`tests/for-set-test.rkt`) — through every mechanism the
module has: what a template is, how a candidate is matched, how hygiene is
checked without being implemented, how utility is measured, and what the
search around all of that looks like. Two shorter examples follow, for the
ellipsis and for learning a second macro on top of the first. Every number
and every expander output below is real; nothing is schematic.

The question, precisely: micro.rkt asks *which function compresses this
corpus most*. This module asks *which single hygienic `syntax-rules` macro
compresses this corpus most*, where using the macro means replacing a
subexpression by a call `(m e1 ... ek)` that **expands back** to it.

## 1. The corpus

Racket's `for/set` builds a set by iterating a body over a sequence:

```racket
(for/set ([x s]) (+ x n))
```

expands, in essence, to a fold. In this repository's small object language
(one-binder lambdas, one-binding lets, everything else a plain form), that
expansion is:

```racket
(sequence-fold (lambda (v) (lambda (x) (set-add v (+ x n)))) (set) s)
```

where `v` is an accumulator the macro made up and `x` is the iteration
variable the user chose. The corpus is four programs of that shape — the
kind of thing a code base acquires when a macro *doesn't* exist and people
write its expansion out by hand:

```racket
(define p1 '(sequence-fold (lambda (v)   (lambda (x) (set-add v   (+ x n)))) (set) s))
(define p2 '(sequence-fold (lambda (acc) (lambda (y) (set-add acc (* y y)))) (set) (nums)))
(define p3 '(sequence-fold (lambda (w)   (lambda (e) (set-add w   (f e 1)))) (set) q))
(define p4 '(let ([set-add (lambda (p) p)])
              (sequence-fold (lambda (u) (lambda (z) (set-add u (g z)))) (set) r)))
```

The accumulator's name varies (`v`, `acc`, `w`, `u`); the iteration
variable's name varies (`x`, `y`, `e`, `z`); the body and the sequence vary.
And `p4` is a trap, placed deliberately: its `set-add` is a **local**
binding, so its fold — identical in shape to the others — means something
different, and a correct learner must leave it alone.

The macro we hope to recover:

```racket
(define-syntax m0
  (syntax-rules ()
    [(_ %x0 %x1 %x2)
     (sequence-fold (lambda (%t0) (lambda (%x0) (set-add %t0 %x1))) (set) %x2)]))
```

Read it as `for/set` itself: `%x0` is the iteration variable, `%x1` the
body, `%x2` the sequence, and `%t0` the accumulator, which stays the macro's
own private business. `p1` should become `(m0 x (+ x n) s)`.

## 2. What "means the same" means

Everything in this module rests on one judgment: *does the rewritten program
still mean what it meant?* The meaning of a program is its hygienic
expansion — computed by `src/expander.rkt`, the model expander from
"Hygienic macro expansion explained" — and two expansions mean the same when
they are alpha-equivalent (`alpha=?`): binders may differ in name,
everything else must agree exactly.

The expander resolves everything. Each binder comes out with a fresh
identity (`x` becomes `x.1`), each reference comes out spelled as the binder
it resolved to, and each global stays a bare symbol. Expanding `p1` (no
macros involved yet, so this only freshens):

```racket
(sequence-fold (lambda (v.1) (lambda (x.1) (set-add v.1 (+ x.1 n)))) (set) s)
```

`v.1` and `x.1` are bound; `sequence-fold`, `set-add`, `n`, `s` are globals.
Now `p4`, the trap:

```racket
(let ((set-add.1 (lambda (p.1) p.1)))
  (sequence-fold (lambda (u.1) (lambda (z.1) (set-add.1 u.1 (g z.1)))) (set) r))
```

Look at the fold's `set-add`: it came out as `set-add.1`, the *local*
binding. The shadowing that was implicit in `p4`'s text is explicit in its
expansion — which is exactly what will let a dumb equality check catch it
later.

## 3. A macro use, expanded back

Splice the hoped-for call in place of `p1` and expand it with `m0` defined:

```racket
(m0 x (+ x n) s)
```

expands to

```racket
(sequence-fold (lambda (%t0.1) (lambda (x.1) (set-add %t0.1 (+ x.1 n)))) (set) s)
```

Compare with `p1`'s expansion above: the accumulator is spelled `%t0.1`
instead of `v.1` — the macro invented its own name, freshened by hygiene —
and everything else is identical. `alpha=?` maps `v.1` to `%t0.1` at the
binder and answers `#t`. That, in one sentence, is the module's correctness
criterion:

> Expanding the rewritten program, with the macro defined, yields a program
> alpha-equivalent to the expansion of the original.

Notice what the criterion quietly handled. The template's `%x0` sits in the
inner lambda's **binder position**, so the call's first argument `x` is not
an expression — it is the *name* the site wants the iteration variable to
have. Because the site supplies the name, the body argument `(+ x n)` may
mention it, and after transcription both are use-site syntax; the reference
resolves to the binder just as it did in the original. A pattern variable in
binder position is the mechanism that makes `for/set` learnable at all, as
the next section shows by taking it away.

## 4. Rewrites that lie, and how they are caught

The learner never implements hygiene rules. It implements one function,
`site-valid?`: build the call, expand the whole program, compare with
`alpha=?`. The design note
(notes/2026-08-18-0323-syntax-rules-learning-design.md) derives four
conditions H1–H4 a faithful rewrite must satisfy; here is the oracle
enforcing three of them, with real outputs. (The fourth, H3 — a template
binder's name is irrelevant — is what section 3 already showed working:
`v.1` against `%t0.1`.)

**Capturing an argument (H1).** Suppose the template used a private binder
for the iteration variable too — the natural first guess, since that is
what it does for the accumulator:

```racket
(syntax-rules ()
  [(_ %x0 %x1)
   (sequence-fold (lambda (%t0) (lambda (%t1) (set-add %t0 %x0))) (set) %x1)])
```

The structural matcher is perfectly happy to match this at `p1` — a `tvar`
matches whatever name the site binds, and the arguments read off as
`(+ x n)` and `s`. But expand the call `(mb (+ x n) s)`:

```racket
(sequence-fold (lambda (%t0.1) (lambda (%t1.1) (set-add %t0.1 (+ x n)))) (set) s)
```

The body still says `(+ x n)` — but `x` is now a *global*. The binder the
site called `x` became `%t1.1`, freshened away from the argument, exactly as
hygiene demands: an argument is use-site syntax and cannot be captured by a
binder the template introduces. In `p1`'s expansion the corresponding
reference was `x.1`, bound. `alpha=?` says `#f`; the site is refused. No
capture-avoidance logic anywhere — the freshening that hygiene *always
performs* becomes visible as an inequality of outputs.

**Using a shadowed global (H2).** Now the trap. Splice the call into `p4`,
over the fold inside the `let`:

```racket
(let ([set-add (lambda (p) p)]) (m0 z (g z) r))
```

expands to

```racket
(let ((set-add.1 (lambda (p.1) p.1)))
  (sequence-fold (lambda (%t0.1) (lambda (z.1) (set-add %t0.1 (g z.1)))) (set) r))
```

The macro's `set-add` is template syntax, so it resolves where the macro was
*defined*: globally. It came out as the bare global `set-add` — but `p4`'s
own expansion (section 2) has `set-add.1`, the local. Same spelling in the
source, different referents, plainly different expansions. `#f`; refused.
The oracle finds no valid site anywhere in `p4`, and the benchmark asserts
exactly that.

**Duplicating an argument (H4).** A pattern variable used twice in a
template is where compression really pays — and it imposes a condition on
the site: expansion will produce two copies of *one* argument, so the site's
two subterms had better mean the same thing. With `m2` defined as
`(g %x0 %x0)`, the call `(m2 (lambda (a) a))` expands to

```racket
(g (lambda (a.1) a.1) (lambda (a.2) a.2))
```

That is alpha-equivalent to the expansion of `(g (lambda (a) a)
(lambda (b) b))` — two identity functions, spelled differently, are still
two identity functions — so that site is accepted; it is not equivalent to
the expansion of `(g (lambda (a) a) (lambda (b) 1))`, so that site is
refused. The matcher never compared the two subterms at all: it took the
first as the argument and let the second match anything, because any
disagreement is guaranteed to surface as an expansion mismatch at the
other position.

The division of labor this section illustrates is the module's whole design:
`skeleton-match` settles *shape* and reads off arguments, deliberately blind
to hygiene, sound to prune with; `site-valid?` settles *meaning* by running
the expander. Utility-by-rewriting, micro.rkt's move, has a twin here —
hygiene-by-expansion.

## 5. The search

Where do candidate templates come from? The same place micro.rkt's come
from: grow a `hole` by filling it, leftmost first, with every production the
corpus could still match, and keep whatever matches somewhere in at least
two programs. The productions are read off the corpus (`corpus-grammar`):
for this corpus, 21 identifiers (`*`, `+`, `acc`, ..., `sequence-fold`,
`set`, `set-add`, ..., `z`), one literal (`1`), plain forms of lengths 1–4,
and both binding forms — with a lambda's or let's binder slot offering
either a fresh anonymous binder or a pattern variable. At the very first
hole there are 31 choices; at max-arity 3 the enumeration finishes with
**217,200** completed templates, each of which skeleton-matches into at
least two programs.

Scoring is where the oracle comes in, and it is savage: of those 217,200
templates, exactly **25** have oracle-valid sites in two or more programs.
Everything else was a shape coincidence — matched text whose meaning does
not survive being routed through a macro. Each survivor is scored by
actually rewriting the corpus (next section); the best positive score wins.
This is why the benchmark takes minutes: 59 expression positions across the
four programs, an expansion per skeleton match per candidate, no cleverness
anywhere. That is the price of a specification you can read, and paying it
is the module's declared genre.

Two of the 25 survivors are worth meeting. One is the winner. Another is

```racket
(sequence-fold %x0 (set) %x1)     ; utility 202
```

— the fold abstracted *as a function would have to*, each whole curried
lambda swallowed opaquely into `%x0`. It is valid, it compresses, and it is
exactly what micro.rkt could have found; nothing about it is syntactic. The
winner beats it by reaching *inside* the lambdas, which only a macro can do:

```racket
(sequence-fold (lambda (%t0) (lambda (%x0) (set-add %t0 %x1))) (set) %x2)   ; utility 1111
```

## 6. Utility, by rewriting

Utility needs no formula: rewrite the corpus, weigh it, subtract the cost of
the macro itself. Costs are 100 per atom, 1 per form, 0 per pattern
variable (a parameter is not structure). The rewritten corpus:

```racket
(m0 x (+ x n) s)
(m0 y (* y y) (nums))
(m0 e (f e 1) q)
(let ([set-add (lambda (p) p)])       ; p4, untouched
  (sequence-fold (lambda (u) (lambda (z) (set-add u (g z)))) (set) r))
```

The arithmetic, all of it checkable by hand:

|                    | cost |
|--------------------|-----:|
| corpus before      | 5238 |
| corpus after       | 3420 |
| the macro's template (7 atoms, 7 forms; three pattern variables free) | 707 |
| **utility = 5238 − 3420 − 707** | **1111** |

Note what is *not* charged: the pattern `(_ %x0 %x1 %x2)` costs nothing,
mirroring stitch, which charges an invention's body but not its binder
prefix — a parameter is free wherever it is written down; arity is paid at
each call, where the arguments are.

After rewriting, `rewrite-corpus` re-checks both of the module's promises
the slow way: the cost its dynamic program predicted equals the cost the
rewritten corpus actually has, and every rewritten program still expands to
something alpha-equivalent to its original. The learner does not trust
itself; it re-runs the oracle on its own output.

## 7. Abstraction over arity: the ellipsis

The second example is small enough to show whole. The corpus:

```racket
(f (g 1) (g 2))
(f (g a) (g b) (g c))
(f (g h) (g 1) (g 2) (g p))
```

Three programs, one shape, three *lengths* — and that last fact defeats
every ordinary template: a template is a form of some fixed length, so no
fixed template can cover two of these programs, and the two-programs rule
refuses every one. What is shared here is not a form; it is a form *family*,
and abstracting it takes the distinctive power of `syntax-rules`:

```racket
(syntax-rules () [(_ %xs ...) (f (g %xs) ...)])
```

In the learner's representation the template is `(f (ellip (g (svar))))`:
an `ellip` stands as the last element of a plain form and means "transcribe
my sub-template once per sequence element"; the `(svar)` inside it marks
where each element's argument goes. Expansion is the ordinary syntax-rules
behavior — `(m0 1 2)` expands to `(f (g 1) (g 2))`, and the zero-argument
call `(m0)` expands to `(f)` — and, because a sequence argument is just an
ordinary trailing argument of the call, the oracle, the rewriter, and the
cost accounting need no ellipsis cases at all. The search enumerates 670
finished candidates on this corpus and the ellipsis template wins with
utility 607, rewriting the corpus to

```racket
(m0 1 2)
(m0 a b c)
(m0 h 1 2 p)
```

This is abstraction over arity, which stitch cannot express: its inventions
have a fixed number of parameters, full stop.

Two facts about the search around this mechanism are worth knowing. The
module needs no filter against the degenerate splice-everything template —
`(f %xs ...)`, whose sub-template is a bare sequence variable — because a
call that repeats every element back verbatim saves nothing and pays for
the macro: on this corpus it scores −201, and utility already knows. The
module does need one filter for the search to finish at all: an ellipsis
candidate counts as matching a program only if it actually *iterates*
there. A zero-iteration match — a site consisting of just the fixed
prefix — is legal, but it never tests the sub-template against anything,
so it carries no information about whether the candidate's shape is right;
and prefixes that coincide with some short subterm are so common that
counting such matches lets a candidate's sub-template grow unconstrained
through the whole grammar. See `skeleton-programs`, and
notes/2026-08-18-1505-session-2-review-ellipses.md for the measurements.

## 8. Learning the next macro on top

One macro is an abstraction; a *library* is macros learned on top of each
other. `macro-compress` iterates: search, rewrite the corpus with the
winner, search the rewritten corpus with the winner's name off limits.
The module's own test corpus for this is what an earlier iteration would
leave behind: a small lambda-wrapping macro `m0`, with template
`(lambda (%t0) (f %t0 %x0))`, is already in the library, and its calls sit
in the programs as plain forms:

```racket
(g (m0 1) (m0 1))
(g (m0 2) (m0 2))
(g (m0 3) (m0 3))
```

The search finds `(g %x0 %x0)` — a template whose argument *is a macro
call*, which bothers the oracle not at all: expanding the rewritten
`(m1 (m0 2))` under both macros gives

```racket
(g (lambda (%t0.1) (f %t0.1 2)) (lambda (%t0.2) (f %t0.2 2)))
```

exactly what `(g (m0 2) (m0 2))` expands to (note H4 at work again: one
argument, two copies, each expansion freshening its own `%t0`). Two pieces
of bookkeeping make iteration honest. A learned macro's name is withheld
from the identifier productions, since a template that *mentions* a macro
would be a macro expanding to a macro call, which the standing
simplifications exclude. And a learned macro extends the object language's
binding structure: if `m0`'s pattern variable `%x0` had been in binder
position, then in a corpus call `(m0 x (g x))` the `x` at argument position
one is a binder's name, not an expression — so `expr-children` masks it
out of the expression positions exactly as it masks lambda's own binder,
reading the mask off the library macro's template
(`template-binder-mask`).

## 9. Matching, seen through the scope graph

There is a picture worth carrying away, from the scope-graph account of
hygiene in "Hygienic macro expansion explained". One macro expansion
extends a program's scoping structure in two ways at once: syntax that came
from the *template* resolves against the macro's definition site, and
syntax that came from the *arguments* resolves at the use site. The
expander tracks which is which (the paper marks template-origin syntax and
routes its resolutions through a different subgraph); hygiene is exactly
this two-way routing.

Now stand the picture on its head. The learner is handed the *result* —
plain code, uncolored — and a candidate template, and must decide whether
some coloring of the site's syntax into template-origin and
argument-origin reproduces every reference's resolution. Lay `p1` under the
template and the coloring is visible:

```racket
site:      (sequence-fold (lambda (v)   (lambda (x)   (set-add v   (+ x n)))) (set) s)
template:  (sequence-fold (lambda (%t0) (lambda (%x0) (set-add %t0    %x1 ))) (set) %x2)
```

Everything the template row spells out — `sequence-fold`, both lambdas,
`set-add`, `(set)` — is claimed as template-origin: those identifiers must
resolve at the definition site (that claim is what `p4` fails, its `set-add`
being local). Where the template row says `%x1` or `%x2`, the site's syntax
is argument-origin residue, passed through verbatim (and if such an
argument reaches back at a template-claimed binder, that is the H1 failure
of section 4). The two binders split: `v` is matched by `%t0`, template-
origin, so its site spelling is irrelevant and it will be freshened;
`x` is matched by `%x0`, argument-origin *even though it binds* — the one
binding in the template that belongs to the use site's color, which is
precisely what lets `(+ x n)` refer to it.

The learner never constructs this coloring. It picks the arguments by
shape, builds the call, and lets the expander redo the forward direction
while `alpha=?` checks that every resolution landed where the original
had it. But the coloring is what a successful match *means* — and reading
`skeleton-match` plus `site-valid?` with this picture in mind is reading
the module.

## 10. Where to go from here

`src/macro-micro.rkt` is written to be read top to bottom, with these
sections in this order: shapes, positions and costs; templates; the
skeleton matcher; the oracle; rewriting and utility; candidate enumeration;
the search; iteration. The semantics and the hygiene conditions are derived
in notes/2026-08-18-0323-syntax-rules-learning-design.md; ellipses in
notes/2026-08-18-1324-ellipses-design.md; the cases where a transcription
cannot be inverted — sharper than anything this walkthrough needed — are
catalogued in notes/2026-08-18-1541-untranscription-noninjectivity.md. The
benchmarks are
`tests/for-set-test.rkt` (this walkthrough's example, several minutes) and
`tests/my-when-test.rkt` (a binder-position pattern variable and an
ellipsis forced to appear in one macro, seconds — its header is a lesson in
how easily a corpus fails to force the mechanism it was designed for). The
fuzzer, `tests/macro-fuzz.rkt`, drives random corpora through the learner's
internal checks and verifies that matching inverts transcription on
thousands of generated templates.
