# A walkthrough: the paper's running example, twice

This file traces one small corpus end to end through both implementations in
this repository, in their own vocabulary:

* **micro-stitch** (`src/micro.rkt`) — the executable specification. It says
  *what* the optimal abstraction is, by enumerating candidates the obvious way
  and scoring each one by actually rewriting the corpus.
* **mini-stitch** (`src/expr.rkt`, `src/pattern.rkt`, `src/search.rkt`,
  `src/rewrite.rkt`, `src/compress.rkt`) — the replication of real stitch. It
  computes the same answer without ever rewriting the corpus during the search,
  and without ever matching a pattern against the corpus twice.

Every number, pattern and program string below was produced by running the code
in this repository (Racket 8.10) on the corpus in the next section. The final
answer was also checked against the real binary,
`stitch/target/release/compress`.

The corpus is the running example of Section 2 of the paper (POPL 2023,
*Top-Down Synthesis for Library Learning*), translated from the paper's named
variables into the de Bruijn syntax both systems read:

```json
["(lam (+ 3 (* (+ 2 4) 2)))",
 "(lam (map (lam (+ 3 (* 4 (+ 3 $0)))) $0))",
 "(lam (* 2 (+ 3 (* $0 (+ 2 1)))))"]
```

The paper says the optimal abstraction is `fn0 = λα.λβ. (+ 3 (* α β))`. Both
implementations here agree, and so does the real binary. To reproduce:

```
racket src/compress.rkt YOUR-COPY-OF-THAT-JSON --max-arity 2 --iterations 3
```

---

## 1. The problem

### The corpus, parsed

Applications are binary and curried, so `(+ 3 x)` is `((+ 3) x)`; `lam` binds a
de Bruijn variable, so the paper's `λxs. map (λx. + 3 (* 4 (+ 3 x))) xs` becomes
`(lam (map (lam (+ 3 (* 4 (+ 3 $0)))) $0))` — the inner `$0` is the inner
lambda's variable, the outer `$0` is the outer lambda's.

Nothing in the system knows that `+`, `*`, `3` or `map` mean anything. They are
primitives, i.e. opaque leaves with names.

### The cost model

From `src/expr.rkt` (stitch's dreamcoder defaults): `COST-APP = COST-LAM = 1`,
`COST-VAR = COST-IVAR = COST-PRIM = 100`, and a freshly invented abstraction
name is a primitive like any other, `COST-NEW-PRIM = 100`. Structure is nearly
free; leaves are expensive. `cost` (mini) and `term-cost` (micro) compute it.

| program | cost |
|---|---|
| `(lam (+ 3 (* (+ 2 4) 2)))` | 707 |
| `(lam (map (lam (+ 3 (* 4 (+ 3 $0)))) $0))` | 910 |
| `(lam (* 2 (+ 3 (* $0 (+ 2 1)))))` | 909 |
| **total** | **2526** |

### What "best abstraction" means

An abstraction is a body over abstraction variables `#0 … #(k-1)`. Rewriting
replaces a matching subtree by a call `(fn_0 a1 … ak)`. Utility is

```
utility(A) = cost(corpus) - cost(rewrite(corpus, A)) - cost(A)
```

— what rewriting saves, less the size of the abstraction itself (stitch's
structure penalty, weight 1). In the abstraction's own cost, abstraction
variables are free of charge (`term-cost` gives `(ivar i)` cost 0): they are
parameters, not structure. The function is the paper's `cost_{α=0}` (defined
after Eq. 9) — but note this is one more place where we follow the
implementation against the paper's letter, in the same category as sentinels
instead of `&i` and the greedy rewrite instead of the DP. The paper's utility
(Eq. 8) charges the abstraction at full `cost(A)` with `cost_α = 100` in the
experimental configuration, which on `simple1` would give `202 − 302 = −100`;
real stitch charges `−cost_{α=0}(A)` (its `noncompressive_utility` is minus the
body's concrete cost, with ivar expansions contributing nothing), which gives
the `200` that both implementations and the binary report. Reconciling Eq. 8
against the code requires knowing this substitution.

Both implementations also inherit two of stitch's *semantic* defaults, which are
choices about what we want rather than speed hacks: an abstraction body may not
contain a free de Bruijn variable, and an abstraction must match in **at least
two distinct programs**.

---

## 2. micro-stitch: what is computed

`src/micro.rkt` is about 250 lines of actual code (and as much again in
commentary) with no cleverness anywhere in it. Programs are plain
immutable trees (`parse`); two occurrences of the same subtree are two unrelated
pieces of memory; equality is `equal?`.

### 2.1 The search space

Start from the pattern `'hole`, printed `??`, and fill one hole at a time —
micro always fills the **leftmost** hole (`hole-depth`, `fill-hole`). The
productions (`expansions`) at a hole are:

* `(app 'hole 'hole)` — `(?? ??)`
* `(lam 'hole)` — `(lam ??)`
* `(var i)` for every `i` less than the hole's lambda depth **inside the
  pattern**
* `(prim s)` for every primitive occurring in the corpus (`corpus-prims`); here
  seven of them: `*`, `+`, `1`, `2`, `3`, `4`, `map`
* `(ivar i)` for every abstraction variable already introduced, plus one fresh
  one while arity is below `max-arity`

At the top of the body the hole depth is 0, so no `$i` is offered at all — that
is the free-variable ban, enforced by construction. Concretely, the candidate
`(+ 3 (* $0 ??))` is never generated even though it would match
`(+ 3 (* $0 (+ 2 1)))` in program 3: `$0` there is bound by the *program's*
lambda, which is outside the abstraction, so the "abstraction" would not be a
function. (mini enforces the same thing with an explicit test,
`free-variable-prune?`.)

So the initial frontier `??` has 10 children; a hole under one of the pattern's
own lambdas would have 11.

### 2.2 Matching

`match-pattern` walks pattern and term together (the paper's LambdaUnify): holes
match anything and bind nothing; an abstraction variable binds whatever is
there; a repeated variable must see the *same* argument at each of its uses.
`pattern-sites` calls it against **every subterm of every program**, from
scratch, for every candidate. The corpus has 14 + 19 + 18 = **51 subterms**.

Four real match sets on this corpus:

| pattern | sites |
|---|---|
| `??` | 51 — every subterm |
| `(?? ??)` | 22 — every application |
| `(+ 3 ??)` | 4 — `(+ 3 (* (+ 2 4) 2))`, `(+ 3 (* 4 (+ 3 $0)))`, `(+ 3 $0)`, `(+ 3 (* $0 (+ 2 1)))` |
| `(+ 3 (* #0 #1))` | 3 — the same list minus `(+ 3 $0)` |

That last pair is Figure 2B of the paper: expanding a hole can only ever *lose*
match locations, never gain them. `(+ 3 ??)` matches at 4 sites; the finished
abstraction below it matches at 3 of those 4.

Micro's path from `??` to the winner, with site counts at each step:

```
??                 51 sites
(?? ??)            22
(?? ?? ??)         11
(+ ?? ??)           6
(+ 3 ??)            4      <- the paper's blue partial abstraction
(+ 3 (?? ??))       3
(+ 3 (?? ?? ??))    3
(+ 3 (* ?? ??))     3
(+ 3 (* #0 ??))     3
(+ 3 (* #0 #1))     3      <- the paper's green complete abstraction
```

### 2.3 Lifting arguments out from under lambdas

`lift` restates a matched subterm relative to the match location. If the
variable sits under `m` of the *pattern's own* lambdas, a free `$d` with
`d >= m` survives as `$(d-m)`, and a free `$d` with `d < m` pointed at a lambda
**inside the abstraction body** — there is no way to pass that in from outside,
so it becomes the paper's `&d` (micro's `captured` struct). `captures?` detects
one, and a site whose arguments contain one is matched but can never be
rewritten.

This corpus exercises it. The candidate `(lam (+ 3 (* #0 #1)))` matches two
subterms: `(lam (+ 3 (* (+ 2 4) 2)))` in program 1 and
`(lam (+ 3 (* 4 (+ 3 $0))))` in program 2. In the second, `#0` would receive
`(+ 3 $0)` — and that `$0` is the lambda the abstraction body itself contains.
Lifting gives `(+ 3 &0)`; the site is dropped by the rewriter.

### 2.4 The filters, each with a candidate it killed here

`reject?` runs on every child. On this corpus, of 828 children generated (each
counted against the first filter that applies, in `reject?`'s own order):

| filter | count | a candidate it killed |
|---|---|---|
| `null? sites` (zero matches) | 622 | `(* * ??)`, `(lam (+ 3 +))` |
| `too-few-programs?` (< 2 programs) | 87 | `(+ 2 1)` — matches only in program 3 |
| `constant-argument?` (argument capture) | 17 | `(#0 (* ?? ??))` |
| `identity-body?` | 1 | `#0` |
| `duplicate-argument?` (redundant argument) | 0 | — see below |
| — passed, finished, and scored | 27 | |
| — passed, still had holes, queued | 74 | |

The argument-capture example is worth spelling out, because the candidate it
kills is one step off the winner's path. `(#0 (* ?? ??))` matches at exactly the
three locations the winner will match at, and at all three `#0` receives the
same closed argument, `(+ 3)`:

```
program 0  (+ 3 (* (+ 2 4) 2))   #0 = (+ 3)
program 1  (+ 3 (* 4 (+ 3 $0)))  #0 = (+ 3)
program 2  (+ 3 (* $0 (+ 2 1)))  #0 = (+ 3)
```

A variable that is constant is not a parameter. Writing the argument into the
body gives `(+ 3 (* ?? ??))` — smaller, same match locations, strictly better —
and the enumeration reaches that anyway. This is the paper's Section 4.3
argument capture, and micro keeps it even though (paper footnote 2) it is not
strictly dominance-safe: stitch optimizes *subject to* it, so dropping it here
would let micro return something better than stitch and the two would disagree.

**Redundant argument elimination never fires on this corpus.** Nothing here has
two variables receiving identical arguments everywhere. The canonical shape is
`(f #0 #1)` over `["(f a a)", "(f b b)"]`: `#0` and `#1` agree at every site, so
`(f #0 #0)` matches the same places with smaller arity *and* collects the
multiuse bonus. Both implementations have the filter (`duplicate-argument?` in
micro, `redundant-argument-prune?` in `src/search.rkt`), and both have unit
tests for it; this corpus simply does not need it.

### 2.5 Utility by rewriting

There is no utility formula in micro. `rewrite-corpus` runs the paper's
Section 4.4 dynamic program bottom-up over each program: at every node,

* `reject-cost` — keep this node, rewrite below it as cheaply as possible;
* `accept-cost` — if the abstraction matches here and no argument captures,
  emit `(fn_0 a1 … ak)`: `COST-NEW-PRIM + COST-APP × arity` plus the best cost
  of each argument's original subterm (nested matches inside arguments are still
  rewritten);

and takes the cheaper. Then a top-down pass performs the accepted rewrites.
`abstraction-utility` subtracts costs, and cross-checks the DP's predicted cost
against the cost of the tree it actually built.

Here is the DP's verdict on program 1 for the body `(+ 3 (* #0 #1))`, bottom-up
(`accept` is `#f` where the abstraction does not match):

```
2, 4, 2, +, (+ 2), (+ 2 4), *, (* (+ 2 4)), (* (+ 2 4) 2), 3, +, (+ 3)
                                    accept #f everywhere -> reject
(+ 3 (* (+ 2 4) 2))       reject 706   accept 504   -> ACCEPT
    accept = 100 (fn_0) + 2 (two apps) + 302 ((+ 2 4)) + 100 (2)
(lam (+ 3 (* (+ 2 4) 2))) reject 505   accept #f    -> reject
```

Program 1 goes from 707 to 505. The three programs go to 505 + 708 + 707 =
**1920**, so rewriting saves 2526 − 1920 = **606**.

### 2.6 The winner

`micro-search` scores all 27 finished candidates and keeps the best:

```
body     (+ 3 (* #0 #1))
arity    2
utility  2526 - 1920 - 304 = 302
```

where 304 = `term-cost` of the body: three primitives (`+`, `3`, `*`) at 100
each, four applications at 1 each, and the two abstraction variables free. The
rewritten corpus is

```
(lam (fn_0 (+ 2 4) 2))
(lam (map (lam (fn_0 4 (+ 3 $0))) $0))
(lam (* 2 (fn_0 $0 (+ 2 1))))
```

which is, character for character modulo syntax, Eq. (3) of the paper.

Micro also passes through the runners-up on the way, and it is useful to see how
flat the landscape is. All 27 finished candidates were scored the same way; the
top of the list:

```
(+ 3 (* #0 #1))   302     <- winner
(+ 3)             203     <- an arity-zero abstraction: just a name for (+ 3)
(+ 3 #0)          202
(+ 3 (#0 #1))     100
(* #0 (+ 3 #1))   100
(+ 2)               1
(+ 2 #0)            0
(#0 #1)            -1
(lam (+ 3 (* #0 #1)))  -102
```

Note that arity-zero abstractions need no special treatment in micro: a
candidate with no abstraction variables is reached by the enumeration like any
other. `(+ 3)` scoring 203 will matter twice below — it is what mini computes up
front as its pruning cutoff (§3.2), and `(+ 2)` scoring 1 is what iteration 2
will find (§5).

### 2.7 What that cost

Micro generated **828 candidates**, matched each against all 51 subterms, and
rewrote the whole corpus **27 times**: 13 ms. That is fine for three tiny
programs and hopeless immediately afterwards. On prefixes of
`stitch/data/cogsci/nuts-bolts.json` (the corpus mini is tested on at full
size, 250 programs):

| programs | micro | mini |
|---|---|---|
| 2 | 620 ms | 14 ms |
| 3 | 1820 ms | 22 ms |
| 4 | 3272 ms | 22 ms |
| 5 | 9037 ms | 27 ms |
| 250 (3 iterations) | — | 2.9 s |

Everything in the next section exists to close that gap without changing the
answer.

---

## 3. mini-stitch: the same computation, made fast

### 3.1 One hash-consed corpus

`corpus-from-programs` parses all three programs into a single append-only
arena (`add-node!` interns), so identical subtrees anywhere in the corpus are
the same `Idx` and subtree equality is integer `=`. Micro's 51 subterms collapse
to **30 nodes**. The whole corpus, as the search sees it (the `programs` column
numbers the three programs 0, 1, 2):

```
idx  cost  num-paths  programs  subtree
  0   100      6      {0,1,2}   +
  1   100      4      {0,1,2}   3
  2   100      4      {0,1,2}   *
  3   100      4      {0,2}     2
  4   100      2      {0,1}     4
  5   201      2      {0,2}     (+ 2)
  6   302      1      {0}       (+ 2 4)
  7   403      1      {0}       (* (+ 2 4))
  8   504      1      {0}       (* (+ 2 4) 2)
  9   201      4      {0,1,2}   (+ 3)
 10   706      1      {0}       (+ 3 (* (+ 2 4) 2))
 11   707      1      {0}       (lam (+ 3 (* (+ 2 4) 2)))          <- root
 12   100      1      {1}       map
 13   100      3      {1,2}     $0
 14   302      1      {1}       (+ 3 $0)
 15   201      1      {1}       (* 4)
 16   504      1      {1}       (* 4 (+ 3 $0))
 17   706      1      {1}       (+ 3 (* 4 (+ 3 $0)))
 18   707      1      {1}       (lam (+ 3 (* 4 (+ 3 $0))))
 19   808      1      {1}       (map (lam (+ 3 (* 4 (+ 3 $0)))))
 20   909      1      {1}       (map (lam (+ 3 (* 4 (+ 3 $0)))) $0)
 21   910      1      {1}       (lam (map ...))                    <- root
 22   100      1      {2}       1
 23   302      1      {2}       (+ 2 1)
 24   201      1      {2}       (* $0)
 25   504      1      {2}       (* $0 (+ 2 1))
 26   706      1      {2}       (+ 3 (* $0 (+ 2 1)))
 27   201      1      {2}       (* 2)
 28   908      1      {2}       (* 2 (+ 3 (* $0 (+ 2 1))))
 29   909      1      {2}       (lam (* 2 (+ 3 ...)))              <- root
```

Two columns replace the sharing the arena folded away:

* **`num-paths`** — how many times this unique subtree occurs across the corpus.
  `(+ 3)` is one node with `num-paths` 4 (once in program 1, *twice* in program
  2 — `(+ 3 (* 4 …))` and `(+ 3 $0)` — and once in program 3). The 30 nodes'
  `num-paths` sum to 51, micro's subterm count.
* **`programs-with`** — which programs contain it, which is what the
  ≥ 2-programs rule consults (`single-task-prune?`).

Both are computed once in one downward sweep at `seal-corpus!`, exploiting the
arena's child-first invariant.

### 3.2 Arity-zero priming: a cutoff before the search starts

`arity-zero-best` scores every closed node occurring in ≥ 2 programs as an
abstraction with no arguments — just a name for a repeated piece of code:
`compressive = num-paths × (cost − 100)`, `utility = compressive − cost`. Only
two nodes score positive here:

```
(+ 2)   num-paths 2   compressive 2 × 101 = 202   utility 202 - 201 =   1
(+ 3)   num-paths 4   compressive 4 × 101 = 404   utility 404 - 201 = 203   <- best
```

So before expanding a single hole, the search has a candidate answer worth 203
and a pruning cutoff of 203. (This step is also why the whole `num-paths` column
matters: `(+ 3)` is a *single node* in the arena, and it is worth 203 only
because it occurs four times.)

### 3.3 The initial pattern and the upper bound

`initial-pattern` is `??` with match locations = all 30 span nodes.
`utility-upper-bound` scores a set of locations by pretending each one collapses
to a bare call:

```
bound(locs) = Σ max(0, num-paths(loc) × (cost(loc) - COST-NEW-PRIM))
```

For the 30 nodes above that is **10006**. It is deliberately blind to the body:
that is what makes it monotone — expanding a hole only removes locations, so a
child's bound is a sub-sum of its parent's. `search` asserts exactly that on
every expansion, and `finish` asserts that no finished utility exceeds its own
pattern's bound.

### 3.4 The winning path, location by location

`search` pops the highest-bound pattern, takes the most recently created hole
(`pattern-next-hole` — depth-first), and asks two questions.
`syntactic-expansions` groups the current match locations by
`(arg-expands-to (extract-arg c loc hole))` — a table lookup and a groupby, no
unification anywhere — and `ivar-expansions` offers a fresh abstraction variable
(keeping every location) or a reuse of an existing one (keeping the locations
where this hole sees the same argument the variable already sees, which is a
single integer comparison thanks to hash-consing).

Here is the path to the winner, as `expand-pattern` builds it. Match locations
never grow:

| step | hole filled | pattern | locations | bound | body-utility |
|---|---|---|---|---|---|
| 0 | — | `??` | 30 | 10006 | 0 |
| 1 | `()` → app | `(?? ??)` | 18 | 7173 | 1 |
| 2 | `(arg)` → app | `(?? (?? ??))` | 7 | 3737 | 2 |
| 3 | `(arg arg)` → `#0` | `(?? (?? #0))` | 7 | 3737 | 2 |
| 4 | `(arg fun)` → app | `(?? (?? ?? #0))` | 7 | 3737 | 3 |
| 5 | `(arg fun arg)` → `#1` | `(?? (?? #1 #0))` | 7 | 3737 | 3 |
| 6 | `(arg fun fun)` → `*` | `(?? (* #1 #0))` | 3 | 1818 | 103 |
| 7 | `(fun)` → app | `(?? ?? (* #1 #0))` | 3 | 1818 | 104 |
| 8 | `(fun arg)` → `3` | `(?? 3 (* #1 #0))` | 3 | 1818 | 204 |
| 9 | `(fun fun)` → `+` | `(+ 3 (* #1 #0))` | 3 | 1818 | 304 |

The 18 locations after step 1 are exactly the 18 `app` nodes of the table above;
the 7 after step 2 are the applications whose argument is itself an application;
the 3 after step 6 are 10, 17 and 26 — the same three subtrees micro found, now
as three integers.

Note the variable numbering. mini fills the *newest* hole first, so the second
operand of `*` gets `#0` and the first gets `#1`; micro fills the leftmost hole
and gets the opposite. `(fn_0 a b)` under mini's body is `(fn_0 b a)` under
micro's — the same abstraction, and the same one the paper writes as
`λα.λβ. (+ 3 (* α β))`. The real binary agrees with mini, which is the point:
its printed body is `(+ 3 (* #1 #0))`, its dreamcoder rendering
`#(lambda (lambda (+ 3 (* $0 $1))))`.

### 3.5 Argument extraction and de Bruijn shifts

`extract-arg` answers "what would the abstraction receive at this hole, at this
location?", memoized on `(location, path)`. It returns an `arg` with four
interesting fields: `unshifted` (the corpus subtree, which is what the rewriter
walks), `shifted` (the same subtree as seen *from the match root*), `shift`, and
`captures?`.

The subtree `(+ 3 $0)` in program 2 is the example to look at, because its
answer depends entirely on where you look from:

```
loc 17 = (+ 3 (* 4 (+ 3 $0)))          path (arg arg)        0 lambdas crossed
   unshifted (+ 3 $0)   shifted (+ 3 $0)   shift 0    captures? #f

loc 18 = (lam (+ 3 (* 4 (+ 3 $0))))    path (body arg arg)   1 lambda crossed
   unshifted (+ 3 $0)   shifted (+ 3 #0)   shift -1   captures? #t

loc 21 = the whole program              path (body fun arg body arg arg)
                                                             2 lambdas crossed
   unshifted (+ 3 $0)   shifted (+ 3 #0)   shift -1   captures? #t
```

`shift-arg` implements one downward pass equivalent to stitch's per-lambda
bubbling: relative to the argument's own root, a free `$d` becomes the
*sentinel* `#d` when `d < m` and `$(d-m)` otherwise, where `m` is the number of
lambdas crossed. At loc 18 and 21, `$0` points at a lambda that is *inside* the
abstraction body, so it becomes the sentinel `#0`, `captures?` is true, and
`marginal-utilities` forces that location's utility to zero: it is matched but
can never be rewritten. (This is why `shift` is −1 and not −2 at loc 21: the
argument closes up after the first crossing, and stitch only counts a downshift
at a lambda where the argument still has free variables.)

`shifted` is what makes variable reuse cheap: two holes see "the same argument"
exactly when their `shifted` Idxs are `=`. Hash-consing turns the
abstraction-variable equality constraint into an integer comparison, and it is
de Bruijn-correct because both sides are stated relative to the match root.

(One honest note on what mini-stitch does *not* replicate here. Real stitch
does not extract arguments on demand at all: `get_zippers` precomputes, in one
bottom-up pass, an `arg_of_zid_node` table holding the shifted argument for
every (path, node) pair in the corpus, each record built in O(1) by extending
the child's records, so that search-time matching is a single hash lookup and
every shifted subtree is computed once and shared by all its parents. Our
memoized `extract-arg` walk has the same asymptotics in the match-list
dimension but worse constants in the argument dimension. The zipper table is a
genuine architectural idea of the Rust — not mere interning — and it is the
main thing this replication deliberately trades away for legibility.)

Nothing on the *winner's* path crosses a lambda, so all six of its arguments
have `shift 0` and `captures? #f`:

```
loc 10  (+ 3 (* (+ 2 4) 2))    #0 = 2          #1 = (+ 2 4)
loc 17  (+ 3 (* 4 (+ 3 $0)))   #0 = (+ 3 $0)   #1 = 4
loc 26  (+ 3 (* $0 (+ 2 1)))   #0 = (+ 2 1)    #1 = $0
```

The capture machinery still shows up in the *answer*, though — through what it
excluded. `(lam (+ 3 (* #1 #0)))`, the same body with the lambda pulled inside,
matches at two locations (11 and 18) but is usable at only one, because at 18
its `#0` would be `(+ 3 $0)` with the sentinel. Its utility is −102, and the
abstraction that keeps the lambda *outside* itself wins.

### 3.6 The prunings

Every expansion runs the gauntlet in `consider!`. Counts and examples from this
corpus:

* `free-variable-prune?` — `$0` at the top of the body (1 location), and
  `(?? $0 #0)` further down. A variable no lambda of the body binds.
* `single-use-prune?` — a pattern matching a single *unique subtree* with no
  free variables, e.g. `map` or `(* 4)`. Whatever it grows into, the arity-zero
  abstraction for that subtree is at least as good, and `arity-zero-best`
  already scored every one of those.
* `single-task-prune?` — e.g. `(?? 4 #0)`, whose one surviving location is
  `(* 4 (+ 3 $0))` in program 2. (Single-use pruning does *not* also apply
  there: that subtree has a free variable, so it is not a legal arity-zero body
  and nothing dominates the pattern.)
* `useless-abstract-prune?` (argument capture) — fires twice here. The clean
  case: `(lam (+ #1 #0))`, matching at locations 11 and 18, where `#1` receives
  the closed argument `3` at both. Inlining gives `(lam (+ 3 #0))`, which is
  smaller and matches the same places — and the search reaches it anyway (it
  finishes with utility −101).
* `redundant-argument-prune?` — never fires here, as in micro.
* the bound, `bound <= cutoff` — see the next section.

Both dominance prunings are checked on *every* expansion, and both consult the
**parent's** variables against the **child's** locations, exactly as stitch does:
a variable introduced by this very expansion is not judged until the next one.

### 3.7 The bound, honestly

On this corpus the upper bound prunes **nothing**. Instrumenting `search` to
count: 59 pops with the bound enabled, 59 with it disabled. The cutoff starts at
203 and rises to 302 when the winner is found, and every branch that survived
the other filters has a bound of at least 303. A 30-node corpus is simply too
small for the bound to bite.

It is not too small to *see* the bound working, though: the worklist is a
max-heap on it, so the search visits branches in descending order of promise
(10006, 7173, 5253, 3737, …), and the winner is reached long before the
low-bound leftovers like `(?? 2)` (bound 707) and `(?? 4)` (bound 303).

The pruning power appears the moment the corpus is realistic. Same code, same
instrumentation, on prefixes of `nuts-bolts.json`:

| corpus | pops with the bound | pops without | bound-prunes |
|---|---|---|---|
| this example (3 programs) | 59 | 59 | 0 |
| nuts-bolts, first 10 | 1311 | 14956 | 380 |
| nuts-bolts, first 40 | 2439 | 81969 | 673 |

Both configurations return the identical abstraction and utility, which is what
"pruning" is supposed to mean. The paper's ablation (§6.4) reports 12×–208×
more nodes explored without upper-bound pruning; 11× and 34× here are the same
phenomenon at small scale.

### 3.8 Utility, analytically

When a pattern has no holes left, `finish` scores it without rewriting
anything. `marginal-utilities` computes, per location,

```
util-once = body-utility - (COST-NEW-PRIM + COST-APP × arity)
                         + Σ over multiply-used variables of (uses-1) × cost(arg)
```

zeroed at any location where an argument `captures?`. For the winner:

```
body-utility = 304          (+, 3, * at 100 each; four apps at 1)
arity        = 2
multiuse     = none         (each variable is used once)
util-once    = 304 - (100 + 2) = 202       at each of locations 10, 17, 26
```

`correct-for-self-overlap` then discounts a location by the utility already
credited to any match nested inside it at a *concrete* (non-variable) position.
`self-overlap-paths` returns `'()` for this pattern — `(+ 3 (* #1 #0))` cannot
match inside itself — so there is nothing to correct.

`compressive-utility` weights each location by its occurrence count and drops
locations left with nothing:

```
compressive = 202 × num-paths(10) + 202 × num-paths(17) + 202 × num-paths(26)
            = 202 × 1 + 202 × 1 + 202 × 1
            = 606
utility     = 606 - 304 = 302
```

**606 and 302 are the same numbers micro obtained by rewriting the corpus and
weighing it** (2526 − 1920 = 606; 606 − 304 = 302). One computes them by doing
the work, the other by an arithmetic identity over match locations. `num_uses`,
which stitch reports, sums `num-paths` over *all* match locations including
unused ones: 3.

### 3.9 What that cost

59 pops, 159 children considered, 23 finished candidates scored, 58 patterns
queued: **0.8 ms**, against micro's 828 candidates, 27 corpus rewrites and
13 ms. The gap is a factor of 16 here and a factor of 300 at five nuts-bolts
programs, and grows without limit after that.

---

## 4. Rewriting

`rewrite-with` (in `src/rewrite.rkt`) walks each original program top-down and,
at every location in the abstraction's `used` list, emits the curried call with
argument `#0` applied first:

```
(lam (fn_0 2 (+ 2 4)))
(lam (map (lam (fn_0 (+ 3 $0) 4)) $0))
(lam (* 2 (fn_0 (+ 2 1) $0)))
```

The real binary produces these three strings exactly. (Micro's are the same
programs with the two arguments swapped, per §3.4.) Costs: 505 + 708 + 707 =
1920.

**The de Bruijn fixup.** An argument is *lifted* to the call site, so a variable
in it whose binder lies at or above the match root now counts too many binders
and must be renumbered — by exactly the `shift` that `extract-arg` recorded. The
rewriter pushes a `ShiftRule` (a depth cutoff and a negative amount) while
descending into such an argument, so that variables bound *inside* the argument
are left alone. This example does not exercise it: every argument here has
`shift 0`. For a worked case see the tests in `src/rewrite.rkt` — "the de Bruijn
fixup" (`(lam (lam (h (lam (foo $2 p q r)))))` → `(lam (lam (fn_0 $1)))`, the
argument's index dropping by one as it moves outside one lambda) and "a lambda
inside the argument keeps its own variable" — and the `ctx_thread_*` corpora in
`stitch/data/basic`.

**The oracle.** `check-cost-mismatch` insists that

```
cost(rewritten corpus) = cost(original corpus) - compressive utility
```

to the unit: 1920 = 2526 − 606 here. The two sides are computed by completely
different routes — one analytic over match locations, one by actually building
the trees — so their agreement checks the utility formula, the multiuse
accounting, the self-overlap correction, the used/unused split and the rewriter
all at once. Real stitch keeps the same assert in release builds; §7 below is
about the one family of corpora where it fires.

---

## 5. Iteration

`compress` rewrites the corpus with the winner, names it `fn_0`, and searches
again. The new primitive is *only* a primitive: the rewritten programs are
printed to strings and parsed back into a fresh corpus, and nothing downstream
knows `fn_0` was invented.

**Iteration 2.** The once-rewritten corpus costs 1920 and has 28 nodes. Almost
nothing is shared any more; the nodes occurring in ≥ 2 programs are `fn_0`, `2`,
`+`, `4`, `$0` and `(+ 2)`, and only `(+ 2)` is worth naming:

```
fn_1 = (+ 2)   arity 0   num-paths 2   compressive 202   utility 1
```

The arity-2 search finds nothing better, so the arity-zero prime is the answer —
a reminder that arity-zero priming is a candidate answer and not only a cutoff.
`(+ 2)` is a *partially applied* primitive, which looks odd until you remember
that applications are binary: `(+ 2 4)` really is `((+ 2) 4)`, and `(+ 2)` is a
genuine shared subtree. Its utility of 1 is the smallest positive number the
cost model allows: it saves 202 and costs 201.

```
(lam (fn_0 2 (fn_1 4)))
(lam (map (lam (fn_0 (+ 3 $0) 4)) $0))
(lam (* 2 (fn_0 (fn_1 1) $0)))          cost 1718
```

**Iteration 3.** `search` returns `#f`: nothing left has positive utility, so
`compress` stops early with two abstractions. The real binary reports the same
two abstractions, the same utilities (302 and 1), the same `num_uses` (3 and 2),
and the same final cost, 1718. Micro's `micro-compress` reports the same two
abstractions and the same costs, with its own argument order.

---

## 6. The anti-unification lens

It is worth naming what the search space *is*.

Order patterns by generality: `??` is the most general thing there is, and a
finished abstraction is more specific than every partial abstraction on its path.
That order is the lattice of generalizations, and it is the same lattice
anti-unification works in. Anti-unification computes, bottom-up, the **least
general generalization** (lgg) of a *fixed* set of terms: given
`(+ 3 (* (+ 2 4) 2))` and `(+ 3 (* 4 (+ 3 $0)))` it returns `(+ 3 (* α β))`
directly.

Stitch runs the same lattice in the opposite direction. It descends from the
most general pattern, and the thing it is really searching over is not terms but
**match sets**: each expansion partitions the current locations
(`syntactic-expansions` groups them; `ivar-expansions` intersects them), and
every node of the search tree is a pattern together with the set of subtrees it
still generalizes. The two dominance prunings enforce two *necessary*
conditions of least-generality — no constant argument column, no duplicated
argument column:

* **argument capture** (`useless-abstract-prune?` / `constant-argument?`) — if a
  variable receives the same closed argument at every location, the lgg of that
  match set would have inlined the constant rather than abstracting it. The
  over-general pattern is discarded; the inlined one is reached anyway.
* **redundant argument** (`redundant-argument-prune?` / `duplicate-argument?`)
  — if two variables receive identical arguments everywhere, the lgg is
  *non-linear*: it reuses one variable in both positions. The two-variable
  version is discarded.

They do *not* enforce least-generality outright. A pattern with a variable
where the lgg of its match set has concrete shared structure is pruned by
neither rule: on `["(f (g (h a)) x)", "(f (g (h b)) x)"]` the candidates
`(#0 x)`, `(f #0 x)`, and `(f (g #0) x)` all reach scoring alongside the lgg
`(f (g (h #0)) x)` — their argument columns are neither constant nor
duplicated. What eliminates them is the **utility**: refining a variable into
structure shared by every match location gains
`(Σ num-paths − 1) · cost(structure)`, strictly positive whenever the
≥ 2-programs rule holds, so the lgg of a match set (generically — ties aside)
beats every strictly-more-general pattern over that same set. Least-generality
is thus enforced in two dimensions by pruning and in all the rest by
arithmetic: the *winner* is an anti-unifier of its match set, but plenty of
non-lggs get scored on the way there.

The upper bound is the part that has no anti-unification
analogue at all: it decides **which match sets are worth reaching**, discarding
whole regions of the lattice before their lggs are ever constructed. That
inversion — enumerate match sets top-down under a bound, instead of
anti-unifying fixed tuples bottom-up — is the paper's contribution, and it is
why stitch never has to consider which subsets of the corpus to anti-unify.

The contrast with *babble* (POPL 2023, same volume) is instructive: babble
computes anti-unifications over an e-graph, which lets it generalize modulo an
equational theory and find abstractions that are equal only up to rewriting —
strictly more expressive, but it must build and saturate the e-graph and then
extract, and its search is over e-classes rather than over corpus locations.
Stitch gives up the equational theory entirely and buys, with the bound and the
match-set representation, several orders of magnitude of speed on the syntactic
problem. Where babble asks "what generalizes these terms modulo the theory",
stitch asks "which set of corpus locations is worth generalizing at all".

---

## 7. Coda: where the specification and the fast version can disagree

Writing the same algorithm twice is only useful if the two copies can disagree.
Three places where they do, or where either departs from the real system:

**1. The utility over-count bug in real stitch.** Fuzzing micro against mini
found a corpus family where stitch's analytic utility is simply wrong — and
stitch itself says so, aborting on its own rewrite cost-mismatch assertion. The
smallest reproducer is

```
["(((a a) (a a)) ((a a) (a a)))", "((a f) (a f))"]   --max-arity=1
```

With `X = (Y Y)`, `Y = (Z Z)`, `Z = (a a)`, the pattern `(#0 #0)` matches at
`X`, at both `Y`s and at all four `Z`s, and the search credits each location's
saving once per occurrence. But rewriting `X` to `(fn_0 Y)` is exactly the move
that *deletes* one copy of `Y` — and with it the nested matches inside the
deleted copy that were already credited. The self-overlap correction misses this
because it deliberately ignores overlaps at variable positions (normally
correct: the rewriter descends into arguments), which is wrong precisely when a
multiuse variable keeps only one copy. Micro, which never predicts a saving,
gets it right (utility 504, rewriting to `(fn_0 (fn_0 (a a)))` / `(fn_0 (a f))`
— matching what stitch's own rewriter produces); mini reproduces stitch's 605
and then fails its own oracle with a message pointing at the note. Full account:
`notes/2026-08-17-2030-stitch-utility-overcount-bug.md`. None of stitch's own
corpora trigger it.

**2. Fused-lambda tags.** stitch's parser accepts `lam_1`, `$0_1` and friends,
which make `$0_1` and `$0_2` distinct nodes even though the tags are inert
unless `--fused-lambda-tags` is passed. `src/expr.rkt` has no tag field and
raises a clear error instead of silently conflating tagged variables, so
`simple3`, `simple4` and `simple5` in `stitch/data/basic` are out of scope
rather than failing.

**3. One genuine tie.** Two abstractions can have exactly equal utility, in
which case the winner is whichever the worklist reaches first — and mini's
worklist is not the real one's (no threads, no batching, a different heap). On
`ctx_thread_twice` at `--max-arity=3`, real stitch picks
`(A (lam (lam (+ (#0 $0 $1 f) (#0 $0 $1 f)))))` and mini picks
`(A (lam (lam (+ (a b #0 $0 $1 f) (a b #0 $0 $1 f)))))`, both with utility 1213.
`tests/differential.rkt` reports that as TIE rather than FAIL, and only when the
utilities are equal. It is the only tie in the suite — showing up in 2 of the 87
runs, the same corpus and arity at both iteration settings — and it is listed
explicitly in `known-ties` so that a *new* tie shows up as something to look at
rather than as noise.

Micro and mini also number abstraction variables differently, as this
walkthrough has shown throughout — micro fills the leftmost hole, mini the
newest. The tests compare bodies up to renaming the variables in order of first
appearance (`canonical` in `src/micro.rkt`), which is the right equivalence:
they are the same function with its arguments in a different order.
