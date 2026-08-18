# Adversarial review 3: V2, the north-star benchmark, the fuzzer

Reviewer: an Opus subagent over commits 2eabd01..5d664b4 (V2
binder-position pattern variables, tests/for-set-test.rkt,
tests/macro-fuzz.rkt, the expander's appendix-B tests), 2026-08-18. All
findings below are applied (by two sonnet subagents plus one expander fix
made directly); dispositions inline. The reviewer's refutations were as
valuable as its findings and are recorded too.

## The headline: the blanket error handler was hiding a real expander bug

The review flagged (finding 3) that site-valid?'s `exn:fail?` handler --
"errors count as no" -- was routinely swallowing CONTRACT VIOLATIONS, not
exotic hygiene accidents: enumeration freely proposes templates where a
pattern variable's first occurrence is an expression position and a later
occurrence is a binder position, so transcription splices a compound term
into a binder list and crashes somewhere inside the expander. 36 such
swallowed crashes per macro-search on a small corpus. Two-part fix:
skeleton-match now refuses, as a SHAPE judgment, a binder-position reuse
of a pvar whose recorded argument is not a symbol; and the handler now
excludes exn:fail:contract?, so contract violations propagate as the bugs
they are.

Narrowing the handler immediately earned its keep: the corpus fuzzer then
FAILED with a genuine contract violation the old handler had been hiding.
Minimal repro (no fuzzer needed): a learned macro whose template reuses
#0 both as an expression argument and as its let's binder --

    m0 : (#0 2 (let ([#0 #1]) 2))
    (valid-sites (list m0) 'm1 'f '(m0 f f) ...)

The arity-0 constant candidate `f` validly matches the bare `f` in m0's
first argument slot; splicing `(m1)` there and transcribing through m0
puts the compound `(m1)` into m0's let-binder slot -- and expander.rkt's
lambda/let clauses called identifier-symbol on the binder WITHOUT an
identifier? guard (unlike every identifier clause around them), crashing
with a Racket contract violation where "not an identifier in binder
position" is a perfectly ordinary user-level expansion error. Fixed in
expander.rkt: both clauses now raise a proper (error 'expand ...) --
which site-valid? correctly reads as "no match", since a rewrite whose
expansion is ill-formed certainly changed the meaning. The repro now
yields exactly the right verdict: the compound-into-binder site refused,
the legitimately-matching site accepted.

The moral is the one the repo already believes, run one level deeper:
oracles must be allowed to fail loudly. "Errors count as no" is right for
the errors that ARE verdicts and dead wrong for the errors that are bugs;
telling them apart (user-level exn:fail vs exn:fail:contract) is cheap
and found a bug within minutes of being enforced.

## Findings fixed in macro-micro.rkt

1. (BUG, latent) hole-scope/finished? are blind to a hole in binder
   position while fill-hole fills it, and match-binder crashed on
   anything neither tvar nor pvar. The enumerator never produces either
   situation, but nothing enforced that. match-binder is now total (#f =
   no match), and check-corpus grew from a %-name check into a real
   well-formedness pass: lambda/let-headed forms must have their binding
   shape, binder positions must hold symbols, and corpus names may not
   collide with the expander's output namespace (a trailing `.N`, e.g.
   `x.1`, could alias a binder identity inside alpha=?).
2. (WEAKNESS) rewrite-program claimed to be "micro.rkt's dynamic program,
   verbatim in structure" while missing the memo table micro's own
   comment calls "not an optimization ... it IS the dynamic program".
   Measured exponential blowup on self-similar programs (4x per two
   nesting levels). Memoized on path, with the comment adapted (path, not
   subterm, is the right key here: the sites table is positional).
3. (see headline.)
4. (MISLEADING) for-set-test overclaimed "V2 is the only way any site
   rewrites at all" -- false: the reviewer exhibited a pure-V1 template,
   (sequence-fold #0 (set) #1), utility 202, rewriting all four programs
   (p4 included -- its shadowed set-add is INSIDE the argument, which is
   use-site syntax, so H2 does not apply to it). The true claim, kept: no
   V1 template of the target's shape survives H1, so V1 cannot recover
   for/set itself. Also added: a warning that the target's binder pvar is
   deliberately unreferenced in the template (the reference lives in the
   #1 argument) so nobody "cleans it up" later.
5. (WEAKNESS, documented not fixed) learned macros never extend the
   binding spec (design note section 7 requires an mdef binder mask):
   iteration-2 corpora like (m0 x (g x)) have their binder-position x
   walked as an expression and offered to corpus-facts as an identifier.
   Harmless today -- the oracle refuses wrong rewrites and a bare-symbol
   template cannot out-cost its site -- but it is the one place the
   "skeleton is a sound over-approximation" story leans on the oracle
   rather than the walkers. expr-children's comment now says all of this;
   the mask is future work.
6. (NITs) best-candidate was computing valid-sites twice per candidate
   (once for the >=2-programs filter, once inside macro-utility) -- the
   dominant cost of the benchmark, now computed once and threaded through
   an optional precomputed argument (backward compatible). Measured
   honestly: ~11% wall-time reduction (319.6s vs 358.6s same-container),
   not the naive 2x -- only filter-surviving candidates were ever
   double-computed. Policy-check and "only channel" comments corrected
   (the macro-name refusal is deliberately coarse in binder positions; an
   argument that IS a macro call is fine and intended). A committed
   "wait:" thinking artifact removed.

## Findings fixed in tests/macro-fuzz.rkt

7. (WEAKNESS) The corpus fuzzer could never generate an H2 case (globals
   and binder names were disjoint by construction, so nothing ever
   shadowed a global) nor an H3 case (perturb kept binder spellings
   identical across the three derived programs). Now ~20% of binders draw
   from the global pool (measured ~22% of corpora shadow) and perturb
   alpha-renames binders (~12%).
8. (WEAKNESS) The inverse property never exercised V2's reason to exist:
   no generated argument ever referenced a binder-pvar's name (the pools
   were disjoint) and no argument contained a lambda (H4's
   alpha-across-spellings untested). Arguments can now reference in-scope
   binder-pvar names (~2% of trials) and contain small lambdas (~20%).
   The trial also got stronger (finding 16c): recovered (path . arg)
   pairs must be path-consistent with the site, binder-origin arguments
   must be symbols, closed expression arguments must come back equal?.
9. (MISLEADING) The module header stated "un-transcription inverts
   transcription" flat; the property is FALSE in general (transcription
   is not injective -- (lambda (#0) (lambda (#1) (f #0))) with args a a
   loses the outer reference to shadowing). The generator's pscope gate
   and without-replacement naming are exactly what make it true; the
   header now says so. During the fix a THIRD non-injectivity source
   surfaced: a binder-pvar bound at two binder positions pins
   un-transcription's recovered name to the FIRST occurrence, while a
   capture reference resolves to the lexically nearest -- so capture
   references are only generated against once-bound binder-pvars. The
   family of these restrictions is becoming a de facto characterization
   of when un-transcription is well-defined; worth consolidating into
   the design note if a fourth one appears.
10. (NIT) fuzz-corpora ran macro-compress twice per corpus; now once.

## Refutations worth keeping (no code change)

- "Junk binder-pvar templates" (session log's own worry): the arithmetic
  was wrong (saves 1/site, not 2; break-even at 103 sites; -99 on a
  3-site corpus -- session log corrected in place), and the proposed
  filter would have DELETED THE FOR/SET ANSWER, whose binder pvar is
  unreferenced in the template by design. The genuinely degenerate
  subclass (unreferenced in template AND all arguments) is dominated by
  its tvar variant, which always matches a superset of sites. No filter.
  Empirically: 300 random corpora, 81 winners, none beaten by their V1
  variant.
- The missing constant/duplicate-argument filters cannot produce
  degenerate winners under this cost model: pvars are free in the
  template and cost cost(arg) per call, so the inlined/merged template
  strictly dominates for >=2 sites and is always enumerated. This is a
  real divergence from micro.rkt (where constant-argument is part of the
  OBJECTIVE, documented as not dominance-safe) -- macro-micro optimizes a
  cleaner objective. Recorded at reject?.
- No misalignment from the first-occurrence rule (paths and args always
  come from the same occurrence; the oracle validates exactly the call
  the rewriter emits); V2 binder paths cannot collide with expression
  positions in the DP; fresh-name does see binder occurrences (flatten
  reaches them).
- alpha=? survived directed attack (same symbol at different depths both
  sides, free-vs-bound both directions, shadowing).
- for-set-test's H2 claim verified by intervention: rename the shadowing
  binder and the site appears; drop the let and the root site appears.
  It is the shadowing doing the refusing.

## Suite state after everything

41 tests pass across src/expander.rkt (23, incl. ellipses), 
src/macro-micro.rkt (16), tests/macro-fuzz.rkt (2 properties: 400
corpora + 2000 inverse trials), tests/micro-test.rkt; for/set benchmark
passes in ~5.3 minutes (naive search, one container's timing; figures
move between containers).
