# Related work: learning macros by corpus compression

Survey by a Claude subagent (web search, 2026-08-18), lightly edited. The
question: does anything already occupy "stitch-for-syntax-rules" -- search-
driven discovery of hygienic syntactic abstractions from expanded corpora?
Short answer: no; the two nearest traditions bracket it without covering it.

## 1. Compression-based abstraction discovery for macros/syntactic abstractions

**Nothing found that does this directly.** Extensive searching ("macro
synthesis," "learning syntactic abstractions," "syntax-rules synthesis",
"anti-unification macros," "macro discovery/mining," "learning hygienic
macros") turned up no work that runs a stitch/DreamCoder-style
corpus-compression search over a *space of syntax-rules-like rewrite rules*
to invent new macros. This looks like a genuinely unoccupied problem
statement. The closest neighbors are (a) resugaring, which inverts *known*
sugar, and (b) library learning over functional/lambda-calculus DSLs
(stitch, babble, DreamCoder), which learns reusable *functions*, not
syntactic rewrite rules with binding pattern variables.

**Resugaring** (Pombrio & Krishnamurthi and coauthors) is the closest
neighbor in spirit:

- Justin Pombrio and Shriram Krishnamurthi, "Resugaring: Lifting Evaluation
  Sequences through Syntactic Sugar," PLDI 2014. Given a *user-supplied*
  desugaring (a set of macro-like rewrite rules from surface to core), it
  reflects the core language's evaluation steps back into surface syntax, so
  a stepper/debugger shows reduction in terms of the sugar the programmer
  wrote, without modifying the evaluator.
- Pombrio & Krishnamurthi, "Hygienic Resugaring of Compositional
  Desugaring," ICFP 2015. Extends the above to handle hygiene and
  near-arbitrary (compositional) rewriting rules, rather than a restricted
  pattern class.
- Pombrio, Krishnamurthi, and Mitchell Wand, "Inferring Scope through
  Syntactic Sugar," ICFP 2017 (PACMPL). Given the desugaring rules and the
  core language's *scoping* rules, it lifts/infers the surface language's
  scoping rules -- i.e., it infers a derived property (scope) from a known
  transformation, not the transformation itself.
- Pombrio & Krishnamurthi, "Inferring Type Rules for Syntactic Sugar,"
  PLDI 2018 -- same pattern, inferring type rules for the surface language
  from known desugaring + core type rules.
- Sorawee Porncharoenwase, "An Inside-Out Resugaring System" (Brown CS
  undergrad honors thesis, 2018), extends resugaring to inside-out
  desugaring orders and permits matched terms to be duplicated in the
  expansion, which prior resugaring work forbade.
- Justin Pombrio's PhD dissertation, "Lifting Languages through Syntactic
  Sugar," Brown University, collects this line.

**How this differs from our project:** in every resugaring paper, *the
desugaring rule (the macro) is given as input*; the machinery only ever
inverts or lifts properties through an already-known transformation. There
is no search over a space of candidate sugar definitions, no corpus to
compress, and no objective trading off rule size against number of uses.
Our project starts from a corpus of *already-expanded* code with the macro
definitions *unknown* -- "reverse-engineer the sugar that must have
existed" rather than "given the sugar, explain evaluation through it."
Resugaring's hygiene treatment (ICFP 2015) is nonetheless relevant prior
art for what a hygiene-respecting rewrite-rule formalism looks like.

## 2. Inverting macro expansion / decompiling expanded code

- Christopher Schuster, Tim Disney, and Cormac Flanagan, "Macrofication:
  Refactoring by Reverse Macro Expansion," ESOP 2016. For a *given,
  already-written* pattern-template macro, derives a refactoring procedure
  that scans a codebase for expanded fragments matching the macro's
  template and offers to replace them with the macro invocation.
  Implemented for a hygienic macro system in JavaScript (sweet.js-style).
- This is the single most directly relevant "unexpansion" paper, and it
  draws the sharpest contrast with our problem: Macrofication matches
  against **one specific, known** macro definition -- it detects *uses* of
  a known macro. It never infers what the macro definition should be, and
  does not search a corpus to discover which abstraction would be most
  compressive. That inversion -- from "here is the macro, find its uses"
  to "here is a corpus with no known macros, invent one" -- is exactly the
  gap this project sits in.
- Nothing else surfaced on inverting macro expansion for debugger or
  error-message purposes beyond the resugaring line (which handles
  *evaluation steps*, not static decompilation of expanded terms).

## 3. Synthesis/compression work that must respect binding when abstracting

- stitch (Bowers et al., POPL 2023): lambda-calculus DSL; abstraction =
  closing a term into a function; no pattern variable ever stands in binder
  position, and no hygiene-of-the-rule condition exists, since the invented
  thing is a function, not a transformer.
- babble (Cao et al., POPL 2023): e-graph anti-unification for corpus
  compression. Its recent line adopts **slotted e-graphs**, making bound
  variables first-class so alpha-equivalent subterms with different names
  are shared and anti-unified correctly -- directly relevant precedent for
  "binders inside a library-learning anti-unification loop," but still
  learning ordinary functional abstractions.
- DreamCoder (Ellis et al., PLDI 2021): de Bruijn representation;
  abstraction discovery reduces to lambda-abstraction, sidestepping hygiene
  by construction.
- No work found where the learned rule's *own correctness condition is a
  hygiene condition*. This appears to be the actual novel technical crux:
  none of stitch, babble, or DreamCoder need to check that the thing they
  invented is hygienic, because they never invent syntax transformers.

## 4. Anti-unification modulo alpha / higher-order anti-unification

Well developed; plausible formal grounding for "matching a template =
anti-unifying sites," though none of it targets macros or hygiene:

- Baumgartner & Kutsia (with Levy, Villaret), "Higher-Order Pattern
  Anti-Unification in Linear Time" (J. Automated Reasoning 2017; RTA 2013
  variant): unique least-general generalization modulo alpha for Miller's
  pattern fragment.
- **Nominal anti-unification** (Baumgartner, Kutsia et al., RTA 2015; 2025
  arXiv follow-ups incl. modulo equational theories): nominal-logic
  techniques -- explicit atoms for bound names, freshness constraints,
  permutations -- computing least-general generalizations unique modulo
  alpha when the atom set is finite. The nominal framing (atoms vs.
  substitutable variables, freshness constraints) maps naturally onto
  "template binders vs. pattern variables" and is probably the best formal
  vocabulary to borrow for grounding un-transcription.
- Baumgartner & Kutsia, "Generalization of Variadic Structures with
  Binders" (arXiv 2025): nominal binder-aware generalization for variadic
  (hedge) structures with a parametrizable rigidity function -- close to
  what anti-unifying realistic variadic forms while respecting binders
  needs; targets clone detection, not rule synthesis.
- Cerna & Kutsia, "Anti-Unification and Generalization: A Survey," IJCAI
  2023 -- entry point for the area.
- Cerna & Buran, "One or Nothing: Anti-unification over the Simply-Typed
  Lambda Calculus" (TOCL 2024): once free variables may nest inside one
  another's arguments, STLC anti-unification becomes *nullary* -- no finite
  complete set of generalizations. Cautionary: over-aggressive
  generalization over nested binder structure may have no well-defined
  "best generalization"; the search space may need restriction (as stitch
  restricts its DSL) to retain unitarity.

## 5. Rewrite-rule inference from before/after pairs

Several efforts synthesize rewrite rules from example transformations
(RuleFlow/RULEGEN 2026; transformation-by-demonstration; SMT-synthesized
instruction-selection rules, arXiv 2405.06127; PACMPL 2021 "Deriving
Efficient Program Transformations from Rewrite Rules"; self-supervised
equivalence learning, arXiv 2109.10476). None deal with variable-binding
rules or hygiene -- the before/after-to-rule literature is uniformly
first-order, which is exactly the gap the syntax-rules setting opens.

## Explicit negatives

- No corpus/compression-driven *discovery* of new macros or
  syntax-rules-style rules.
- No reverse-engineering of an *unknown* macro definition from expanded
  output (vs. Macrofication's known-macro use-detection).
- No anti-unification with an explicit, checked *hygiene* condition on the
  resulting rule (hygiene of a fixed expander is well studied separately:
  Herman & Wand; Adams; the Ballantyne/Rosenblatt pearl this project
  builds on).
- No hits combining "hygiene" with "library learning" or with
  stitch/babble/DreamCoder by name.

## Assessment

Two mature, disjoint traditions bracket this project without covering it:
(1) resugaring, which handles hygienic surface-syntax rewrite rules
formally but always takes the rule as *given*; and (2) library learning,
which searches a corpus to invent abstractions but only ever invents
functions, never syntactic rules, so never needs a hygiene condition on
what it invents. "Stitch-for-syntax-rules" sits at the crossing --
search-driven discovery of the rule, in a rule language (syntax-rules with
pattern variables in binder position) whose correctness condition is
hygiene -- and nothing found occupies that intersection. The nearest
"someone almost did this" is Macrofication (ESOP 2016): macro expansion run
in reverse over real code, but strictly for a known definition.

**Recommended close reads:** (1) Pombrio & Krishnamurthi ICFP 2015
(hygienic resugaring) -- how they formalize hygienic rewrite rules and what
invariants they check; (2) the nominal anti-unification line (RTA 2015 plus
the 2025 variadic-with-binders paper) -- a ready-made formal vocabulary
(atoms vs. pattern variables, freshness, lgg modulo alpha) that could
ground un-transcription non-operationally, complementing the operational
hygiene-by-expansion check.
