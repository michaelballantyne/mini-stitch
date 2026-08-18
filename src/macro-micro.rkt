#lang racket

;; ---------------------------------------------------------------------------
;; macro-micro.rkt --- learning hygienic syntax-rules macros, slowly and plainly
;; ---------------------------------------------------------------------------
;;
;; micro.rkt learns the function that compresses a corpus of lambda-calculus
;; programs the most.  This module asks the same question about *syntactic*
;; abstractions: which single hygienic syntax-rules macro
;;
;;     (define-syntax m (syntax-rules () [(_ x1 ... xk) template]))
;;
;; compresses a corpus of s-expression programs the most, where "using" the
;; macro means replacing a subexpression by a call (m e1 ... ek) that would
;; EXPAND BACK to it?  Design: notes/2026-08-18-0323-syntax-rules-learning-
;; design.md.  This file started as the smallest version that note admits:
;; expressions only, one rule, flat patterns, no ellipses; binder positions
;; hold either an anonymous template binder or a pattern variable (the note's
;; V2, notes/2026-08-18-0323-syntax-rules-learning-design.md section 5 "V1 vs
;; V2"); no optimizations of any kind.  It now also admits stage 2: ELLIPSES,
;; designed in notes/2026-08-18-1324-ellipses-design.md -- abstraction over
;; arity, "the real prize" that note's section 0 names.
;;
;; THE ONE-ELLIPSIS-PER-TEMPLATE AMENDMENT
;;
;; The design note (section 2) allows at most one ellip per FORM and numbers
;; its depth-1 pattern variable as the highest pvar index, forced last by
;; construction -- workable, but it makes every piece of pvar-numbering code
;; reason about an exception ("the last index might be special").  The
;; session lead amended this before implementation: at most one ellipsis per
;; TEMPLATE (not merely per form), and its depth-1 pattern variable is a
;; DISTINCT NODE KIND -- (svar), a nullary struct -- never a numbered pvar at
;; all.  This dissolves the numbering complication rather than working around
;; it: pvars stay exactly what they were pre-ellipses (0..arity-1, ordinary
;; per-call parameters), and the sequence variable is simply never one of
;; them.  The consequence advertised in the amendment and realized below is
;; that sequence arguments become ORDINARY TRAILING ENTRIES in the same
;; (path . subterm) argument list every pre-ellipsis consumer already walks --
;; site-valid?'s call-building, the rewriter's recursion, the DP's cost sum,
;; and macro-utility all needed no changes at all, only doc-comment updates.
;;
;; DATA DEFINITIONS, ellipses
;;
;;   (ellip sub)  an element standing ONLY as the LAST element of a plain
;;                (non-binding) form template, meaning `sub ...`: sub is
;;                transcribed once per matched site element and spliced in.
;;   (svar)       the sequence variable, occurring ONLY inside an ellip's
;;                sub, one or more times; at least one occurrence is required
;;                for the template to be FINISHED (it is what controls the
;;                iteration count -- nothing else could).  Depth-0 (pvar i)
;;                and (tvar j) references are also legal inside an ellip's
;;                sub (repeated per iteration, freshened per iteration,
;;                respectively) -- ellip does not create a new sublanguage,
;;                it only adds one production directly usable in sub's holes.
;;
;; Restrictions kept from the design note's section 2 (their reasons there
;; still apply verbatim): plain forms only (lambda/let have fixed shapes,
;; nothing variadic to abstract); trailing position only; and -- now framed
;; as "per template" rather than "per form, forced-last-index" -- exactly one
;; ellip, so the learned PATTERN is always the flat prefix plus at most one
;; trailing `xs ...`, never more.
;;
;; WHAT REPLACES BETA
;;
;; micro.rkt's rewrite is justified by beta-reduction: (fn a1 .. ak) reduces to
;; the subterm it replaced.  Here the justification is hygienic expansion, and
;; the correctness criterion is the note's:
;;
;;     expanding the rewritten program, with the macro defined, yields a
;;     program alpha-equivalent to the expansion of the original.
;;
;; Where micro refuses to predict what the rewriter will save and instead runs
;; it, this module refuses to predict what the expander will do and instead
;; runs it -- expander.rkt, the model expander from "Hygienic macro expansion
;; explained", is called on every candidate rewrite (`site-valid?` below).
;; None of the note's hygiene side conditions H1-H4 are implemented anywhere
;; in this file; they are consequences the oracle enforces:
;;
;;   H1  an argument may not reference a template-introduced binder
;;       (the expander freshens template binders, so the reference dangles
;;        and the outputs differ);
;;   H2  a free identifier in the template must resolve at the site exactly
;;       as it resolves at the macro's definition site -- in this module's
;;       one-global-scope corpora, it must not be locally shadowed;
;;   H3  template binder names are irrelevant (the site's choice of name is
;;       absorbed by alpha-comparison of the expansions);
;;   H4  two uses of one pattern variable must receive alpha-equivalent
;;       arguments with identical free references.
;;
;; The structural matcher below (`skeleton-match`) is correspondingly sloppy on
;; purpose: it settles shape and reads off the arguments, and is never trusted
;; about hygiene.  It is a sound over-approximation, used to prune.
;;
;; THE OBJECT LANGUAGE
;;
;; Corpus programs are expressions of expander.rkt's language:
;;
;;   e ::= symbol                      a variable or global reference
;;       | number | boolean            a literal constant
;;       | (lambda (x) e)              one binder, one body form
;;       | (let ([x e]) e)             one binding, one body form
;;       | (e1 e2 ...)                 any other form: an application, an
;;                                     (if e1 e2 e3), a primitive call, ...
;;
;; Only lambda and let BIND; every other form is a plain list whose elements
;; are all expressions -- `if` and primitive applications need no cases of
;; their own anywhere in this file, and their heads are ordinary free
;; identifiers a template may mention.  Corpora are assumed well-formed and to
;; not shadow the names `lambda` and `let` (the oracle would still be right if
;; they did; the position-walkers here would misread the program's shape).
;;
;; DATA DEFINITIONS
;;
;; A Template is a partial macro body: an expression extended with
;;   'hole        an unfilled ??
;;   (pvar i)     pattern variable #i -- a parameter, filled at each use site
;;   (tvar j)     template binder j -- a binder the MACRO introduces.  These
;;                are anonymous (hygiene renames them at every expansion, so a
;;                name would be information the semantics ignores); they get
;;                names only when the template is rendered as syntax-rules.
;; (tvar j) appears in binder positions and, as a reference, in expression
;; positions; 'hole appears in expression positions only.  (pvar i) appears
;; in expression positions AND, as of V2, in binder positions: there the
;; macro user supplies the binder's NAME as pattern variable #i's argument,
;; so a use-site binder introduced by the call can hygienically capture
;; use-site references passed as other arguments -- exactly the sites H1
;; blocks a template-binder-only (V1) template from reaching.
;;
;; A Path is a list of element indices from a form's root down into it: in
;; (lambda (x) body), body is at (2); in (let ([x rhs]) body), rhs is at
;; (1 0 1) and body at (2); in any other form, element i is at (i).
;;
;; An MDef is (mdef Symbol Natural Template): a learned macro's name, arity,
;; and finished template.  A list of MDefs is a library; expanding a program
;; "under" a library wraps it in one let-syntax per macro.
;;
;; A Cost is an integer: 100 per atom (symbols, numbers, booleans, and the
;; identifiers a tvar will become), 1 per parenthesized form, 0 per pvar --
;; parameters are not structure.  An (ellip sub) element costs 100 (the
;; rendered `...` is an atom of the macro's source) plus sub's own cost; a
;; (svar) costs 0, same reasoning as a pvar -- it too is a parameter, never
;; structure.  The macro itself is charged for its
;; TEMPLATE only, mirroring stitch exactly: stitch's structure penalty is the
;; invention body at cost_{alpha=0} (ivars hardcoded to 0 in expansion.rs's
;; local_expansion_utility, whatever the inert cost_ivar config says), and
;; neither the invention's binder prefix nor its library entry costs
;; anything.  The pattern (m x1 ... xk) is the binder prefix's analog, so it
;; is likewise free; arity is paid only where stitch pays it, at each call.
;; ---------------------------------------------------------------------------

(require (only-in "expander.rkt" expand))

(provide (struct-out pvar) (struct-out tvar) (struct-out ellip) (struct-out svar)
         (struct-out mdef)
         (struct-out learned)
         sexpr-cost corpus-cost template-arity macro-cost
         mdef-syntax-rules wrap-with-library expand-under
         alpha=? expr-positions skeleton-match valid-sites
         rewrite-corpus macro-utility fresh-name
         macro-search macro-compress)

(module+ test (require rackunit))

(struct pvar (i) #:transparent)
(struct tvar (j) #:transparent)
;; ellip and svar are stage 2's addition -- see the module header below for
;; the amendment that shapes them (one ellipsis per TEMPLATE, its sequence
;; variable a distinct node kind rather than a numbered pvar).
(struct ellip (sub) #:transparent)
(struct svar () #:transparent)
(struct mdef (name arity template) #:transparent)

;; ---------------------------------------------------------------------------
;; Shapes, positions and costs
;; ---------------------------------------------------------------------------

;; lambda-form?, let-form? : Any -> Boolean
;; The two binding shapes of the object language.  They are also the template
;; shapes, with a tvar in the binder position; both readings are used below.
(define (lambda-form? t)
  (match t [`(lambda (,_) ,_) #t] [_ #f]))
(define (let-form? t)
  (match t [`(let ([,_ ,_]) ,_) #t] [_ #f]))

;; expr-children : Sexpr -> (Listof (cons Path Sexpr))
;; The immediate subexpressions of an expression, each with its path.  For
;; lambda and let this IS the binding spec: only the expression parts are
;; contributed, never the binder position.  Any other form contributes every
;; element (its head too -- a head is an expression, and `(if ...)`'s head is
;; where templates learn to say `if`) -- INCLUDING a learned macro's call
;; `(m1 e1 ... ek)`.  That is honest about lambda and let, but not the whole
;; story once a library is in play: a learned macro's own binder-position
;; arguments (which of #0..#(k-1) are binders is recorded in its mdef, per
;; V2) are NOT in the spec this function reads, so they are walked here as
;; plain expressions.  A corpus program like `(m0 x (g x))`, where m0's #0 is
;; a binder, has its `x` at position (1) mis-read as an expression position,
;; and its spelling enters corpus-facts' identifier list like any other free
;; reference.  This is harmless today for two reasons that have nothing to do
;; with this function being right: the oracle (site-valid?) refuses any
;; rewrite whose skeleton match got a binder wrong, and a bare-symbol
;; template can never out-cost the site it would replace.  Design note
;; section 7 flags the proper fix: an mdef binder mask, something that lets
;; this function (and corpus-facts) walk a learned macro's call correctly
;; instead of leaning on the oracle to catch a wrong walk after the fact.
;; Everything that walks programs walks through here.
(define (expr-children t)
  (cond [(lambda-form? t) (list (cons '(2) (caddr t)))]
        [(let-form? t) (list (cons '(1 0 1) (cadr (caadr t)))
                             (cons '(2) (caddr t)))]
        [(list? t) (for/list ([e (in-list t)] [i (in-naturals)])
                     (cons (list i) e))]
        [else '()]))

;; subterm-at : Sexpr Path -> Sexpr
(define (subterm-at t path)
  (if (null? path) t (subterm-at (list-ref t (car path)) (cdr path))))

;; replace-at : Sexpr Path Sexpr -> Sexpr
(define (replace-at t path new)
  (if (null? path)
      new
      (for/list ([e (in-list t)] [i (in-naturals)])
        (if (= i (car path)) (replace-at e (cdr path) new) e))))

;; expr-positions : Sexpr -> (Listof (cons Path Sexpr))
;; Every expression position of a program, the whole program first.  These are
;; the places a macro call could stand.
(define (expr-positions t)
  (let walk ([t t] [path '()])
    (cons (cons path t)
          (append* (for/list ([c (in-list (expr-children t))])
                     (walk (cdr c) (append path (car c))))))))

;; sexpr-cost : (U Sexpr Template) -> Cost
;; What a piece of syntax costs.  One function serves programs, arguments and
;; templates: a pvar is a parameter and costs nothing, a tvar will be an
;; identifier in the rendered macro and costs like one; likewise (stage 2) a
;; svar is a parameter and costs nothing, and an ellip costs its rendered
;; `...` (100, an atom) plus whatever its sub costs -- ellip only ever
;; appears as a LIST ELEMENT (never as the t passed in directly), which is
;; exactly where the list case below calls sexpr-cost on it.
(define (sexpr-cost t)
  (cond [(pvar? t) 0]
        [(tvar? t) 100]
        [(svar? t) 0]
        [(ellip? t) (+ 100 (sexpr-cost (ellip-sub t)))]
        [(list? t) (+ 1 (for/sum ([e (in-list t)]) (sexpr-cost e)))]
        [else 100]))

;; corpus-cost : (Listof Sexpr) -> Cost
(define (corpus-cost programs)
  (for/sum ([p (in-list programs)]) (sexpr-cost p)))

(module+ test
  (test-case "shapes, positions, costs"
    (define P '(lambda (x) (f x 1)))
    (check-equal? (sexpr-cost P) 503)
    ;; (lambda (x) (f x 1)) is 3 forms (the lambda, the binder list, the
    ;; call) and 5 atoms (lambda x f x 1): 3 + 500 = 503
    (check-equal? (subterm-at P '(2 0)) 'f)
    (check-equal? (replace-at P '(2) 'y) '(lambda (x) y))
    ;; positions: the program, its body, and the body's three elements --
    ;; the binder list and the binder are NOT expression positions
    (check-equal? (map car (expr-positions P))
                  '(() (2) (2 0) (2 1) (2 2)))
    ;; let has two subexpressions: the right-hand side and the body
    (check-equal? (map car (expr-positions '(let ([x 1]) x)))
                  '(() (1 0 1) (2)))
    ;; an if is a plain form; all four elements are expression positions
    (check-equal? (length (expr-positions '(if a b c))) 5)))

;; ---------------------------------------------------------------------------
;; Templates
;; ---------------------------------------------------------------------------

;; template-arity : Template -> Natural
;; Pattern variables are numbered 0, 1, ... in the order the search introduced
;; them, so the largest index plus one is the count.  A pvar can stand inside
;; an ellip's sub too (a depth-0 reference, repeated per iteration), so this
;; walks into sub; svar itself contributes no pvar index.
(define (template-arity t)
  (cond [(pvar? t) (add1 (pvar-i t))]
        [(ellip? t) (template-arity (ellip-sub t))]
        [(list? t) (apply max 0 (map template-arity t))]
        [else 0]))

;; template-tvars : Template -> Natural
;; How many template binders exist so far (they are numbered like pvars).
;; Walks into an ellip's sub for the same reason as template-arity.
(define (template-tvars t)
  (cond [(tvar? t) (add1 (tvar-j t))]
        [(ellip? t) (template-tvars (ellip-sub t))]
        [(list? t) (apply max 0 (map template-tvars t))]
        [else 0]))

;; template-has-ellip? : Template -> Boolean
;; Does this template already contain its one allowed ellip anywhere?  Used
;; both to render the macro's pattern (mdef-syntax-rules) and to keep the
;; enumerator from ever proposing a second one (see `expansions` below).
(define (template-has-ellip? t)
  (cond [(ellip? t) #t]
        [(list? t) (ormap template-has-ellip? t)]
        [else #f]))

;; template-has-svar? : Template -> Boolean
;; Does this (sub-)template already contain a sequence variable anywhere?
;; Used to decide whether an ellip is finished, and whether the enumerator
;; should still offer (svar) inside a given ellip's sub.
(define (template-has-svar? t)
  (cond [(svar? t) #t]
        [(ellip? t) (template-has-svar? (ellip-sub t))]
        [(list? t) (ormap template-has-svar? t)]
        [else #f]))

;; template-ellipses-ok? : Template -> Boolean
;; True unless some ellip in the template has a sub with no (svar) inside it
;; -- the note's "nothing controls the iteration" condition.  Checked here,
;; at the enumerator's finished? gate, so the expander's own error for
;; exactly this malformed case is never triggered by a template this search
;; hands it (the design note's "errors kept honest" policy: the enumerator
;; asserts, the expander still errors, but on candidates the enumerator was
;; never supposed to produce).
(define (template-ellipses-ok? t)
  (cond [(ellip? t) (and (template-has-svar? (ellip-sub t))
                         (template-ellipses-ok? (ellip-sub t)))]
        [(list? t) (andmap template-ellipses-ok? t)]
        [else #t]))

;; hole-scope : Template -> (U (Listof Natural) #f)
;; The template binders in scope at the leftmost hole -- what a reference
;; production may name there -- or #f if the template is finished.  A let's
;; right-hand side does not see the let's own binder, matching the expander.
;; An ellip introduces no binder of its own, so scope passes through its sub
;; unchanged -- it is walked into purely so a hole there is still found.
(define (hole-scope tpl)
  ;; binder-scope : Sexpr (Listof Natural) -> (Listof Natural)
  ;; A binder-position tvar extends the tvar scope; a binder-position pvar
  ;; extends nothing -- references to it are written as that same pvar in
  ;; expression position, an existing production.
  (define (binder-scope binder scope)
    (if (tvar? binder) (cons (tvar-j binder) scope) scope))
  (let/ec found
    (let walk ([t tpl] [scope '()])
      (cond [(eq? t 'hole) (found scope)]
            [(lambda-form? t)
             (walk (caddr t) (binder-scope (car (cadr t)) scope))]
            [(let-form? t)
             (walk (cadr (caadr t)) scope)
             (walk (caddr t) (binder-scope (car (caadr t)) scope))]
            [(ellip? t) (walk (ellip-sub t) scope)]
            [(list? t) (for ([e (in-list t)]) (walk e scope))]
            [else (void)]))
    #f))

;; hole-ellip-scope : Template -> (U #f (cons Boolean Boolean))
;; A SIBLING of hole-scope (design note section 4, as amended): what an
;; ellip-aware production at the leftmost hole needs to know, that the tvar
;; scope does not capture.  #f exactly when hole-scope is #f (the template is
;; finished); otherwise (cons in-ellip? has-svar?) where in-ellip? says
;; whether the leftmost hole sits inside some ellip's sub, and has-svar? --
;; meaningful only when in-ellip? is true -- says whether that ellip's sub
;; already contains an (svar) somewhere (before or after the hole; existence
;; is all that matters).  `expansions` uses in-ellip? to withhold binder-form
;; and nested-ellip productions and has-svar? to withhold a second (svar)
;; production once the first is placed.  Kept as a separate walk rather than
;; folded into hole-scope's return so hole-scope's existing contract (and
;; every pre-ellipses caller and test of it) is untouched.
(define (hole-ellip-scope tpl)
  (let/ec found
    (let walk ([t tpl] [in-ellip? #f] [has-svar? #f])
      (cond [(eq? t 'hole) (found (cons in-ellip? has-svar?))]
            [(lambda-form? t) (walk (caddr t) in-ellip? has-svar?)]
            [(let-form? t)
             (walk (cadr (caadr t)) in-ellip? has-svar?)
             (walk (caddr t) in-ellip? has-svar?)]
            [(ellip? t)
             (walk (ellip-sub t) #t (template-has-svar? (ellip-sub t)))]
            [(list? t) (for ([e (in-list t)]) (walk e in-ellip? has-svar?))]
            [else (void)]))
    #f))

;; finished? : Template -> Boolean
;; No hole left AND every ellip's sub has something controlling its
;; iteration (template-ellipses-ok?) -- both conditions the note requires of
;; a candidate before it may reach the oracle.
(define (finished? tpl)
  (and (not (hole-scope tpl)) (template-ellipses-ok? tpl)))

;; fill-hole : Template Template -> Template
;; Replace the leftmost hole by `piece`.  Purely structural: binder positions
;; hold tvars, never holes, so a plain left-to-right walk is safe.  An ellip
;; is not itself a list (it is a one-field struct), so it needs its own case
;; to be walked into; the result re-wraps a filled sub back in `ellip`.
(define (fill-hole tpl piece)
  (define (walk t)
    (cond
      [(eq? t 'hole) (values piece #t)]
      [(ellip? t)
       (define-values (e filled?) (walk (ellip-sub t)))
       (values (if filled? (ellip e) t) filled?)]
      [(list? t)
       (let loop ([done '()] [rest t])
         (cond [(null? rest) (values (reverse done) #f)]
               [else
                (define-values (e filled?) (walk (car rest)))
                (if filled?
                    (values (append (reverse done) (cons e (cdr rest))) #t)
                    (loop (cons e done) (cdr rest)))]))]
      [else (values t #f)]))
  (define-values (out filled?) (walk tpl))
  (unless filled? (error 'fill-hole "no hole in ~a" tpl))
  out)

;; pvar-name, tvar-name : Natural -> Symbol
;; The spellings used when a template is rendered as syntax-rules.  The %
;; prefix keeps them out of the corpus's namespace: transcription substitutes
;; pattern variables by NAME, so a pattern variable spelled like a template
;; free identifier would swallow it.  (Corpora are checked for %-free names.)
(define (pvar-name i) (string->symbol (format "%x~a" i)))
(define (tvar-name j) (string->symbol (format "%t~a" j)))
;; svar-name : Symbol
;; There is at most one svar per template, so unlike pvar/tvar it needs no
;; index -- one reserved spelling suffices.  Still inside the %-namespace, so
;; check-corpus's existing %-ban already protects it.
(define svar-name '%xs)

;; render-template : Template -> Sexpr
;; The template as it appears inside the macro definition.  An ellip element
;; renders as TWO spliced elements -- its sub's rendering, then the literal
;; symbol `...` -- so the list case can no longer be a plain `map`; it maps
;; each element to the (one- or two-element) list it contributes and appends
;; the results, splicing an ellip's pair into the enclosing form exactly the
;; way syntax-rules notation itself reads.
(define (render-template t)
  (cond [(pvar? t) (pvar-name (pvar-i t))]
        [(tvar? t) (tvar-name (tvar-j t))]
        [(svar? t) svar-name]
        [(list? t)
         (append-map (lambda (e)
                       (if (ellip? e)
                           (list (render-template (ellip-sub e)) '...)
                           (list (render-template e))))
                     t)]
        [else t]))

;; mdef-syntax-rules : MDef -> Sexpr
;; The whole macro transformer, ready for let-syntax.  When the template
;; contains an ellip, the learned pattern gains a trailing `%xs ...` after
;; the flat prefix -- the one place the macro's ARITY (a count of pvars) and
;; its pattern's shape now diverge, exactly the divergence
;; template-has-ellip? exists to detect.
(define (mdef-syntax-rules m)
  (define fixed-pat (for/list ([i (in-range (mdef-arity m))]) (pvar-name i)))
  (define pat (if (template-has-ellip? (mdef-template m))
                  (append fixed-pat (list svar-name '...))
                  fixed-pat))
  `(syntax-rules ()
     [(_ ,@pat)
      ,(render-template (mdef-template m))]))

;; macro-cost : Template -> Cost
;; What the library pays to carry the macro: its template, with pattern
;; variables free.  The flat pattern (m x1 ... xk) costs nothing, just as
;; stitch charges nothing for an invention's binder prefix or its library
;; entry -- a parameter is not structure, wherever it is written down.
(define (macro-cost tpl)
  (sexpr-cost tpl))

(module+ test
  (test-case "templates"
    (define T `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0))))
    (check-equal? (template-arity T) 1)
    (check-equal? (template-tvars T) 1)
    (check-true (finished? T))
    (check-equal? (render-template T) '(lambda (%t0) (f %t0 %x0)))
    ;; template cost: 3 forms + lambda,f + two tvars = 3 + 400; the pattern
    ;; adds nothing
    (check-equal? (sexpr-cost T) 403)
    (check-equal? (macro-cost T) 403)
    ;; the leftmost hole of (?? (lambda (t0) ??)) is outside the lambda;
    ;; fill it and the next hole sees t0
    (define U `(hole (lambda (,(tvar 0)) hole)))
    (check-equal? (hole-scope U) '())
    (check-equal? (hole-scope (fill-hole U 'g)) '(0))
    ;; a let's right-hand-side hole does not see the let's binder
    (check-equal? (hole-scope `(let ([,(tvar 0) hole]) hole)) '())
    ;; a pvar binder (V2) adds no tvar reference: it is use-site syntax, not
    ;; a template binder, so nothing is in scope beneath it
    (check-equal? (hole-scope `(lambda (,(pvar 0)) hole)) '())
    (check-false (hole-scope T))))

;; ---------------------------------------------------------------------------
;; The skeleton matcher
;; ---------------------------------------------------------------------------

;; skeleton-match : Template Sexpr -> (U #f (Listof (cons Path Sexpr)))
;; Does the template have the shape of this expression, and if so what does
;; each pattern variable -- and (stage 2) each matched ellipsis element --
;; receive?  Returns one (path . argument) per pattern variable, in index
;; order, FOLLOWED BY one (path . argument) per matched ellipsis element, in
;; site order (empty when the template has no ellip, or when it matched zero
;; elements) -- the amendment's "beautiful consequence": a sequence argument
;; is just an ordinary trailing entry in the same list, so every consumer of
;; this return value (the call-builder in site-valid?, the rewriter's
;; recursion, the DP's cost sum) needed no change at all, only this comment.
;; A pvar's path is the FIRST occurrence's; a sequence element's path is the
;; FIRST (svar) occurrence WITHIN THAT ELEMENT's match of the ellip's sub.
;; Deliberately hygiene-blind:
;;   * a tvar in binder position matches whatever name the site binds there,
;;     recording nothing;
;;   * a pvar in binder position (V2) is matched by the SAME first-occurrence
;;     rule as a pvar in expression position, taking the site's binder NAME
;;     (a bare symbol, not a subterm) as the argument;
;;   * a tvar in expression position matches any identifier;
;;   * later occurrences of a pattern variable -- in either kind of position
;;     -- match anything at all, WITH ONE EXCEPTION that is shape, not
;;     hygiene: a later occurrence in BINDER position requires the argument
;;     recorded at the first occurrence to be a symbol (a compound argument
;;     can never legally stand as a binder's name, whichever position it was
;;     first read from);
;;   * (stage 2) when a template's last element is (ellip sub), a site plain
;;     form of length >= k-1 (k-1 fixed elements before the ellip) matches:
;;     the prefix positionally as always, then EACH remaining site element
;;     independently against sub (zero remaining elements is a legal match,
;;     contributing no sequence arguments -- syntax-rules agrees, and so does
;;     the expander for zero iterations).  Depth-0 pvars inside sub follow
;;     the SAME global first-occurrence rule as anywhere else in the template
;;     (the `binds` hash persists across elements, unmodified in kind); a
;;     later (svar) occurrence within one element's match matches anything,
;;     exactly like a later pvar occurrence (H4 pointwise remains the
;;     oracle's business, as always) -- but the "later" reset is PER ELEMENT,
;;     since each element gets its own first (svar) sighting;
;; every one of those judgments -- except the shape-only ones (arity/length,
;; and F3's binder-reuse check) -- is deferred to the expansion oracle.  Only
;; shape is settled here -- in particular a binding form only matches a
;; template written with that binding form, holes stand at expression
;; positions and nothing else, and a binder position holding anything but a
;; tvar or a pvar (an ill-formed corpus's doing, never the enumerator's) is
;; simply no match.
(define (skeleton-match tpl t)
  (define arity (template-arity tpl))
  ;; current-svar-box : (Parameterof (U #f (Box (U #f (cons Path Sexpr)))))
  ;; The first-(svar)-in-this-element bookkeeping.  Set (via parameterize) to
  ;; a fresh box around each site element's match against an ellip's sub;
  ;; #f outside any such match (svar never legally occurs there, by
  ;; construction, so this default is never actually consulted).
  (define current-svar-box (make-parameter #f))
  ;; match-binder : Any Symbol Path (HashOf Natural (cons Path Any))
  ;;               -> (U (HashOf Natural (cons Path Any)) #f)
  ;; The binder position's own judgment, parallel to the pvar/tvar cases of
  ;; `walk` below but never reached by it (walk only recurses into a binding
  ;; form's expression parts). Total, unlike the enumerator's own binders
  ;; (which are always tvar or pvar): the CORPUS's binder position can hold
  ;; anything a well-formed program puts there, so this is where an ill-formed
  ;; corpus would otherwise crash on `pvar-i` deep inside a match. A tvar
  ;; binder matches whatever name the site binds there and records nothing
  ;; (H3). A pvar binder is the site's binder NAME, by the identical
  ;; first-occurrence rule as an expression-position pvar: recorded if this is
  ;; the first sighting of that index; on a later sighting, matches only if
  ;; what was recorded the first time was itself a symbol -- a pvar that is
  ;; sometimes an expression-position argument and sometimes a binder can
  ;; never be legally reused as a binder once its first occurrence bound it to
  ;; a compound argument (a binder position is a SHAPE judgment, not merely a
  ;; hygiene one, and it is the skeleton's job to enforce per its own
  ;; docstring). Anything that is neither tvar nor pvar in binder position is
  ;; no match at all -- #f -- rather than a crash.
  (define (match-binder binder-p binder-sym binder-path binds)
    (cond [(tvar? binder-p) binds]
          [(not (pvar? binder-p)) #f]
          [(hash-has-key? binds (pvar-i binder-p))
           (and (symbol? (cdr (hash-ref binds (pvar-i binder-p)))) binds)]
          [else (hash-set binds (pvar-i binder-p) (cons binder-path binder-sym))]))
  (define (walk p t path binds)
    (cond
      [(eq? p 'hole) binds]
      [(pvar? p)
       (if (hash-has-key? binds (pvar-i p))
           binds
           (hash-set binds (pvar-i p) (cons path t)))]
      [(tvar? p) (and (symbol? t) binds)]
      [(svar? p)
       (define b (current-svar-box))
       (unless (unbox b) (set-box! b (cons path t)))
       binds]
      [(lambda-form? p)
       (and (lambda-form? t)
            (let ([binds (match-binder (car (cadr p)) (car (cadr t))
                                       (append path '(1 0)) binds)])
              (and binds
                   (walk (caddr p) (caddr t) (append path '(2)) binds))))]
      [(let-form? p)
       (and (let-form? t)
            (let ([binds (match-binder (car (caadr p)) (car (caadr t))
                                       (append path '(1 0 0)) binds)])
              (and binds
                   (let ([binds (walk (cadr (caadr p)) (cadr (caadr t))
                                      (append path '(1 0 1)) binds)])
                     (and binds
                          (walk (caddr p) (caddr t) (append path '(2)) binds))))))]
      [(and (pair? p) (ellip? (last p)))
       ;; The k-1 fixed elements before the ellip match positionally, exactly
       ;; like the plain list? case below; the ellip's sub then matches each
       ;; remaining site element independently, in order, threading `binds`
       ;; through (so a depth-0 pvar's global first-occurrence rule sees
       ;; every element) and collecting one sequence argument per element
       ;; under the reserved key 'seq-args (a symbol, so it never collides
       ;; with a pvar's natural-number key).
       (and (list? t) (not (lambda-form? t)) (not (let-form? t))
            (let* ([k-1 (sub1 (length p))] [sub (ellip-sub (last p))])
              (and (>= (length t) k-1)
                   (let fixed-loop ([pe (take p k-1)] [te (take t k-1)]
                                     [i 0] [binds binds])
                     (cond
                       [(null? pe)
                        (let elem-loop ([telems (list-tail t k-1)] [idx k-1]
                                         [binds binds] [seq '()])
                          (cond
                            [(null? telems)
                             (hash-set binds 'seq-args (reverse seq))]
                            [else
                             (define b (box #f))
                             (define binds2
                               (parameterize ([current-svar-box b])
                                 (walk sub (car telems)
                                       (append path (list idx)) binds)))
                             (and binds2
                                  (elem-loop (cdr telems) (add1 idx) binds2
                                             (cons (unbox b) seq)))]))]
                       [else
                        (define binds2
                          (walk (car pe) (car te) (append path (list i)) binds))
                        (and binds2
                             (fixed-loop (cdr pe) (cdr te) (add1 i) binds2))])))))]
      [(list? p)
       (and (list? t) (not (lambda-form? t)) (not (let-form? t))
            (= (length p) (length t))
            (for/fold ([binds binds])
                      ([pe (in-list p)] [te (in-list t)] [i (in-naturals)])
              (and binds (walk pe te (append path (list i)) binds))))]
      [else (and (equal? p t) binds)]))
  (define binds (walk tpl t '() (hash)))
  ;; A depth-0 pvar whose ONLY occurrence in the whole template lives inside
  ;; an ellip's sub is a stage-2 possibility the enumerator does not exclude
  ;; (nothing requires a depth-0 pvar production inside sub to be a REUSE of
  ;; one already placed in the fixed prefix): if THIS site's ellip matches
  ;; zero elements, sub is never walked against anything, and that pvar's
  ;; index never enters `binds` at all -- there is no zero-th occurrence to
  ;; fall back on. Rather than let `hash-ref` crash deep in a candidate the
  ;; enumerator was free to propose, treat a site that cannot supply every
  ;; pvar's argument as NO MATCH here: sound (it only narrows which sites
  ;; match, never widens), and consistent with this function's own
  ;; over-approximation philosophy -- the same one `(= (length p) (length
  ;; t))` already uses elsewhere in this function to fail the shape rather
  ;; than guess.
  (and binds
       (for/and ([i (in-range arity)]) (hash-has-key? binds i))
       (append (for/list ([i (in-range arity)]) (hash-ref binds i))
               (hash-ref binds 'seq-args '()))))

(module+ test
  (test-case "skeleton matching"
    (define T `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0))))
    ;; the site's binder name is not the template's business (that is H3,
    ;; which the oracle owns); the argument and its path come back
    (check-equal? (skeleton-match T '(lambda (y) (f y 2)))
                  (list (cons '(2 2) 2)))
    ;; ... and the matcher happily accepts what the oracle will refuse:
    ;; an argument mentioning the bound variable (H1's business)
    (check-equal? (skeleton-match T '(lambda (y) (f y (g y))))
                  (list (cons '(2 2) '(g y))))
    ;; shape is the matcher's business: an application template does not
    ;; match a lambda, nor the other way around
    (check-false (skeleton-match '(hole hole hole) '(lambda (x) x)))
    (check-false (skeleton-match T '(f (lambda (x) x) 2)))
    ;; a later occurrence of a pattern variable matches anything (H4 is the
    ;; oracle's business); the first occurrence is the argument
    (check-equal? (skeleton-match `(g ,(pvar 0) ,(pvar 0)) '(g 1 2))
                  (list (cons '(1) 1)))
    ;; V2: a pvar in binder position takes the site's binder NAME as its
    ;; argument -- the first-occurrence rule applies there too, so the later
    ;; reference in the body records nothing
    (define T2 `(lambda (,(pvar 0)) (f ,(pvar 0) ,(pvar 1))))
    (check-equal? (skeleton-match T2 '(lambda (x) (f x (g x))))
                  (list (cons '(1 0) 'x) (cons '(2 2) '(g x))))
    ;; ... and the matcher still doesn't check consistency of later
    ;; occurrences (H4 again is the oracle's business): the body's reference
    ;; to #0 need not even be spelled the same as the binder it names
    (check-equal? (skeleton-match T2 '(lambda (x) (f y (g x))))
                  (list (cons '(1 0) 'x) (cons '(2 2) '(g x))))
    ;; F1: a hand-built template with a raw symbol in binder position is not
    ;; something the enumerator ever produces (it only ever puts a tvar or a
    ;; pvar there), but match-binder must still be total rather than crash
    ;; deep inside pvar-i's struct-field contract -- it is simply no match
    ;; ('bogus is neither tvar nor pvar)
    (check-false (skeleton-match '(lambda (bogus) 1) '(lambda (x) 1)))
    ;; F3: a pvar recorded once as a COMPOUND expression-position argument
    ;; can never afterward be reused as a binder -- the second occurrence's
    ;; shape judgment fails cleanly instead of transcription later splicing
    ;; a compound term into a binder list
    (define T3 `(f ,(pvar 0) (lambda (,(pvar 0)) 1)))
    (check-false (skeleton-match T3 '(f (g 1) (lambda (x) 1))))
    ;; ... while a symbol recorded first is fine to reuse as a binder
    (check-equal? (skeleton-match T3 '(f w (lambda (x) 1)))
                  (list (cons '(1) 'w)))))

;; ---------------------------------------------------------------------------
;; The oracle: does this rewrite expand back?
;; ---------------------------------------------------------------------------

;; wrap-with-library : (Listof MDef) Sexpr -> Sexpr
;; The program with every learned macro in scope, earliest outermost.
(define (wrap-with-library library prog)
  (for/fold ([e prog]) ([m (in-list (reverse library))])
    `(let-syntax ([,(mdef-name m) ,(mdef-syntax-rules m)]) ,e)))

;; expand-under : (Listof MDef) Sexpr -> Sexpr
;; The program's meaning: its hygienic expansion under the library.
(define (expand-under library prog)
  (expand (wrap-with-library library prog)))

;; alpha=? : Sexpr Sexpr -> Boolean
;; Alpha-equivalence of two EXPANDED programs.  The expander has already
;; resolved everything -- each binder came out with a fresh identity, each
;; global as its bare symbol -- so this is ordinary alpha-comparison of the
;; output language: corresponding binders may differ, and everything else
;; must agree.  `env` maps left binders to right binders, innermost first;
;; a symbol pair must be related by the innermost entry that mentions either
;; of them, or by being the very same free symbol.
(define (alpha=? a b)
  (let walk ([a a] [b b] [env '()])
    (match* (a b)
      [(`(lambda (,(? symbol? x)) ,ab) `(lambda (,(? symbol? y)) ,bb))
       (walk ab bb (cons (cons x y) env))]
      [(`(let ([,(? symbol? x) ,ae]) ,ab) `(let ([,(? symbol? y) ,be]) ,bb))
       (and (walk ae be env)
            (walk ab bb (cons (cons x y) env)))]
      [((? list?) (? list?))
       (and (= (length a) (length b))
            (for/and ([ea (in-list a)] [eb (in-list b)])
              (walk ea eb env)))]
      [((? symbol?) (? symbol?))
       (let loop ([env env])
         (cond [(null? env) (eq? a b)]
               [(or (eq? (caar env) a) (eq? (cdar env) b))
                (and (eq? (caar env) a) (eq? (cdar env) b))]
               [else (loop (cdr env))]))]
      [(_ _) (equal? a b)])))

(module+ test
  (test-case "alpha-equivalence of expanded programs"
    (check-true (alpha=? '(lambda (x.1) (f x.1 1)) '(lambda (y.1) (f y.1 1))))
    (check-false (alpha=? '(lambda (x.1) (f x.1 1)) '(lambda (y.1) (f y.2 1))))
    ;; shadowing: innermost correspondence wins
    (check-true (alpha=? '(lambda (x) (lambda (x) x))
                         '(lambda (a) (lambda (b) b))))
    (check-false (alpha=? '(lambda (x) (lambda (x) x))
                          '(lambda (a) (lambda (b) a))))
    ;; free symbols must be identical, not just consistently renamed
    (check-false (alpha=? '(f 1) '(g 1)))
    (check-true (alpha=? '(let ([x 1]) x) '(let ([y 1]) y)))))

;; site-valid? : (Listof MDef) Symbol Template Sexpr Sexpr Path
;;               (Listof (cons Path Sexpr)) -> Boolean
;; The oracle itself.  Splice the call (name arg1 ... argk) over the subterm
;; at `path`, expand the whole program with the candidate macro added to the
;; library, and ask whether it still means what it meant.  A rewrite that
;; makes expansion crash (however it manages to) certainly changed the
;; meaning, so errors count as no -- but only USER-LEVEL expansion errors:
;; expander.rkt's own `error` calls for "no pattern matched", "name already
;; bound", and transcribe's depth mismatches are the expander correctly
;; reporting that this splice does not make sense at this site, which is
;; exactly a no. Those are plain exn:fail?, never exn:fail:contract?. A
;; contract violation escaping from this call graph (for instance, the one
;; F1/F3 fixed: skeleton-match recording a compound argument where
;; transcription then expects a binder-list symbol) is a BUG in this module
;; or in expander.rkt, not a hygiene verdict, and must not be silently read
;; as "no match" -- so it is excluded from the handler and left to propagate,
;; where it belongs, as the crash it is.
(define (site-valid? library name tpl prog expanded path args)
  (define call (cons name (map cdr args)))
  (define library+ (append library (list (mdef name (template-arity tpl) tpl))))
  (with-handlers ([(lambda (e) (and (exn:fail? e) (not (exn:fail:contract? e))))
                   (lambda (_) #f)])
    (alpha=? (expand-under library+ (replace-at prog path call))
             expanded)))

;; valid-sites : (Listof MDef) Symbol Template Sexpr Sexpr
;;               -> (HashOf Path (Listof (cons Path Sexpr)))
;; Every expression position of one program where the finished template both
;; matches in shape and survives the oracle, with its arguments.  `expanded`
;; is the program's own expansion under the library, computed once by the
;; caller.
;;
;; One refusal is a POLICY, not a hygiene fact: an argument may not be the
;; bare name of a library macro.  The oracle would accept it -- passing a
;; macro's name for a pattern variable the template drops into HEAD position
;; of the spliced call is perfectly hygienic -- but a macro parameterized
;; over which macro to call is a higher-order macro, which this module's
;; standing simplifications exclude.  (This is not the only channel a macro
;; name can reach an argument through -- an argument that IS a macro call,
;; e.g. `(m0 1)`, expands just fine and is exercised on purpose by the
;; iteration test below; only a BARE, unapplied macro name is refused here.)
;; The check is also deliberately coarser than its own rationale needs: it
;; refuses a macro name supplied as a BINDER position's argument (V2) just
;; the same, where the higher-order-macro worry does not even apply -- a
;; binder-position argument only names a fresh local, it never gets called
;; -- but refusing there costs nothing this module's corpora would ever want
;; back; it only refuses more than strictly necessary, never less.
(define (valid-sites library name tpl prog expanded)
  (define macro-names (map mdef-name library))
  (for/fold ([sites (hash)])
            ([pos (in-list (expr-positions prog))])
    (define args (skeleton-match tpl (cdr pos)))
    (if (and args
             (not (for/or ([a (in-list args)]) (memq (cdr a) macro-names)))
             (site-valid? library name tpl prog expanded (car pos) args))
        (hash-set sites (car pos) args)
        sites)))

(module+ test
  (test-case "the oracle enforces the note's H conditions, unimplemented"
    (define T `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0))))
    (define (sites-of prog)
      (hash-keys (valid-sites '() 'm T prog (expand-under '() prog))))
    ;; H3: any binder name at the site will do
    (check-equal? (sites-of '(lambda (veryown) (f veryown 1))) '(()))
    ;; H1: an argument that mentions the matched binder cannot be passed --
    ;; the template's binder is freshened away from it at expansion
    (check-equal? (sites-of '(lambda (y) (f y (g y)))) '())
    ;; V2 rescue: the very site H1 just refused has a valid root site once
    ;; the binder position holds a pvar instead of a tvar -- the argument
    ;; for #0 is the binder's own NAME, so #1's reference to it is use-site
    ;; syntax on both ends and transcribes back literally
    (define T-v2 `(lambda (,(pvar 0)) (f ,(pvar 0) ,(pvar 1))))
    (define capturing '(lambda (y) (f y (g y))))
    (check-equal? (valid-sites '() 'm T-v2 capturing (expand-under '() capturing))
                  (hash '() (list (cons '(1 0) 'y) (cons '(2 2) '(g y)))))
    ;; H2: the template's free f must mean the definition site's f
    (define shadowed '(lambda (f) (f (f 9 1) 1)))
    ;; the inner (f (f 9 1) 1)-shaped sites use the LOCAL f: no match...
    (check-equal? (valid-sites '() 'm `(f ,(pvar 0) 1) shadowed
                               (expand-under '() shadowed))
                  (hash))
    ;; ...while the same shape under an unrelated binder is fine
    (define unshadowed '(lambda (g) (f (f 9 1) 1)))
    (check-equal? (sort (hash-keys
                         (valid-sites '() 'm `(f ,(pvar 0) 1) unshadowed
                                      (expand-under '() unshadowed)))
                        < #:key length)
                  '((2) (2 1)))
    ;; H4: one pattern variable, two uses -- alpha-equivalent arguments are
    ;; accepted, different ones are refused
    (define T2 `(g ,(pvar 0) ,(pvar 0)))
    (define ok '(g (lambda (a) a) (lambda (b) b)))
    (check-equal? (hash-keys (valid-sites '() 'm T2 ok (expand-under '() ok)))
                  '(()))
    (define no '(g (lambda (a) a) (lambda (b) 1)))
    (check-equal? (valid-sites '() 'm T2 no (expand-under '() no))
                  (hash))))

;; ---------------------------------------------------------------------------
;; Rewriting, and utility by rewriting
;; ---------------------------------------------------------------------------
;;
;; micro.rkt's Section 4.4 dynamic program, verbatim in structure: at every
;; expression position either leave the node and rewrite its subexpressions,
;; or -- if the position is an oracle-approved site -- emit the call and
;; rewrite inside the arguments; take whichever costs less, ties to leaving.
;; Site validity was judged against the ORIGINAL program; rewriting beneath a
;; site can only remove enclosing binders that no surviving argument
;; references, so composed rewrites stay valid -- and `rewrite-corpus`'s
;; final assertion re-runs the oracle on the whole result rather than
;; trusting that argument. Like micro.rkt's own rewrite-corpus, best-cost
;; below is memoized, and for the same reason: the memo table IS the dynamic
;; program, not an optimization on top of it (see the comment there).

;; rewrite-program : (HashOf Path ...) Symbol Sexpr -> (values Sexpr Cost)
;; One program rewritten as cheaply as the sites allow, and what the dynamic
;; program says it now costs.
(define (rewrite-program sites name prog)
  ;; This table is not an optimization bolted onto the dynamic program -- it
  ;; IS the dynamic program, exactly as in micro.rkt's rewrite-corpus: the DP
  ;; is stated bottom-up, one verdict per subtree, and memoizing this
  ;; top-down recursion computes the same table. Without it, `best-cost`
  ;; visits every descendant TWICE at each node (once from accept-cost, once
  ;; from reject-cost), so a program nested through the same shape at every
  ;; level revisits identical subtrees an exponential number of times --
  ;; measured 4x per two nesting levels on self-similar programs before this
  ;; fix. Keyed on PATH, not on the subterm: within one call to
  ;; rewrite-program, a path names exactly one occurrence, and (unlike
  ;; micro.rkt's plain terms) two occurrences of an identical-looking subterm
  ;; at different paths can have different verdicts here -- `sites` itself is
  ;; keyed by path, because the oracle's hygiene judgment is positional (the
  ;; H2 shadowing test above is exactly two such occurrences) -- so the
  ;; subterm alone is not a safe memo key.
  (define memo (make-hash))
  ;; best-cost : Sexpr Path -> Cost
  (define (best-cost t path)
    (hash-ref! memo path
               (lambda ()
                 (define a (accept-cost t path))
                 (define r (reject-cost t path))
                 (if (and a (< a r)) a r))))
  ;; reject-cost: keep this node; its non-expression parts keep their cost
  (define (reject-cost t path)
    (+ (sexpr-cost t)
       (for/sum ([c (in-list (expr-children t))])
         (- (best-cost (cdr c) (append path (car c)))
            (sexpr-cost (cdr c))))))
  ;; accept-cost: the call's form, its name, and the arguments at their best
  (define (accept-cost t path)
    (define args (hash-ref sites path #f))
    (and args
         (+ 1 100
            (for/sum ([a (in-list args)])
              (best-cost (cdr a) (append path (car a)))))))
  (define (rewrite t path)
    (define a (accept-cost t path))
    (cond
      [(and a (< a (reject-cost t path)))
       (cons name (for/list ([arg (in-list (hash-ref sites path))])
                    (rewrite (cdr arg) (append path (car arg)))))]
      [(list? t)
       (for/fold ([out t]) ([c (in-list (expr-children t))])
         (replace-at out (car c) (rewrite (cdr c) (append path (car c)))))]
      [else t]))
  (values (rewrite prog '()) (best-cost prog '())))

;; rewrite-corpus : (Listof MDef) Symbol Template (Listof Sexpr)
;;                  [(U #f (Listof (cons Sexpr (HashOf Path ...))))]
;;                  -> (values (Listof Sexpr) Cost)
;; Rewrite every program with the macro, and also return the cost the dynamic
;; program predicts.  Then check everything this module promises, the slow
;; way: the predicted cost is the real cost, and every rewritten program
;; still expands to what its original expands to.
;;
;; F15: the optional final argument, when supplied, is one (expanded . sites)
;; pair per program -- exactly what `best-candidate` already has to compute,
;; for every candidate, to apply its >=2-valid-programs filter.  Passing it
;; through here (and on into `macro-utility`) avoids recomputing expand-under
;; and valid-sites a second time per candidate on the scoring path, which was
;; an exact 2x on the whole search. #f (the default) recomputes them exactly
;; as before, so every other caller -- including the tests below -- is
;; unaffected and every public arity stays backward compatible.
(define (rewrite-corpus library name tpl programs [precomputed #f])
  (define library+ (append library (list (mdef name (template-arity tpl) tpl))))
  (define results
    (for/list ([prog (in-list programs)]
               [pc (in-list (or precomputed (make-list (length programs) #f)))])
      (define expanded (if pc (car pc) (expand-under library prog)))
      (define sites (if pc (cdr pc) (valid-sites library name tpl prog expanded)))
      (define-values (rewritten predicted) (rewrite-program sites name prog))
      (unless (= (sexpr-cost rewritten) predicted)
        (error 'rewrite-corpus "the DP promised cost ~a; rewriting gave ~a"
               predicted (sexpr-cost rewritten)))
      (unless (alpha=? (expand-under library+ rewritten) expanded)
        (error 'rewrite-corpus
               "rewriting changed the meaning of ~a: ~a" prog rewritten))
      (cons rewritten predicted)))
  (values (map car results) (for/sum ([r (in-list results)]) (cdr r))))

;; macro-utility : (Listof MDef) Template (Listof Sexpr)
;;                 [(U #f (Listof (cons Sexpr (HashOf Path ...))))] -> Cost
;; How much better off the corpus is for having this macro: the cost it
;; saves, less the cost of carrying the macro itself.  The optional final
;; argument passes through to `rewrite-corpus`, same contract, same default.
(define (macro-utility library tpl programs [precomputed #f])
  (define-values (rewritten after)
    (rewrite-corpus library (fresh-name library programs) tpl programs
                     precomputed))
  (- (corpus-cost programs) after (macro-cost tpl)))

;; fresh-name : (Listof MDef) (Listof Sexpr) -> Symbol
;; A macro name nothing in sight is using.
(define (fresh-name library programs)
  (define taken (list->set (append (map mdef-name library)
                                   (append-map flatten programs))))
  (for/first ([k (in-naturals)]
              #:unless (set-member? taken (string->symbol (format "m~a" k))))
    (string->symbol (format "m~a" k))))

(module+ test
  (test-case "utility by rewriting"
    ;; three lambdas that differ only in a literal
    (define programs '((lambda (x) (f x 1))
                       (lambda (y) (f y 2))
                       (lambda (z) (f z 3))))
    (define T `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0))))
    (define-values (rewritten after) (rewrite-corpus '() 'm0 T programs))
    (check-equal? rewritten '((m0 1) (m0 2) (m0 3)))
    ;; each program went from 503 to 201; the macro costs its template, 403
    (check-equal? after 603)
    (check-equal? (macro-utility '() T programs) (- 1509 603 403)))

  (test-case "the rewriter leaves an oracle-refused site alone"
    ;; the first program's argument would capture; the other two rewrite
    (define programs '((lambda (x) (p x (q x)))
                       (lambda (y) (p y 7))
                       (lambda (z) (p z 8))))
    (define T `(lambda (,(tvar 0)) (p ,(tvar 0) ,(pvar 0))))
    (define-values (rewritten _) (rewrite-corpus '() 'm0 T programs))
    (check-equal? rewritten '((lambda (x) (p x (q x))) (m0 7) (m0 8)))))

;; ---------------------------------------------------------------------------
;; Candidate enumeration
;; ---------------------------------------------------------------------------
;;
;; micro.rkt's enumeration with the productions of this grammar: start from
;; ??, fill the leftmost hole with everything the corpus could still match,
;; keep whatever skeleton-matches somewhere in at least two programs.  The
;; skeleton over-approximates the oracle, so pruning by it is sound; finished
;; candidates face the oracle when they are scored.

;; corpus-facts : (Listof Sexpr) -> (values (Listof Symbol) (Listof Sexpr)
;;                                          (Listof Natural) (Listof Symbol))
;; What the corpus offers as productions: the identifiers and literal
;; constants that stand anywhere in expression position, the lengths of its
;; plain (non-binding) forms, and which binding forms appear at all.
(define (corpus-facts programs)
  (define exprs (append-map (lambda (p) (map cdr (expr-positions p))) programs))
  (values (sort (set->list (for/set ([e (in-list exprs)] #:when (symbol? e)) e))
                symbol<?)
          (set->list (for/set ([e (in-list exprs)]
                               #:when (or (number? e) (boolean? e)))
                       e))
          (sort (set->list (for/set ([e (in-list exprs)]
                                     #:when (and (list? e)
                                                 (not (lambda-form? e))
                                                 (not (let-form? e))))
                             (length e)))
                <)
          (for/list ([shape (list lambda-form? let-form?)]
                     [name '(lambda let)]
                     #:when (for/or ([e (in-list exprs)]) (shape e)))
            name)))

;; expansions : Template ... Natural -> (Listof Template)
;; Every production this grammar allows in the leftmost hole: a plain form of
;; a length the corpus uses, an ellip-headed plain-form skeleton (stage 2,
;; see below), a binding form the corpus uses (with a fresh anonymous
;; binder), a reference to a template binder in scope, a corpus identifier or
;; literal, a pattern variable already introduced, or a fresh one if the
;; arity limit allows -- and, when the leftmost hole sits inside an ellip's
;; sub, (svar) if that ellip does not have one yet.
;;
;; STAGE 2's TWO NEW PRODUCTION FAMILIES
;;
;; 1. Ellip-headed form skeletons.  Alongside each plain length n the corpus
;;    exhibits, ALSO propose -- for each prefix length p from 1 to (max
;;    lens) - 1 -- the skeleton (hole * p, (ellip hole)): a plain form of p
;;    fixed positions followed by a splice.  p starts at 1, not 0: a form
;;    always has a head, and the p=0 skeleton ((ellip hole)) alone would
;;    skeleton-match EVERY plain form of EVERY length in EVERY program (its
;;    "head" is itself part of the splice) -- pure junk width by a search-
;;    width choice, not a semantic one (nothing about matching or the
;;    expander forbids p=0; it is simply never worth the oracle calls it
;;    would cost). These are gated by corpus-facts' own `lens`: only offered
;;    when the corpus exhibits at least two DISTINCT plain-form lengths (the
;;    design note's coarsest useful gate) -- on a corpus of uniformly n-ary
;;    forms, any ellip candidate here is either shape-rejected immediately or
;;    degenerates to matching exactly one arity, all for a guaranteed loss
;;    -- and by `template-has-ellip?`: at most one ellip per TEMPLATE (the
;;    session lead's amendment), so once one exists anywhere in `tpl` no
;;    second one is ever offered, here or in the ellip-context branch below.
;; 2. Inside an ellip's sub -- `hole-ellip-scope` says so -- the usual
;;    productions apply EXCEPT no binder forms (lambda/let: a binder scoped
;;    to one splice iteration abstracts nothing this corpus language can use
;;    -- the oracle could actually handle it, since each transcribed copy
;;    freshens its own binder, but the enumerator does not bother proposing
;;    it) and no nested ellip (excluded by the same template-has-ellip? gate
;;    as family 1, plus being inside an ellip already). One extra production
;;    appears instead: (svar), offered only while this ellip's sub does not
;;    already have one (hole-ellip-scope's has-svar? bit) -- ellip's sub
;;    needs exactly one occurrence to be finished, not a specific count, but
;;    offering it once it is already present would only grow needless
;;    duplicate-svar candidates the oracle would score identically to their
;;    single-svar parent.
(define (expansions tpl syms lits lens binders max-arity)
  (define scope (hole-scope tpl))
  (define arity (template-arity tpl))
  (define next (template-tvars tpl))
  (define ellip-ctx (hole-ellip-scope tpl))
  (define in-ellip? (and ellip-ctx (car ellip-ctx)))
  (define has-svar? (and ellip-ctx (cdr ellip-ctx)))
  ;; binder-pvars : (Listof Pvar)
  ;; The pattern variables a binder position may hold (V2): every pvar index
  ;; already in use (reuse) plus one fresh index, if the arity limit allows.
  ;; Depth-0 pvar reuse/creation is legal inside an ellip's sub too (the
  ;; design note's "depth-0 pvars ... inside an ellip are allowed"), so this
  ;; list is unaffected by in-ellip? -- only its use to build BINDER forms is.
  (define binder-pvars
    (for/list ([i (in-range (if (< arity max-arity) (add1 arity) arity))])
      (pvar i)))
  (define plain-form-productions
    (for/list ([n (in-list lens)]) (make-list n 'hole)))
  (define ellip-form-productions
    (if (or in-ellip? (template-has-ellip? tpl) (< (length lens) 2))
        '()
        (for/list ([p (in-range 1 (apply max lens))])
          (append (make-list p 'hole) (list (ellip 'hole))))))
  (define binder-productions
    (if in-ellip?
        '()
        (append*
         (for/list ([b (in-list binders)])
           (case b
             [(lambda) (cons `(lambda (,(tvar next)) hole)
                             (for/list ([bv (in-list binder-pvars)])
                               `(lambda (,bv) hole)))]
             [(let) (cons `(let ([,(tvar next) hole]) hole)
                          (for/list ([bv (in-list binder-pvars)])
                            `(let ([,bv hole]) hole)))])))))
  (define svar-productions (if (and in-ellip? (not has-svar?)) (list (svar)) '()))
  (append
   plain-form-productions
   ellip-form-productions
   binder-productions
   (for/list ([j (in-list (sort scope <))]) (tvar j))
   syms
   lits
   binder-pvars
   svar-productions))

(module+ test
  (test-case "corpus facts and expansions"
    (define programs '((lambda (x) (f x 1)) (if a (g b) #t)))
    (define-values (syms lits lens binders) (corpus-facts programs))
    (check-equal? syms '(a b f g if x))       ; x: it stands in expr position
    (check-equal? (sort lits (lambda (a b) (string<? (format "~a" a)
                                                     (format "~a" b))))
                  '(#t 1))
    (check-equal? lens '(2 3 4))              ; (g b), (f x 1), (if ...)
    (check-equal? binders '(lambda))
    ;; at the top of a fresh template: no tvar references are in scope, and
    ;; the lambda binder position offers both an anonymous tvar and (V2) the
    ;; one pvar index available at arity 0.  lens has three distinct lengths
    ;; (>= 2), so the gate opens: prefix lengths p = 1, 2, 3 (max lens - 1 =
    ;; 3), each an ellip-headed skeleton (hole * p, (ellip hole))
    (check-equal? (expansions 'hole syms lits lens binders 1)
                  (append '((hole hole) (hole hole hole)
                            (hole hole hole hole))
                          (list (list 'hole (ellip 'hole))
                                (list 'hole 'hole (ellip 'hole))
                                (list 'hole 'hole 'hole (ellip 'hole)))
                          (list `(lambda (,(tvar 0)) hole)
                                `(lambda (,(pvar 0)) hole))
                          syms lits (list (pvar 0))))
    ;; inside an ellip's sub: no lambda/let productions, no nested ellip, and
    ;; (svar) joins the tail once (since this sub has none yet)
    (define ellip-tpl `(f ,(ellip 'hole)))
    (define sub-expansions (expansions ellip-tpl syms lits lens binders 1))
    (check-false (for/or ([e (in-list sub-expansions)]) (lambda-form? e)))
    (check-false (for/or ([e (in-list sub-expansions)]) (ellip? e)))
    (check-true (for/or ([e (in-list sub-expansions)]) (svar? e)))
    ;; once the sub already has a svar, no second one is offered
    (define ellip-tpl2 `(f ,(ellip (list 'g (svar) 'hole))))
    (check-false (for/or ([e (in-list (expansions ellip-tpl2 syms lits lens
                                                  binders 1))])
                   (svar? e)))))

;; skeleton-programs : Template (Listof Sexpr) -> (Setof Natural)
;; Which programs the template skeleton-matches into, anywhere.
;;
;; STAGE 2 NECESSITY, discovered while measuring junk-width (not merely a
;; quality preference -- the search does not finish in practice without it):
;; for a template that CONTAINS AN ELLIP, a match is only counted here if it
;; actually iterates (captures >= 1 element) SOMEWHERE.  Reason: a match that
;; only ever succeeds via ZERO iterations (site length exactly k-1: legal
;; per spec, see skeleton-match) never once evaluates `sub` against
;; anything, so it gives this filter NO INFORMATION about whether `sub`'s
;; shape is on the right track. Since matching a program's tiny existing
;; subterms zero-iteration-style is trivially easy -- any literal fixed
;; prefix that happens to equal some actual (short) subterm elsewhere in the
;; corpus is such a witness, and corpora have many of these (every (g N) for
;; every N, for instance) -- an ellip candidate can satisfy the ">= 2
;; programs" bar via such coincidences ALONE, with `sub` never once
;; constrained by anything real.  Measured consequence before this guard: a
;; single small 3-program benchmark exploded past 900,000 open candidates by
;; enumeration level 7 (and climbing), because `sub` was then free to
;; re-explore the ENTIRE top-level template grammar completely unconstrained,
;; once per coincidentally-matching fixed prefix.  Requiring a REAL (>= 1
;; element) witness closes exactly that hole: `sub` only survives to be grown
;; further once some program has actually forced it to match something.
;; This changes nothing about MATCHING or SCORING semantics -- a finished
;; candidate's zero-iteration sites remain perfectly legal at valid-sites
;; time (skeleton-match and site-valid? are untouched) -- it only sharpens
;; the coarse STRUCTURAL PRE-FILTER this function exists to be (its own
;; docstring already calls it "a sound over-approximation, used to prune");
;; for a template with NO ellip, `has-ellip?` is #f and this is exactly the
;; pre-ellipsis check, unchanged.
(define (skeleton-programs tpl programs)
  (define has-ellip? (template-has-ellip? tpl))
  (define arity (template-arity tpl))
  (for/set ([p (in-list programs)] [k (in-naturals)]
            #:when (for/or ([pos (in-list (expr-positions p))])
                     (define args (skeleton-match tpl (cdr pos)))
                     (and args (or (not has-ellip?) (> (length args) arity)))))
    k))

;; reject? : Template (Listof Sexpr) -> Boolean
;; Should this candidate be dropped rather than grown or scored?  A bare
;; pattern variable is the identity macro; a template whose SHAPE already
;; fails to appear in two programs can never come back (children only
;; constrain, and the oracle only refuses more).
;;
;; F10: micro.rkt has two filters this function does NOT -- a CONSTANT-
;; argument filter (a parameter that receives the same closed argument at
;; every call site is not earning its keep as a parameter) and a DUPLICATE-
;; argument filter (two parameters that always receive alpha-equivalent
;; arguments are one parameter wearing two names).  Design note section 7
;; called these "unchanged in spirit"; the truth is narrower.  Neither is
;; implemented here, and neither is missed: under this module's cost model a
;; pvar is free wherever it stands and costs cost(arg) per call, so merging
;; or inlining such a pvar can only shrink or hold the template's cost while
;; leaving sites at least as valid -- the merged/inlined template strictly
;; DOMINATES whenever there are >= 2 call sites, and it IS enumerated (no
;; special case excludes it).  The filter would be an optimization, not a
;; correctness fix; it is simply unnecessary under this cost model, not
;; deliberately left out of caution.
;;
;; F9: a filter that WOULD be wrong, and so is also not here: rejecting an
;; "unreferenced binder pvar" -- a binder-position pvar whose index never
;; recurs anywhere else in the template.  The for/set north-star's own
;; target (tests/for-set-test.rkt) is exactly that shape: its binder pvar
;; #0 (the iteration variable) never recurs in the TEMPLATE; its only
;; reference lives in the argument supplied for #1 at each call site.  Such
;; a filter would delete this benchmark's answer.  The genuinely degenerate
;; subclass -- unreferenced in the template AND in every site's argument
;; too -- needs no filter either: it is dominated by its tvar variant, which
;; always matches a superset of sites (a tvar binder never needs a site's
;; argument to name anything usable) and saves 100 more per extra site
;; besides, so search never prefers it.
(define (reject? tpl programs)
  (or (pvar? tpl)
      (< (set-count (skeleton-programs tpl programs)) 2)))

;; all-candidates : (Listof MDef) (Listof Sexpr) Natural -> (Listof Template)
;; Every finished candidate the enumeration reaches, level by level from the
;; single hole.  Learned macro names are withheld from the identifier
;; productions: a template that mentions one is a macro expanding to a macro
;; call, which this module does not do yet.
(define (all-candidates library programs max-arity)
  (define-values (syms lits lens binders) (corpus-facts programs))
  (define fresh-syms
    (remove* (map mdef-name library) syms))
  (let level ([frontier (list 'hole)] [found '()])
    (cond
      [(null? frontier) found]
      [else
       (define children
         (for*/list ([tpl (in-list frontier)]
                     [piece (in-list (expansions tpl fresh-syms lits lens
                                                 binders max-arity))]
                     [child (in-value (fill-hole tpl piece))]
                     #:unless (reject? child programs))
           child))
       (define-values (done rest) (partition finished? children))
       ;; Stage 2 wrinkle: finished? no longer follows from "no hole left".
       ;; A depth-0 pvar or a corpus symbol/literal can fill an ellip's ONLY
       ;; hole without ever placing an (svar) in its sub -- legal productions
       ;; to offer there (depth-0 references are allowed inside sub), but the
       ;; result has nothing controlling its iteration, so finished? (rightly)
       ;; refuses it. Such a child is a DEAD END, not an open candidate:
       ;; `expansions` assumes hole-scope is truthy (a hole exists to grow),
       ;; and there is none left here to fill.  Filtering `rest` down to
       ;; children that still HAVE a hole drops the dead ends instead of
       ;; forwarding them into a `level` call that would crash on a hole-less
       ;; template.  They are simply never completable, so dropping them
       ;; silently is correct, not merely convenient.
       (define open (filter hole-scope rest))
       (level open (append found done))])))

;; best-candidate : (Listof MDef) (Listof Template) (Listof Sexpr)
;;                  -> (U Template #f)
;; The candidate that saves the most -- the first such, when utilities tie --
;; or #f if none saves anything.  Scoring a candidate consults the oracle at
;; every site, so this is where a finished template's hygiene is settled.
;; One judgment is not utility's to make: a macro whose valid sites are
;; confined to one program is not an abstraction we want, whatever it would
;; save -- so such a template is EXCLUDED by the >=2-programs filter before
;; it is ever scored, not scored as a plain loss and left to drop out with
;; the rest (micro.rkt's two-programs rule, applied to the sites that
;; survived the oracle rather than to the skeleton's guesses).
;;
;; F15: computing that filter needs valid-sites (hence expand-under) for
;; every (candidate, program) pair -- the dominant cost of a search -- and
;; scoring a surviving candidate via macro-utility -> rewrite-corpus used to
;; recompute the very same expand-under and valid-sites from scratch, an
;; exact 2x on the whole search. Compute each candidate's per-program
;; (expanded . sites) list exactly ONCE, filter on it, and hand the same list
;; into macro-utility for the candidates that survive.
(define (best-candidate library candidates programs)
  (define name (fresh-name library programs))
  (define scored
    (for*/list ([tpl (in-list candidates)]
                [per-program
                 (in-value
                  (for/list ([p (in-list programs)])
                    (define expanded (expand-under library p))
                    (cons expanded (valid-sites library name tpl p expanded))))]
                #:when (>= (for/sum ([pc (in-list per-program)]
                                     #:unless (hash-empty? (cdr pc)))
                             1)
                           2))
      (cons tpl (macro-utility library tpl programs per-program))))
  (define best (and (pair? scored) (argmax cdr scored)))
  (and best (positive? (cdr best)) (car best)))

;; macro-search : (Listof Sexpr) [Natural] [(Listof MDef)] -> (U Template #f)
;; The macro template of at most `max-arity` pattern variables that saves the
;; most on this corpus, or #f if none saves anything.
(define (macro-search programs [max-arity 2] [library '()])
  (check-corpus programs)
  (best-candidate library (all-candidates library programs max-arity)
                  programs))

;; check-corpus : (Listof Sexpr) -> Void
;; A well-formedness pass over the corpus, run once before search begins.
;; This is no longer just the one spelling this module reserves for itself
;; (F1): a corpus this module's own position-walkers (expr-children,
;; lambda-form?, let-form?, ...) would misread is worse than merely wrong --
;; it can drive the enumerator's own well-formed candidates into a shape
;; mismatch deep in the expander, mid-search, with a confusing error far from
;; the actual problem (a `(lambda (x) 1 2)` in the corpus, lambda-headed but
;; not lambda-shaped, is walked as a plain 4-element application by
;; expr-children, `lambda` lands in the identifier productions via
;; corpus-facts, and some later candidate's `lambda` reference gets spliced
;; where the real expander does not expect one). So three things are checked,
;; each naming its offending subterm the way the %-check below always has:
;;   * a form whose HEAD is the symbol `lambda` or `let` must actually be
;;     lambda-form?/let-form? shaped (arity 2, one binder, matching structure)
;;     -- not merely lambda/let-headed;
;;   * a well-shaped lambda's or let's binder position holds a symbol;
;;   * no symbol anywhere is spelled with the expander's own output-namespace
;;     suffix #rx"\\.[0-9]+$" (e.g. `x.1`) -- that is the suffix `expand`
;;     appends to freshen a binder's name during expansion, and alpha=?'s
;;     free-symbol comparison assumes a corpus symbol never collides with one
;;     manufactured that way; a corpus containing `x.1` could accidentally
;;     alpha=?-match a binder identity that was never actually the same
;;     variable.
(define (check-corpus programs)
  (define (check-well-formed t)
    (cond
      [(and (pair? t) (eq? (car t) 'lambda))
       (unless (lambda-form? t)
         (error 'macro-search "lambda-headed but not lambda-shaped: ~a" t))
       (unless (symbol? (car (cadr t)))
         (error 'macro-search "lambda binder position is not a symbol: ~a" t))
       (check-well-formed (caddr t))]
      [(and (pair? t) (eq? (car t) 'let))
       (unless (let-form? t)
         (error 'macro-search "let-headed but not let-shaped: ~a" t))
       (unless (symbol? (car (caadr t)))
         (error 'macro-search "let binder position is not a symbol: ~a" t))
       (check-well-formed (cadr (caadr t)))
       (check-well-formed (caddr t))]
      [(list? t) (for-each check-well-formed t)]
      [else (void)]))
  (for-each check-well-formed programs)
  (for* ([p (in-list programs)] [s (in-list (flatten p))]
         #:when (symbol? s))
    (define name (symbol->string s))
    (cond
      [(regexp-match? #rx"^%" name)
       (error 'macro-search "corpus uses a reserved %-name: ~a" s)]
      [(regexp-match? #rx"\\.[0-9]+$" name)
       (error 'macro-search
              "corpus uses the expander's reserved output spelling: ~a" s)])))

(module+ test
  (test-case "check-corpus rejects ill-formed corpora (F1)"
    ;; lambda-headed but not lambda-shaped: three body forms, not one
    (check-exn exn:fail? (lambda () (check-corpus '((lambda (x) 1 2)))))
    ;; lambda-headed but not lambda-shaped the other way: no binder list and
    ;; no body at all -- (lambda) is a 1-element form headed by the symbol
    ;; `lambda`, buried here as ((lambda) 1)'s own head
    (check-exn exn:fail? (lambda () (check-corpus '(((lambda) 1)))))
    ;; a symbol spelled like the expander's own freshened output namespace
    (check-exn exn:fail? (lambda () (check-corpus '((f x.1 1)))))
    ;; well-formed corpora still pass
    (check-not-exn (lambda () (check-corpus '((lambda (x) (f x 1)) (if a b c))))))

  (test-case "the search finds the lambda-wrapping macro"
    (define programs '((lambda (x) (f x 1))
                       (lambda (y) (f y 2))
                       (lambda (z) (f z 3))))
    (check-equal? (macro-search programs)
                  `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0)))))

  (test-case "the search finds an or-shaped macro through if and booleans"
    ;; three programs in the classic (or a b) encoding
    ;;   ((lambda (t) (if t t b)) a)
    ;; with different names for the temporary, different a's and b's, and a
    ;; second program whose b is a boolean literal.  The whole or-shape wins
    ;; over its eta-reduced half (the bare lambda, applied at the use site):
    ;; parameters cost nothing, so absorbing the application saves its form
    ;; at every use.  (Both are enumerated; utility settles it, 705 to 703.)
    (define programs '(((lambda (t) (if t t (g 2))) (f 1))
                       ((lambda (u) (if u u #f)) (h 3))
                       ((lambda (v) (if v v 9)) k)))
    (define T (macro-search programs))
    (check-equal? T `((lambda (,(tvar 0)) (if ,(tvar 0) ,(tvar 0) ,(pvar 0)))
                      ,(pvar 1)))
    (check-equal? (macro-utility '() T programs) 705)
    (define-values (rewritten _) (rewrite-corpus '() 'm0 T programs))
    (check-equal? rewritten
                  '((m0 (g 2) (f 1)) (m0 #f (h 3)) (m0 9 k))))

  (test-case "the search finds a V2 binder-position-pvar macro"
    ;; each lambda's argument mentions its own binder -- H1 blocks any V1
    ;; template with a tvar there, but a binder-position pvar (V2) passes the
    ;; binder's own name through and rescues every site
    (define programs '((lambda (x) (f x (g x)))
                       (lambda (y) (f y (h y)))
                       (lambda (z) (f z (k z 1)))))
    (define T (macro-search programs))
    (check-equal? T `(lambda (,(pvar 0)) (f ,(pvar 0) ,(pvar 1))))
    ;; utility by hand, from the cost model (100/atom, 1/form, pvars 0):
    ;;   corpus: (lambda (x) (f x (g x)))   4 forms, 6 atoms = 604
    ;;           (lambda (y) (f y (h y)))                     = 604
    ;;           (lambda (z) (f z (k z 1)))  4 forms, 7 atoms = 704
    ;;           total 1912
    ;;   macro:  3 forms (lambda, binder list, call), 2 atoms (lambda, f),
    ;;           three pvars free -- 203
    ;;   rewritten calls pay 1 (call form) + 100 (name) + each arg at cost:
    ;;     (m0 x (g x))   1+100+100+201 = 402
    ;;     (m0 y (h y))                 = 402
    ;;     (m0 z (k z 1)) 1+100+100+301 = 502
    ;;   after = 1306; utility = 1912 - 1306 - 203 = 403
    (check-equal? (macro-utility '() T programs) 403)
    (define-values (rewritten after) (rewrite-corpus '() 'm0 T programs))
    (check-equal? rewritten '((m0 x (g x)) (m0 y (h y)) (m0 z (k z 1))))
    (check-equal? after 1306))

  (test-case "V2 mixes a template binder and a binder-position pvar"
    ;; the for/set mechanism: an outer template binder (the accumulator) and
    ;; an inner binder-position pvar (the iteration variable) under it, with
    ;; a body pvar under both
    (define T `(lambda (,(tvar 0))
                 (lambda (,(pvar 0)) (cons ,(tvar 0) ,(pvar 1)))))
    (define site '(lambda (acc) (lambda (elem) (cons acc (add elem q)))))
    (check-equal? (valid-sites '() 'm T site (expand-under '() site))
                  (hash '() (list (cons '(2 1 0) 'elem)
                                  (cons '(2 2 2) '(add elem q))))))

  (test-case "nothing shared, nothing learned"
    (check-false (macro-search '((f 1) (g 2))))))

;; ---------------------------------------------------------------------------
;; Ellipses (stage 2): rendering, matching, the oracle, end to end
;; ---------------------------------------------------------------------------
;; notes/2026-08-18-1324-ellipses-design.md sections 2-5, as amended (module
;; header above): one ellip per template, its sequence variable a distinct
;; (svar) node rather than a numbered pvar.

(module+ test
  (test-case "ellipses: rendering and cost"
    ;; (f (ellip (g (svar)))) -- "f applied to (g X) ... splice"
    (define T `(f ,(ellip (list 'g (svar)))))
    (check-equal? (render-template T) '(f (g %xs) ...))
    ;; arity 0 (no pvar anywhere), so the rendered pattern is bare (_ %xs ...)
    (check-equal? (template-arity T) 0)
    (check-equal? (mdef-syntax-rules (mdef 'm0 0 T))
                  '(syntax-rules () [(_ %xs ...) (f (g %xs) ...)]))
    ;; cost by hand: outer form 1 + f 100 + ellip's `...` 100 + inner form 1
    ;; + g 100 + svar 0 = 302
    (check-equal? (sexpr-cost T) 302))

  (test-case "ellipses: skeleton-match"
    (define T `(f ,(ellip (list 'g (svar)))))
    ;; three matched elements: each contributes (path-of-its-svar . value),
    ;; the svar sitting at index 1 inside the (g _) at site index 1, 2, 3
    (check-equal? (skeleton-match T '(f (g 1) (g 2) (g 3)))
                  (list (cons '(1 1) 1) (cons '(2 1) 2) (cons '(3 1) 3)))
    ;; zero iterations (site length exactly k-1 = 1) is a legal match with no
    ;; sequence arguments
    (check-equal? (skeleton-match T '(f)) '())
    ;; a site element that does not fit sub's shape (h, not g) is no match
    (check-false (skeleton-match T '(f (g 1) (h 2)))))

  (test-case "ellipses: mixed fixed pvar and sequence arguments"
    ;; (f #0 (g (svar)) ...) -- one ordinary pvar before the splice
    (define T `(f ,(pvar 0) ,(ellip (list 'g (svar)))))
    ;; pvar arg first (path (1), value 9), then the sequence args in order
    (check-equal? (skeleton-match T '(f 9 (g 1) (g 2)))
                  (list (cons '(1) 9) (cons '(2 1) 1) (cons '(3 1) 2))))

  (test-case "ellipses: the oracle accepts, rewrites, and enforces H2"
    (define T `(f ,(ellip (list 'g (svar)))))
    (define prog '(f (g 1) (g 2)))
    (define expanded (expand-under '() prog))
    (check-equal? (valid-sites '() 'm0 T prog expanded)
                  (hash '() (list (cons '(1 1) 1) (cons '(2 1) 2))))
    (define-values (rewritten _) (rewrite-corpus '() 'm0 T (list prog)))
    (check-equal? rewritten (list '(m0 1 2)))
    ;; H2 under ellipsis: the identical fold-shape, but its `g` is a LOCAL
    ;; binding at the site -- the template's free `g` means the global one,
    ;; so every site inside this let is refused, and none survive elsewhere
    (define shadowed '(let ([g (lambda (p) p)]) (f (g 1) (g 2))))
    (check-equal? (valid-sites '() 'm0 T shadowed (expand-under '() shadowed))
                  (hash)))

  (test-case "ellipses: end-to-end benchmark"
    ;; the micro benchmark from the design note (section 5), corpus lengths
    ;; 3, 4, 5 -- all distinct, so no fixed-arity template can ever cover two
    ;; of them (the >=2-programs filter refuses every one), leaving the
    ;; ellip template as the only real competitor
    (define programs '((f (g 1) (g 2))
                       (f (g a) (g b) (g c))
                       (f (g h) (g 1) (g 2) (g p))))
    (define T (macro-search programs 2))
    (check-equal? T `(f ,(ellip (list 'g (svar)))))
    ;; corpus-cost by hand: (f (g1)(g2)) 3 forms/5 atoms=503;
    ;; (f (ga)(gb)(gc)) 4 forms/7 atoms=704; (f (gh)(g1)(g2)(gp)) 5 forms/9
    ;; atoms=905; total 2112.  macro-cost 302 (as above).  Rewritten calls:
    ;; (m0 1 2) 1+100+100+100=301; (m0 a b c) 1+100+300=401;
    ;; (m0 h 1 2 p) 1+100+400=501; after=1203.
    ;; utility = 2112 - 1203 - 302 = 607
    (check-equal? (macro-utility '() T programs) 607)
    (define-values (rewritten after) (rewrite-corpus '() 'm0 T programs))
    (check-equal? rewritten '((m0 1 2) (m0 a b c) (m0 h 1 2 p)))
    (check-equal? after 1203)))

;; ---------------------------------------------------------------------------
;; Iteration
;; ---------------------------------------------------------------------------

;; A Learned records one iteration's answer -- the macro that joined the
;; library, what it earned, and the corpus the next iteration learns from.
(struct learned (macro utility programs) #:transparent)

;; learn-one : (Listof MDef) (Listof Sexpr) Natural -> (U Learned #f)
(define (learn-one library programs max-arity)
  (define tpl (macro-search programs max-arity library))
  (cond
    [(not tpl) #f]
    [else
     (define name (fresh-name library programs))
     (define-values (rewritten after)
       (rewrite-corpus library name tpl programs))
     (learned (mdef name (template-arity tpl) tpl)
              (- (corpus-cost programs) after (macro-cost tpl))
              rewritten)]))

;; macro-compress : (Listof Sexpr) [Natural] [Natural] -> (Listof Learned)
;; Learn a library, one macro at a time: search, rewrite the corpus with the
;; winner, and search the result again with the winner's name off limits.
;; Stops early when nothing is worth abstracting any more.
(define (macro-compress programs [max-arity 2] [iterations 1])
  (let loop ([library '()] [programs programs] [k 0] [out '()])
    (define l (and (< k iterations) (learn-one library programs max-arity)))
    (cond
      [(not l) (reverse out)]
      [else (loop (append library (list (learned-macro l)))
                  (learned-programs l)
                  (add1 k)
                  (cons l out))])))

(module+ test
  (test-case "searching a corpus that already contains macro calls"
    ;; the corpus a previous iteration would leave behind: m0 is in the
    ;; library, its calls sit in the programs as plain forms, and its name
    ;; is off limits to new templates.  The right macro here is (g #0 #0):
    ;; its argument IS a macro call, which the oracle happily expands.
    (define library (list (mdef 'm0 1 `(lambda (,(tvar 0))
                                         (f ,(tvar 0) ,(pvar 0))))))
    (define programs '((g (m0 1) (m0 1))
                       (g (m0 2) (m0 2))
                       (g (m0 3) (m0 3))))
    (define T (macro-search programs 2 library))
    (check-equal? T `(g ,(pvar 0) ,(pvar 0)))
    (define name (fresh-name library programs))
    (check-equal? name 'm1)
    (define-values (rewritten _) (rewrite-corpus library name T programs))
    (check-equal? rewritten '((m1 (m0 1)) (m1 (m0 2)) (m1 (m0 3)))))

  (test-case "macro-compress stops when nothing is left to learn"
    ;; iteration 1 collapses each program to a call; iteration 2 finds the
    ;; calls share nothing a macro-call-free template may mention
    (define programs '((lambda (x) (f x 1))
                       (lambda (y) (f y 2))
                       (lambda (z) (f z 3))))
    (define steps (macro-compress programs 2 2))
    (check-equal? (length steps) 1)
    (check-equal? (mdef-template (learned-macro (first steps)))
                  `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0))))
    (check-equal? (learned-utility (first steps)) 503)
    (check-equal? (learned-programs (first steps)) '((m0 1) (m0 2) (m0 3)))))
