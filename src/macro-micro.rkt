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
;; EXPAND BACK to it?  Like micro.rkt, everything here is written to be read:
;; naive enumeration, matching from scratch, utility computed by actually
;; rewriting the corpus -- and one genuinely new move, described next.
;; Design notes: notes/2026-08-18-0323-syntax-rules-learning-design.md (the
;; semantics) and notes/2026-08-18-1324-ellipses-design.md; the worked
;; example is walkthrough-macros.md.
;;
;; WHAT REPLACES BETA
;;
;; micro.rkt's rewrite is justified by beta-reduction: (fn a1 .. ak) reduces
;; to the subterm it replaced.  Here the justification is hygienic expansion,
;; and the correctness criterion is:
;;
;;     expanding the rewritten program, with the macro defined, yields a
;;     program alpha-equivalent to the expansion of the original.
;;
;; Where micro refuses to predict what the rewriter will save and instead
;; runs it, this module refuses to predict what the expander will do and
;; instead runs it -- expander.rkt, the model expander from "Hygienic macro
;; expansion explained" (Ballantyne and Rosenblatt), is called on every
;; candidate rewrite (`site-valid?` below).  The design note derives four
;; hygiene conditions a rewrite must satisfy; none of them is implemented
;; anywhere in this file.  They are consequences the expander enforces:
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
;; The structural matcher below (`skeleton-match`) is correspondingly sloppy
;; on purpose: it settles shape and reads off the arguments, and is never
;; trusted about hygiene.  It is a sound over-approximation, used to prune.
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
;; identifiers a template may mention.  Corpora must be well-formed and must
;; not shadow the names `lambda` and `let` (the expander would still be
;; right if they did; the position-walkers here would misread the program's
;; shape).  `check-corpus`, at the end of this file, rejects offenders up
;; front.
;;
;; STANDING SIMPLIFICATIONS
;;
;; Single-rule macros; flat patterns (m x1 ... xk), so every pattern variable
;; is a whole argument, plus at most one trailing `xs ...`; no literals
;; lists; no recursive macros, no macro-defining macros, and no macros that
;; expand to macro calls; the macro is defined at top level, so its
;; template's free identifiers resolve globally.
;;
;; Those simplify the LANGUAGE of macros considered.  Separately, the search
;; does not propose every template that language admits: its productions are
;; read off the corpus, and the ellipsis productions are narrowed further.
;; Unlike micro.rkt, whose two prunings provably preserve the optimum, these
;; width choices can lose a better macro; each one is recorded where it is
;; made, at `expansions` and `skeleton-programs`.
;;
;; DATA DEFINITIONS
;;
;; A Template is a partial macro body: an expression extended with
;;   'hole        an unfilled ??
;;   (pvar i)     pattern variable #i -- a parameter, filled at each use
;;                site.  In expression position its argument is a whole
;;                subexpression.  In BINDER position -- lambda's or let's
;;                binder slot -- its argument is the binder's NAME, supplied
;;                by the macro user, so a binder introduced by the call can
;;                hygienically capture use-site references passed as other
;;                arguments.  Those are exactly the sites H1 makes
;;                unreachable for a template binder.
;;   (tvar j)     template binder j -- a binder the MACRO introduces.  These
;;                are anonymous (hygiene renames them at every expansion, so
;;                a name would be information the semantics ignores); they
;;                get names only when the template is rendered as
;;                syntax-rules.  A tvar appears in binder positions and, as
;;                a reference, in expression positions.
;;   (ellip sub)  `sub ...`: sub is transcribed once per matched sequence
;;                element and the copies are spliced in.  An ellip stands
;;                only as the LAST element of a plain (non-binding) form.
;;   (svar)       the sequence variable, occurring only inside an ellip's
;;                sub, one or more times.  At least one occurrence is
;;                required for the template to be finished: it is what
;;                controls the iteration count -- nothing else could.
;;                Depth-0 (pvar i) and (tvar j) references are also legal
;;                inside a sub (repeated per iteration and freshened per
;;                iteration, respectively).
;;
;; A template contains at most ONE ellipsis, and its sequence variable is
;; its own node kind rather than a numbered pattern variable.  This choice
;; keeps pattern variables exactly what they are without ellipses -- indices
;; 0 .. arity-1, one ordinary argument each per call -- and it makes the
;; sequence arguments ordinary trailing entries in the same argument list
;; every consumer walks: the expansion check, the rewriter's recursion, and
;; the cost accounting have no ellipsis cases at all.
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
;; (svar) costs 0, same reasoning as a pvar.  The macro itself is charged
;; for its TEMPLATE only, mirroring stitch exactly: stitch's structure
;; penalty is the invention body at cost_{alpha=0}, and neither the
;; invention's binder prefix nor its library entry costs anything.  The
;; pattern (m x1 ... xk) is the binder prefix's analog, so it is likewise
;; free; arity is paid only where stitch pays it, at each call.
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
(struct ellip (sub) #:transparent)
(struct svar () #:transparent)
(struct mdef (name arity template) #:transparent)

;; ---------------------------------------------------------------------------
;; Shapes, positions and costs
;; ---------------------------------------------------------------------------

;; lambda-form?, let-form? : Any -> Boolean
;; The two binding shapes of the object language.  They are also the template
;; shapes, with a tvar or pvar in the binder position; both readings are used
;; below.
(define (lambda-form? t)
  (match t [`(lambda (,_) ,_) #t] [_ #f]))
(define (let-form? t)
  (match t [`(let ([,_ ,_]) ,_) #t] [_ #f]))

;; expr-children : Sexpr [(Listof MDef)] -> (Listof (cons Path Sexpr))
;; The immediate subexpressions of an expression, each with its path.  This
;; function IS the object language's binding spec: lambda and let contribute
;; only their expression parts, never the binder position.  Any other form
;; contributes every element, its head included -- a head is an expression,
;; and `(if ...)`'s head is where templates learn to say `if` -- unless the
;; head names a macro in `library`.  Then the form is a call (m e1 ... ek):
;; its head is the macro's name, not an expression, and argument position i
;; (element i+1) is excluded exactly when the template binds it, i.e. when i
;; is one of the template's binder-position pattern-variable indices
;; (template-binder-mask) -- a binder argument is the use site's name for
;; that binder, no more an expression than lambda's own binder.  A sequence
;; argument past the arity is always an ordinary expression.  `library`
;; defaults to '(): templates are walked without one (they never contain
;; calls), and programs are walked with the macros already learned.
(define (expr-children t [library '()])
  (cond [(lambda-form? t) (list (cons '(2) (caddr t)))]
        [(let-form? t) (list (cons '(1 0 1) (cadr (caadr t)))
                             (cons '(2) (caddr t)))]
        [(and (pair? t) (symbol? (car t))
              (findf (lambda (m) (eq? (mdef-name m) (car t))) library))
         => (lambda (m)
              (define mask (template-binder-mask (mdef-template m)))
              (define arity (mdef-arity m))
              (for/list ([e (in-list t)] [j (in-naturals)]
                         #:unless (or (zero? j)
                                      (let ([i (sub1 j)])
                                        (and (< i arity) (memv i mask)))))
                (cons (list j) e)))]
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

;; expr-positions : Sexpr [(Listof MDef)] -> (Listof (cons Path Sexpr))
;; Every expression position of a program, the whole program first.  These
;; are the places a macro call could stand.  `library` has the same meaning
;; and default as in expr-children, and is threaded straight through, so a
;; program already containing calls to library macros is walked honestly.
(define (expr-positions t [library '()])
  (let walk ([t t] [path '()])
    (cons (cons path t)
          (append* (for/list ([c (in-list (expr-children t library))])
                     (walk (cdr c) (append path (car c))))))))

;; sexpr-cost : (U Sexpr Template) -> Cost
;; What a piece of syntax costs.  One function serves programs, arguments
;; and templates: a pvar or svar is a parameter and costs nothing, a tvar
;; will be an identifier in the rendered macro and costs like one, and an
;; ellip costs its rendered `...` plus whatever its sub costs.  An ellip
;; only ever appears as a list element, which is exactly where the list case
;; reaches it.
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
    ;; (lambda (x) (f x 1)) is 3 forms (the lambda, the binder list, the
    ;; call) and 5 atoms (lambda x f x 1): 3 + 500 = 503
    (check-equal? (sexpr-cost P) 503)
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
;; Pattern variables are numbered 0, 1, ... in the order the search
;; introduced them, so the largest index plus one is the count.  A pvar can
;; stand inside an ellip's sub too, so this walks into sub; svar itself is
;; not a pvar and contributes nothing.
(define (template-arity t)
  (cond [(pvar? t) (add1 (pvar-i t))]
        [(ellip? t) (template-arity (ellip-sub t))]
        [(list? t) (apply max 0 (map template-arity t))]
        [else 0]))

;; template-tvars : Template -> Natural
;; How many template binders exist so far (they are numbered like pvars).
(define (template-tvars t)
  (cond [(tvar? t) (add1 (tvar-j t))]
        [(ellip? t) (template-tvars (ellip-sub t))]
        [(list? t) (apply max 0 (map template-tvars t))]
        [else 0]))

;; template-binder-mask : Template -> (Listof Natural)
;; The pattern-variable indices that occur in BINDER position anywhere in
;; the template, so that a walker over a CALL to this template's macro can
;; tell a binder argument (the use site's name for that binder) from an
;; ordinary expression argument.  Derived from the template rather than
;; stored on the mdef, so it can never drift out of sync with the template
;; it describes.
(define (template-binder-mask t)
  (cond
    [(lambda-form? t)
     (define binder (car (cadr t)))
     (append (if (pvar? binder) (list (pvar-i binder)) '())
             (template-binder-mask (caddr t)))]
    [(let-form? t)
     (define binder (car (caadr t)))
     (append (if (pvar? binder) (list (pvar-i binder)) '())
             (template-binder-mask (cadr (caadr t)))
             (template-binder-mask (caddr t)))]
    [(ellip? t) (template-binder-mask (ellip-sub t))]
    [(list? t) (append-map template-binder-mask t)]
    [else '()]))

;; template-has-ellip? : Template -> Boolean
;; Does this template already contain its one allowed ellipsis anywhere?
(define (template-has-ellip? t)
  (cond [(ellip? t) #t]
        [(list? t) (ormap template-has-ellip? t)]
        [else #f]))

;; template-has-svar? : Template -> Boolean
;; Does this (sub-)template contain a sequence variable anywhere?
(define (template-has-svar? t)
  (cond [(svar? t) #t]
        [(ellip? t) (template-has-svar? (ellip-sub t))]
        [(list? t) (ormap template-has-svar? t)]
        [else #f]))

;; template-ellipses-ok? : Template -> Boolean
;; True unless some ellip's sub has no (svar) inside it -- a template like
;; that has nothing controlling its iteration count, so it is not a macro.
(define (template-ellipses-ok? t)
  (cond [(ellip? t) (and (template-has-svar? (ellip-sub t))
                         (template-ellipses-ok? (ellip-sub t)))]
        [(list? t) (andmap template-ellipses-ok? t)]
        [else #t]))

;; A HoleCtx describes what the leftmost hole of a template sees:
;;   scope      the template binders in scope there -- what a tvar reference
;;              may name.  A binder-position pvar extends nothing:
;;              references to it are written as that same pvar in expression
;;              position, an existing production.
;;   in-ellip?  does the hole sit inside some ellip's sub?  Productions
;;              differ there (see `expansions`).
;;   has-svar?  meaningful only when in-ellip? is true: does that ellip's
;;              sub already contain an (svar) somewhere?
(struct hole-ctx (scope in-ellip? has-svar?) #:transparent)

;; hole-context : Template -> (U HoleCtx #f)
;; The leftmost hole's context, or #f if the template has no holes.  A let's
;; right-hand side does not see the let's own binder, matching the expander.
;; An ellip introduces no binder of its own, so scope passes through its sub
;; unchanged.
(define (hole-context tpl)
  (define (binder-scope binder scope)
    (if (tvar? binder) (cons (tvar-j binder) scope) scope))
  (let/ec found
    (let walk ([t tpl] [scope '()] [in-ellip? #f] [has-svar? #f])
      (cond [(eq? t 'hole) (found (hole-ctx scope in-ellip? has-svar?))]
            [(lambda-form? t)
             (walk (caddr t) (binder-scope (car (cadr t)) scope)
                   in-ellip? has-svar?)]
            [(let-form? t)
             (walk (cadr (caadr t)) scope in-ellip? has-svar?)
             (walk (caddr t) (binder-scope (car (caadr t)) scope)
                   in-ellip? has-svar?)]
            [(ellip? t)
             (walk (ellip-sub t) scope #t (template-has-svar? (ellip-sub t)))]
            [(list? t) (for ([e (in-list t)])
                         (walk e scope in-ellip? has-svar?))]
            [else (void)]))
    #f))

;; finished? : Template -> Boolean
;; No hole left AND every ellip's sub has something controlling its
;; iteration -- both conditions a candidate must meet before it may be
;; scored.
(define (finished? tpl)
  (and (not (hole-context tpl)) (template-ellipses-ok? tpl)))

;; fill-hole : Template Template -> Template
;; Replace the leftmost hole by `piece`.  Purely structural: binder
;; positions hold tvars or pvars, never holes, so a plain left-to-right walk
;; is safe.  An ellip is a one-field struct, not a list, so it needs its own
;; case to be walked into.
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
;; prefix keeps them out of the corpus's namespace: transcription
;; substitutes pattern variables by NAME, so a pattern variable spelled like
;; a template free identifier would swallow it.  (check-corpus rejects
;; %-names in corpora.)
(define (pvar-name i) (string->symbol (format "%x~a" i)))
(define (tvar-name j) (string->symbol (format "%t~a" j)))
;; svar-name : Symbol
;; There is at most one svar per template, so unlike pvar/tvar it needs no
;; index -- one reserved spelling suffices.
(define svar-name '%xs)

;; render-template : Template -> Sexpr
;; The template as it appears inside the macro definition.  An ellip element
;; renders as TWO spliced elements -- its sub's rendering, then the literal
;; symbol `...` -- exactly the way syntax-rules notation itself reads.
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
;; contains an ellip, the pattern gains a trailing `%xs ...` after the flat
;; prefix -- the one place the macro's arity (a count of pvars) and its
;; pattern's shape diverge.
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
    (check-equal? (hole-ctx-scope (hole-context U)) '())
    (check-equal? (hole-ctx-scope (hole-context (fill-hole U 'g))) '(0))
    ;; a let's right-hand-side hole does not see the let's binder
    (check-equal? (hole-ctx-scope (hole-context `(let ([,(tvar 0) hole]) hole)))
                  '())
    ;; a pvar binder adds no tvar reference: it is use-site syntax, not a
    ;; template binder, so nothing is in scope beneath it
    (check-equal? (hole-ctx-scope (hole-context `(lambda (,(pvar 0)) hole)))
                  '())
    (check-false (hole-context T)))

  (test-case "templates with an ellipsis: rendering and cost"
    ;; (f (ellip (g (svar)))) -- "f applied to (g X) ... splice"
    (define T `(f ,(ellip (list 'g (svar)))))
    (check-equal? (render-template T) '(f (g %xs) ...))
    ;; arity 0 (no pvar anywhere), so the rendered pattern is bare (_ %xs ...)
    (check-equal? (template-arity T) 0)
    (check-equal? (mdef-syntax-rules (mdef 'm0 0 T))
                  '(syntax-rules () [(_ %xs ...) (f (g %xs) ...)]))
    ;; cost by hand: outer form 1 + f 100 + ellip's `...` 100 + inner form 1
    ;; + g 100 + svar 0 = 302
    (check-equal? (sexpr-cost T) 302)
    ;; a hole inside the ellip's sub reports its ellipsis context
    (define U `(f ,(ellip (list 'g 'hole))))
    (check-true (hole-ctx-in-ellip? (hole-context U)))
    (check-false (hole-ctx-has-svar? (hole-context U)))
    (check-true (hole-ctx-has-svar?
                 (hole-context `(f ,(ellip (list 'hole (svar)))))))))

;; ---------------------------------------------------------------------------
;; The skeleton matcher
;; ---------------------------------------------------------------------------

;; match-binder : Any Symbol Path (HashOf Natural (cons Path Any))
;;               -> (U (HashOf Natural (cons Path Any)) #f)
;; A binder position's own judgment, parallel to the pvar/tvar cases of the
;; walk below but never reached by it (the walk only recurses into a binding
;; form's expression parts).  A tvar binder matches whatever name the site
;; binds there and records nothing (H3).  A pvar binder takes the site's
;; binder NAME as its argument, by the identical first-occurrence rule as an
;; expression-position pvar; on a later sighting it matches only if what was
;; recorded the first time was itself a symbol -- a compound argument can
;; never legally stand as a binder's name, and that is a SHAPE judgment,
;; not a hygiene one, so it is the skeleton's to make.  Anything that is
;; neither tvar nor pvar in a template's binder position (an ill-formed
;; hand-built template; the enumerator never makes one) is no match.
(define (match-binder binder-p binder-sym binder-path binds)
  (cond [(tvar? binder-p) binds]
        [(not (pvar? binder-p)) #f]
        [(hash-has-key? binds (pvar-i binder-p))
         (and (symbol? (cdr (hash-ref binds (pvar-i binder-p)))) binds)]
        [else (hash-set binds (pvar-i binder-p) (cons binder-path binder-sym))]))

;; skeleton-match : Template Sexpr -> (U #f (Listof (cons Path Sexpr)))
;; Does the template have the shape of this expression, and if so what does
;; each pattern variable -- and each matched sequence element -- receive?
;; Returns one (path . argument) per pattern variable, in index order,
;; followed by one (path . argument) per matched sequence element, in site
;; order (empty when the template has no ellipsis, or when it matched zero
;; elements).  A sequence argument is just an ordinary trailing entry in the
;; same list, so every consumer of this return value -- the call built in
;; site-valid?, the rewriter's recursion, the cost accounting -- treats all
;; the arguments alike.
;;
;; Deliberately hygiene-blind: a tvar in binder position matches whatever
;; name the site binds there, recording nothing; a tvar in expression
;; position matches any identifier; a pvar's FIRST occurrence (in either
;; kind of position) records the site's subterm -- or binder name -- as its
;; argument, and every later occurrence matches anything at all, except that
;; a later occurrence in binder position requires the recorded argument to
;; be a symbol (shape, not hygiene -- see match-binder).  When a plain
;; form's last template element is (ellip sub), a site plain form with at
;; least the fixed elements matches: the fixed prefix positionally, then
;; each remaining site element independently against sub.  Zero remaining
;; elements is a legal match -- syntax-rules agrees, and so does the
;; expander for zero iterations.  A pvar inside sub follows the same global
;; first-occurrence rule as anywhere else.  Every judgment beyond shape is
;; deferred to the expansion check: in particular a binding form only
;; matches a template written with that binding form, and holes stand at
;; expression positions and nothing else.
(define (skeleton-match tpl t)
  (define arity (template-arity tpl))
  (define (walk p t path binds)
    (cond
      [(eq? p 'hole) binds]
      [(pvar? p)
       (if (hash-has-key? binds (pvar-i p))
           binds
           (hash-set binds (pvar-i p) (cons path t)))]
      [(tvar? p) (and (symbol? t) binds)]
      ;; a sequence variable matches anything and records nothing here:
      ;; which subterm each sequence element contributes is read off the
      ;; site by position, after the walk -- see sequence-args below
      [(svar? p) binds]
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
       ;; the fixed elements before the ellipsis match positionally, exactly
       ;; like the plain list case below; the ellipsis's sub then matches
       ;; each remaining site element independently, in order, threading
       ;; `binds` through so a pattern variable inside sub sees every element
       (and (list? t) (not (lambda-form? t)) (not (let-form? t))
            (let ([fixed (sub1 (length p))]
                  [sub (ellip-sub (last p))])
              (and (>= (length t) fixed)
                   (let ([binds (for/fold ([binds binds])
                                          ([pe (in-list (take p fixed))]
                                           [te (in-list t)]
                                           [i (in-naturals)])
                                  (and binds
                                       (walk pe te (append path (list i))
                                             binds)))])
                     (for/fold ([binds binds])
                               ([te (in-list (drop t fixed))]
                                [i (in-naturals fixed)])
                       (and binds
                            (walk sub te (append path (list i)) binds)))))))]
      [(list? p)
       (and (list? t) (not (lambda-form? t)) (not (let-form? t))
            (= (length p) (length t))
            (for/fold ([binds binds])
                      ([pe (in-list p)] [te (in-list t)] [i (in-naturals)])
              (and binds (walk pe te (append path (list i)) binds))))]
      [else (and (equal? p t) binds)]))
  (define binds (walk tpl t '() (hash)))
  ;; A pvar whose only occurrence in the whole template lives inside an
  ;; ellip's sub never enters `binds` at a site the ellipsis matched with
  ;; zero iterations: the argument appears nowhere in the site, so there is
  ;; nothing to recover.  A site that cannot supply every pattern variable's
  ;; argument is no match -- sound (it only narrows which sites match), and
  ;; the learner loses nothing, since such a site is also matched by the
  ;; cheaper ellipsis-free prefix template.
  (and binds
       (for/and ([i (in-range arity)]) (hash-has-key? binds i))
       (append (for/list ([i (in-range arity)]) (hash-ref binds i))
               (sequence-args tpl t))))

;; ellip-form-path : Template -> (U #f Path)
;; The path to the plain form whose last element is the template's one
;; ellipsis, or #f if the template has none.  Well-defined because a
;; template has at most one.
(define (ellip-form-path tpl)
  (define (under prefix sub)
    (define p (ellip-form-path sub))
    (and p (append prefix p)))
  (cond [(lambda-form? tpl) (under '(2) (caddr tpl))]
        [(let-form? tpl) (or (under '(1 0 1) (cadr (caadr tpl)))
                             (under '(2) (caddr tpl)))]
        [(and (pair? tpl) (ellip? (last tpl))) '()]
        [(list? tpl)
         (for/or ([e (in-list tpl)] [i (in-naturals)])
           (under (list i) e))]
        [else #f]))

;; svar-path : Template -> (U #f Path)
;; The path to the leftmost (svar) in an ellipsis's sub-template, or #f if
;; there is none yet.  "Leftmost" follows the same order as the match walk
;; (a let's right-hand side before its body), so it names the same
;; occurrence the walk reaches first.
(define (svar-path t)
  (define (under prefix sub)
    (define p (svar-path sub))
    (and p (append prefix p)))
  (cond [(svar? t) '()]
        [(lambda-form? t) (under '(2) (caddr t))]
        [(let-form? t) (or (under '(1 0 1) (cadr (caadr t)))
                           (under '(2) (caddr t)))]
        [(list? t)
         (for/or ([e (in-list t)] [i (in-naturals)])
           (under (list i) e))]
        [else #f]))

;; sequence-args : Template Sexpr -> (Listof (cons Path Sexpr))
;; The sequence arguments an ellipsis template reads off a site it has
;; matched: one per site element beyond the fixed prefix, in site order.
;; No bookkeeping during the match walk is needed, because everything about
;; them is positional: the ellipsis's form sits at the same path in the
;; site as in the template (matching is positional, and no form above the
;; one ellipsis can differ in length), and within each matched element the
;; argument is the site's subterm at the sub-template's first (svar) --
;; later (svar) occurrences match anything, like later pattern-variable
;; occurrences, and whether the copies agree is the expansion check's
;; business (H4), as always.  A sub with no (svar) yet -- a template still
;; being grown -- contributes each element itself: such a template can
;; never be finished, and only the COUNT of its sequence arguments is ever
;; consulted (see skeleton-programs).
(define (sequence-args tpl t)
  (define form-path (ellip-form-path tpl))
  (cond
    [(not form-path) '()]
    [else
     (define form (subterm-at tpl form-path))
     (define fixed (sub1 (length form)))
     (define arg-path (or (svar-path (ellip-sub (last form))) '()))
     (for/list ([elem (in-list (drop (subterm-at t form-path) fixed))]
                [i (in-naturals fixed)])
       (define p (append form-path (list i) arg-path))
       (cons p (subterm-at t p)))]))

(module+ test
  (test-case "skeleton matching"
    (define T `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0))))
    ;; the site's binder name is not the template's business (that is H3,
    ;; which the expansion check owns); the argument and its path come back
    (check-equal? (skeleton-match T '(lambda (y) (f y 2)))
                  (list (cons '(2 2) 2)))
    ;; ... and the matcher happily accepts what the expansion check will
    ;; refuse: an argument mentioning the bound variable (H1's business)
    (check-equal? (skeleton-match T '(lambda (y) (f y (g y))))
                  (list (cons '(2 2) '(g y))))
    ;; shape is the matcher's business: an application template does not
    ;; match a lambda, nor the other way around
    (check-false (skeleton-match '(hole hole hole) '(lambda (x) x)))
    (check-false (skeleton-match T '(f (lambda (x) x) 2)))
    ;; a later occurrence of a pattern variable matches anything (H4 is the
    ;; expansion check's business); the first occurrence is the argument
    (check-equal? (skeleton-match `(g ,(pvar 0) ,(pvar 0)) '(g 1 2))
                  (list (cons '(1) 1)))
    ;; a pvar in binder position takes the site's binder NAME as its
    ;; argument -- the first-occurrence rule applies there too, so the later
    ;; reference in the body records nothing
    (define T2 `(lambda (,(pvar 0)) (f ,(pvar 0) ,(pvar 1))))
    (check-equal? (skeleton-match T2 '(lambda (x) (f x (g x))))
                  (list (cons '(1 0) 'x) (cons '(2 2) '(g x))))
    ;; ... and the matcher still doesn't check consistency of later
    ;; occurrences (H4 again): the body's reference to #0 need not even be
    ;; spelled the same as the binder it names
    (check-equal? (skeleton-match T2 '(lambda (x) (f y (g x))))
                  (list (cons '(1 0) 'x) (cons '(2 2) '(g x))))
    ;; a hand-built template with a raw symbol in binder position is not
    ;; something the enumerator ever produces (it only ever puts a tvar or a
    ;; pvar there), but match-binder is total rather than crashing deep
    ;; inside a struct accessor -- it is simply no match
    (check-false (skeleton-match '(lambda (bogus) 1) '(lambda (x) 1)))
    ;; a pvar recorded once as a COMPOUND expression-position argument can
    ;; never afterward be reused as a binder -- the second occurrence's
    ;; shape judgment fails cleanly instead of transcription later splicing
    ;; a compound term into a binder list
    (define T3 `(f ,(pvar 0) (lambda (,(pvar 0)) 1)))
    (check-false (skeleton-match T3 '(f (g 1) (lambda (x) 1))))
    ;; ... while a symbol recorded first is fine to reuse as a binder
    (check-equal? (skeleton-match T3 '(f w (lambda (x) 1)))
                  (list (cons '(1) 'w))))

  (test-case "skeleton matching with an ellipsis"
    (define T `(f ,(ellip (list 'g (svar)))))
    ;; three matched elements: each contributes (path-of-its-svar . value),
    ;; the svar sitting at index 1 inside the (g _) at site index 1, 2, 3
    (check-equal? (skeleton-match T '(f (g 1) (g 2) (g 3)))
                  (list (cons '(1 1) 1) (cons '(2 1) 2) (cons '(3 1) 3)))
    ;; zero iterations (a site with just the fixed prefix) is a legal match
    ;; with no sequence arguments
    (check-equal? (skeleton-match T '(f)) '())
    ;; a site element that does not fit sub's shape (h, not g) is no match
    (check-false (skeleton-match T '(f (g 1) (h 2))))
    ;; an ordinary pvar before the splice: its argument comes first, then
    ;; the sequence arguments in site order
    (define T2 `(f ,(pvar 0) ,(ellip (list 'g (svar)))))
    (check-equal? (skeleton-match T2 '(f 9 (g 1) (g 2)))
                  (list (cons '(1) 9) (cons '(2 1) 1) (cons '(3 1) 2)))))

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
;; makes expansion fail certainly changed the meaning, so failures count as
;; no -- but only the expander's own `error` reports ("no pattern matched",
;; "name already bound", a transcription depth mismatch), which are it
;; correctly saying that this splice makes no sense at this site.  Those are
;; plain exn:fail?, never exn:fail:contract?.  A contract violation escaping
;; from this call graph is a bug in this module or in expander.rkt, not a
;; hygiene verdict, and it is left to propagate as the crash it is: an
;; oracle is only trustworthy if its verdicts and its bugs are told apart.
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
;; macro's name for a pattern variable the template drops into head position
;; of the spliced call is perfectly hygienic -- but a macro parameterized
;; over which macro to call is a higher-order macro, which the standing
;; simplifications exclude.  (An argument that IS a macro call, like
;; `(m0 1)`, expands fine and is exercised on purpose by the iteration test
;; near the end of this file; only a bare, unapplied macro name is refused.)
;; The check refuses more than its rationale strictly needs -- a macro name
;; supplied as a binder's argument only names a fresh local and never gets
;; called -- but refusing there too costs nothing these corpora would want
;; back.
(define (valid-sites library name tpl prog expanded)
  (define macro-names (map mdef-name library))
  (for/fold ([sites (hash)])
            ([pos (in-list (expr-positions prog library))])
    (define args (skeleton-match tpl (cdr pos)))
    (if (and args
             (not (for/or ([a (in-list args)]) (memq (cdr a) macro-names)))
             (site-valid? library name tpl prog expanded (car pos) args))
        (hash-set sites (car pos) args)
        sites)))

(module+ test
  (test-case "the oracle enforces the design note's H conditions, unimplemented"
    (define T `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0))))
    (define (sites-of prog)
      (hash-keys (valid-sites '() 'm T prog (expand-under '() prog))))
    ;; H3: any binder name at the site will do
    (check-equal? (sites-of '(lambda (veryown) (f veryown 1))) '(()))
    ;; H1: an argument that mentions the matched binder cannot be passed --
    ;; the template's binder is freshened away from it at expansion
    (check-equal? (sites-of '(lambda (y) (f y (g y)))) '())
    ;; the very site H1 just refused has a valid root site once the binder
    ;; position holds a pvar instead of a tvar -- the argument for #0 is the
    ;; binder's own NAME, so #1's reference to it is use-site syntax on both
    ;; ends and transcribes back literally
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
                  (hash)))

  (test-case "one template binder recovers differently-named temporaries"
    ;; A macro that introduces a temporary must match a differently-named
    ;; binding at each place its expansion put one -- and iterated expansion
    ;; freshens every copy, so the site's temporaries may all be spelled
    ;; differently from each other too.  Template binders being anonymous is
    ;; what makes this free: the one tvar below recovers a, b, and c at
    ;; once.  (The enumerator does not currently propose binder forms inside
    ;; an ellip's sub -- a search-width choice noted at `expansions` -- but
    ;; matching and the oracle handle them fully.)
    (define T `(f ,(ellip `(lambda (,(tvar 0)) (g ,(tvar 0) ,(svar))))))
    (define site '(f (lambda (a) (g a 1))
                     (lambda (b) (g b 2))
                     (lambda (c) (g c 3))))
    (check-equal? (valid-sites '() 'm T site (expand-under '() site))
                  (hash '() (list (cons '(1 2 2) 1)
                                  (cons '(2 2 2) 2)
                                  (cons '(3 2 2) 3))))
    ;; ... and H1 holds per copy: an element whose sequence argument
    ;; mentions its own matched binder cannot be passed back in
    (define bad '(f (lambda (a) (g a (h a))) (lambda (b) (g b 2))))
    (check-equal? (valid-sites '() 'm T bad (expand-under '() bad))
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
;; trusting that argument.

;; rewrite-program : (HashOf Path ...) Symbol Sexpr [(Listof MDef)]
;;                   -> (values Sexpr Cost)
;; One program rewritten as cheaply as the sites allow, and what the dynamic
;; program says it now costs.  `library` (default '()), the macros already
;; in scope before this one, is threaded into every expr-children call so a
;; program already containing calls to those macros is walked honestly.
(define (rewrite-program sites name prog [library '()])
  ;; As in micro.rkt, this memo table is not an optimization bolted onto the
  ;; dynamic program -- it IS the dynamic program: the DP is stated
  ;; bottom-up, one verdict per subtree, and memoizing the top-down
  ;; recursion computes the same table.  It is keyed on PATH, not on the
  ;; subterm, because `sites` is: the oracle's judgment is positional, so
  ;; two identical-looking subterms at different paths can have different
  ;; verdicts (one under a shadowing binder, one not).
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
       (for/sum ([c (in-list (expr-children t library))])
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
       (for/fold ([out t]) ([c (in-list (expr-children t library))])
         (replace-at out (car c) (rewrite (cdr c) (append path (car c)))))]
      [else t]))
  (values (rewrite prog '()) (best-cost prog '())))

;; rewrite-corpus : (Listof MDef) Symbol Template (Listof Sexpr)
;;                  -> (values (Listof Sexpr) Cost)
;; Rewrite every program with the macro, and also return the cost the
;; dynamic program predicts.  Then check everything this module promises,
;; the slow way: the predicted cost is the real cost, and every rewritten
;; program still expands to what its original expands to.
(define (rewrite-corpus library name tpl programs)
  (define library+ (append library (list (mdef name (template-arity tpl) tpl))))
  (define results
    (for/list ([prog (in-list programs)])
      (define expanded (expand-under library prog))
      (define sites (valid-sites library name tpl prog expanded))
      (define-values (rewritten predicted)
        (rewrite-program sites name prog library))
      (unless (= (sexpr-cost rewritten) predicted)
        (error 'rewrite-corpus "the DP promised cost ~a; rewriting gave ~a"
               predicted (sexpr-cost rewritten)))
      (unless (alpha=? (expand-under library+ rewritten) expanded)
        (error 'rewrite-corpus
               "rewriting changed the meaning of ~a: ~a" prog rewritten))
      (cons rewritten predicted)))
  (values (map car results) (for/sum ([r (in-list results)]) (cdr r))))

;; macro-utility : (Listof MDef) Template (Listof Sexpr) -> Cost
;; How much better off the corpus is for having this macro: the cost it
;; saves, less the cost of carrying the macro itself.
(define (macro-utility library tpl programs)
  (define-values (rewritten after)
    (rewrite-corpus library (fresh-name library programs) tpl programs))
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
    (check-equal? rewritten '((lambda (x) (p x (q x))) (m0 7) (m0 8))))

  (test-case "an ellipsis template rewrites, and H2 still holds under it"
    (define T `(f ,(ellip (list 'g (svar)))))
    (define prog '(f (g 1) (g 2)))
    (define expanded (expand-under '() prog))
    (check-equal? (valid-sites '() 'm0 T prog expanded)
                  (hash '() (list (cons '(1 1) 1) (cons '(2 1) 2))))
    (define-values (rewritten _) (rewrite-corpus '() 'm0 T (list prog)))
    (check-equal? rewritten (list '(m0 1 2)))
    ;; the identical shape, but its `g` is a LOCAL binding at the site --
    ;; the template's free `g` means the global one, so every site inside
    ;; this let is refused, and none survive elsewhere
    (define shadowed '(let ([g (lambda (p) p)]) (f (g 1) (g 2))))
    (check-equal? (valid-sites '() 'm0 T shadowed (expand-under '() shadowed))
                  (hash))))

;; ---------------------------------------------------------------------------
;; Candidate enumeration
;; ---------------------------------------------------------------------------
;;
;; micro.rkt's enumeration with the productions of this grammar: start from
;; ??, fill the leftmost hole with everything the corpus could still match,
;; keep whatever skeleton-matches somewhere in at least two programs.  The
;; skeleton over-approximates the oracle, so pruning by it is sound;
;; finished candidates face the oracle when they are scored.

;; A Grammar is what the corpus offers as productions:
;;   syms       the identifiers standing anywhere in expression position
;;   lits       the literal constants (numbers, booleans) likewise
;;   lens       the lengths of the corpus's plain (non-binding) forms
;;   binders    which binding forms appear at all: a sublist of (lambda let)
;;   variadic?  does some plain-form family vary in arity -- one head symbol
;;              standing at two distinct lengths?  An ellipsis abstracts
;;              over arity, so ellipsis skeletons are offered only when the
;;              corpus actually shows the same head at different arities.
;;              The looser test (any two lengths anywhere) is true of
;;              essentially every corpus and wastes the search's time on
;;              candidates that cannot win; a variadic family spread across
;;              DIFFERENT heads is missed -- a search-width choice of the
;;              same kind as proposing only corpus-observed lengths.
;;              (Measurements: notes/2026-08-18-1505-session-2-review-
;;              ellipses.md.)
(struct grammar (syms lits lens binders variadic?) #:transparent)

;; corpus-grammar : (Listof Sexpr) [(Listof MDef)] -> Grammar
;; Read the productions off the corpus.  `library` has the same meaning and
;; default as in expr-children; threading it through expr-positions means a
;; corpus already containing calls to learned macros never offers a
;; binder-position argument's spelling as an identifier production.
(define (corpus-grammar programs [library '()])
  (define exprs
    (append-map (lambda (p) (map cdr (expr-positions p library))) programs))
  (define plains (for/list ([e (in-list exprs)]
                            #:when (and (list? e)
                                        (not (lambda-form? e))
                                        (not (let-form? e))))
                   e))
  (define lengths-by-head
    (for/fold ([acc (hash)])
              ([e (in-list plains)] #:when (and (pair? e) (symbol? (car e))))
      (hash-update acc (car e) (lambda (s) (set-add s (length e))) (set))))
  (grammar
   (sort (set->list (for/set ([e (in-list exprs)] #:when (symbol? e)) e))
         symbol<?)
   (set->list (for/set ([e (in-list exprs)]
                        #:when (or (number? e) (boolean? e)))
                e))
   (sort (set->list (for/set ([e (in-list plains)]) (length e))) <)
   (for/list ([shape (list lambda-form? let-form?)]
              [name '(lambda let)]
              #:when (for/or ([e (in-list exprs)]) (shape e)))
     name)
   (for/or ([(_ ls) (in-hash lengths-by-head)])
     (>= (set-count ls) 2))))

;; expansions : Template Grammar Natural -> (Listof Template)
;; Every production the grammar allows in the leftmost hole: a plain form of
;; a length the corpus uses; a plain form ending in an ellipsis; a binding
;; form the corpus uses, its binder either a fresh anonymous tvar or a
;; pattern variable; a reference to a template binder in scope; a corpus
;; identifier or literal; a pattern variable, reused or (if the arity limit
;; allows) fresh; and, when the hole sits inside an ellip's sub with no
;; (svar) yet, the sequence variable.
;;
;; Two choices about the ellipsis productions are search width, not
;; semantics.  First, the ellipsis skeletons run over prefix lengths 1 to
;; (max lens) - 1, starting at 1 because a form always has a head: the
;; prefix-0 skeleton ((ellip hole)) alone would match every plain form of
;; every length in every program, pure junk for the price of its oracle
;; calls.  They are offered only when the corpus is variadic
;; (grammar-variadic?), and never once the template has its one ellipsis.
;; Second, inside an ellip's sub the binder forms are withheld -- a binder
;; scoped to one splice iteration abstracts nothing these corpora can use,
;; though the matcher and the oracle both handle one fully if a template is
;; built by hand -- and (svar) is withheld once the sub already has one.
;; That last choice narrows more than it may look: a second (svar) adds no
;; SKELETON constraint (later occurrences match anything), but the oracle
;; can exploit per-element agreement, so on a corpus whose elements repeat
;; a value, a template like (f (g %xs %xs) ...) beats every single-svar
;; candidate -- a strictly better macro this search will not propose.  (A
;; worked corpus: notes/2026-08-18-1800-consolidation-pass.md.)
(define (expansions tpl g max-arity)
  (define ctx (hole-context tpl))
  (define scope (hole-ctx-scope ctx))
  (define in-ellip? (hole-ctx-in-ellip? ctx))
  (define arity (template-arity tpl))
  (define next (template-tvars tpl))
  ;; the pattern variables a hole may hold, in binder or expression
  ;; position: every index already in use, plus one fresh
  (define pvars
    (for/list ([i (in-range (if (< arity max-arity) (add1 arity) arity))])
      (pvar i)))
  (define plain-forms
    (for/list ([n (in-list (grammar-lens g))]) (make-list n 'hole)))
  (define ellip-forms
    (if (or in-ellip? (template-has-ellip? tpl) (not (grammar-variadic? g)))
        '()
        (for/list ([p (in-range 1 (apply max (grammar-lens g)))])
          (append (make-list p 'hole) (list (ellip 'hole))))))
  (define binder-forms
    (if in-ellip?
        '()
        (append*
         (for/list ([b (in-list (grammar-binders g))])
           (case b
             [(lambda) (cons `(lambda (,(tvar next)) hole)
                             (for/list ([bv (in-list pvars)])
                               `(lambda (,bv) hole)))]
             [(let) (cons `(let ([,(tvar next) hole]) hole)
                          (for/list ([bv (in-list pvars)])
                            `(let ([,bv hole]) hole)))])))))
  (define svars
    (if (and in-ellip? (not (hole-ctx-has-svar? ctx))) (list (svar)) '()))
  (append
   plain-forms
   ellip-forms
   binder-forms
   (for/list ([j (in-list (sort scope <))]) (tvar j))
   (grammar-syms g)
   (grammar-lits g)
   pvars
   svars))

(module+ test
  (test-case "the corpus grammar and its expansions"
    (define programs '((lambda (x) (f x 1)) (if a (g b) #t)))
    (define g (corpus-grammar programs))
    (check-equal? (grammar-syms g) '(a b f g if x)) ; x stands in expr position
    (check-equal? (sort (grammar-lits g)
                        (lambda (a b) (string<? (format "~a" a)
                                                (format "~a" b))))
                  '(#t 1))
    (check-equal? (grammar-lens g) '(2 3 4))  ; (g b), (f x 1), (if ...)
    (check-equal? (grammar-binders g) '(lambda))
    ;; three distinct lengths, but under three different HEADS (g, f, if) --
    ;; no family is variadic, so no ellipsis productions are offered
    (check-false (grammar-variadic? g))
    ;; ... and they are offered exactly when one head shows two arities
    (check-true (grammar-variadic? (corpus-grammar '((f 1) (f 1 2)))))
    ;; at the top of a fresh template: no tvar references are in scope, and
    ;; the lambda binder position offers both an anonymous tvar and the one
    ;; pvar index available at arity 0
    (check-equal? (expansions 'hole g 1)
                  (append '((hole hole) (hole hole hole)
                            (hole hole hole hole))
                          (list `(lambda (,(tvar 0)) hole)
                                `(lambda (,(pvar 0)) hole))
                          (grammar-syms g) (grammar-lits g)
                          (list (pvar 0))))
    ;; on a variadic corpus, the ellipsis skeletons appear after the plain
    ;; ones: prefix lengths 1 through (max lens) - 1
    (define g+ (struct-copy grammar g [variadic? #t]))
    (check-equal? (expansions 'hole g+ 1)
                  (append '((hole hole) (hole hole hole)
                            (hole hole hole hole))
                          (list (list 'hole (ellip 'hole))
                                (list 'hole 'hole (ellip 'hole))
                                (list 'hole 'hole 'hole (ellip 'hole)))
                          (list `(lambda (,(tvar 0)) hole)
                                `(lambda (,(pvar 0)) hole))
                          (grammar-syms g) (grammar-lits g)
                          (list (pvar 0))))
    ;; inside an ellip's sub: no lambda/let productions, no second ellipsis,
    ;; and (svar) joins the productions while this sub has none yet
    (define ellip-tpl `(f ,(ellip 'hole)))
    (define sub-expansions (expansions ellip-tpl g 1))
    (check-false (for/or ([e (in-list sub-expansions)]) (lambda-form? e)))
    (check-false (for/or ([e (in-list sub-expansions)]) (ellip? e)))
    (check-true (for/or ([e (in-list sub-expansions)]) (svar? e)))
    ;; once the sub has its svar, no second one is offered
    (define ellip-tpl2 `(f ,(ellip (list 'g (svar) 'hole))))
    (check-false (for/or ([e (in-list (expansions ellip-tpl2 g 1))])
                   (svar? e)))))

;; skeleton-programs : Template (Listof Sexpr) [(Listof MDef)] -> (Setof Natural)
;; Which programs the template skeleton-matches into, anywhere.  `library`
;; is threaded into expr-positions so a candidate is never credited with
;; matching at a binder-position argument of a library macro's call.
;;
;; For an ellipsis template, only matches that actually iterate count.  A
;; zero-iteration match -- a site of exactly the fixed prefix's length --
;; never tests the sub against anything, so it says nothing about whether
;; the sub's shape is on the right track; and such matches are trivially
;; easy to come by, since any fixed prefix that happens to equal some short
;; subterm elsewhere in the corpus is one.  Counting them lets a candidate
;; pass this filter with its sub completely unconstrained, free to grow
;; through the entire template grammar once per coincidence, and the search
;; does not finish in practice (measurements:
;; notes/2026-08-18-1505-session-2-review-ellipses.md).
;; Matching and scoring are untouched -- a finished candidate's
;; zero-iteration sites remain perfectly legal at valid-sites time; this
;; only sharpens the structural pre-filter, which was already a sound
;; over-approximation used to prune.
(define (skeleton-programs tpl programs [library '()])
  (define has-ellip? (template-has-ellip? tpl))
  (define arity (template-arity tpl))
  (for/set ([p (in-list programs)] [k (in-naturals)]
            #:when (for/or ([pos (in-list (expr-positions p library))])
                     (define args (skeleton-match tpl (cdr pos)))
                     (and args (or (not has-ellip?) (> (length args) arity)))))
    k))

;; reject? : Template (Listof Sexpr) [(Listof MDef)] -> Boolean
;; Should this candidate be dropped rather than grown or scored?  A bare
;; pattern variable is the identity macro; a template whose SHAPE already
;; fails to appear in two programs can never come back (children only
;; constrain, and the oracle only refuses more).
;;
;; micro.rkt has two filters this function does not: constant-argument (a
;; parameter receiving the same closed argument at every site is not
;; earning its keep) and duplicate-argument (two parameters that always
;; agree are one parameter wearing two names).  Neither is needed here,
;; because under this cost model neither ever changes the answer: a pvar is
;; free wherever it stands and costs its argument at every call, so the
;; template with the offending pvar merged or inlined away is never more
;; expensive, matches at least the same sites, and IS enumerated -- with two
;; or more call sites it strictly dominates.  In micro the constant-argument
;; filter is part of the objective (stitch optimizes subject to it); here it
;; would be a no-op, which is a genuine difference between the two cost
;; models, not an omission.
;;
;; One filter that looks tempting would be wrong: rejecting a
;; binder-position pvar whose index never recurs in the template.  The
;; for/set benchmark's own answer is exactly that shape -- its iteration
;; variable appears once, as a binder, and its uses live in the arguments
;; supplied for the body parameter at each site.  The genuinely useless
;; subclass (unreferenced in the template AND in every site's arguments) is
;; already dominated by its tvar variant, which matches a superset of sites
;; and saves 100 more per extra site, so the search never prefers it.
(define (reject? tpl programs [library '()])
  (or (pvar? tpl)
      (< (set-count (skeleton-programs tpl programs library)) 2)))

;; all-candidates : (Listof MDef) (Listof Sexpr) Natural -> (Listof Template)
;; Every finished candidate the enumeration reaches, level by level from the
;; single hole.  Learned macro names are withheld from the identifier
;; productions: a template that mentions one is a macro expanding to a macro
;; call, which the standing simplifications exclude.
(define (all-candidates library programs max-arity)
  (define g (corpus-grammar programs library))
  (define fresh-syms (remove* (map mdef-name library) (grammar-syms g)))
  (define g* (struct-copy grammar g [syms fresh-syms]))
  (let level ([frontier (list 'hole)] [found '()])
    (cond
      [(null? frontier) found]
      [else
       (define children
         (for*/list ([tpl (in-list frontier)]
                     [piece (in-list (expansions tpl g* max-arity))]
                     [child (in-value (fill-hole tpl piece))]
                     #:unless (reject? child programs library))
           child))
       (define-values (done rest) (partition finished? children))
       ;; being unfinished does not imply having a hole: a pvar or a corpus
       ;; symbol can fill an ellip's ONLY hole without an (svar) ever being
       ;; placed in its sub.  Nothing then controls the iteration, so
       ;; finished? rightly refuses -- and with no hole left to fill, such a
       ;; child can never be completed either.  Drop it.
       (define open (filter hole-context rest))
       (level open (append found done))])))

;; ---------------------------------------------------------------------------
;; The search
;; ---------------------------------------------------------------------------

;; too-few-programs? : (Listof MDef) Symbol Template (Listof Sexpr)
;;                     (Listof Sexpr) -> Boolean
;; Are the template's oracle-valid sites confined to fewer than two
;; programs?  This is micro.rkt's two-programs rule, applied to the sites
;; that survive the oracle rather than to the skeleton's guesses: the
;; skeleton's sites over-approximate, so the rule has to be re-checked here,
;; at scoring time, where the oracle's answers are in hand.
(define (too-few-programs? library name tpl programs expandeds)
  (< (for/sum ([p (in-list programs)] [e (in-list expandeds)])
       (if (hash-empty? (valid-sites library name tpl p e)) 0 1))
     2))

;; best-candidate : (Listof MDef) (Listof Template) (Listof Sexpr)
;;                  -> (U Template #f)
;; The candidate that saves the most -- the first such, when utilities tie --
;; or #f if none saves anything.  Scoring a candidate consults the oracle at
;; every site, so this is where a finished template's hygiene is settled.
;; One judgment is not utility's to make: a macro whose valid sites are
;; confined to one program is not an abstraction we want, whatever it would
;; save -- so such a template is excluded before it is ever scored, not
;; scored as a loss and left to drop out with the rest.  (The filter and the
;; scoring each ask the oracle about the same sites; like every micro-style
;; module, this one computes a thing twice rather than carry plumbing to
;; share it.)
(define (best-candidate library candidates programs)
  (define name (fresh-name library programs))
  (define expandeds
    (for/list ([p (in-list programs)]) (expand-under library p)))
  (define scored
    (for/list ([tpl (in-list candidates)]
               #:unless (too-few-programs? library name tpl programs expandeds))
      (cons tpl (macro-utility library tpl programs))))
  (define best (and (pair? scored) (argmax cdr scored)))
  (and best (positive? (cdr best)) (car best)))

;; macro-search : (Listof Sexpr) [Natural] [(Listof MDef)] -> (U Template #f)
;; The macro template of at most `max-arity` pattern variables that saves
;; the most on this corpus, among the candidates the enumeration proposes --
;; the search's width choices, recorded at `expansions` and
;; `skeleton-programs`, mean this is not always the best template the
;; language admits -- or #f if none saves anything.
(define (macro-search programs [max-arity 2] [library '()])
  (check-corpus programs)
  (best-candidate library (all-candidates library programs max-arity)
                  programs))

;; check-corpus : (Listof Sexpr) -> Void
;; A well-formedness pass over the corpus, run once before search begins.
;; A corpus this module's own position-walkers would misread is worse than
;; merely wrong -- it can drive a well-formed candidate into a confusing
;; error deep in the expander, far from the actual problem.  Four checks,
;; each naming its offending subterm:
;;   * a form whose head is the symbol `lambda` or `let` must actually have
;;     that binding form's shape, not merely its head;
;;   * a well-shaped lambda's or let's binder position holds a symbol;
;;   * that symbol is not itself `lambda` or `let` -- a binder is the one
;;     way this language could shadow them, and a program that does is
;;     exactly the one the position-walkers misread;
;;   * no symbol is spelled with a reserved name: the % prefix belongs to
;;     rendered pattern variables (see pvar-name), and the .N suffix (as in
;;     `x.1`) is how the expander freshens binders, so a corpus symbol
;;     spelled that way could collide with one the expander manufactures
;;     and confuse alpha=?'s free-symbol comparison.
(define (check-corpus programs)
  (define (check-binder binder form)
    (unless (symbol? binder)
      (error 'macro-search "binder position is not a symbol: ~a" form))
    (when (memq binder '(lambda let))
      (error 'macro-search "corpus shadows a binding form's name: ~a" form)))
  (define (check-well-formed t)
    (cond
      [(and (pair? t) (eq? (car t) 'lambda))
       (unless (lambda-form? t)
         (error 'macro-search "lambda-headed but not lambda-shaped: ~a" t))
       (check-binder (car (cadr t)) t)
       (check-well-formed (caddr t))]
      [(and (pair? t) (eq? (car t) 'let))
       (unless (let-form? t)
         (error 'macro-search "let-headed but not let-shaped: ~a" t))
       (check-binder (car (caadr t)) t)
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
  (test-case "check-corpus rejects ill-formed corpora"
    ;; lambda-headed but not lambda-shaped: three body forms, not one
    (check-exn exn:fail? (lambda () (check-corpus '((lambda (x) 1 2)))))
    ;; lambda-headed but not lambda-shaped the other way: no binder list and
    ;; no body at all -- (lambda) is a 1-element form headed by the symbol
    ;; `lambda`, buried here as ((lambda) 1)'s own head
    (check-exn exn:fail? (lambda () (check-corpus '(((lambda) 1)))))
    ;; a binder named after a binding form: the one way this language could
    ;; shadow lambda or let, and the position-walkers would misread the body
    (check-exn exn:fail? (lambda () (check-corpus '((lambda (let) (let ([x 1]) x))))))
    ;; a symbol spelled like the expander's own freshened output
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

  (test-case "the search finds a binder-position-pvar macro"
    ;; each lambda's argument mentions its own binder -- H1 blocks any
    ;; template with a tvar there, but a binder-position pvar passes the
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

  (test-case "a template binder and a binder-position pvar mix"
    ;; the for/set mechanism: an outer template binder (the accumulator) and
    ;; an inner binder-position pvar (the iteration variable) under it, with
    ;; a body pvar under both
    (define T `(lambda (,(tvar 0))
                 (lambda (,(pvar 0)) (cons ,(tvar 0) ,(pvar 1)))))
    (define site '(lambda (acc) (lambda (elem) (cons acc (add elem q)))))
    (check-equal? (valid-sites '() 'm T site (expand-under '() site))
                  (hash '() (list (cons '(2 1 0) 'elem)
                                  (cons '(2 2 2) '(add elem q))))))

  (test-case "the search finds a variadic macro across three arities"
    ;; the corpus's three programs use the (f (g _) ...) shape at lengths 3,
    ;; 4, 5 -- all distinct, so no fixed-arity template can ever cover two of
    ;; them (the two-programs rule refuses every one), leaving the ellipsis
    ;; template as the only real competitor.  This is abstraction over
    ;; arity, which stitch cannot express at all.
    (define programs '((f (g 1) (g 2))
                       (f (g a) (g b) (g c))
                       (f (g h) (g 1) (g 2) (g p))))
    (define T (macro-search programs 2))
    (check-equal? T `(f ,(ellip (list 'g (svar)))))
    ;; corpus cost by hand: (f (g 1) (g 2)) 3 forms/5 atoms = 503;
    ;; (f (g a) (g b) (g c)) 4 forms/7 atoms = 704; (f (g h) (g 1) (g 2)
    ;; (g p)) 5 forms/9 atoms = 905; total 2112.  The macro costs 302 (as in
    ;; the rendering test above).  Rewritten calls: (m0 1 2) 1+100+200 = 301;
    ;; (m0 a b c) 1+100+300 = 401; (m0 h 1 2 p) 1+100+400 = 501; after 1203.
    ;; utility = 2112 - 1203 - 302 = 607
    (check-equal? (macro-utility '() T programs) 607)
    (define-values (rewritten after) (rewrite-corpus '() 'm0 T programs))
    (check-equal? rewritten '((m0 1 2) (m0 a b c) (m0 h 1 2 p)))
    (check-equal? after 1203))

  (test-case "nothing shared, nothing learned"
    (check-false (macro-search '((f 1) (g 2))))))

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

  (test-case "a learned macro's binder-position argument is not an expression"
    ;; m0's pattern variable #0 is a binder, so a corpus call like
    ;; (m0 x (g x)) has its own `x` -- the binder-position argument at path
    ;; (1) -- masked out of expr-children and expr-positions the same way
    ;; lambda's and let's binder slots always have been.
    (define m0 (mdef 'm0 2 `(lambda (,(pvar 0)) (f ,(pvar 0) ,(pvar 1)))))
    (define library (list m0))
    (define programs '((m0 x (g x)) (m0 y (h y))))
    ;; (a) with the library, path (1) is gone; the OTHER argument (path (2))
    ;; and its own children -- including (2 1), the `x` INSIDE (g x) -- are
    ;; still ordinary expression positions, exactly as in any plain form
    (check-equal? (map car (expr-positions (first programs) library))
                  '(() (2) (2 0) (2 1)))
    ;; without a library (the default), nothing is masked: the binder
    ;; argument at (1) is walked as a plain expression, and so is the
    ;; macro's own NAME at (0)
    (check-equal? (map car (expr-positions (first programs)))
                  '(() (0) (1) (2) (2 0) (2 1)))
    ;; (b) with the library, m0 -- otherwise an ordinary head symbol -- no
    ;; longer leaks into the identifier productions.  `x` and `y`, though,
    ;; are not purely binder spellings in THIS corpus: each recurs as an
    ;; ordinary free reference inside its call's second argument, (g x) /
    ;; (h y), and that occurrence at (2 1) is a genuine expression position
    ;; the mask does not touch -- the mask excludes one PATH, not a symbol
    ;; everywhere it is spelled, exactly as H3's "binder names are
    ;; irrelevant, but a body may still legally spell one" implies.
    (check-equal? (grammar-syms (corpus-grammar programs library))
                  '(g h x y))
    (check-equal? (grammar-syms (corpus-grammar programs))
                  '(g h m0 x y))
    ;; a corpus where the binder argument has no OTHER occurrence shows the
    ;; mask's effect cleanly: x and y vanish entirely
    (check-equal? (grammar-syms
                   (corpus-grammar '((m0 x (g 1)) (m0 y (h 2))) library))
                  '(g h))
    ;; (c) a search over this corpus, with the library, still runs end to
    ;; end: with only two programs and nothing left for a macro-call-free
    ;; template to share beyond what m0 already absorbed (each call's second
    ;; argument has a different head, g vs h), nothing saves anything
    (check-false (macro-search programs 2 library)))

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
