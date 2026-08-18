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
;; design.md.  This file is the smallest version that note admits: expressions
;; only, one rule, flat patterns, no ellipses; template binders only in binder
;; positions (the note's V1); no optimizations of any kind.
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
;; positions; (pvar i) and 'hole appear in expression positions only.
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
;; parameters are not structure, which is micro.rkt's cost_{alpha=0} choice.
;; The macro itself is charged for BOTH halves of its rule: the template and
;; the flat pattern (m x1 ... xk) the library carries.
;; ---------------------------------------------------------------------------

(require (only-in "expander.rkt" expand))

(provide (struct-out pvar) (struct-out tvar) (struct-out mdef)
         (struct-out learned)
         sexpr-cost corpus-cost template-arity macro-cost
         mdef-syntax-rules wrap-with-library expand-under
         alpha=? expr-positions skeleton-match valid-sites
         rewrite-corpus macro-utility fresh-name
         macro-search macro-compress)

(module+ test (require rackunit))

(struct pvar (i) #:transparent)
(struct tvar (j) #:transparent)
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
;; The immediate subexpressions of an expression, each with its path.  This is
;; the one place the binding spec lives: lambda and let contribute only their
;; expression parts, any other form contributes every element (its head too --
;; a head is an expression, and `(if ...)`'s head is where templates learn to
;; say `if`).  Everything that walks programs walks through here.
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
;; identifier in the rendered macro and costs like one.
(define (sexpr-cost t)
  (cond [(pvar? t) 0]
        [(tvar? t) 100]
        [(list? t) (+ 1 (for/sum ([e (in-list t)]) (sexpr-cost e)))]
        [else 100]))

;; corpus-cost : (Listof Sexpr) -> Cost
(define (corpus-cost programs)
  (for/sum ([p (in-list programs)]) (sexpr-cost p)))

(module+ test
  (test-case "shapes, positions, costs"
    (define P '(lambda (x) (f x 1)))
    (check-equal? (sexpr-cost P) 503)             ; 2 forms, 5 atoms... wait:
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
;; them, so the largest index plus one is the count.
(define (template-arity t)
  (cond [(pvar? t) (add1 (pvar-i t))]
        [(list? t) (apply max 0 (map template-arity t))]
        [else 0]))

;; template-tvars : Template -> Natural
;; How many template binders exist so far (they are numbered like pvars).
(define (template-tvars t)
  (cond [(tvar? t) (add1 (tvar-j t))]
        [(list? t) (apply max 0 (map template-tvars t))]
        [else 0]))

;; hole-scope : Template -> (U (Listof Natural) #f)
;; The template binders in scope at the leftmost hole -- what a reference
;; production may name there -- or #f if the template is finished.  A let's
;; right-hand side does not see the let's own binder, matching the expander.
(define (hole-scope tpl)
  (let/ec found
    (let walk ([t tpl] [scope '()])
      (cond [(eq? t 'hole) (found scope)]
            [(lambda-form? t)
             (walk (caddr t) (cons (tvar-j (car (cadr t))) scope))]
            [(let-form? t)
             (walk (cadr (caadr t)) scope)
             (walk (caddr t) (cons (tvar-j (car (caadr t))) scope))]
            [(list? t) (for ([e (in-list t)]) (walk e scope))]
            [else (void)]))
    #f))

;; finished? : Template -> Boolean
(define (finished? tpl) (not (hole-scope tpl)))

;; fill-hole : Template Template -> Template
;; Replace the leftmost hole by `piece`.  Purely structural: binder positions
;; hold tvars, never holes, so a plain left-to-right walk is safe.
(define (fill-hole tpl piece)
  (define (walk t)
    (cond
      [(eq? t 'hole) (values piece #t)]
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

;; render-template : Template -> Sexpr
;; The template as it appears inside the macro definition.
(define (render-template t)
  (cond [(pvar? t) (pvar-name (pvar-i t))]
        [(tvar? t) (tvar-name (tvar-j t))]
        [(list? t) (map render-template t)]
        [else t]))

;; mdef-syntax-rules : MDef -> Sexpr
;; The whole macro transformer, ready for let-syntax.
(define (mdef-syntax-rules m)
  `(syntax-rules ()
     [(_ ,@(for/list ([i (in-range (mdef-arity m))]) (pvar-name i)))
      ,(render-template (mdef-template m))]))

;; macro-cost : Template -> Cost
;; What the library pays to carry the macro: its template, and its flat
;; pattern (m x1 ... xk) -- arity made syntactic.
(define (macro-cost tpl)
  (+ (sexpr-cost tpl)
     (+ 1 (* 100 (add1 (template-arity tpl))))))

(module+ test
  (test-case "templates"
    (define T `(lambda (,(tvar 0)) (f ,(tvar 0) ,(pvar 0))))
    (check-equal? (template-arity T) 1)
    (check-equal? (template-tvars T) 1)
    (check-true (finished? T))
    (check-equal? (render-template T) '(lambda (%t0) (f %t0 %x0)))
    ;; template cost: 3 forms + lambda,f + two tvars = 3 + 400; the pattern
    ;; (m %x0) adds 201
    (check-equal? (sexpr-cost T) 403)
    (check-equal? (macro-cost T) 604)
    ;; the leftmost hole of (?? (lambda (t0) ??)) is outside the lambda;
    ;; fill it and the next hole sees t0
    (define U `(hole (lambda (,(tvar 0)) hole)))
    (check-equal? (hole-scope U) '())
    (check-equal? (hole-scope (fill-hole U 'g)) '(0))
    ;; a let's right-hand-side hole does not see the let's binder
    (check-equal? (hole-scope `(let ([,(tvar 0) hole]) hole)) '())
    (check-false (hole-scope T))))

;; ---------------------------------------------------------------------------
;; The skeleton matcher
;; ---------------------------------------------------------------------------

;; skeleton-match : Template Sexpr -> (U #f (Listof (cons Path Sexpr)))
;; Does the template have the shape of this expression, and if so what does
;; each pattern variable receive?  Returns one (path . argument) per pattern
;; variable, in index order; the path is the FIRST occurrence's, and it is
;; where the rewriter recurses.  Deliberately hygiene-blind:
;;   * a tvar in binder position matches whatever name the site binds there;
;;   * a tvar in expression position matches any identifier;
;;   * later occurrences of a pattern variable match anything at all;
;; every one of those judgments is deferred to the expansion oracle.  Only
;; shape is settled here -- in particular a binding form only matches a
;; template written with that binding form, so holes and pattern variables
;; stand at expression positions and nothing else.
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
      [(lambda-form? p)
       (and (lambda-form? t)
            (walk (caddr p) (caddr t) (append path '(2)) binds))]
      [(let-form? p)
       (and (let-form? t)
            (let ([binds (walk (cadr (caadr p)) (cadr (caadr t))
                               (append path '(1 0 1)) binds)])
              (and binds
                   (walk (caddr p) (caddr t) (append path '(2)) binds))))]
      [(list? p)
       (and (list? t) (not (lambda-form? t)) (not (let-form? t))
            (= (length p) (length t))
            (for/fold ([binds binds])
                      ([pe (in-list p)] [te (in-list t)] [i (in-naturals)])
              (and binds (walk pe te (append path (list i)) binds))))]
      [else (and (equal? p t) binds)]))
  (define binds (walk tpl t '() (hash)))
  (and binds
       (for/list ([i (in-range arity)]) (hash-ref binds i))))

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
                  (list (cons '(1) 1)))))

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
;; meaning, so errors count as no.
(define (site-valid? library name tpl prog expanded path args)
  (define call (cons name (map cdr args)))
  (define library+ (append library (list (mdef name (template-arity tpl) tpl))))
  (with-handlers ([exn:fail? (lambda (_) #f)])
    (alpha=? (expand-under library+ (replace-at prog path call))
             expanded)))

;; valid-sites : (Listof MDef) Symbol Template Sexpr Sexpr
;;               -> (HashOf Path (Listof (cons Path Sexpr)))
;; Every expression position of one program where the finished template both
;; matches in shape and survives the oracle, with its arguments.  `expanded`
;; is the program's own expansion under the library, computed once by the
;; caller.
(define (valid-sites library name tpl prog expanded)
  (for/fold ([sites (hash)])
            ([pos (in-list (expr-positions prog))])
    (define args (skeleton-match tpl (cdr pos)))
    (if (and args
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
;; trusting that argument.

;; rewrite-program : (HashOf Path ...) Symbol Sexpr -> (values Sexpr Cost)
;; One program rewritten as cheaply as the sites allow, and what the dynamic
;; program says it now costs.
(define (rewrite-program sites name prog)
  ;; best-cost : Sexpr Path -> Cost
  (define (best-cost t path)
    (define a (accept-cost t path))
    (define r (reject-cost t path))
    (if (and a (< a r)) a r))
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
;;                  -> (values (Listof Sexpr) Cost)
;; Rewrite every program with the macro, and also return the cost the dynamic
;; program predicts.  Then check everything this module promises, the slow
;; way: the predicted cost is the real cost, and every rewritten program
;; still expands to what its original expands to.
(define (rewrite-corpus library name tpl programs)
  (define library+ (append library (list (mdef name (template-arity tpl) tpl))))
  (define results
    (for/list ([prog (in-list programs)])
      (define expanded (expand-under library prog))
      (define sites (valid-sites library name tpl prog expanded))
      (define-values (rewritten predicted) (rewrite-program sites name prog))
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
    ;; each program went from 503 to 201; the macro costs 403 + 201
    (check-equal? after 603)
    (check-equal? (macro-utility '() T programs) (- 1509 603 604)))

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
;; a length the corpus uses, a binding form the corpus uses (with a fresh
;; anonymous binder), a reference to a template binder in scope, a corpus
;; identifier or literal, a pattern variable already introduced, or a fresh
;; one if the arity limit allows.
(define (expansions tpl syms lits lens binders max-arity)
  (define scope (hole-scope tpl))
  (define arity (template-arity tpl))
  (define next (template-tvars tpl))
  (append
   (for/list ([n (in-list lens)]) (make-list n 'hole))
   (for/list ([b (in-list binders)])
     (case b
       [(lambda) `(lambda (,(tvar next)) hole)]
       [(let) `(let ([,(tvar next) hole]) hole)]))
   (for/list ([j (in-list (sort scope <))]) (tvar j))
   syms
   lits
   (for/list ([i (in-range (if (< arity max-arity) (add1 arity) arity))])
     (pvar i))))

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
    ;; at the top of a fresh template: no tvar references are in scope
    (check-equal? (expansions 'hole syms lits lens binders 1)
                  (append '((hole hole) (hole hole hole)
                            (hole hole hole hole))
                          (list `(lambda (,(tvar 0)) hole))
                          syms lits (list (pvar 0))))))

;; skeleton-programs : Template (Listof Sexpr) -> (Setof Natural)
;; Which programs the template skeleton-matches into, anywhere.
(define (skeleton-programs tpl programs)
  (for/set ([p (in-list programs)] [k (in-naturals)]
            #:when (for/or ([pos (in-list (expr-positions p))])
                     (and (skeleton-match tpl (cdr pos)) #t)))
    k))

;; reject? : Template (Listof Sexpr) -> Boolean
;; Should this candidate be dropped rather than grown or scored?  A bare
;; pattern variable is the identity macro; a template whose SHAPE already
;; fails to appear in two programs can never come back (children only
;; constrain, and the oracle only refuses more).
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
       (define-values (done open) (partition finished? children))
       (level open (append found done))])))

;; best-candidate : (Listof MDef) (Listof Template) (Listof Sexpr)
;;                  -> (U Template #f)
;; The candidate that saves the most -- the first such, when utilities tie --
;; or #f if none saves anything.  Scoring a candidate consults the oracle at
;; every site, so this is where a finished template's hygiene is settled; a
;; template the oracle refuses everywhere scores as a plain loss and drops
;; out with the rest.  One judgment is not utility's to make: a macro whose
;; valid sites are confined to one program is not an abstraction we want,
;; whatever it saves (micro.rkt's two-programs rule, applied to the sites
;; that survived the oracle rather than to the skeleton's guesses).
(define (best-candidate library candidates programs)
  (define name (fresh-name library programs))
  (define scored
    (for/list ([tpl (in-list candidates)]
               #:when (>= (set-count
                           (for/set ([p (in-list programs)] [k (in-naturals)]
                                     #:unless (hash-empty?
                                               (valid-sites library name tpl p
                                                            (expand-under library p))))
                             k))
                          2))
      (cons tpl (macro-utility library tpl programs))))
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
;; The one spelling this module reserves for itself.
(define (check-corpus programs)
  (for* ([p (in-list programs)] [s (in-list (flatten p))]
         #:when (and (symbol? s)
                     (regexp-match? #rx"^%" (symbol->string s))))
    (error 'macro-search "corpus uses a reserved %-name: ~a" s)))

(module+ test
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
    ;; second program whose b is a boolean literal.  The winner is the
    ;; lambda half alone -- (lambda (t) (if t t b)), applied at the use
    ;; site -- not the whole application: taking the tested expression as a
    ;; second pattern variable would cost 100 in the pattern plus 100 in
    ;; every call's name-free slot, while leaving the application outside
    ;; costs 1 per program.  (Both are enumerated; utility settles it.)
    (define programs '(((lambda (t) (if t t (g 2))) (f 1))
                       ((lambda (u) (if u u #f)) (h 3))
                       ((lambda (v) (if v v 9)) k)))
    (define T (macro-search programs))
    (check-equal? T `(lambda (,(tvar 0)) (if ,(tvar 0) ,(tvar 0) ,(pvar 0))))
    (check-equal? (macro-utility '() T programs) 502)
    (define-values (rewritten _) (rewrite-corpus '() 'm0 T programs))
    (check-equal? rewritten
                  '(((m0 (g 2)) (f 1)) ((m0 #f) (h 3)) ((m0 9) k))))

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
    (check-equal? (learned-utility (first steps)) 302)
    (check-equal? (learned-programs (first steps)) '((m0 1) (m0 2) (m0 3)))))
