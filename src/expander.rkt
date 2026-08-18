#lang racket

;; ---------------------------------------------------------------------------
;; expander.rkt --- the hygienic macro expander from "Hygienic macro expansion
;; explained" (Ballantyne and Rosenblatt), appendix C, minimally extended
;; ---------------------------------------------------------------------------
;;
;; This is the paper's model expander -- marks, scope graphs with disjoin
;; nodes, syntax-rules matching and transcription -- taken verbatim except for
;; four additions that macro-micro.rkt needs to use it as its semantic oracle
;; (see notes/2026-08-18-0323-syntax-rules-learning-design.md, addendum A,
;; and notes/2026-08-18-1324-ellipses-design.md for the fourth):
;;
;;   1. `lambda`, one binder and one body form, expanded exactly like the
;;      binding half of `let`;
;;   2. applications: a form whose head resolves to no keyword and no macro
;;      expands each element and rebuilds the list;
;;   3. an identifier that resolves to nothing expands to its bare symbol,
;;      marks dropped.  This is the "one shared global scope" convention: all
;;      unbound identifiers with the same name mean the same global, whichever
;;      site they were written at.  It is also exactly the both-unbound arm of
;;      this file's own `literal-match?`.
;;   4. syntax-rules patterns and templates support one trailing ellipsis
;;      element per list, at ellipsis depth 1: a pattern `(p .. sub ...)`
;;      binds sub's pattern variables to the SEQUENCE of their per-element
;;      matches, and a template `(t .. sub ...)` transcribes sub once per
;;      element of that sequence, splicing the copies in. This is what makes
;;      variadic macros like `(define-syntax-rule (m x ...) (f x ...))`
;;      expressible.
;;
;; Everything else -- including definition contexts and macro-defining macros,
;; which the learner does not use yet -- is the paper's code, kept intact so
;; that this file stays checkable against the paper.
;;
;; Grammar of the language accepted by this expander:
;;
;; var, mname, pvar are ids
;;
;; expr := number
;;       | boolean                                                [extension]
;;       | var                            [unbound var expands to its symbol]
;;       | (lambda (var) expr)                                    [extension]
;;       | (block def ...)
;;       | (let ([var expr]) expr)
;;       | (let-syntax ([mname macrot]) expr)
;;       | (mname . stx)
;;       | (expr ...)                       an application         [extension]
;; def := (define-syntax mname macrot)
;;      | (define var expr)
;;      | (begin def ...)
;;      | (mname . stx)
;;      | expr
;;
;; macrot := (syntax-rules (id ...) [(_ . stx) stx] ...)
;;
;; stx := id | number | (stx . stx) | ()

(provide expand)

(require racket/hash)

(define name-ctr (make-parameter #f))
(define (fresh-binding-identity x)
  (define ctr (hash-ref (name-ctr) x 1))
  (name-ctr (hash-set (name-ctr) x (+ ctr 1)))
  (string->symbol (format "~a.~a" (symbol->string x) ctr)))

(define mark-ctr (make-parameter #f))
(define (fresh-mark)
  (define ctr (mark-ctr))
  (mark-ctr (+ ctr 1))
  (string->symbol (format "d~a" ctr)))

;; Syntax is one of:
;;    1. (ListOf Syntax), 2. (identifier Symbol (ListOf Mark)) 3. Number,
;; A Mark is a Symbol.
(struct identifier [symbol marks] #:transparent)

(define (mark-id id mark)
  (match id
    [(identifier sym marks)
     (identifier sym (cons mark marks))]))

(define (top-mark=? id mark)
  (match id
    [(identifier sym (cons (== mark) _))
     #t]
    [_ #f]))

(define (drop-top-mark id)
  (match id
    [(identifier sym (cons top-mark marks-rest))
     (identifier sym marks-rest)]))

;; A BindingTable is (HashOf Identifier BindingVal)

;; A Node is one of:
;;   1. (core-scope BindingTable)
;;   2. (scope Node BindingTable)
;;   3. (disjoin Node Mark Node)
(struct core-scope [bindings])
(struct scope [parent bindings])
(struct disjoin [use-node def-mark def-node])

;; A BindingVal is one of:
;;   1. (var-binding Symbol)
;;   2. (kw-binding Symbol)
;;   3. (macro-closure Transformer Node)
(struct var-binding [identity])
(struct kw-binding [keyword] #:transparent)
(struct macro-closure [macrot node])

(struct unbound [])

(define (new-scope parent)
  (scope parent (make-hash)))

;; Node, Identifier -> (or BindingVal Unbound)
;; Attempt to resolve a reference to a binding value by following parent and projection edges in
;; the scope graph. Return the unique unbound value if the graph has no corresponding binding.
(define (resolve node id)
  (match node
    [(core-scope core-bindings)
     (hash-ref core-bindings id (unbound))]
    [(scope parent bindings)
     (define (resolve-in-parent)
       (resolve parent id))
     (hash-ref bindings id resolve-in-parent)]
    [(disjoin use-node def-mark def-node)
     (cond
       [(top-mark=? id def-mark) (resolve def-node (drop-top-mark id))]
       [else (resolve use-node id)])]))

;; Node, Identifier, BindingVal -> Void
;; Create a new binding in the scope graph associating the given id with a binding value. For
;; simple scopes, the binding is attached directly to the given node. For a disjoin, binding
;; continues with the node pointed to by the appropriate projection edge.
(define (bind! node id bnd)
  (match node
    [(core-scope _)
     (error 'bind! "cannot bind in core scope")]
    [(scope parent bindings)
     (when (hash-has-key? bindings id)
       (error 'bind! "name already bound: ~a" id))
     (hash-set! bindings id bnd)]
    [(disjoin use-node def-mark def-node)
     (cond
       [(top-mark=? id def-mark) (bind! def-node (drop-top-mark id) bnd)]
       [else (bind! use-node id bnd)])]))

(define keywords '(let lambda let-syntax syntax-rules
                   define define-syntax block begin))

(define initial-scope
  (core-scope
   (for/fold ([acc (hash)])
             ([sym keywords])
     (hash-set acc (identifier sym '()) (kw-binding sym)))))

;; Syntax, Node -> Syntax
(define (expand-expr expr node)
  (match expr
    [(? number? n) n]
    [(? boolean? b) b]                     ; [extension] #t / #f literals
    [(? identifier? id)
     #:when (var-binding? (resolve node id))
     (var-binding-identity (resolve node id))]
    ;; [extension] an unbound identifier is a global: its symbol, marks
    ;; dropped, so that a definition-site global and a use-site global with
    ;; the same name expand to the same thing (literal-match?'s unbound arm)
    [(? identifier? id)
     #:when (unbound? (resolve node id))
     (identifier-symbol id)]
    ;; [extension] lambda: the binding half of `let`
    [`(,lambda-id (,x) ,body)
     #:when (equal? (kw-binding 'lambda) (resolve node lambda-id))
     (define x^ (fresh-binding-identity (identifier-symbol x)))
     (define node^ (new-scope node))
     (bind! node^ x (var-binding x^))
     `(lambda (,x^) ,(expand-expr body node^))]
    [`(,block-id ,def* ...)
     #:when (equal? (kw-binding 'block) (resolve node block-id))
     (define node^ (new-scope node))
     (define def*^ (expand-def*-pass1 def* node^))
     (define def*^^ (expand-def*-pass2 def*^ node^))
     `(block . ,def*^^)]
    [`(,let-id ([,x ,e]) ,b)
     #:when (equal? (kw-binding 'let) (resolve node let-id))
     (define x^ (fresh-binding-identity (identifier-symbol x)))
     (define node^ (new-scope node))
     (bind! node^ x (var-binding x^))
     (define e^ (expand-expr e node))
     (define b^ (expand-expr b node^))
     `(let ([,x^ ,e^]) ,b^)]
    [`(,let-syntax-id ([,mname ,macrot])
                      ,body)
     #:when (equal? (kw-binding 'let-syntax) (resolve node let-syntax-id))
     (define node^ (new-scope node))
     (bind! node^ mname (macro-closure macrot node))
     (expand-expr body node^)]
    [`(,mname . ,stx)
     #:when (macro-closure? (resolve node mname))
     (define-values (marked-stx disjoin-node)
       (expand-macro mname `(,mname . ,stx) node))
     (expand-expr marked-stx disjoin-node)]
    ;; [extension] an application: any form whose head is neither a keyword
    ;; nor a macro in this scope.  Every element is an expression.
    [`(,e* ...)
     (for/list ([e (in-list e*)])
       (expand-expr e node))]))

(define (expand-def*-pass1 def* node)
  (for/list ([def def*])
    (expand-def-pass1 def node)))

(define (expand-def*-pass2 def* node)
  (for/list ([def def*])
    (expand-def-pass2 def node)))

;; When a macro expands in the first pass of definition
;; context expansion, continued expansion in the second
;; pass needs to use the disjoin node. The result of
;; pass 1 expansion may include this structure in order
;; to remember that node for pass 2.
(struct with-disjoin [stx node])

;; Syntax, Node -> Syntax
(define (expand-def-pass1 def node)
  (match def
    [`(,define-id ,var ,expr)
     #:when (equal? (kw-binding 'define) (resolve node define-id))
     (define var^ (fresh-binding-identity (identifier-symbol var)))
     (bind! node var (var-binding var^))
     `(define ,var^ ,expr)]
    [`(,define-syntax-id ,var ,macrot)
     #:when (equal? (kw-binding 'define-syntax) (resolve node define-syntax-id))
     (bind! node var (macro-closure macrot node))
     `(begin)]
    [`(,begin-id ,def* ...)
     #:when (equal? (kw-binding 'begin) (resolve node begin-id))
     (define def*^ (expand-def*-pass1 def* node))
     `(begin . ,def*^)]
    [`(,mname . ,stx)
     #:when (macro-closure? (resolve node mname))
     (define-values (marked-stx disjoin-node) (expand-macro mname def node))
     (with-disjoin (expand-def-pass1 marked-stx disjoin-node) disjoin-node)]
    [expr ; assume anything else is an expression and defer to pass 2.
     expr]))

;; Syntax, Node -> Syntax
(define (expand-def-pass2 def node)
  (match def
    [`(define ,var ,expr)
     `(define ,var ,(expand-expr expr node))]
    [`(begin ,def* ...)
     (define def*^ (expand-def*-pass2 def* node))
     `(begin . ,def*^)]
    [(with-disjoin stx node)
     (expand-def-pass2 stx node)]
    [expr
     (expand-expr expr node)]))

;; Identifier, Syntax, Node -> (values Syntax Node)
(define (expand-macro mname expr use-node)
  (match-define
    (macro-closure macrot def-node)
    (resolve use-node mname))
  (define-values (penv tmpl)
    (select-syntax-rule macrot expr def-node use-node))
  (define def-mark (fresh-mark))
  (define transcribed-syntax (transcribe tmpl penv def-mark))
  (define introduced-defn-scp (new-scope def-node))
  (define disjoin-node (disjoin use-node def-mark introduced-defn-scp))
  (values transcribed-syntax disjoin-node))

(define (select-syntax-rule macrot expr def-node use-node)
  (match macrot
    [`(,syntax-rules-id (,literal-id* ...)
        ,clause* ...)
     (define is-literal? (make-is-literal? literal-id*))
     (define literal-match? (make-literal-match? def-node use-node))
     (try-clauses clause* expr is-literal? literal-match?)]))

(define (make-is-literal? literal-id*)
  (lambda (id)
    (memf (lambda (x) (bound-identifier=? id x)) literal-id*)))

;; Identifier -> Identifier -> Boolean
(define (bound-identifier=? id1 id2)
  (and (eq? (identifier-symbol id1) (identifier-symbol id2))
       (equal? (identifier-marks id1) (identifier-marks id2))))

;; Node, Node -> (Identifier, Identifier -> Boolean)
(define (make-literal-match? def-node use-node)
  (lambda (literal-id target-id)
    (define literal-binding (resolve def-node literal-id))
    (define target-binding (resolve use-node target-id))
    (or (and (not (unbound? literal-binding)) (not (unbound? target-binding))
             (eq? literal-binding target-binding))
        (and (unbound? literal-binding) (unbound? target-binding)
             (eq? (identifier-symbol literal-id) (identifier-symbol target-id))))))

(define (try-clauses clauses expr is-literal? literal-match?)
  (match clauses
    [(cons `[,pat ,tmpl] rest)
     (define maybe-penv (match-top-pattern pat expr is-literal? literal-match?))
     (if maybe-penv
         (values maybe-penv tmpl)
         (try-clauses rest expr is-literal? literal-match?))]
    ['() (error 'syntax-rules "no pattern matched")]))

;; This implementation of syntax-rules matching supports ellipses at ellipsis
;; depth 1, one per list, trailing position only [extension] -- see
;; match-pattern's ellipsis case below and
;; notes/2026-08-18-1324-ellipses-design.md. It still omits datatypes not
;; supported in the input language, such as vectors.
(define (match-top-pattern pat expr is-literal? literal-match?)
  ;; The `car` of the `expr` is the macro name, and in syntax-rules
  ;; the `car` of the `pat` stands for the macro name and is ignored.
  (match-pattern (cdr pat) (cdr expr) is-literal? literal-match?))

;; [extension] Is this identifier the ellipsis marker `...`? Checked
;; structurally (by symbol only, ignoring marks): the ellipsis is a
;; structural marker in pattern/template position, never a pattern variable
;; or a hygienically-tracked free identifier. This predicate is only ever
;; applied to elements read out of a pattern or template by match-pattern /
;; transcribe, so it cannot misfire on the `...` that Racket's own `match`
;; uses at the meta level elsewhere in this file (e.g. in select-syntax-rule).
(define (ellipsis-id? x)
  (and (identifier? x) (eq? (identifier-symbol x) '...)))

;; (ListOf Any) -> Natural
;; The length of a proper cons/'() list. Used both for actual target lists
;; and for the fixed pattern-suffix after an ellipsis (which this rung never
;; itself contains a further ellipsis, so it is always a plain proper list).
(define (proper-length lst)
  (match lst
    ['() 0]
    [(cons _ d) (+ 1 (proper-length d))]))

;; Pattern, (Identifier -> Boolean) -> (Listof Identifier)              [extension]
;; All the pattern variables occurring anywhere in a pattern (literals and
;; the `...` marker excluded). Used to find which variables an ellipsis's
;; sub-pattern binds, so they can be bound at depth 1 even when the
;; ellipsis matches zero elements.
(define (pattern-vars pat is-literal?)
  (match pat
    [(? identifier? id)
     #:when (and (not (is-literal? id)) (not (ellipsis-id? id)))
     (list id)]
    [(cons pa pd) (append (pattern-vars pa is-literal?) (pattern-vars pd is-literal?))]
    [_ '()]))

;; Pattern, (Listof PatternEnv), (Identifier -> Boolean) -> PatternEnv   [extension]
;; Merge the per-element envs produced by matching an ellipsis's sub-pattern
;; against each matched element into one depth-1 env: each pattern variable
;; in sub-pat maps to the list of its per-element (depth-0) values, in
;; order -- the empty list when there were zero elements.
(define (merge-ellipsis-envs sub-pat sub-envs is-literal?)
  (define vars (remove-duplicates (pattern-vars sub-pat is-literal?)))
  (for/fold ([acc (hash)]) ([v (in-list vars)])
    (hash-set acc v (cons 1 (for/list ([env (in-list sub-envs)])
                              (cdr (hash-ref env v)))))))

;; Pattern, Pattern, Any, ... -> (or PatternEnv #f)                     [extension]
;; Match a pattern `(sub-pat ... . prest-pat)` -- prest-pat is the fixed
;; pattern after the ellipsis, empty in the trailing case this rung needs --
;; against the corresponding tail of the target list. sub-pat consumes
;; elements deterministically: exactly enough that (proper-length
;; prest-pat) target elements remain for prest-pat. Zero elements is a legal
;; match.
(define (match-ellipsis-pattern sub-pat prest-pat ex is-literal? literal-match?)
  (and (list? ex)
       (let* ([suffix-len (proper-length prest-pat)]
              [n (length ex)])
         (and (>= n suffix-len)
              (let-values ([(rep-elems suffix-elems) (split-at ex (- n suffix-len))])
                (define sub-envs
                  (for/list ([e (in-list rep-elems)])
                    (match-pattern sub-pat e is-literal? literal-match?)))
                (and (andmap values sub-envs)
                     (let ([rep-env (merge-ellipsis-envs sub-pat sub-envs is-literal?)]
                           [suffix-env (match-pattern prest-pat suffix-elems is-literal? literal-match?)])
                       (and suffix-env
                            (hash-union rep-env suffix-env)))))))))

(define (match-pattern pat expr is-literal? literal-match?)
  (match* (pat expr)
    ;; literal-id
    [((? identifier? lit) (? identifier? target-id))
     #:when (is-literal? lit)
     (and (literal-match? lit target-id)
          (hash))]
    ;; pvar -- bound at ellipsis depth 0: a single syntax value.  [extension]:
    ;; depth-tagged as (cons 0 stx) so the ellipsis case below can share this
    ;; env representation with its own depth-1 bindings.
    [((? identifier? pvar) stx)
     #:when (and (not (is-literal? pvar)) (not (ellipsis-id? pvar)))
     (hash pvar (cons 0 stx))]
    ;; datum literal
    [((? number? v) v)
     (hash)]
    [((? boolean? v) v)                    ; [extension] #t / #f literals
     (hash)]
    ;; [extension] ellipsis: pattern `(sub-pat ... . prest-pat)` against the
    ;; matching tail of the target list -- see match-ellipsis-pattern.
    [(`(,sub-pat ,ellip . ,prest-pat) ex)
     #:when (ellipsis-id? ellip)
     (match-ellipsis-pattern sub-pat prest-pat ex is-literal? literal-match?)]
    ;; cons
    [(`(,pa . ,pd) `(,ea . ,ed))
     (let ([resa (match-pattern pa ea is-literal? literal-match?)])
       (and resa
            (let ([resd (match-pattern pd ed is-literal? literal-match?)])
              (and resd
                   (hash-union resa resd)))))]
    [('() '()) (hash)]
    [(_ _) #f]))

;; Template, PatternEnv -> (Listof Identifier)                         [extension]
;; The identifiers occurring in a template that are bound in penv at
;; ellipsis depth 1 -- exactly the variables that can control how many
;; times an ellipsis's sub-template repeats.
(define (template-depth1-vars tmpl penv)
  (match tmpl
    [(? identifier? id)
     #:when (and (hash-has-key? penv id) (= (car (hash-ref penv id)) 1))
     (list id)]
    [(cons a d) (append (template-depth1-vars a penv) (template-depth1-vars d penv))]
    [_ '()]))

;; Template, PatternEnv, Mark -> (Listof Syntax)                        [extension]
;; Transcribe a template ellipsis's sub-template once per index of its
;; controlling depth-1 pattern variables (found by template-depth1-vars),
;; with the env overridden so each maps, at depth 0, to its i-th element;
;; the def-mark is applied to template identifiers by transcribe itself,
;; independently for each copy, exactly as for any other template -- no new
;; freshening machinery is needed. Errors if nothing controls the
;; iteration, or if the controlling sequences disagree on length.
(define (transcribe-ellipsis sub-tmpl penv def-mark)
  (define ctrl-vars (remove-duplicates (template-depth1-vars sub-tmpl penv)))
  (when (null? ctrl-vars)
    (error 'transcribe
           "ellipsis template has no pattern variable at depth 1 to control its length: ~a"
           sub-tmpl))
  (define lengths (for/list ([v (in-list ctrl-vars)]) (length (cdr (hash-ref penv v)))))
  (unless (andmap (lambda (l) (= l (car lengths))) lengths)
    (error 'transcribe
           "ellipsis's pattern variables disagree on length: ~a"
           (map cons (map identifier-symbol ctrl-vars) lengths)))
  (define n (car lengths))
  (for/list ([i (in-range n)])
    (define penv^
      (for/fold ([e penv]) ([v (in-list ctrl-vars)])
        (hash-set e v (cons 0 (list-ref (cdr (hash-ref penv v)) i)))))
    (transcribe sub-tmpl penv^ def-mark)))

;; Syntax, PatternEnv, Mark -> Syntax
(define (transcribe tmpl penv def-mark)
  (match tmpl
    ;; pvar -- depth 0 transcribes to its single bound syntax value; using a
    ;; depth-1 variable outside of an ellipsis is a syntax-rules error, not
    ;; something the expander should silently mis-transcribe.  [extension]:
    ;; depth check.
    [(? identifier? pvar)
     #:when (hash-has-key? penv pvar)
     (match (hash-ref penv pvar)
       [(cons 0 stx) stx]
       [(cons 1 _)
        (error 'transcribe
               "pattern variable ~a used at ellipsis depth 1 outside of an ellipsis"
               (identifier-symbol pvar))])]
    [(? identifier? id)
     (mark-id id def-mark)]
    ;; [extension] ellipsis: template `(sub-tmpl ... . rest-tmpl)` splices in
    ;; one transcription of sub-tmpl per element of its controlling depth-1
    ;; variables, then continues with rest-tmpl (empty in the trailing case
    ;; this rung needs).
    [(cons sub-tmpl (cons (? ellipsis-id?) rest-tmpl))
     (append (transcribe-ellipsis sub-tmpl penv def-mark)
             (transcribe rest-tmpl penv def-mark))]
    [(cons a d)
     (cons (transcribe a penv def-mark)
           (transcribe d penv def-mark))]
    [(or '() (? number?) (? boolean?)) tmpl]))  ; booleans: [extension]

(define (sexpr->syntax s)
  (match s
    [(cons a d)
     (cons (sexpr->syntax a) (sexpr->syntax d))]
    [(? symbol? s) (symbol->id s)]
    [_ s]))

(define (symbol->id s)
  (identifier s (list)))

;; SExpression -> SExpression
(define (expand e)
  (parameterize ([name-ctr (hash)] [mark-ctr 1])
    (expand-expr (sexpr->syntax e) initial-scope))) 

;; The example from Fig. 12.
(module+ test
  (require rackunit)
  (check-equal?
   (expand
    '(block
       (define-syntax def-m
         (syntax-rules ()
           [(_ m given-x)
            (begin
              (define x 1)
              (define-syntax m
                (syntax-rules ()
                  [(_)
                   (begin
                     (define given-x 2)
                     x)])))]))
       (def-m m x)
       (m)))
   '(block
      (begin)
      (begin
        (define x.1 1)
        (begin))
      (begin
        (define x.2 2)
        x.1)))

  ;; The extensions: lambda binds and renames, applications recurse, and
  ;; unbound identifiers come out as bare global symbols.
  (check-equal? (expand '(lambda (x) (f x 1)))
                '(lambda (x.1) (f x.1 1)))

  ;; Hygiene across the extensions, both directions at once.  The template
  ;; binder `t` cannot capture the use-site argument `t` (they get distinct
  ;; identities), and the template's free `f` stays the global `f` even where
  ;; the use site has bound its own `f`.
  (check-equal?
   (expand
    '(let-syntax ([m (syntax-rules () [(_ a) (lambda (t) (f t a))])])
       (lambda (t) (m t))))
   '(lambda (t.1) (lambda (t.2) (f t.2 t.1))))
  (check-equal?
   (expand
    '(let-syntax ([m (syntax-rules () [(_ a) (f a)])])
       (let ([f 1]) (m f))))
   '(let ([f.1 1]) (f f.1)))

  ;; The paper's appendix B boundary cases, kept as executable documentation:
  ;; where alpha-renaming-style hygiene accounts (and the learner's H1-H4
  ;; reading of hygiene) stop being the right kind of story, though the
  ;; expander itself -- and the learner's expand-and-compare criterion --
  ;; remain correct.  If the learner ever admits definition contexts, these
  ;; two programs go straight into its adversarial test set.
  ;;
  ;; B.1: a use-site `define` binding CAN capture a macro-introduced
  ;; reference, when the macro is used in the very definition context where
  ;; it is defined.  The template's free `x` resolves to the binding that
  ;; its own expansion contributed.
  (check-equal?
   (expand
    '(block
      (define-syntax define-and-ref-x
        (syntax-rules () [(_ a) (begin (define a 5) x)]))
      (define-and-ref-x x)))
   '(block (begin) (begin (define x.1 5) x.1)))

  ;; B.2: the referent of a transcribed free identifier may be determined
  ;; only after transcription.  The template's free `x` resolves to the
  ;; (define x 6) that the expander has not even reached yet -- not to the
  ;; enclosing let's x.
  (check-equal?
   (expand
    '(let ([x 5])
       (block
        (define-syntax m
          (syntax-rules () [(_ a b) (define a (lambda (b) x))]))
        (m f x)
        (define x 6)
        (f 7))))
   '(let ([x.1 5])
      (block (begin)
             (define f.1 (lambda (x.3) x.2))
             (define x.2 6)
             (f.1 7))))

  ;; [extension] Ellipses, depth 1, trailing position: (a) plain splice at
  ;; 0/1/3 arguments -- the same macro clause covers every arity.
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (f x ...)])])
              (m)))
   '(f))
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (f x ...)])])
              (m 1)))
   '(f 1))
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (f x ...)])])
              (m 1 2 3)))
   '(f 1 2 3))

  ;; (b) structure under the ellipsis: each element is wrapped, not just
  ;; copied.
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (f (g x) ...)])])
              (m 1 2 3)))
   '(f (g 1) (g 2) (g 3)))

  ;; (c) a fixed prefix ahead of the ellipsis.
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ a x ...) (f a (g x) ...)])])
              (m 0 1 2 3)))
   '(f 0 (g 1) (g 2) (g 3)))

  ;; (d) hygiene under iteration: the template's own binder `t` must freshen
  ;; away from a `t` supplied, once per spliced argument, by the use site.
  ;; Both use-site `t`s share one identity (they're the same reference,
  ;; expanded twice), and the template `t` is a second, distinct identity.
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (lambda (t) (f t x ...))])])
              (lambda (t) (m t t))))
   '(lambda (t.1) (lambda (t.2) (f t.2 t.1 t.1))))

  ;; (e) a template binder INSIDE the ellipsis: each copy freshens its own
  ;; `t`, independently of the others -- not one shared binder split across
  ;; iterations.
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (f (lambda (t) (h t x)) ...)])])
              (m 1 2)))
   '(f (lambda (t.1) (h t.1 1)) (lambda (t.2) (h t.2 2))))

  ;; (f) H2 under iteration: the template's free `f`, repeated once per
  ;; spliced element, still resolves at the definition site even where the
  ;; use site has shadowed `f`.
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (f x ...)])])
              (let ([f 1]) (m f))))
   '(let ([f.1 1]) (f f.1)))

  ;; (g) depth errors, kept honest rather than silently mis-transcribed.
  ;; A depth-1 variable used outside of any ellipsis:
  (check-exn exn:fail?
             (lambda ()
               (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (f x)])])
                          (m 1 2)))))
  ;; An ellipsis whose sub-template has no depth-1 pattern variable at all --
  ;; here `a` is bound, but only at depth 0, so nothing controls how many
  ;; times to repeat.
  (check-exn exn:fail?
             (lambda ()
               (expand '(let-syntax ([m (syntax-rules () [(_ a x ...) (f a ...)])])
                          (m 1 2 3)))))

  ;; (h) zero-iteration edge: the ellipsis is legal to match against nothing,
  ;; and splices in nothing.
  (check-equal?
   (expand '(let-syntax ([m (syntax-rules () [(_ x ...) (f x ...)])])
              (m)))
   '(f)))
