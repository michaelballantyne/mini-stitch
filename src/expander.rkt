#lang racket

;; ---------------------------------------------------------------------------
;; expander.rkt --- the hygienic macro expander from "Hygienic macro expansion
;; explained" (Ballantyne and Rosenblatt), appendix C, minimally extended
;; ---------------------------------------------------------------------------
;;
;; This is the paper's model expander -- marks, scope graphs with disjoin
;; nodes, syntax-rules matching and transcription -- taken verbatim except for
;; three additions that macro-micro.rkt needs to use it as its semantic oracle
;; (see notes/2026-08-18-0323-syntax-rules-learning-design.md, addendum A):
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

;; This implementation of syntax-rules matching omits ellipses (as well as datatypes
;; not supported in the input language, such as vectors and boolean literals)
(define (match-top-pattern pat expr is-literal? literal-match?)
  ;; The `car` of the `expr` is the macro name, and in syntax-rules
  ;; the `car` of the `pat` stands for the macro name and is ignored.
  (match-pattern (cdr pat) (cdr expr) is-literal? literal-match?))

(define (match-pattern pat expr is-literal? literal-match?)
  (match* (pat expr)
    ;; literal-id
    [((? identifier? lit) (? identifier? target-id))
     #:when (is-literal? lit)
     (and (literal-match? lit target-id)
          (hash))]
    ;; pvar
    [((? identifier? pvar) stx)
     #:when (not (is-literal? pvar))
     (hash pvar stx)]
    ;; datum literal
    [((? number? v) v)
     (hash)]
    [((? boolean? v) v)                    ; [extension] #t / #f literals
     (hash)]
    ;; cons
    [(`(,pa . ,pd) `(,ea . ,ed))
     (let ([resa (match-pattern pa ea is-literal? literal-match?)])
       (and resa
            (let ([resd (match-pattern pd ed is-literal? literal-match?)])
              (and resd
                   (hash-union resa resd)))))]
    [('() '()) (hash)]
    [(_ _) #f]))

;; Syntax, PatternEnv, Mark -> Syntax
(define (transcribe tmpl penv def-mark)
  (match tmpl
    [(? identifier? pvar)
     #:when (hash-has-key? penv pvar)
     (hash-ref penv pvar)]
    [(? identifier? id)
     (mark-id id def-mark)]
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
             (f.1 7)))))
