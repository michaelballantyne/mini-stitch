#lang racket

;; ---------------------------------------------------------------------------
;; micro.rkt --- stitch, written as slowly and as plainly as possible
;; ---------------------------------------------------------------------------
;;
;; This module is the *executable specification* of mini-stitch.  It computes
;; the same abstractions as `search.rkt`, on the same corpora, by the same
;; definitions -- and it is far too slow to use on anything but a handful of
;; toy programs.  That is the point.  Everything here is written to be read.
;; When something in `search.rkt` looks like a trick, this file is where you
;; find out what the trick is a trick *for*.
;;
;; Read it as the paper's Sections 3 and 4 made executable:
;;
;;   Section 3   grow a partial abstraction `??` by filling one hole at a time
;;               with every production of the grammar, keeping whatever still
;;               matches the corpus somewhere        -> "Candidate enumeration"
;;   Section 4.4 to score a candidate, actually rewrite the corpus with it,
;;               using the bottom-up accept/reject dynamic program, and see how
;;               much smaller the corpus got          -> "Rewriting"
;;   Section 4.3 discard candidates that some other candidate provably beats
;;                                                    -> "Filters"
;;
;; HOW THIS DIFFERS FROM search.rkt (all of it deliberate)
;;
;;   * Programs are plain immutable trees and equality is `equal?`.  There is no
;;     hash-consed arena, so two occurrences of the same subtree are two
;;     unrelated pieces of memory and every question about them is asked twice.
;;   * Match locations are recomputed from scratch for every candidate, by
;;     structurally matching the candidate against every subtree of every
;;     program (the paper's LambdaUnify).  mini instead notes that a child
;;     pattern's matches are a subset of its parent's and never re-matches.
;;   * The worklist is a FIFO list, processed level by level.  There is no
;;     upper bound on utility, so there is no priority queue and no
;;     branch-and-bound: every candidate that matches anywhere is expanded.
;;   * There is no analytic utility formula.  `abstraction-utility` literally
;;     rewrites the corpus and subtracts costs.  So there is no multiuse
;;     accounting, no self-overlap correction, no used/unused location
;;     bookkeeping, and no `num-paths` weighting: the rewriter is the
;;     definition of utility, and the rest is arithmetic that follows from it.
;;   * The dominance-safe prunings are gone: no single-use pruning, no
;;     arity-zero priming (an arity-zero abstraction is just a candidate with no
;;     abstraction variables, and the enumeration reaches it like any other).
;;
;; WHAT IS KEPT, BECAUSE DROPPING IT WOULD CHANGE THE ANSWER
;;
;;   * zero-match pruning -- also what makes the enumeration finite;
;;   * a candidate must match in at least two distinct programs (stitch's
;;     default single-task pruning);
;;   * no de Bruijn variable may be free at the top of the body;
;;   * a location whose argument would capture a lambda *inside* the body is
;;     matched but never rewritten (the paper's &i indices, Appendix B);
;;   * the two Section 4.3 filters.  The argument-capture one is not actually
;;     dominance-safe (paper footnote 2): stitch optimizes subject to it, so
;;     without it micro could return a *better* abstraction than stitch and the
;;     two would disagree.  The redundant-argument one *is* dominance-safe and
;;     could be dropped; it is kept because it is two lines and it makes micro's
;;     tie-breaking agree with mini's more often.
;;
;; WHERE MICRO AND MINI DISAGREE
;;
;; On one class of corpus they do, and micro is right: when a candidate matches
;; at nested locations *and* uses a variable more than once, stitch's analytic
;; utility credits the inner saving once per occurrence, but rewriting the outer
;; location is exactly what deletes the duplicate occurrences.  stitch itself
;; detects this -- the real binary aborts on its rewrite cost-mismatch assertion
;; -- and mini reproduces stitch faithfully, so it inherits the over-count.  The
;; last test in this file is a two-program corpus that pins the whole story
;; down.  It is the clearest argument for having written the specification
;; twice.
;;
;; DATA DEFINITIONS
;;
;; A Term is one of
;;   (prim s)     a DSL primitive named by the symbol s
;;   (var i)      a de Bruijn variable $i, i >= 0
;;   (app f x)    an application; f and x are Terms
;;   (lam b)      a lambda; b is a Term
;; -- expr.rkt's node structs, but with Term children instead of arena indices.
;; A corpus is just a (Listof Term), one per program.
;;
;; A Pattern is a partial abstraction: a Term extended with
;;   'hole        an unfilled `??`
;;   (ivar i)     the abstraction variable #i
;; A Pattern with no holes is a finished abstraction body.  Abstraction
;; variables are always numbered 0, 1, ... in the order the search introduced
;; them, so a Pattern of arity k uses exactly #0 .. #(k-1).
;;
;; An Argument is what an abstraction variable receives at one match location:
;; a Term, possibly containing
;;   (captured d) the paper's &d -- a variable that pointed at the d-th lambda
;;                *inside* the abstraction body, counting from the innermost.
;; An argument containing a `captured` cannot be passed in from outside, so a
;; location that produces one is matched but cannot be rewritten.
;;
;; A Cost is an integer in expr.rkt's cost model.
;;
;; Parsing, printing and the cost constants come from expr.rkt, so micro and
;; mini read and write exactly the same corpora.
;; ---------------------------------------------------------------------------

(require "expr.rkt"
         racket/set)

(provide (struct-out captured)
         (struct-out learned)
         parse term->string term-cost
         micro-search micro-compress
         ;; exposed for the tests below and for anyone reading along
         lift match-pattern pattern-arity
         abstraction-utility rewrite-corpus)

(module+ test (require rackunit))

;; ---------------------------------------------------------------------------
;; Terms
;; ---------------------------------------------------------------------------

;; The paper's &d: a de Bruijn variable that has been lifted out of the lambda
;; that bound it.  d counts the crossed lambdas from the innermost one outwards.
(struct captured (i) #:transparent)

;; parse : String -> Term
;; Read one program in stitch's surface syntax.  expr.rkt owns the parser (and
;; its error messages); we immediately unfold its arena representation back into
;; an ordinary tree, which is the only representation this module knows.
(define (parse text)
  (define c (make-corpus))
  (define root (parse-program! c text))
  (let unfold ([i root])
    (define n (corpus-node c i))
    (cond [(app? n) (app (unfold (app-fun n)) (unfold (app-arg n)))]
          [(lam? n) (lam (unfold (lam-body n)))]
          [else n])))

;; term->string : Pattern -> String
;; Print a Term, an Argument or a Pattern in stitch's surface syntax, by folding
;; it into a scratch corpus and deferring to expr.rkt's printer -- so micro's
;; output is character-for-character mini's.  A hole prints as `??` and the
;; paper's &d prints as `&d`; neither can occur in a finished abstraction body.
(define scratch-corpus (make-corpus))
(define (term->string t)
  (define (intern t)
    (cond [(app? t) (add-node! scratch-corpus (app (intern (app-fun t))
                                                   (intern (app-arg t))))]
          [(lam? t) (add-node! scratch-corpus (lam (intern (lam-body t))))]
          [(eq? t 'hole) (add-node! scratch-corpus (prim '??))]
          [(captured? t)
           (add-node! scratch-corpus (prim (string->symbol
                                            (format "&~a" (captured-i t)))))]
          [else (add-node! scratch-corpus t)]))
  (expr->string scratch-corpus (intern t)))

;; term-cost : Pattern -> Cost
;; The cost model's size of a term.  Abstraction variables cost *nothing*: they
;; are parameters, not structure.  That is the paper's `cost_{alpha=0}`, and it
;; is the price stitch charges for the abstraction itself (its structure
;; penalty).  Programs contain no abstraction variables, so the same function
;; measures them.
(define (term-cost t)
  (cond [(app? t) (+ COST-APP (term-cost (app-fun t)) (term-cost (app-arg t)))]
        [(lam? t) (+ COST-LAM (term-cost (lam-body t)))]
        [(ivar? t) 0]
        [(var? t) COST-VAR]
        [(captured? t) COST-VAR]
        [(prim? t) COST-PRIM]
        [else (error 'term-cost "not a term: ~a" t)]))

;; corpus-cost : (Listof Term) -> Cost
;; What the whole corpus costs.  Compression is exactly the reduction of this
;; number.
(define (corpus-cost programs)
  (for/sum ([t (in-list programs)]) (term-cost t)))

(module+ test
  (test-case "parsing, printing and cost"
    (check-equal? (term->string (parse "(a a a)")) "(a a a)")
    (check-equal? (term->string (parse "((f x) y)")) "(f x y)")
    (check-equal? (term->string (parse "(lambda (+ $0 b))")) "(lam (+ $0 b))")
    ;; (a a a) = ((a a) a): two apps, three prims -- stitch's original_cost for
    ;; data/basic/simple1.json is 604 for the two programs together
    (check-equal? (term-cost (parse "(a a a)")) 302)
    (check-equal? (corpus-cost (map parse '("(a a a)" "(b b b)"))) 604)
    ;; abstraction variables are free of charge
    (check-equal? (term-cost (parse "(#0 #0 #0)")) 2)))

;; term-free-vars : Term -> (Setof Natural)
;; The de Bruijn indices that escape the term, expressed relative to its root.
;; Crossing a lambda drops 0 and decrements the rest.  A `captured` is not a de
;; Bruijn variable any more, so it contributes nothing.
(define (term-free-vars t)
  (cond [(var? t) (seteqv (var-i t))]
        [(app? t) (set-union (term-free-vars (app-fun t))
                             (term-free-vars (app-arg t)))]
        [(lam? t) (for/seteqv ([i (in-set (term-free-vars (lam-body t)))]
                               #:when (> i 0))
                    (sub1 i))]
        [else (seteqv)]))

;; subterms : Term -> (Listof Term)
;; Every subterm of t, itself included.  These are the places an abstraction
;; could possibly be used, and micro tries all of them for every candidate.
(define (subterms t)
  (cons t (cond [(app? t) (append (subterms (app-fun t)) (subterms (app-arg t)))]
                [(lam? t) (subterms (lam-body t))]
                [else '()])))

(module+ test
  (test-case "free variables and subterms"
    (check-equal? (term-free-vars (parse "(lam ($0 $1))")) (seteqv 0))
    (check-equal? (term-free-vars (parse "(f x)")) (seteqv))
    ;; (f x) has 3 subterms: itself, f, x
    (check-equal? (length (subterms (parse "(f x)"))) 3)
    ;; (a a a) = ((a a) a) has 5: the two apps and three copies of `a`
    (check-equal? (length (subterms (parse "(a a a)"))) 5)))

;; ---------------------------------------------------------------------------
;; Lifting an argument out of the body (the paper's &i)
;; ---------------------------------------------------------------------------
;;
;; When an abstraction variable sits under m of the *pattern's own* lambdas, the
;; subterm it matches is being lifted out past those m binders.  Its de Bruijn
;; indices are stated relative to where it sat, so they have to be restated
;; relative to the match location:
;;
;;   * a variable bound inside the subterm itself is untouched;
;;   * a free $d with d >= m referred to a binder above the match location and
;;     survives the lift as $(d-m);
;;   * a free $d with d < m referred to one of the crossed lambdas -- a lambda
;;     that lives *inside* the abstraction body.  There is no way to pass that
;;     in from outside, so it becomes the paper's &d, and any location whose
;;     arguments contain one cannot be rewritten.
;;
;; This is the same function as expr.rkt's `shift-arg`, with sentinel ivars
;; renamed to `captured` so that nothing can confuse them with the abstraction's
;; own variables.

;; lift : Term Natural -> Argument
;; The term as seen from m lambdas further out.
(define (lift t m)
  (let walk ([t t] [depth 0])          ; depth = the term's own binders crossed
    (cond
      [(var? t)
       (define d (- (var-i t) depth))  ; index relative to the term's root
       (cond [(< (var-i t) depth) t]   ; bound inside the term
             [(< d m) (captured d)]    ; points at a lambda inside the body
             [else (var (- (var-i t) m))])]
      [(app? t) (app (walk (app-fun t) depth) (walk (app-arg t) depth))]
      [(lam? t) (lam (walk (lam-body t) (add1 depth)))]
      [else t])))

;; captures? : Argument -> Boolean
;; Would this argument have to capture a lambda inside the abstraction body?
(define (captures? t)
  (cond [(captured? t) #t]
        [(app? t) (or (captures? (app-fun t)) (captures? (app-arg t)))]
        [(lam? t) (captures? (lam-body t))]
        [else #f]))

(module+ test
  (test-case "lifting arguments out from under lambdas"
    ;; nothing crossed: nothing happens
    (check-equal? (lift (parse "(g x)") 0) (parse "(g x)"))
    ;; a variable pointing above the match location is renumbered
    (check-equal? (lift (parse "$3") 1) (parse "$2"))
    (check-equal? (lift (parse "$3") 2) (parse "$1"))
    ;; a variable pointing at a crossed lambda becomes &d, counting the crossed
    ;; lambdas from the inside
    (check-equal? (lift (parse "$0") 1) (captured 0))
    (check-equal? (lift (parse "$0") 2) (captured 0))
    (check-equal? (lift (parse "$1") 2) (captured 1))
    (check-true (captures? (lift (parse "$0") 1)))
    (check-false (captures? (lift (parse "$3") 1)))
    ;; a variable bound inside the argument is untouched, one that escapes it is
    ;; not: in (lam ($0 $1 $2)) with m = 1, $0 is the argument's own binder,
    ;; $1 lands on the crossed lambda, $2 points above the match location
    (check-equal? (term->string (lift (parse "(lam ($0 $1 $2))") 1))
                  "(lam ($0 &0 $1))")))

;; ---------------------------------------------------------------------------
;; Matching
;; ---------------------------------------------------------------------------
;;
;; The paper's LambdaUnify, written out.  A pattern matches a term when they
;; agree constructor for constructor, holes match anything, and every use of an
;; abstraction variable sees the same argument -- where "the same" is judged
;; *after* lifting, since two uses at different depths inside the body see the
;; same argument only if they agree once both are stated relative to the match
;; location.

;; A Binding is a (binding Natural Argument Term Natural):
;;   index     which abstraction variable
;;   arg       the subterm as the abstraction would receive it (lifted)
;;   subterm   the subterm as it actually sits in the program; this is what the
;;             rewriter recurses into, since nested uses of the abstraction
;;             inside an argument still get rewritten
;;   depth     how many of the pattern's lambdas enclose this use
(struct binding (index arg subterm depth) #:transparent)

;; match-pattern : Pattern Term -> (U #f (Listof Binding))
;; Does the pattern match this term, and if so what does each of its abstraction
;; variables receive?  The bindings come back one per variable, sorted by index.
(define (match-pattern p t)
  ;; walk : Pattern Term Natural (Listof Binding) -> (U #f (Listof Binding))
  (define (walk p t depth bs)
    (cond
      [(eq? p 'hole) bs]                       ; a hole is undecided: anything
      [(ivar? p)
       (define new (binding (ivar-i p) (lift t depth) t depth))
       (define old (findf (lambda (b) (= (binding-index b) (ivar-i p))) bs))
       (cond [(not old) (cons new bs)]
             [(equal? (binding-arg old) (binding-arg new)) bs]
             [else #f])]                        ; one variable, two arguments
      [(app? p) (and (app? t)
                     (let ([bs (walk (app-fun p) (app-fun t) depth bs)])
                       (and bs (walk (app-arg p) (app-arg t) depth bs))))]
      [(lam? p) (and (lam? t) (walk (lam-body p) (lam-body t) (add1 depth) bs))]
      [else (and (equal? p t) bs)]))            ; two leaves
  (define bs (walk p t 0 '()))
  (and bs (sort bs < #:key binding-index)))

(module+ test
  (test-case "matching"
    ;; a concrete pattern matches only itself
    (check-equal? (match-pattern (parse "(f x)") (parse "(f x)")) '())
    (check-false (match-pattern (parse "(f x)") (parse "(f y)")))
    ;; #0 absorbs whatever is there
    (check-equal? (map binding-arg (match-pattern (parse "(f #0)") (parse "(f (g y))")))
                  (list (parse "(g y)")))
    ;; two uses of #0 must agree
    (check-not-false (match-pattern (parse "(f #0 #0)") (parse "(f a a)")))
    (check-false (match-pattern (parse "(f #0 #0)") (parse "(f a b)")))
    ;; two variables need not
    (check-equal? (length (match-pattern (parse "(f #0 #1)") (parse "(f a b)"))) 2)
    ;; a hole matches anything and binds nothing
    (check-equal? (match-pattern (app (prim 'f) 'hole) (parse "(f (g y))")) '())
    ;; an argument taken from under the pattern's own lambda is lifted, so a
    ;; variable bound by that lambda comes out as &0 and the location, while
    ;; matched, cannot be rewritten
    (define bs (match-pattern (parse "(lam (f #0))") (parse "(lam (f $0))")))
    (check-equal? (map binding-arg bs) (list (captured 0)))
    (check-true (captures? (binding-arg (car bs))))
    ;; ... and "the same argument" is judged after lifting: here #0 is used at
    ;; two different depths, and $1 under two lambdas is the same argument as
    ;; $0 under one
    (check-not-false (match-pattern (parse "(f (lam #0) (lam (lam #0)))")
                                    (parse "(f (lam $1) (lam (lam $2)))")))
    (check-false (match-pattern (parse "(f (lam #0) (lam (lam #0)))")
                                (parse "(f (lam $1) (lam (lam $1)))")))))

;; ---------------------------------------------------------------------------
;; Rewriting, and utility by rewriting
;; ---------------------------------------------------------------------------
;;
;; Section 4.4.  To rewrite a program with an abstraction we must choose, at
;; every node, whether to replace that node by a call to the abstraction.  The
;; choices interact: rewriting a node destroys any use of the abstraction that
;; overlapped it, except inside the arguments, which survive untouched.  So this
;; is a little dynamic program, computed bottom-up:
;;
;;   reject:  leave this node alone and rewrite the children as best we can
;;   accept:  emit (fn a1 ... ak) -- a new primitive plus k applications --
;;            and rewrite each argument as best we can
;;
;; and each node takes whichever is cheaper.  (The paper phrases the same DP in
;; terms of utility saved rather than cost remaining; the two differ by the
;; constant cost of the untouched subtree, so the argmax is the same.  Costs
;; read more directly here, because the whole point is to end up with a
;; rewritten corpus we can weigh.)
;;
;; Utility then needs no formula of its own:
;;
;;     utility(A) = cost(corpus) - cost(rewrite(corpus, A)) - cost(A)
;;
;; -- what we saved, less what the abstraction itself costs.  Everything mini
;; computes analytically (the multiuse bonus, the self-overlap correction, the
;; used/unused split, the per-location occurrence counts) is a consequence of
;; this one line.

;; rewrite-corpus : Pattern (Listof Term) Symbol -> (values (Listof Term) Cost)
;; Rewrite every program with the abstraction, naming it `name`, and also return
;; the cost the dynamic program predicts.  The two are checked against each
;; other by the caller: that check is the paper's Eq. 8 = Eq. 15.
(define (rewrite-corpus p programs name)
  (define arity (pattern-arity p))
  ;; The memo is not part of the specification -- it just stops the two ways of
  ;; reaching a node (as a child, and as an argument) from doubling the work at
  ;; every level.
  (define memo (make-hash))

  ;; best-cost : Term -> Cost ; the cheapest this subterm can be made
  (define (best-cost t)
    (hash-ref! memo t
               (lambda ()
                 (define a (accept-cost t))
                 (define r (reject-cost t))
                 (if (and a (< a r)) a r))))

  ;; reject-cost : Term -> Cost ; keep this node, rewrite below it
  (define (reject-cost t)
    (cond [(app? t) (+ COST-APP (best-cost (app-fun t)) (best-cost (app-arg t)))]
          [(lam? t) (+ COST-LAM (best-cost (lam-body t)))]
          [else (term-cost t)]))

  ;; accept-cost : Term -> (U Cost #f) ; replace this node by a call, or #f if
  ;; the abstraction does not match here, or matches but would have to capture
  (define (accept-cost t)
    (define bs (match-pattern p t))
    (and bs
         (not (ormap (lambda (b) (captures? (binding-arg b))) bs))
         (+ COST-NEW-PRIM
            (* COST-APP arity)
            (for/sum ([b (in-list bs)]) (best-cost (binding-subterm b))))))

  ;; rewrite : Term -> Term ; the top-down pass that performs the accepted
  ;; rewrites.  Ties go to rejecting, which is what stitch's greedy rewriter
  ;; does; either way the cost is the same.
  (define (rewrite t)
    (define a (accept-cost t))
    (cond
      [(and a (< a (reject-cost t)))
       (for/fold ([call (prim name)]) ([b (in-list (match-pattern p t))])
         (app call (lift (rewrite (binding-subterm b)) (binding-depth b))))]
      [(app? t) (app (rewrite (app-fun t)) (rewrite (app-arg t)))]
      [(lam? t) (lam (rewrite (lam-body t)))]
      [else t]))

  (values (map rewrite programs)
          (for/sum ([t (in-list programs)]) (best-cost t))))

;; abstraction-utility : Pattern (Listof Term) -> Cost
;; How much better off the corpus is for having this abstraction: the cost it
;; saves, less the cost of the abstraction body itself.
(define (abstraction-utility p programs)
  (define-values (rewritten predicted) (rewrite-corpus p programs 'fn))
  (define after (corpus-cost rewritten))
  (unless (= after predicted)
    (error 'abstraction-utility
           "the rewrite costs ~a but the dynamic program predicted ~a, for ~a"
           after predicted (term->string p)))
  (- (corpus-cost programs) after (term-cost p)))

(module+ test
  (test-case "utility by rewriting: stitch's data/basic/simple1.json"
    ;; (a a a) and (b b b) both become (fn_0 a) / (fn_0 b) under (#0 #0 #0).
    ;;   before: 302 + 302 = 604
    ;;   after:  201 + 201 = 402      (one app, the new primitive, the argument)
    ;;   body:   two apps = 2
    ;; so utility = 604 - 402 - 2 = 200, which is what the real binary reports.
    (define programs (map parse '("(a a a)" "(b b b)")))
    (define body (parse "(#0 #0 #0)"))
    (define-values (rewritten predicted) (rewrite-corpus body programs 'fn_0))
    (check-equal? (map term->string rewritten) '("(fn_0 a)" "(fn_0 b)"))
    (check-equal? predicted 402)
    (check-equal? (abstraction-utility body programs) 200))

  (test-case "utility by rewriting: an arity-zero abstraction"
    ;; data/basic/identical.json: naming the whole program is worth 304.
    (define programs (map parse '("(a b c d e)" "(a b c d e)")))
    (define body (parse "(a b c d e)"))
    (check-equal? (abstraction-utility body programs) 304)
    (define-values (rewritten _) (rewrite-corpus body programs 'fn_0))
    (check-equal? (map term->string rewritten) '("fn_0" "fn_0")))

  (test-case "the rewriter refuses a location that would capture"
    ;; (lam (f a #0)) matches both programs, but in the first one the argument
    ;; is $0 -- the variable bound by the pattern's own lambda.  That location
    ;; is matched and cannot be rewritten, so only the second one changes.
    (define programs (map parse '("(lam (f a $0))" "(lam (f a b))")))
    (define body (parse "(lam (f a #0))"))
    (define-values (rewritten _) (rewrite-corpus body programs 'fn_0))
    (check-equal? (map term->string rewritten)
                  '("(lam (f a $0))" "(fn_0 b)")))

  (test-case "the DP prefers the better of two overlapping uses"
    ;; (#0 #0) can be used at the root of (h (h x)) or at the inner (h x), but
    ;; not both: they overlap.  Rewriting the inner one and leaving the outer
    ;; alone costs 1 + 100 + (100 + 1 + 100) = 302; rewriting the outer one
    ;; costs 100 + 1 + cost((h x)) = 302 as well, so the tie goes to rejecting
    ;; the outer.  Either way the corpus shrinks by the same amount.
    (define programs (map parse '("(h (h x))" "(h (h y))")))
    (define body (parse "(#0 #0)"))
    (define-values (rewritten predicted) (rewrite-corpus body programs 'fn_0))
    (check-equal? (corpus-cost rewritten) predicted)))

;; ---------------------------------------------------------------------------
;; Candidate enumeration
;; ---------------------------------------------------------------------------
;;
;; Section 3.  Start from `??` and repeatedly fill one hole with every
;; production of the grammar.  micro always fills the *leftmost* hole; the
;; choice does not change the set of finished abstractions reached, only the
;; order they are reached in (and therefore which of two equally good ones is
;; found first).

;; pattern-arity : Pattern -> Natural
;; How many abstraction variables the pattern uses.  They are always numbered
;; 0 .. arity-1, so the largest index plus one is the count.
(define (pattern-arity p)
  (cond [(ivar? p) (add1 (ivar-i p))]
        [(app? p) (max (pattern-arity (app-fun p)) (pattern-arity (app-arg p)))]
        [(lam? p) (pattern-arity (lam-body p))]
        [else 0]))

;; hole-depth : Pattern -> (U Natural #f)
;; How many of the pattern's own lambdas enclose its leftmost hole, or #f if the
;; pattern has no holes.  The depth is what says which de Bruijn variables may
;; be written there: $0 .. $(depth-1) are bound by the body's own lambdas, and
;; anything beyond would be free at the top of the abstraction -- and an
;; abstraction with a free variable is not a function.
(define (hole-depth p)
  (let walk ([t p] [d 0])
    (cond [(eq? t 'hole) d]
          [(app? t) (or (walk (app-fun t) d) (walk (app-arg t) d))]
          [(lam? t) (walk (lam-body t) (add1 d))]
          [else #f])))

;; finished? : Pattern -> Boolean
;; Is this a complete abstraction body?
(define (finished? p) (not (hole-depth p)))

;; fill-hole : Pattern Pattern -> Pattern
;; Replace the leftmost hole by `piece`.
(define (fill-hole p piece)
  (define (walk t)
    (cond
      [(eq? t 'hole) (values piece #t)]
      [(app? t)
       (define-values (f filled?) (walk (app-fun t)))
       (cond [filled? (values (app f (app-arg t)) #t)]
             [else (define-values (x filled?) (walk (app-arg t)))
                   (values (app f x) filled?)])]
      [(lam? t)
       (define-values (b filled?) (walk (lam-body t)))
       (values (lam b) filled?)]
      [else (values t #f)]))
  (define-values (out filled?) (walk p))
  (unless filled? (error 'fill-hole "~a has no hole" (term->string p)))
  out)

;; corpus-prims : (Listof Term) -> (Listof Symbol)
;; Every primitive that appears anywhere in the corpus, sorted.  A production
;; naming any other primitive could never match, so the enumeration skips it.
(define (corpus-prims programs)
  (sort (set->list
         (for*/set ([t (in-list programs)]
                    [s (in-list (subterms t))]
                    #:when (prim? s))
           (prim-name s)))
        symbol<?))

;; expansions : Pattern (Listof Symbol) Natural -> (Listof Pattern)
;; Every production the grammar allows in the pattern's leftmost hole: an
;; application, a lambda, a de Bruijn variable the body's own lambdas bind, any
;; primitive of the corpus, a reuse of an abstraction variable already
;; introduced, or a fresh one if the arity limit allows.
(define (expansions p prims max-arity)
  (define depth (hole-depth p))
  (define arity (pattern-arity p))
  (append (list (app 'hole 'hole) (lam 'hole))
          (for/list ([i (in-range depth)]) (var i))
          (for/list ([s (in-list prims)]) (prim s))
          (for/list ([i (in-range (if (< arity max-arity) (add1 arity) arity))])
            (ivar i))))

(module+ test
  (test-case "holes, arity and expansion"
    (check-equal? (hole-depth 'hole) 0)
    (check-equal? (hole-depth (parse "(f x)")) #f)
    (check-true (finished? (parse "(#0 #0)")))
    ;; the leftmost hole of (?? (lam ??)) is the function position, at depth 0;
    ;; once that is filled the next one is inside the lambda, at depth 1
    (define p (app 'hole (lam 'hole)))
    (check-equal? (hole-depth p) 0)
    (check-equal? (hole-depth (fill-hole p (prim 'f))) 1)
    (check-equal? (term->string (fill-hole p (prim 'f))) "(f (lam ??))")
    (check-equal? (pattern-arity (parse "(#0 (#1 #0))")) 2)
    (check-equal? (pattern-arity 'hole) 0)
    ;; at depth 0 no de Bruijn variable is legal; at depth 1 exactly $0 is
    (check-equal? (map term->string (expansions p '(f) 1))
                  '("(?? ??)" "(lam ??)" "f" "#0"))
    (check-equal? (map term->string (expansions (fill-hole p (prim 'f)) '(f) 2))
                  '("(?? ??)" "(lam ??)" "$0" "f" "#0"))))

;; ---------------------------------------------------------------------------
;; Where a candidate matches, and the filters
;; ---------------------------------------------------------------------------

;; A Site is a (site Natural (Listof Binding)): one place the candidate matches,
;; recorded with which program it was found in.
(struct site (program bindings) #:transparent)

;; pattern-sites : Pattern (Listof Term) -> (Listof Site)
;; Every place in the corpus the candidate matches.  This is the from-scratch
;; matching micro is built around: mini gets the same answer by intersecting the
;; parent pattern's locations, and never walks the corpus again after the first
;; pass.
(define (pattern-sites p programs)
  (append*
   (for/list ([t (in-list programs)] [k (in-naturals)])
     (filter-map (lambda (s)
                   (define bs (match-pattern p s))
                   (and bs (site k bs)))
                 (subterms t)))))

;; site-arg : Site Natural -> Argument
;; What abstraction variable #i receives at this site.
(define (site-arg s i) (binding-arg (list-ref (site-bindings s) i)))

;; too-few-programs? : (Listof Site) -> Boolean
;; Is the candidate confined to a single program?  stitch discards those by
;; default: an abstraction is meant to capture something shared, and one that
;; only ever appears in one program tends to win on raw cost while being
;; useless.  This is a judgement about what we want, not a speed hack, so micro
;; keeps it.
(define (too-few-programs? sites)
  (< (set-count (for/seteqv ([s (in-list sites)]) (site-program s))) 2))

;; constant-argument? : (Listof Site) Natural -> Boolean
;; Does some abstraction variable below `arity` receive the very same argument
;; everywhere, with no free variables in it?  Then it is not really a parameter:
;; writing that argument into the body instead gives a smaller abstraction that
;; matches the same places.  This is the paper's argument capture (Section 4.3).
;;
;; It is the one filter here that is not strictly dominance-safe -- footnote 2
;; of the paper admits an abstraction used many times at a single location can
;; be worth more with the variable than without.  stitch optimizes subject to
;; it anyway, so micro must too, or micro would sometimes return something
;; better than stitch and the two would disagree.
;;
;; The free-variable proviso matters: an argument that mentions something bound
;; outside the match location cannot be written into the body at all.
(define (constant-argument? sites arity)
  (for/or ([i (in-range arity)])
    (define a (site-arg (car sites) i))
    (and (for/and ([s (in-list (cdr sites))]) (equal? (site-arg s i) a))
         (set-empty? (term-free-vars a)))))

;; duplicate-argument? : (Listof Site) Natural -> Boolean
;; Do two different abstraction variables below `arity` receive the same
;; argument at every site?  Then using one variable twice matches the same
;; places with a smaller arity and gets paid for the repetition, so it strictly
;; dominates (the paper's redundant argument elimination).  Unlike the filter
;; above this one really is safe to drop; it is kept because it costs two lines
;; and keeps micro's choices closer to mini's.
(define (duplicate-argument? sites arity)
  (for*/or ([i (in-range arity)]
            [j (in-range (add1 i) arity)])
    (for/and ([s (in-list sites)])
      (equal? (site-arg s i) (site-arg s j)))))

;; identity-body? : Pattern -> Boolean
;; Is the body nothing but an abstraction variable?  Then the abstraction is the
;; identity function: rewriting e into (fn e) only ever adds cost, so no corpus
;; would ever use it.  It has to be named explicitly because it is the one
;; candidate whose argument is the whole match location, which would send the
;; rewriter's dynamic program looking up the cost of a term in terms of itself.
(define (identity-body? p) (ivar? p))

;; reject? : Pattern (Listof Site) Natural -> Boolean
;; Should this candidate be thrown away rather than expanded or scored?
;;
;; `arity` is the arity of the candidate's PARENT, so a variable is not judged
;; until at least one further expansion has happened.  That is what stitch does
;; (it checks the parent's variables against the child's locations), and since
;; the argument-capture filter is not dominance-safe, checking it a step early
;; could genuinely change the answer.
(define (reject? p sites arity)
  (or (identity-body? p)
      (null? sites)                          ; matches nowhere: nothing to learn
      (too-few-programs? sites)
      (constant-argument? sites arity)
      (duplicate-argument? sites arity)))

(module+ test
  (test-case "sites and filters"
    (define programs (map parse '("(f a x)" "(f a y)")))
    ;; (f a ??) matches the root of both programs and nowhere else
    (define sites (pattern-sites (app (app (prim 'f) (prim 'a)) 'hole) programs))
    (check-equal? (length sites) 2)
    (check-equal? (map site-program sites) '(0 1))
    (check-false (too-few-programs? sites))
    ;; ... but (f a x) matches only the first, and is therefore rejected
    (check-true (too-few-programs? (pattern-sites (parse "(f a x)") programs)))
    (check-true (reject? (parse "(f a x)") (pattern-sites (parse "(f a x)") programs) 0))
    ;; the identity function is not an abstraction
    (check-true (reject? (ivar 0) (pattern-sites (ivar 0) programs) 0))
    ;; (#0 #1 ??): #0 sees `f` at both sites and `f` is closed, so #0 is not
    ;; really a parameter
    (define p (app (app (ivar 0) (ivar 1)) 'hole))
    (check-true (constant-argument? (pattern-sites p programs) 2))
    (check-false (duplicate-argument? (pattern-sites p programs) 2))
    ;; (f #0 #1) over (f a a) and (f b b): the two variables always agree
    (define q (parse "(f #0 #1)"))
    (define qsites (pattern-sites q (map parse '("(f a a)" "(f b b)"))))
    (check-true (duplicate-argument? qsites 2))
    (check-false (constant-argument? qsites 2))))

;; ---------------------------------------------------------------------------
;; The search
;; ---------------------------------------------------------------------------

;; micro-search : (Listof Term) [Natural] -> (U Pattern #f)
;; The abstraction body of at most `max-arity` arguments that saves the most, or
;; #f if none saves anything.  Breadth-first over the candidates, scoring every
;; finished one by rewriting the corpus with it; ties go to whichever was
;; reached first.
;;
;; The loop is this short because there is no bound to maintain, no queue to
;; prioritize and no incremental state to thread: every candidate is matched
;; against the corpus from scratch and every finished one is scored by rewriting
;; the corpus from scratch.  Nearly all of mini's machinery exists to avoid
;; doing exactly that.
(define (micro-search programs [max-arity 2])
  (define prims (corpus-prims programs))
  (let level ([frontier (list 'hole)] [best #f] [best-utility 0])
    (cond
      [(null? frontier) best]
      [else
       (define-values (next best* best-utility*)
         (for*/fold ([next '()] [best best] [best-utility best-utility])
                    ([p (in-list frontier)]
                     [piece (in-list (expansions p prims max-arity))])
           (define child (fill-hole p piece))
           (define sites (pattern-sites child programs))
           (cond
             [(reject? child sites (pattern-arity p))
              (values next best best-utility)]
             [(finished? child)
              (define u (abstraction-utility child programs))
              (if (> u best-utility)
                  (values next child u)
                  (values next best best-utility))]
             [else (values (cons child next) best best-utility)])))
       (level (reverse next) best* best-utility*)])))

;; ---------------------------------------------------------------------------
;; Iteration
;; ---------------------------------------------------------------------------

;; A Learned records one iteration's answer:
;;   body        the abstraction body, printed in stitch's format
;;   arity       how many arguments it takes
;;   utility     cost saved, less the cost of the abstraction itself
;;   compressive cost saved
;;   final-cost  what the corpus costs after rewriting
;;   programs    the rewritten corpus, which the next iteration learns from
(struct learned (body arity utility compressive final-cost programs)
  #:transparent)

;; micro-compress : (Listof String) [Natural] [Natural] -> (Listof Learned)
;; Learn a library, one abstraction at a time: search, rewrite the corpus with
;; the winner under the name fn_k, and search the result again.  Stops early
;; when nothing is worth abstracting any more.
(define (micro-compress program-texts [max-arity 2] [iterations 1])
  (let loop ([programs (map parse program-texts)] [k 0] [out '()])
    (cond
      [(= k iterations) (reverse out)]
      [else
       (define body (micro-search programs max-arity))
       (cond
         [(not body) (reverse out)]
         [else
          (define name (string->symbol (format "fn_~a" k)))
          (define-values (rewritten predicted) (rewrite-corpus body programs name))
          (define before (corpus-cost programs))
          (define after (corpus-cost rewritten))
          (loop rewritten (add1 k)
                (cons (learned (term->string body)
                               (pattern-arity body)
                               (- before after (term-cost body))
                               (- before after)
                               after
                               rewritten)
                      out))])])))

;; ---------------------------------------------------------------------------
;; micro against mini
;; ---------------------------------------------------------------------------
;;
;; The point of writing the specification twice.  For each corpus, micro's
;; slow-but-obvious answer must agree with search.rkt's fast one: the same
;; utility, the same corpus cost after rewriting, and -- when the winner is not
;; a tie -- the same body.
;;
;; Bodies are compared up to renaming the abstraction variables, because the two
;; searches introduce them in different orders (micro fills the leftmost hole,
;; mini the most recently created one), so the same abstraction can come out as
;; (f #0 #1) here and (f #1 #0) there.

(module+ test
  (require (prefix-in mini: "search.rkt"))

  ;; canonical : Pattern -> String
  ;; The body printed with its abstraction variables renumbered in order of
  ;; first appearance, left to right.
  (define (canonical p)
    (define seen '())
    (define (rename t)
      (cond [(ivar? t)
             (unless (memv (ivar-i t) seen) (set! seen (append seen (list (ivar-i t)))))
             (ivar (index-of seen (ivar-i t)))]
            [(app? t) (app (rename (app-fun t)) (rename (app-arg t)))]
            [(lam? t) (lam (rename (lam-body t)))]
            [else t]))
    (term->string (rename p)))

  ;; check-agrees : String (Listof String) [Natural] -> Void
  ;; Run both implementations on the same corpus and compare.
  (define (check-agrees name texts [max-arity 2])
    (define start (current-inexact-milliseconds))
    (define programs (map parse texts))
    (define micro (micro-search programs max-arity))
    (define elapsed (- (current-inexact-milliseconds) start))
    (define mini (mini:search (corpus-from-programs texts) max-arity))
    (cond
      [(not mini) (check-false micro (format "~a: mini found nothing" name))]
      [else
       (check-not-false micro (format "~a: micro found nothing" name))
       (when micro
         (define utility (abstraction-utility micro programs))
         (define-values (rewritten _) (rewrite-corpus micro programs 'fn_0))
         (check-equal? utility (mini:abstraction-utility mini)
                       (format "~a: utility" name))
         (check-equal? (- (corpus-cost programs) (corpus-cost rewritten))
                       (mini:abstraction-compressive mini)
                       (format "~a: cost after rewriting" name))
         (check-equal? (pattern-arity micro) (mini:abstraction-arity mini)
                       (format "~a: arity" name))
         (check-equal? (canonical micro) (canonical (parse (mini:abstraction-body mini)))
                       (format "~a: body" name))
         (printf "  ~a: ~a  utility ~a  (micro ~ams)\n"
                 name (term->string micro) utility (round elapsed)))]))

  (test-case "micro agrees with mini: stitch's smallest corpora"
    ;; every corpus here is a file in stitch/data/basic, named to match
    (check-agrees "simple1" '("(a a a)" "(b b b)"))
    (check-agrees "simple2" '("(a (lam (a a)))" "(b (lam (b b)))"))
    (check-agrees "identical" '("(a b c d e)" "(a b c d e)"))
    (check-agrees "simple_hof" '("(a (lam ((a $0) (a $0))))"
                                 "(a (lam (($0 b) ($0 b))))"))
    (check-agrees "tmp_minimal" '("(a b)" "(a c)"))
    (check-agrees "ctx_thread_2" '("(lam (lam (+ (a b c $0 f) (a b c $0 f))))"
                                   "(lam (lam (+ (a b z $0 f) (a b z $0 f))))"))
    (check-agrees "ctx_thread_1" '("(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))"
                                   "(A (lam (lam (+ (a b z $0 f) (a b z $0 f)))))"))
    ;; hof is the largest corpus micro can still be asked about; it is also the
    ;; one where the two searches number the abstraction variables differently,
    ;; which is what `canonical` is for
    (check-agrees "hof"
                  '("(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))"
                    "(lam (app (app cons (app dec $0)) (app (app cons (app dec $0)) empty)))"
                    "(lam (app (app cons (app (app plus $0) $0)) (app (app cons (app (app plus $0) $0)) empty)))")))

  (test-case "micro agrees with mini: hand-written corner cases"
    ;; an abstraction variable used twice: the multiuse bonus, which micro gets
    ;; for free because rewriting really does delete the second copy
    (check-agrees "multiuse" '("(f a a)" "(f b b)"))
    ;; a location that matches but would capture, so it cannot be rewritten
    (check-agrees "capture" '("(lam (g (f a b) $0))"
                              "(lam (g (f a c) $0))"
                              "(h (f a $0))"))
    ;; two arguments, one of them a function
    (check-agrees "two-args" '("(f (g x) (h y))" "(f (g z) (h w))"))
    ;; a lambda inside the body, with a variable under it
    (check-agrees "under-lam" '("(m (lam (p $0 q)) r)" "(m (lam (p $0 s)) r)"))
    ;; nothing shared: no abstraction at all
    (check-agrees "nothing" '("(a b)" "(c d)")))

  ;; check-against-stitch : String (Listof String) String Natural Cost Cost -> Void
  ;; The numbers on the right are transcribed from
  ;;   stitch/target/release/compress data/basic/NAME.json --max-arity=2 --iterations=1
  ;; so this ties micro to the real system and not just to mini.
  (define (check-against-stitch name texts body arity utility final-cost)
    (define programs (map parse texts))
    (define micro (micro-search programs 2))
    (check-not-false micro name)
    (when micro
      (define-values (rewritten _) (rewrite-corpus micro programs 'fn_0))
      (check-equal? (canonical micro) (canonical (parse body)) (format "~a: body" name))
      (check-equal? (pattern-arity micro) arity (format "~a: arity" name))
      (check-equal? (abstraction-utility micro programs) utility
                    (format "~a: utility" name))
      (check-equal? (corpus-cost rewritten) final-cost
                    (format "~a: final cost" name))))

  (test-case "micro agrees with the real stitch binary"
    (check-against-stitch "simple1" '("(a a a)" "(b b b)")
                          "(#0 #0 #0)" 1 200 402)
    (check-against-stitch "simple_hof" '("(a (lam ((a $0) (a $0))))"
                                         "(a (lam (($0 b) ($0 b))))")
                          "(#0 #0)" 1 201 808)
    (check-against-stitch "identical" '("(a b c d e)" "(a b c d e)")
                          "(a b c d e)" 0 304 200)
    (check-against-stitch "ctx_thread_1"
                          '("(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))"
                            "(A (lam (lam (+ (a b z $0 f) (a b z $0 f)))))")
                          "(A (lam (lam (+ (#0 $0 f) (#0 $0 f)))))" 1 1011 806)
    (check-against-stitch "hof"
                          '("(lam (app (app cons (app inc $0)) (app (app cons (app inc $0)) empty)))"
                            "(lam (app (app cons (app dec $0)) (app (app cons (app dec $0)) empty)))"
                            "(lam (app (app cons (app (app plus $0) $0)) (app (app cons (app (app plus $0) $0)) empty)))")
                          "(app (app cons (app #1 #0)) (app (app cons (app #1 #0)) empty))"
                          2 2320 1111))

  (test-case "two iterations, against the real stitch binary"
    ;; compress data/basic/ctx_thread_1.json --max-arity=2 --iterations=2 reports
    ;;   fn_0 arity 1 utility 1011 body (A (lam (lam (+ (#0 $0 f) (#0 $0 f)))))
    ;;   fn_1 arity 1 utility  101 body (fn_0 (a b #0))
    ;;   original_cost 2426  final_cost 402
    ;; Learning the second abstraction means searching the corpus the first one
    ;; rewrote, so this exercises the rewriter's output, not just its cost.
    (define steps
      (micro-compress '("(A (lam (lam (+ (a b c $0 f) (a b c $0 f)))))"
                        "(A (lam (lam (+ (a b z $0 f) (a b z $0 f)))))")
                      2 2))
    (check-equal? (map learned-body steps)
                  '("(A (lam (lam (+ (#0 $0 f) (#0 $0 f)))))" "(fn_0 (a b #0))"))
    (check-equal? (map learned-arity steps) '(1 1))
    (check-equal? (map learned-utility steps) '(1011 101))
    (check-equal? (map learned-final-cost steps) '(806 402))
    (check-equal? (map term->string (learned-programs (last steps)))
                  '("(fn_1 c)" "(fn_1 z)")))

  (test-case "where micro and stitch genuinely disagree, and why"
    ;; This is the one class of corpus on which micro's answer differs from
    ;; mini's -- and micro is the one that is right.  Real stitch says so
    ;; itself: on this corpus
    ;;
    ;;   stitch/target/release/compress FILE --max-arity=1 --iterations=1
    ;;
    ;; aborts on its own rewrite cost-mismatch assertion (rewriting.rs:145),
    ;;
    ;;   (#0 #0): ... finished: utility=605, compressive_utility=606, arity=1
    ;;     left: 705   right: 604
    ;;
    ;; where `left` is what stitch's own rewriter actually produced -- exactly
    ;; the 705 micro computes below -- and `right` is what its analytic utility
    ;; predicted.
    ;;
    ;; What goes wrong is the multiuse bonus meeting nested matches.  The first
    ;; program is X = (Y Y) with Y = (Z Z) and Z = (a a), so (#0 #0) matches at
    ;; X, at both copies of Y, and at all four copies of Z.  stitch credits Y's
    ;; saving twice, once per occurrence.  But rewriting X to (fn_0 Y) is
    ;; precisely the move that *deletes* one of the two copies of Y, so only one
    ;; of them is ever rewritten.  stitch's self-overlap correction does not
    ;; catch it, because it deliberately ignores overlaps that land at an
    ;; argument position -- the rewriter does descend into arguments, and
    ;; normally that is right; what it misses is that a multiply-used variable
    ;; keeps only one of them.
    ;;
    ;; micro cannot make this mistake, because it does not predict the saving:
    ;; it rewrites the corpus and weighs the result.
    (define programs (map parse '("(((a a) (a a)) ((a a) (a a)))" "((a f) (a f))")))
    (define body (parse "(#0 #0)"))
    (define-values (rewritten predicted) (rewrite-corpus body programs 'fn_0))
    (check-equal? (map term->string rewritten)
                  '("(fn_0 (fn_0 (a a)))" "(fn_0 (a f))"))
    (check-equal? (corpus-cost programs) 1210)
    (check-equal? (corpus-cost rewritten) 705)     ; stitch's own `left: 705`
    (check-equal? predicted 705)
    (check-equal? (abstraction-utility body programs) 504)
    ;; and that really is the best (#0 #0) can do here, so micro picks it
    (check-equal? (term->string (micro-search programs 1)) "(#0 #0)")
    ;; mini reproduces stitch's number, over-counting one copy of Y by 101
    (check-equal? (mini:abstraction-utility
                   (mini:search (corpus-from-programs
                                 '("(((a a) (a a)) ((a a) (a a)))" "((a f) (a f))"))
                                1))
                  605))

  (test-case "micro agrees with mini across two iterations"
    ;; The second iteration learns from the corpus the first one rewrote, so
    ;; feeding micro's rewritten programs to mini checks the rewriter too.
    (define texts '("(f (g a) (g a))" "(f (g b) (g b))" "(k (g a))"))
    (define steps (micro-compress texts 2 2))
    (check-equal? (length steps) 2)
    (for ([step (in-list steps)] [k (in-naturals)])
      (printf "  iteration ~a: ~a  utility ~a  cost ~a\n"
              k (learned-body step) (learned-utility step) (learned-final-cost step)))
    ;; each iteration's answer must be the one mini would have found on the
    ;; corpus that iteration started from
    (for/fold ([texts texts]) ([step (in-list steps)])
      (define mini (mini:search (corpus-from-programs texts) 2))
      (check-not-false mini)
      (when mini
        (check-equal? (learned-utility step) (mini:abstraction-utility mini))
        (check-equal? (learned-compressive step) (mini:abstraction-compressive mini)))
      (map term->string (learned-programs step)))
    (void)))
