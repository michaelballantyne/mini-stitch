#lang racket

;; ---------------------------------------------------------------------------
;; micro.rkt --- what stitch computes, written as slowly and plainly as possible
;; ---------------------------------------------------------------------------
;;
;; The stitch library-learning system (Bowers et al., POPL 2023, "Top-Down
;; Synthesis for Library Learning") takes a corpus of lambda-calculus programs
;; and returns the one abstraction that compresses it most.  This module answers
;; the question "which abstraction is that?", and nothing else.  It is far too
;; slow to be asked about anything but a handful of toy programs.  That is the
;; point: everything here is written to be read.
;;
;; WHAT THIS IS, RELATIVE TO THE PAPER
;;
;; This file does NOT implement the paper's algorithm.  The algorithm the paper
;; presents (narrated in Section 3.1; the pseudocode is Algorithm 1 in Appendix
;; A) is a corpus-guided top-down search: a branch and bound with upper-bound
;; pruning, dominance pruning, and a best-first worklist, all built in from the
;; start.  Almost none of that is here -- "almost", because two small pieces of
;; the paper's corpus-guidance do appear below: hole productions are drawn from
;; the primitives that occur in the corpus rather than from a whole DSL grammar,
;; and candidates that match nowhere are dropped, which is Algorithm 1's
;; zero-usage pruning (Lemma 2).  The paper's naive-approach paragraph instead
;; stops expanding at a size bound (nothing larger than the largest program);
;; both rules terminate and neither changes the answer.
;;
;; What this file implements is the paper's *objective* -- the thing that
;; algorithm is an efficient way of reaching.  Find the abstraction of at most
;; `max-arity` variables that maximizes the compression utility of Eq. 8 and
;; saves something at all, subject to the semantic filters the paper's Section 6
;; adopts for all its experiments and real stitch applies by default:
;;
;;   * the abstraction must appear in at least two programs.  This is the
;;     paper's own rule (Section 6: DreamCoder "prunes the abstractions that
;;     are only useful in programs from a single task", each program its own
;;     task when no tasks are given), and it is a judgement about what we want,
;;     not a speed hack;
;;   * no de Bruijn variable may be free at the top of its body -- an
;;     abstraction with one is not a function;
;;   * the identity body, a bare abstraction variable, is not an abstraction;
;;   * argument capture (Section 4.3) is imposed, which is not a mere speed
;;     measure: by the paper's own footnote 2 it can rule out an abstraction
;;     that would have scored better, so it is part of WHAT stitch computes and
;;     not only of how fast.  Redundant argument elimination (the other Section
;;     4.3 filter) genuinely is dominance-safe and could be dropped without
;;     changing what is optimal; it is kept because it costs a few lines and it
;;     settles ties the same way stitch settles them.
;;
;; It reaches that objective by the enumeration the paper itself describes and
;; then discards -- "A Naive Approach", Section 3.1, the paragraph just before
;; pruning is introduced -- grow the partial abstraction `??` by filling one
;; hole at a time with every production that could still match, keep whatever
;; does match the corpus somewhere, and score every finished candidate.  And it
;; takes the paper's Section 4.4 rewriting dynamic program as the *definition*
;; of utility rather than as one way to compute it: to score a candidate, we
;; actually rewrite the corpus with it and see how much smaller the corpus got.
;;
;; Two deviations from the paper as written are deliberate, and both follow the
;; real implementation:
;;
;;   * the size charged for the abstraction itself is cost_{alpha=0}(A) --
;;     abstraction variables cost nothing -- where Eq. 8 with the paper's
;;     Section 6 constants would charge cost_alpha = 100 per variable.  This
;;     one is load-bearing: charged literally, the paper's own running example
;;     (Section 2) would be won by the arity-zero (+ 3), not by the
;;     lambda alpha beta. (+ 3 (* alpha beta)) the paper reports;
;;   * a location whose argument would have to capture a lambda *inside* the
;;     abstraction body still COUNTS as a match -- for the two-programs rule
;;     among other things -- and is only refused at rewriting time.  The
;;     paper instead discards such locations from Matches entirely (Section 3,
;;     "Match Locations": mappings binding &i indices to abstraction variables
;;     are dropped).  The &i indices themselves are Section 3's (Fig. 4-5);
;;     this file's `captured` struct plays their role.
;;
;; So: this file pins down what the answer IS.  How to compute it fast is
;; somebody else's problem.  On one family of corpora -- a multiply-used
;; variable whose argument contains further matches of the same pattern --
;; real stitch's analytic utility accounting disagrees with what rewriting
;; actually achieves, and scoring-by-rewriting is the side that is right;
;; see the regression test in tests/micro-test.rkt.
;;
;; DATA DEFINITIONS
;;
;; A Term is one of
;;   (prim s)     a DSL primitive named by the symbol s
;;   (var i)      a de Bruijn variable $i, i >= 0
;;   (app f x)    an application; f and x are Terms
;;   (lam b)      a lambda; b is a Term
;; -- ast.rkt's node structs, with Term children.  A corpus is just a
;; (Listof Term), one per program.
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
;; A Cost is an integer in ast.rkt's cost model.
;; ---------------------------------------------------------------------------

(require "ast.rkt"
         racket/set)

(provide (struct-out captured)
         (struct-out learned)
         term-cost corpus-cost
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
        [else (error 'term-cost "not a term: ~s" t)]))

;; corpus-cost : (Listof Term) -> Cost
;; What the whole corpus costs.  Compression is exactly the reduction of this
;; number.
(define (corpus-cost programs)
  (for/sum ([t (in-list programs)]) (term-cost t)))

(module+ test
  (test-case "the cost of a term"
    (define A (prim 'a))
    (define B (prim 'b))
    ;; (a a a) is ((a a) a): two apps and three prims. 
    (check-equal? (term-cost (app (app A A) A)) 302)
    ;; real stitch reports original_cost 604 for this two-program corpus
    (check-equal? (corpus-cost (list (app (app A A) A) (app (app B B) B))) 604)
    ;; abstraction variables are free of charge, so (#0 #0 #0) costs two apps
    (check-equal? (term-cost (app (app (ivar 0) (ivar 0)) (ivar 0))) 2)))

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
    ;; in (lam ($0 $1)) the $0 is bound by the lambda and the $1 escapes as $0
    (check-equal? (term-free-vars (lam (app (var 0) (var 1)))) (seteqv 0))
    (check-equal? (term-free-vars (app (prim 'f) (prim 'x))) (seteqv))
    ;; (f x) has 3 subterms: itself, f, x
    (check-equal? (length (subterms (app (prim 'f) (prim 'x)))) 3)
    ;; (a a a) = ((a a) a) has 5: the two apps and three copies of `a`
    (define A (prim 'a))
    (check-equal? (length (subterms (app (app A A) A))) 5)))

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
    (define gx (app (prim 'g) (prim 'x)))
    (check-equal? (lift gx 0) gx)
    ;; a variable pointing above the match location is renumbered
    (check-equal? (lift (var 3) 1) (var 2))
    (check-equal? (lift (var 3) 2) (var 1))
    ;; a variable pointing at a crossed lambda becomes &d, counting the crossed
    ;; lambdas from the inside
    (check-equal? (lift (var 0) 1) (captured 0))
    (check-equal? (lift (var 0) 2) (captured 0))
    (check-equal? (lift (var 1) 2) (captured 1))
    (check-true (captures? (lift (var 0) 1)))
    (check-false (captures? (lift (var 3) 1)))
    ;; a variable bound inside the argument is untouched, one that escapes it is
    ;; not: in (lam ($0 $1 $2)) with m = 1, $0 is the argument's own binder,
    ;; $1 lands on the crossed lambda, and $2 points above the match location,
    ;; so the lift produces (lam ($0 &0 $1))
    (check-equal? (lift (lam (app (app (var 0) (var 1)) (var 2))) 1)
                  (lam (app (app (var 0) (captured 0)) (var 1))))))

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
    (define F (prim 'f))
    (define A (prim 'a))
    (define B (prim 'b))
    (define fx (app F (prim 'x)))
    (define gy (app (prim 'g) (prim 'y)))
    ;; a concrete pattern matches only itself
    (check-equal? (match-pattern fx fx) '())
    (check-false (match-pattern fx (app F (prim 'y))))
    ;; (f #0) against (f (g y)): #0 absorbs whatever is there
    (check-equal? (map binding-arg (match-pattern (app F (ivar 0)) (app F gy)))
                  (list gy))
    ;; two uses of #0 must agree: (f #0 #0) matches (f a a) but not (f a b)
    (define ff (app (app F (ivar 0)) (ivar 0)))
    (check-not-false (match-pattern ff (app (app F A) A)))
    (check-false (match-pattern ff (app (app F A) B)))
    ;; two variables need not
    (check-equal? (length (match-pattern (app (app F (ivar 0)) (ivar 1))
                                         (app (app F A) B)))
                  2)
    ;; a hole matches anything and binds nothing
    (check-equal? (match-pattern (app F 'hole) (app F gy)) '())
    ;; an argument taken from under the pattern's own lambda is lifted, so in
    ;; (lam (f #0)) against (lam (f $0)) the argument comes out as &0 and the
    ;; location, while matched, cannot be rewritten
    (define bs (match-pattern (lam (app F (ivar 0))) (lam (app F (var 0)))))
    (check-equal? (map binding-arg bs) (list (captured 0)))
    (check-true (captures? (binding-arg (car bs))))
    ;; ... and "the same argument" is judged after lifting: in
    ;; (f (lam #0) (lam (lam #0))) the variable #0 is used at two different
    ;; depths, and $1 under two lambdas is the same argument as $0 under one
    (define two-depths (app (app F (lam (ivar 0))) (lam (lam (ivar 0)))))
    (check-not-false (match-pattern two-depths
                                    (app (app F (lam (var 1)))
                                         (lam (lam (var 2))))))
    (check-false (match-pattern two-depths
                                (app (app F (lam (var 1)))
                                     (lam (lam (var 1))))))))

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
;; -- what we saved, less what the abstraction itself costs.  The multiuse
;; bonus, the correction for a pattern that overlaps itself, the split between
;; locations that are rewritten and locations that are merely matched: none of
;; them are computed here, because all of them are consequences of this one
;; line.

;; rewrite-corpus : Pattern (Listof Term) Symbol -> (values (Listof Term) Cost)
;; Rewrite every program with the abstraction, naming it `name`, and also return
;; the cost the dynamic program predicts.  The two are checked against each
;; other by the caller: that check is the paper's Eq. 8 = Eq. 15.
(define (rewrite-corpus p programs name)
  (define arity (pattern-arity p))
  ;; This table is not an optimization bolted onto the dynamic program -- it
  ;; IS the dynamic program.  The paper's Eq. 15 is stated bottom-up, one
  ;; verdict per subtree; memoizing the top-down recursion computes the same
  ;; table.  Without it the recursion is exponential on self-similar programs
  ;; (accept descends into the argument, reject into both children).
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
           "the rewrite costs ~a but the dynamic program predicted ~a, for ~s"
           after predicted p))
  (- (corpus-cost programs) after (term-cost p)))

(module+ test
  (test-case "utility by rewriting: an abstraction with one argument"
    ;; The corpus (a a a) and (b b b), which is stitch's data/basic/simple1.
    ;; Both programs become a call to (#0 #0 #0):
    ;;   before: 302 + 302 = 604
    ;;   after:  201 + 201 = 402      (one app, the new primitive, the argument)
    ;;   body:   two apps = 2
    ;; so utility = 604 - 402 - 2 = 200, which is what the real binary reports.
    (define A (prim 'a))
    (define B (prim 'b))
    (define programs (list (app (app A A) A) (app (app B B) B)))
    (define body (app (app (ivar 0) (ivar 0)) (ivar 0)))
    (define-values (rewritten predicted) (rewrite-corpus body programs 'fn_0))
    (check-equal? rewritten (list (app (prim 'fn_0) A) (app (prim 'fn_0) B)))
    (check-equal? predicted 402)
    (check-equal? (abstraction-utility body programs) 200))

  (test-case "utility by rewriting: an arity-zero abstraction"
    ;; Two copies of (a b c d e), stitch's data/basic/identical: naming the whole
    ;; program takes each of them down to a bare primitive, and is worth 304.
    (define abcde
      (app (app (app (app (prim 'a) (prim 'b)) (prim 'c)) (prim 'd)) (prim 'e)))
    (define programs (list abcde abcde))
    (check-equal? (abstraction-utility abcde programs) 304)
    (define-values (rewritten _) (rewrite-corpus abcde programs 'fn_0))
    (check-equal? rewritten (list (prim 'fn_0) (prim 'fn_0))))

  (test-case "the rewriter refuses a location that would capture"
    ;; (lam (f a #0)) matches both programs, but in the first one the argument
    ;; is $0 -- the variable bound by the pattern's own lambda.  That location
    ;; is matched and cannot be rewritten, so only the second one changes.
    (define fa (app (prim 'f) (prim 'a)))
    (define p0 (lam (app fa (var 0))))               ; (lam (f a $0))
    (define p1 (lam (app fa (prim 'b))))             ; (lam (f a b))
    (define body (lam (app fa (ivar 0))))            ; (lam (f a #0))
    (define-values (rewritten _) (rewrite-corpus body (list p0 p1) 'fn_0))
    (check-equal? rewritten (list p0 (app (prim 'fn_0) (prim 'b)))))

  (test-case "the DP prefers the better of two overlapping uses"
    ;; (#0 #0) can be used at the root of (h (h x)) or at the inner (h x), but
    ;; not both: they overlap.  Rewriting the inner one and leaving the outer
    ;; alone costs 1 + 100 + (100 + 1 + 100) = 302; rewriting the outer one
    ;; costs 100 + 1 + cost((h x)) = 302 as well, so the tie goes to rejecting
    ;; the outer.  Either way the corpus shrinks by the same amount.
    (define H (prim 'h))
    (define programs (list (app H (app H (prim 'x))) (app H (app H (prim 'y)))))
    (define body (app (ivar 0) (ivar 0)))
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
  (unless filled? (error 'fill-hole "~s has no hole" p))
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
    (check-equal? (hole-depth (app (prim 'f) (prim 'x))) #f)
    (check-true (finished? (app (ivar 0) (ivar 0))))
    ;; the leftmost hole of (?? (lam ??)) is the function position, at depth 0;
    ;; once that is filled the next one is inside the lambda, at depth 1
    (define p (app 'hole (lam 'hole)))
    (check-equal? (hole-depth p) 0)
    (check-equal? (fill-hole p (prim 'f)) (app (prim 'f) (lam 'hole)))
    (check-equal? (hole-depth (fill-hole p (prim 'f))) 1)
    ;; (#0 (#1 #0)) uses two variables
    (check-equal? (pattern-arity (app (ivar 0) (app (ivar 1) (ivar 0)))) 2)
    (check-equal? (pattern-arity 'hole) 0)
    ;; at depth 0 no de Bruijn variable is legal; at depth 1 exactly $0 is
    (check-equal? (expansions p '(f) 1)
                  (list (app 'hole 'hole) (lam 'hole) (prim 'f) (ivar 0)))
    (check-equal? (expansions (fill-hole p (prim 'f)) '(f) 2)
                  (list (app 'hole 'hole) (lam 'hole)
                        (var 0) (prim 'f) (ivar 0)))))

;; ---------------------------------------------------------------------------
;; Where a candidate matches, and the filters
;; ---------------------------------------------------------------------------

;; A Site is a (site Natural (Listof Binding)): one place the candidate matches,
;; recorded with which program it was found in.
(struct site (program bindings) #:transparent)

;; pattern-sites : Pattern (Listof Term) -> (Listof Site)
;; Every place in the corpus the candidate matches, found by matching the
;; candidate against every subterm of every program, from scratch, every time.
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
;; be worth more with the variable than without.  stitch optimizes subject to it
;; anyway, so the filter is part of the objective and not of the search.
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
;; above this one really is safe to drop; it is kept because it costs a few
;; lines and it settles ties the way stitch settles them.
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
    (define F (prim 'f))
    (define A (prim 'a))
    (define B (prim 'b))
    (define fa (app F A))
    ;; the corpus (f a x) and (f a y)
    (define fax (app fa (prim 'x)))
    (define fay (app fa (prim 'y)))
    (define programs (list fax fay))
    ;; (f a ??) matches the root of both programs and nowhere else
    (define sites (pattern-sites (app fa 'hole) programs))
    (check-equal? (length sites) 2)
    (check-equal? (map site-program sites) '(0 1))
    (check-false (too-few-programs? sites))
    ;; ... but (f a x) matches only the first, and is therefore rejected
    (check-true (too-few-programs? (pattern-sites fax programs)))
    (check-true (reject? fax (pattern-sites fax programs) 0))
    ;; the identity function is not an abstraction
    (check-true (reject? (ivar 0) (pattern-sites (ivar 0) programs) 0))
    ;; (#0 #1 ??): #0 sees `f` at both sites and `f` is closed, so #0 is not
    ;; really a parameter
    (define p (app (app (ivar 0) (ivar 1)) 'hole))
    (check-true (constant-argument? (pattern-sites p programs) 2))
    (check-false (duplicate-argument? (pattern-sites p programs) 2))
    ;; (f #0 #1) over (f a a) and (f b b): the two variables always agree
    (define q (app (app F (ivar 0)) (ivar 1)))
    (define qsites (pattern-sites q (list (app (app F A) A) (app (app F B) B))))
    (check-true (duplicate-argument? qsites 2))
    (check-false (constant-argument? qsites 2))))

;; ---------------------------------------------------------------------------
;; The search
;; ---------------------------------------------------------------------------

;; surviving-children : Pattern (Listof Symbol) Natural (Listof Term)
;;                      -> (Listof Pattern)
;; Every way to fill one hole of `p` that survives the filters: expand the
;; hole with each production, match each result against the corpus from
;; scratch, and keep the children that could still be -- or already are -- a
;; worthwhile abstraction.  This is the same job the paper gives its
;; Expansions procedure, done the slow way: nothing is carried over from `p`,
;; and the only judgments are the semantic filters of `reject?`.
(define (surviving-children p prims max-arity programs)
  (for*/list ([piece (in-list (expansions p prims max-arity))]
              [child (in-value (fill-hole p piece))]
              #:unless (reject? child (pattern-sites child programs)
                                (pattern-arity p)))
    child))

(module+ test
  (test-case "surviving-children: generate, match, filter, in one step"
    (define F (prim 'f)) (define A (prim 'a)) (define B (prim 'b))
    (define X (prim 'x))
    ;; corpus: (f a x) and (f b x)
    (define programs (list (app (app F A) X) (app (app F B) X)))
    (define kids (surviving-children 'hole (corpus-prims programs) 2 programs))
    ;; the application skeleton, f, and x match both programs and survive;
    ;; a and b match only one program each; (lam ??) matches nothing; a fresh
    ;; abstraction variable is the identity body.  So exactly three survive.
    (check-true (and (member (app 'hole 'hole) kids) #t))
    (check-true (and (member F kids) #t))
    (check-true (and (member X kids) #t))
    (check-equal? (length kids) 3)))

;; all-candidates : (Listof Term) Natural -> (Listof Pattern)
;; Every finished candidate the enumeration reaches, in the order it reaches
;; them: level by level from the single hole, each level the surviving
;; children of the last.  There is nothing to maintain between levels -- no
;; bound on what a pattern might grow into, no priority, no state carried from
;; a pattern to its children.
(define (all-candidates programs max-arity)
  (define prims (corpus-prims programs))
  (let level ([frontier (list 'hole)] [found '()])
    (cond
      [(null? frontier) found]
      [else
       (define children
         (append-map (lambda (p) (surviving-children p prims max-arity programs))
                     frontier))
       (define-values (done open) (partition finished? children))
       (level open (append found done))])))

;; best-candidate : (Listof Pattern) (Listof Term) -> (U Pattern #f)
;; The candidate that saves the most, scoring each once by rewriting the
;; corpus with it -- the first such, when utilities tie -- or #f if none
;; saves anything at all.
(define (best-candidate candidates programs)
  (define scored
    (for/list ([c (in-list candidates)])
      (cons c (abstraction-utility c programs))))
  (define best (and (pair? scored) (argmax cdr scored)))
  (and best (positive? (cdr best)) (car best)))

(module+ test
  (test-case "all-candidates and best-candidate"
    (define A (prim 'a)) (define B (prim 'b))
    ;; corpus: (a a a) and (b b b)
    (define programs (list (app (app A A) A) (app (app B B) B)))
    (define cs (all-candidates programs 2))
    (check-true (andmap finished? cs))
    ;; the known winner is among them, and wins
    (define w (app (app (ivar 0) (ivar 0)) (ivar 0)))
    (check-true (and (member w cs) #t))
    (check-equal? (best-candidate cs programs) w)
    (check-false (best-candidate '() programs))))

;; micro-search : (Listof Term) [Natural] -> (U Pattern #f)
;; The abstraction body of at most `max-arity` arguments that saves the most,
;; or #f if none saves anything: enumerate every candidate, then take the best.
(define (micro-search programs [max-arity 2])
  (best-candidate (all-candidates programs max-arity) programs))

;; ---------------------------------------------------------------------------
;; Iteration
;; ---------------------------------------------------------------------------

;; A Learned records one iteration's answer:
;;   body        the abstraction body, a finished Pattern
;;   arity       how many arguments it takes
;;   utility     cost saved, less the cost of the abstraction itself
;;   compressive cost saved
;;   final-cost  what the corpus costs after rewriting
;;   programs    the rewritten corpus, which the next iteration learns from
(struct learned (body arity utility compressive final-cost programs)
  #:transparent)

;; learn-one : (Listof Term) Natural Symbol -> (U Learned #f)
;; One whole iteration: find the best abstraction, rewrite the corpus with it
;; under `name`, and record what happened -- or #f if nothing saves anything.
(define (learn-one programs max-arity name)
  (define body (micro-search programs max-arity))
  (cond
    [(not body) #f]
    [else
     (define-values (rewritten predicted) (rewrite-corpus body programs name))
     (define before (corpus-cost programs))
     (define after (corpus-cost rewritten))
     (unless (= predicted after)
       (error 'learn-one "the DP promised cost ~a; rewriting gave ~a"
              predicted after))
     (learned body (pattern-arity body)
              (- before after (term-cost body)) (- before after)
              after rewritten)]))

(module+ test
  (test-case "learn-one records one iteration"
    (define A (prim 'a)) (define B (prim 'b))
    (define l (learn-one (list (app (app A A) A) (app (app B B) B)) 2 'fn_0))
    (check-equal? (learned-arity l) 1)
    (check-equal? (learned-utility l) 200)      ; 604 -> 402, body costs 2
    (check-equal? (learned-final-cost l) 402)
    ;; each program is now one call: (fn_0 a) and (fn_0 b)
    (check-equal? (learned-programs l)
                  (list (app (prim 'fn_0) A) (app (prim 'fn_0) B)))
    ;; and a corpus with nothing shared learns nothing
    (check-false (learn-one (list A B) 2 'fn_0))))

;; micro-compress : (Listof Term) [Natural] [Natural] -> (Listof Learned)
;; Learn a library, one abstraction at a time: learn fn_0, rewrite, learn fn_1
;; from the rewritten corpus, and so on.  Stops early when nothing more is
;; worth abstracting.
(define (micro-compress programs [max-arity 2] [iterations 1])
  (let loop ([programs programs] [k 0] [out '()])
    (define l (and (< k iterations)
                   (learn-one programs max-arity
                              (string->symbol (format "fn_~a" k)))))
    (if l
        (loop (learned-programs l) (add1 k) (cons l out))
        (reverse out))))
