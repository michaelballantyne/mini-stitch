#lang racket

;; ---------------------------------------------------------------------------
;; tests/for-set-test.rkt --- the north-star benchmark: learning for/set
;; ---------------------------------------------------------------------------
;;
;; notes/2026-08-18-0323-syntax-rules-learning-design.md, addendum F, names
;; the paper's for/set as the benchmark that exercises every mechanism the
;; design note describes in one macro: a template binder (the accumulator),
;; a binder-position pattern variable (the iteration variable), definition-
;; site free identifiers (sequence-fold, set-add, set), and a body pattern
;; variable reachable under both binders.
;;
;; In the object language (one-binder lambdas, no let-values/for forms), a use
;;   (for/set ([elem seq]) body)
;; expands to the curried
;;   (sequence-fold (lambda (v) (lambda (elem) (set-add v body))) (set) seq)
;; so this is the corpus: four hand-written expansions of that shape, varying
;; the accumulator/iteration-variable names, the body, and the sequence.
;; Every body mentions its own iteration variable, so the V1 template OF THIS
;; SHAPE -- a template binder in BOTH lambda positions, i.e. for/set itself --
;; is H1-blocked at every site: no V1 template can recover for/set itself.
;; (This is narrower than "no V1 template rewrites any site here": a
;; differently shaped, less-abstracting V1 template CAN still match --
;; `(sequence-fold ,pvar (set) ,pvar)`, swallowing each whole curried fold
;; opaquely into one pattern variable with no binder position at all, rewrites
;; every site and scores utility 202. It just is not for/set: it abstracts
;; the fold, not the loop.) V2's binder-position pattern variable is what
;; lets the search reach the for/set shape specifically. The fourth program
;; is the H2 exercise: it locally shadows set-add, so the learned macro --
;; whose set-add is the global -- must refuse that site outright.
;;
;;   raco test tests/for-set-test.rkt
;; ---------------------------------------------------------------------------

(require rackunit (file "../src/macro-micro.rkt"))

;; the corpus. p1-p3 share the shape and rewrite; p4's fold calls a LOCALLY
;; bound set-add, so it must survive untouched (H2).
(define p1 '(sequence-fold (lambda (v) (lambda (x) (set-add v (+ x n)))) (set) s))
(define p2 '(sequence-fold (lambda (acc) (lambda (y) (set-add acc (* y y)))) (set) (nums)))
(define p3 '(sequence-fold (lambda (w) (lambda (e) (set-add w (f e 1)))) (set) q))
(define p4 '(let ([set-add (lambda (p) p)])
              (sequence-fold (lambda (u) (lambda (z) (set-add u (g z)))) (set) r)))
(define programs (list p1 p2 p3 p4))

;; the target: the accumulator is a template binder (#0's uses are all tvar
;; 0), the iteration variable is a binder-position pvar (#0 the pattern
;; variable, unrelated numbering -- pvar and tvar indices are separate
;; namespaces), the body is pvar #1, the sequence is pvar #2.
;; NOTE for a future "unreferenced binder pvar" cleanup: %x0 (the binder
;; pvar, the iteration variable) is deliberately unreferenced IN THE TEMPLATE
;; -- its only reference lives in the argument each site supplies for %x1
;; (e.g. `(+ x n)` at p1) -- do not treat that as dead and delete it; it is
;; this benchmark's whole answer.
(define target
  `(sequence-fold (lambda (,(tvar 0))
                    (lambda (,(pvar 0)) (set-add ,(tvar 0) ,(pvar 1))))
                  (set) ,(pvar 2)))

(module+ test
  (test-case "macro-search recovers for/set"
    ;; measured wall time on this corpus (arity 3, all four programs,
    ;; including the H2-shadowed one): originally about 245 seconds on the
    ;; session's own container. [Updated 2026-08-18, adversarial-review
    ;; session, F15] best-candidate used to compute valid-sites for the
    ;; >=2-programs filter and then macro-utility -> rewrite-corpus
    ;; recomputed it all from scratch for every surviving candidate; F15
    ;; makes best-candidate compute each candidate's per-program (expanded .
    ;; sites) once and pass it through. Measured back-to-back in THIS
    ;; session's (evidently slower) container: pre-F15 5m58.6s (358.6s),
    ;; post-F15 5m19.6s (319.6s) -- a real but modest ~11% reduction here,
    ;; short of a full halving, because only the candidates that actually
    ;; clear the >=2-valid-oracle-programs filter were ever double-computed,
    ;; and on this corpus that is a minority of the ~25 skeleton-surviving
    ;; candidates. (The absolute number is container-dependent -- do not
    ;; compare 245s and 319.6s directly, they are different machines; compare
    ;; 358.6s to 319.6s, measured together.) Comfortably inside the ~10-minute
    ;; budget either way, so the corpus is kept whole -- no cutting was
    ;; needed. (macro-search enumerates naively and calls the model expander
    ;; per (candidate, site); this is the expected genre of slow.)
    (check-equal? (macro-search programs 3) target))

  (test-case "rewrite-corpus turns the matching sites into calls, and skips the shadowed one"
    (define-values (rewritten after) (rewrite-corpus '() 'm0 target programs))
    (check-equal? rewritten
                  (list '(m0 x (+ x n) s)
                        '(m0 y (* y y) (nums))
                        '(m0 e (f e 1) q)
                        ;; p4 unchanged: its set-add resolves to the let's
                        ;; local binding, not the macro's definition-site
                        ;; global, so the oracle refuses the site (H2)
                        p4))
    ;; utility by hand, from the cost model (100/atom, 1/form, pvars 0):
    ;;   corpus costs (atoms*100 + forms):
    ;;     p1: sequence-fold lambda v lambda x set-add v + x n set s
    ;;         = 12 atoms, 8 forms                          = 1208
    ;;     p2: sequence-fold lambda acc lambda y set-add acc * y y set nums
    ;;         = 12 atoms, 9 forms ((nums) is an extra form) = 1209
    ;;     p3: sequence-fold lambda w lambda e set-add w f e 1 set q
    ;;         = 12 atoms, 8 forms                           = 1208
    ;;     p4: let set-add lambda p p (the shadowing binding, 5 atoms, 5
    ;;         forms) + sequence-fold lambda u lambda z set-add u g z set r
    ;;         (11 atoms, 8 forms)                           = 1613
    ;;     total = 1208 + 1209 + 1208 + 1613 = 5238
    ;;   macro: template atoms sequence-fold, lambda, tvar0(binder),
    ;;     lambda, set-add, tvar0(reference), set = 7 atoms; forms: the
    ;;     call, the outer lambda, its binder list, the inner lambda, its
    ;;     binder list, the set-add call, (set) = 7 forms; the three pvars
    ;;     are free                                         = 700 + 7 = 707
    ;;   rewritten calls pay 1 (call form) + 100 (name) + each arg at cost:
    ;;     (m0 x (+ x n) s)        1+100+100+301+100 = 602
    ;;     (m0 y (* y y) (nums))   1+100+100+301+101 = 603
    ;;     (m0 e (f e 1) q)        1+100+100+301+100 = 602
    ;;     p4 unchanged                                = 1613
    ;;   after = 602+603+602+1613 = 3420
    ;;   utility = 5238 - 3420 - 707 = 1111
    (check-equal? after 3420)
    (check-equal? (macro-utility '() target programs) 1111))

  (test-case "valid-sites refuses p4 outright: the H2 shadowing exercise"
    ;; not merely "the site doesn't get rewritten" (rewrite-program could in
    ;; principle also leave a valid-but-not-worth-it site alone) -- the
    ;; oracle finds NO valid site at all in p4, because its set-add is the
    ;; let-bound local, not the macro's definition-site global
    (check-equal? (valid-sites '() 'm0 target p4 (expand-under '() p4))
                  (hash))))
