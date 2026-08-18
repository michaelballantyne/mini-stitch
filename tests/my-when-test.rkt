#lang racket

;; ---------------------------------------------------------------------------
;; tests/my-when-test.rkt --- V2 and ellipses TOGETHER: a my-each hybrid
;; ---------------------------------------------------------------------------
;;
;; tests/for-set-test.rkt is the north star for V2 (a binder-position pattern
;; variable) alone; the ellipses-design note's own end-to-end benchmark (in
;; src/macro-micro.rkt's "Ellipses (stage 2)" module+ test) is the north star
;; for ellipses alone.  Neither exercises the other.  This is the first corpus
;; that needs BOTH at once: a my-when/for-each hybrid,
;;
;;     (define-syntax-rule (m v e xs ...) ((lambda (v) (seq xs ...)) e))
;;
;; i.e. "apply a one-argument procedure whose body is a variadic sequence".
;; In the learner's template representation (max-arity 2: #0 the binder, #1
;; the applied argument):
;;
;;     ((lambda (,(pvar 0)) (seq ,(ellip (svar)))) ,(pvar 1))
;;
;; #0 is a BINDER-POSITION pattern variable (V2): every corpus body mentions
;; its own bound variable somewhere, so the V1 analog (a template binder in
;; #0's place) is H1-blocked at every site -- checked explicitly below, per
;; program, the way for-set-test's own review correction insisted on.  `seq`
;; is a definition-site free identifier: it never varies across the corpus
;; (only its arguments do), giving H2 a foothold -- exercised by the fourth
;; program, which locally shadows `seq` and must survive untouched.  The
;; trailing `xs ...` is the ellipsis: the corpus's three real programs use
;; three DIFFERENT sequence lengths (2, 1, 3), so no fixed-arity template can
;; ever cover two of them -- only the ellipsis-headed template can, exactly
;; the shape of the "ellipses: end-to-end benchmark" test in macro-micro.rkt,
;; now combined with a binder-position pvar for the first time.
;;
;; A SURPRISING-WINNER STORY (the task's own contingency, realized twice)
;;
;; The design brief's initial corpus sketch -- reusing a `print` head at the
;; front of two bodies, an `h` head at the tail of two others, plain small
;; integers everywhere -- was tried FIRST, in a scratch script, exactly as
;; instructed, and did NOT produce the target above. It produced two
;; different surprises instead, each genuinely informative about how this
;; search works and worth recording rather than silently patching away:
;;
;;   1. With all four programs present, the winner abstracted `seq` itself
;;      into a PATTERN VARIABLE (not a fixed identifier) and used a TEMPLATE
;;      BINDER (V1, tvar) for the lambda's parameter -- utility 608 against
;;      the intended target's utility of 5 on that same corpus. Once `print`
;;      recurs verbatim as the first body element of two programs, V1 is no
;;      longer H1-blocked there: the reference to the bound variable inside
;;      `(print x)` can be baked directly into the TEMPLATE (as a tvar
;;      reference sitting next to a template-authored `print`), rather than
;;      arriving as a site-supplied argument -- H1 only bites when an
;;      argument (something the template receives opaquely, spliced back in
;;      verbatim) mentions the binder, and here nothing was received
;;      opaquely; the whole `(print v)` shape was absorbed by the template.
;;      Separately, turning `seq` into a pattern variable sidesteps H2
;;      entirely -- a pvar's value is spliced through by the site, unrenamed,
;;      so the shadowed corpus program (H2's whole reason for being) rewrites
;;      just fine once `seq` is passed as an argument instead of asserted as
;;      the template's own free identifier. Both escapes hinge on the SAME
;;      cause: a piece the design meant to keep fixed (an identifier, or the
;;      binder) recurred, or lined up in a fixed slot, often enough for the
;;      search to profitably absorb it into the template instead.
;;   2. Removing that literal recurrence (distinct heads everywhere) but
;;      still giving every body's FIRST element the uniform shape "(head
;;      boundvar)" produced a second, different winner (utility 815): a
;;      template binder again, with the ellipsis's sub `(,(svar) ,(tvar 0))`
;;      -- i.e. "some site-varying head, THEN the template's own binder
;;      reference" -- absorbing the (always-last) bound-variable position
;;      structurally, while the SVAR opaquely carries only the (irrelevant to
;;      hygiene) head symbol.  A shared ELEMENT SHAPE across sites is exactly
;;      as exploitable as a shared literal identifier: whenever a bound-var
;;      reference sits at a position a fixed (or ellipsis-uniform) sub-shape
;;      can name directly, V1 reaches it, no V2 required.
;;
;; The corpus below closes both holes with the same fix: every function head
;; and every literal number in the corpus is used EXACTLY ONCE, and every
;; body element's own LENGTH (as a list) is globally distinct from every
;; other element that shares its position across programs (see the per-
;; element length inventory in the comment above the corpus).  This leaves
;; `seq` as the corpus's ONLY recurring identifier -- so it alone is what any
;; H2-driven abstraction could exploit -- and leaves no fixed-length or
;; fixed-head sub-shape able to explain more than one program's sequence at
;; once, forcing the fully generic `(svar)` (the intended target) as the only
;; template that can reach two-or-more real (non-zero-iteration) programs at
;; all. Only once this corpus was run and matched the intended target, by
;; construction, were the assertions below written.
;;
;; This design is NOT robust in general -- it is a hand-tuned point that
;; happens to close the two escapes actually found, not a proof no third
;; escape exists -- and the margin is thin on purpose to show it: utility 5,
;; not a comfortable one. Saving each of the three real programs nets exactly
;; 103 (the shared fixed overhead of this shape: the outer application form,
;; the lambda's form/atom/binder-list form, and `seq`'s own atom, all paid
;; once by the macro instead of at every site); the macro itself costs 304
;; (its template, `seq`'s atom included); 3 x 103 = 309 clears 304 by exactly
;; 5. Two real programs (206) would NOT have cleared it -- this benchmark
;; needs all three, which is why the sequence-length-diversity requirement
;; ("at least two distinct lengths") undersells how tight this actually is.
;;
;;   raco test tests/my-when-test.rkt
;; ---------------------------------------------------------------------------

(require rackunit (file "../src/macro-micro.rkt"))

;; the corpus. p1-p3 share the shape and rewrite; p4's `seq` is a LOCALLY
;; bound shadow, so it must survive untouched (H2). Every function head and
;; every literal number below is used EXACTLY ONCE in the whole corpus (no
;; recurrence for the search to exploit -- see the header's surprising-winner
;; story). Per-position body-element lengths (as lists), so no fixed sub-
;; shape spans two programs: p1's elements are length 2 and 4; p2's lone
;; element is length 3; p3's are length 6, 7, and 2 -- no two programs share
;; a length at a position both of them have. The three real programs' own
;; sequence LENGTHS (element counts) are 2, 1, 3 -- all distinct, so no
;; fixed-arity (non-ellipsis) template can ever cover two of them either.
(define p1 '((lambda (x) (seq (add1 x) (bfun x 11 12))) (ffun 13)))
(define p2 '((lambda (y) (seq (cfun y 21))) (gfun 22 23)))
(define p3 '((lambda (z) (seq (dfun z 31 32 33 34) (efun z 41 42 43 44 45) (hfun z))) q))
(define p4 '(let ([seq (lambda (p) p)])
              ((lambda (w) (seq (jfun w 51) (kfun w 61 62 63))) e)))
(define programs (list p1 p2 p3 p4))

;; the target: the applied argument is pvar #1; the lambda's own parameter is
;; a BINDER-POSITION pvar #0 (V2), so a use-site body that mentions its own
;; bound variable transcribes back literally, unlike a template binder (V1),
;; which would freshen it away from any site-supplied reference (H1). The
;; sequence body is a single ellipsis whose sub is bare (svar): every element,
;; whatever its own shape, is captured and spliced back as one opaque
;; argument -- exactly the "abstraction over arity" ellipses add.
(define target
  `((lambda (,(pvar 0)) (seq ,(ellip (svar)))) ,(pvar 1)))

(module+ test
  (test-case "macro-search recovers the V2+ellipsis my-each macro"
    ;; measured wall time on this corpus (arity 2, all four programs): about
    ;; 5-6 seconds on the session's own container -- this corpus is far
    ;; smaller than for-set-test's (fewer distinct free identifiers for
    ;; corpus-facts to turn into productions, and a smaller max-arity), so it
    ;; finishes in a small fraction of that benchmark's several-minute
    ;; budget; no shrinking was needed.
    (check-equal? (macro-search programs 2) target))

  (test-case "rewrite-corpus turns the matching sites into calls, and skips the shadowed one"
    (define-values (rewritten after) (rewrite-corpus '() 'm0 target programs))
    (check-equal? rewritten
                  (list '(m0 x (ffun 13) (add1 x) (bfun x 11 12))
                        '(m0 y (gfun 22 23) (cfun y 21))
                        '(m0 z q (dfun z 31 32 33 34) (efun z 41 42 43 44 45) (hfun z))
                        ;; p4 unchanged: its `seq` resolves to the let's local
                        ;; binding, not the macro's definition-site global, so
                        ;; the oracle refuses the site (H2)
                        p4))
    ;; utility by hand, from the cost model (100/atom, 1/form, pvars 0):
    ;;   corpus costs (atoms*100 + forms), counting every symbol/number as one
    ;;   atom and every parenthesized form as 1, INCLUDING p4's let-shadow:
    ;;     p1: (lambda x seq add1 x bfun x 11 12 ffun 13) -- 11 atoms
    ;;         (app, lambda, binder-list, seq-form, add1-elem, bfun-elem,
    ;;          ffun-elem) -- 7 forms                          = 1107
    ;;     p2: (lambda y seq cfun y 21 gfun 22 23) -- 9 atoms, 6 forms = 906
    ;;     p3: (lambda z seq dfun z 31 32 33 34 efun z 41 42 43 44 45
    ;;          hfun z q) -- 19 atoms, 7 forms                  = 1907
    ;;     p4: (let seq lambda p p lambda w seq jfun w 51 kfun w 61 62 63 e)
    ;;         -- 17 atoms, 11 forms (let, bindings-list, binding-pair, the
    ;;         shadow's lambda, its binder-list, the body application, the
    ;;         body's lambda, its binder-list, the body's seq-form, and the
    ;;         two sequence elements)                          = 1711
    ;;     total = 1107 + 906 + 1907 + 1711 = 5631
    ;;   macro: template atoms lambda, seq = 2 atoms; forms: the outer
    ;;     application, the lambda, its binder-list, the seq-form, plus the
    ;;     ellipsis's own rendered `...` (an atom, per sexpr-cost's ellip
    ;;     case: 100 + sub's cost, sub = svar = 0) -- so the template is
    ;;     4 forms + 3 atoms-worth (lambda, seq, and the `...`)  = 304
    ;;     (matches macro-cost's 1(app)+1(lambda)+100+1(binder-list)+1(seq-
    ;;      form)+100(seq)+100(ellip's `...`) = 304; the two pvars are free)
    ;;   rewritten calls pay 1 (call form) + 100 (name) + each arg at cost:
    ;;     (m0 x (ffun 13) (add1 x) (bfun x 11 12))
    ;;       1+100 + 100(x) + 201((ffun 13)) + 201((add1 x)) + 401((bfun...))
    ;;       = 1004
    ;;     (m0 y (gfun 22 23) (cfun y 21))
    ;;       1+100 + 100(y) + 301((gfun 22 23)) + 301((cfun y 21)) = 803
    ;;     (m0 z q (dfun...) (efun...) (hfun z))
    ;;       1+100 + 100(z) + 100(q) + 601(dfun-elem) + 701(efun-elem)
    ;;       + 201(hfun-elem) = 1804
    ;;     p4 unchanged                                          = 1711
    ;;   after = 1004 + 803 + 1804 + 1711 = 5322
    ;;   utility = 5631 - 5322 - 304 = 5
    (check-equal? after 5322)
    (check-equal? (macro-utility '() target programs) 5))

  (test-case "valid-sites refuses p4 outright: the H2 shadowing exercise"
    ;; not merely "the site doesn't get rewritten" -- the oracle finds NO
    ;; valid site at all in p4, because its `seq` is the let-bound local, not
    ;; the macro's definition-site global
    (check-equal? (valid-sites '() 'm0 target p4 (expand-under '() p4))
                  (hash)))

  (test-case "the H1 story: the V1 analog is blocked at every real site"
    ;; swap the binder-position pvar for a template binder (tvar) -- the
    ;; V1-analog of the target -- and every one of p1-p3's sites vanishes:
    ;; each body genuinely mentions its own bound variable (`x`, `y`, `z`),
    ;; and with no recurring head or shape for a template binder to bake that
    ;; reference into (per the header's surprising-winner story), the only
    ;; way V1 could reach these sites is by receiving that reference as a
    ;; site-supplied argument -- which the expander then freshens away from
    ;; (H1). Checked per program, the way for-set-test's own review
    ;; correction insisted on.
    (define target-v1
      `((lambda (,(tvar 0)) (seq ,(ellip (svar)))) ,(pvar 0)))
    (check-equal? (valid-sites '() 'm0 target-v1 p1 (expand-under '() p1)) (hash))
    (check-equal? (valid-sites '() 'm0 target-v1 p2 (expand-under '() p2)) (hash))
    (check-equal? (valid-sites '() 'm0 target-v1 p3 (expand-under '() p3)) (hash))))
