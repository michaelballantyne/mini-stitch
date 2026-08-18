#lang racket

;; ---------------------------------------------------------------------------
;; tests/my-when-test.rkt --- a binder-position pattern variable AND ellipses
;; ---------------------------------------------------------------------------
;;
;; tests/for-set-test.rkt is the benchmark for binder-position pattern
;; variables alone; macro-micro.rkt's "variadic macro across three arities"
;; test is the benchmark for ellipses alone.  Neither exercises the other.
;; This is the first corpus that needs BOTH at once: a my-when/for-each
;; hybrid,
;;
;;     (define-syntax-rule (m v e xs ...) ((lambda (v) (seq xs ...)) e))
;;
;; i.e. "apply a one-argument procedure whose body is a variadic sequence".
;; In the learner's template representation (max-arity 2: #0 the binder, #1
;; the applied argument):
;;
;;     ((lambda (,(pvar 0)) (seq ,(ellip (svar)))) ,(pvar 1))
;;
;; #0 is a BINDER-POSITION pattern variable: every corpus body mentions its
;; own bound variable somewhere, so the same template with a template binder
;; (tvar) in #0's place is blocked by H1 at every site -- checked explicitly
;; below, per program.  `seq` is a definition-site free identifier: it never
;; varies across the corpus (only its arguments do), giving H2 a foothold --
;; exercised by the fourth program, which locally shadows `seq` and must
;; survive untouched.  The trailing `xs ...` is the ellipsis: the corpus's
;; three real programs use three DIFFERENT sequence lengths (2, 1, 3), so no
;; fixed-arity template can ever cover two of them.
;;
;; A corpus has to be designed carefully to force both mechanisms, because
;; the search is inventive about escaping them.  Two easier corpora were
;; tried first, and each was won by something other than the target:
;;
;;   1. When an identifier recurs verbatim in a fixed body position across
;;      programs (a shared `print` head), the winner absorbs the whole
;;      `(print v)` shape into the template, with a template binder for the
;;      lambda's parameter -- H1 only bites when an ARGUMENT, something the
;;      template receives opaquely and splices back verbatim, mentions the
;;      binder; a bound-variable reference the template itself spells out
;;      beside its own binder is not an argument.  And once `seq` itself is
;;      abstracted into a pattern variable, H2 has nothing to say either: a
;;      pattern variable's value is spliced through by the site, unrenamed,
;;      so the shadowed program rewrites just fine.
;;   2. With distinct heads everywhere but every body's first element shaped
;;      "(head boundvar)", the winner puts the template's own binder
;;      reference INSIDE the ellipsis's sub -- `(,(svar) ,(tvar 0))` -- so
;;      the sub's fixed shape names the bound-variable position directly and
;;      the sequence variable carries only the varying head.  A shared
;;      element shape is exactly as exploitable as a shared identifier.
;;
;; The corpus below closes both openings with one rule: every function head
;; and every literal number is used EXACTLY ONCE, and no two programs share
;; a body-element length at a position both of them have (the inventory is
;; in the comment above the corpus).  That leaves `seq` as the only
;; recurring identifier and leaves no fixed sub-shape able to explain more
;; than one program's sequence, so the fully generic `(svar)` is the only
;; template that can reach two or more programs with real iterations.
;;
;; The margin is thin on purpose, to show how tight the arithmetic is:
;; saving each of the three real programs nets exactly 103 (the shared fixed
;; overhead of this shape -- the outer application form, the lambda's
;; form/atom/binder-list, and `seq`'s own atom -- paid once by the macro
;; instead of at every site); the macro itself costs 304; 3 x 103 = 309
;; clears 304 by exactly 5.  Two real programs would not have cleared it.
;;
;;   raco test tests/my-when-test.rkt
;; ---------------------------------------------------------------------------

(require rackunit (file "../src/macro-micro.rkt"))

;; the corpus. p1-p3 share the shape and rewrite; p4's `seq` is a LOCALLY
;; bound shadow, so it must survive untouched (H2). Every function head and
;; every literal number below is used EXACTLY ONCE in the whole corpus (no
;; recurrence for the search to exploit -- see the header). Per-position
;; body-element lengths (as lists), so no fixed sub-shape spans two
;; programs: p1's elements are length 2 and 4; p2's lone element is length
;; 3; p3's are length 6, 7, and 2 -- no two programs share a length at a
;; position both of them have. The three real programs' own sequence
;; LENGTHS (element counts) are 2, 1, 3 -- all distinct, so no fixed-arity
;; (non-ellipsis) template can ever cover two of them either.
(define p1 '((lambda (x) (seq (add1 x) (bfun x 11 12))) (ffun 13)))
(define p2 '((lambda (y) (seq (cfun y 21))) (gfun 22 23)))
(define p3 '((lambda (z) (seq (dfun z 31 32 33 34) (efun z 41 42 43 44 45) (hfun z))) q))
(define p4 '(let ([seq (lambda (p) p)])
              ((lambda (w) (seq (jfun w 51) (kfun w 61 62 63))) e)))
(define programs (list p1 p2 p3 p4))

;; the target: the applied argument is pvar #1; the lambda's own parameter is
;; a binder-position pvar #0, so a use-site body that mentions its own bound
;; variable transcribes back literally -- a template binder would be
;; freshened away from any site-supplied reference (H1). The sequence body
;; is a single ellipsis whose sub is bare (svar): every element, whatever
;; its own shape, is captured and spliced back as one opaque argument --
;; exactly the abstraction over arity that ellipses add.
(define target
  `((lambda (,(pvar 0)) (seq ,(ellip (svar)))) ,(pvar 1)))

(module+ test
  (test-case "macro-search recovers the binder-and-ellipsis my-each macro"
    ;; seconds, not minutes: this corpus offers far fewer identifier
    ;; productions than for-set-test's, and a smaller max-arity
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

  (test-case "with a template binder instead, H1 blocks every real site"
    ;; swap the binder-position pvar for a template binder (tvar) and every
    ;; one of p1-p3's sites vanishes: each body genuinely mentions its own
    ;; bound variable (`x`, `y`, `z`), and with no recurring head or shape
    ;; for a template binder to bake that reference into (see the header),
    ;; the only way this template could reach these sites is by receiving
    ;; that reference as a site-supplied argument -- which the expander then
    ;; freshens away from (H1).  Checked per program.
    (define target-tvar
      `((lambda (,(tvar 0)) (seq ,(ellip (svar)))) ,(pvar 0)))
    (check-equal? (valid-sites '() 'm0 target-tvar p1 (expand-under '() p1)) (hash))
    (check-equal? (valid-sites '() 'm0 target-tvar p2 (expand-under '() p2)) (hash))
    (check-equal? (valid-sites '() 'm0 target-tvar p3 (expand-under '() p3)) (hash))))
