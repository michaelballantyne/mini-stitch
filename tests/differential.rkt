#lang racket

;; ---------------------------------------------------------------------------
;; tests/differential.rkt --- mini-stitch against the real thing
;; ---------------------------------------------------------------------------
;;
;; The unit tests scattered through src/ check pieces against numbers that were
;; once read off the real binary.  This module does the systematic version: for
;; every corpus in stitch/data/basic and for four configurations of each -- plus
;; three runs at realistic scale from stitch/data/cogsci -- it *runs*
;; `stitch/target/release/compress` and compares its `out.json` against what
;; `compress` from src/compress.rkt produces on the same input.  The Rust is
;; ground truth; any difference is a bug in mini-stitch until proven otherwise.
;;
;; Compared, per (corpus, max-arity, iterations):
;;   * the number of abstractions found
;;   * per abstraction: body string, arity, utility, num_uses, final_cost
;;   * top-level original_cost and final_cost
;;   * the final rewritten programs, string for string
;;
;; TIES.  Two different abstraction bodies can have exactly the same utility, in
;; which case which one is "best" is decided by the order the search happens to
;; reach them, and mini-stitch's worklist is not the real one's (no threads, no
;; batching, a different heap).  A body difference at equal utility is therefore
;; reported as TIE rather than FAIL -- but only a body difference at equal
;; utility; anything else is a bug.  Once the two systems have chosen different
;; abstractions the corpora they go on to compress differ as well, so the rest
;; of that run (later iterations, final cost, rewritten programs) is not
;; compared.
;;
;; A tie excuses *only itself*.  Two rules keep that honest, because a verdict
;; that cannot fail is not a test:
;;
;;   * a tie absorbs its own body-difference note and nothing else.  If anything
;;     else disagreed -- the original cost, or a field of an *earlier*
;;     abstraction whose body did match -- the run fails, tie or no tie.
;;   * a tie on a (corpus, max-arity) combination that is not listed in
;;     `known-ties` below fails the suite.  Ties are supposed to be a short,
;;     inspected list of verified coincidences; a new one is a finding, not a
;;     pass.
;;
;; The one tie observed on this data is listed in `known-ties` below.
;;
;; NOT COMPARED: simple3, simple4 and simple5 use stitch's fused-lambda tags
;; (`lam_1`, `$0_1`), which mini-stitch's parser deliberately rejects -- see the
;; header of src/expr.rkt.  They are out of scope, not failing.
;;
;;   raco test tests/differential.rkt
;; ---------------------------------------------------------------------------

(require rackunit
         racket/runtime-path
         json
         "../src/compress.rkt")

(define-runtime-path repo-root "..")

(define real-binary (build-path repo-root "stitch" "target" "release" "compress"))
(define basic-dir (build-path repo-root "stitch" "data" "basic"))
(define cogsci-dir (build-path repo-root "stitch" "data" "cogsci"))
(define nuts-bolts (build-path cogsci-dir "nuts-bolts.json"))
(define wheels (build-path cogsci-dir "wheels.json"))
(define dials (build-path cogsci-dir "dials.json"))

;; Corpora that mini-stitch cannot read at all (fused-lambda tags).
(define skipped-corpora '("simple3" "simple4" "simple5"))

;; Known genuine ties: (corpus-name . max-arity) pairs where the two systems
;; pick different bodies of exactly equal utility.  Kept explicit, and enforced:
;; a tie on any other combination fails the suite (see `failing?`), so a new tie
;; is something someone has to look at and sign off on here.
(define known-ties '(("ctx_thread_twice" . 3)))

;; The real binary's out.json files land here -- outside the repo, since they
;; are scratch.
(define out-dir
  (let ([scratchpad "/tmp/claude-0/-home-user-mini-stitch/eb3c5a29-6df6-54aa-b684-6923baada426/scratchpad"])
    (build-path (if (directory-exists? scratchpad) scratchpad (find-system-path 'temp-dir))
                "diffout")))

;; ---------------------------------------------------------------------------
;; Running the two systems
;; ---------------------------------------------------------------------------

;; read-corpus : Path -> (Listof String)
;; The programs in a stitch `programs-list` corpus file.
(define (read-corpus file)
  (call-with-input-file file read-json))

;; run-real : Path Natural Natural String -> Jsexpr
;; Run the real binary on this corpus and return its parsed out.json.  Raises if
;; the binary exits non-zero.
(define (run-real file max-arity iterations tag)
  (define out (build-path out-dir (string-append tag ".json")))
  (define ok
    (parameterize ([current-output-port (open-output-nowhere)])
      (system* real-binary
               (path->string file)
               (format "--max-arity=~a" max-arity)
               (format "--iterations=~a" iterations)
               "--silent"
               (format "--out=~a" out))))
  (unless ok
    (error 'run-real "~a exited non-zero on ~a (arity ~a, iterations ~a)"
           real-binary file max-arity iterations))
  (call-with-input-file out read-json))

;; ---------------------------------------------------------------------------
;; Comparing
;; ---------------------------------------------------------------------------

;; A Verdict is one of 'match, 'tie, or 'fail.
;; An Outcome is a (outcome String Natural Natural Verdict (Listof String)):
;; which run it was, how it went, and what to say about it.
(struct outcome (corpus max-arity iterations verdict notes) #:transparent)

;; compare-run : String Natural Natural Jsexpr Result -> Outcome
;; Check mini-stitch's Result against the real binary's out.json.
(define (compare-run name max-arity iterations real mini)
  ;; Mismatch notes and the tie note are kept apart on purpose: the tie note is
  ;; the one difference a TIE verdict is allowed to excuse, and `notes` is what
  ;; decides between 'match and 'fail.  Lumping them together is how a run that
  ;; is simultaneously drifting and tying would report TIE.
  (define notes '())
  (define tie-note #f)
  (define (note! fmt . args) (set! notes (cons (apply format fmt args) notes)))
  (define real-abs (hash-ref real 'abstractions))
  (define mini-abs (result-steps mini))

  ;; The original cost is independent of everything the search chooses, so it is
  ;; always worth comparing: a difference means the parser or the cost model has
  ;; drifted, and nothing after it would mean anything.
  (unless (= (hash-ref real 'original_cost) (result-original-cost mini))
    (note! "original_cost: real ~a, mini ~a"
           (hash-ref real 'original_cost) (result-original-cost mini)))

  ;; Walk the abstractions in lockstep until they disagree.
  (define tie?
    (for/or ([r (in-list real-abs)] [m (in-list mini-abs)] [i (in-naturals)])
      (cond
        [(string=? (hash-ref r 'body) (step-body m))
         (for ([field (in-list (list (cons 'arity (step-arity m))
                                     (cons 'utility (step-utility m))
                                     (cons 'num_uses (step-num-uses m))
                                     (cons 'final_cost (step-cost-after m))))])
           (unless (equal? (hash-ref r (car field)) (cdr field))
             (note! "abstraction ~a ~a: real ~a, mini ~a"
                    i (car field) (hash-ref r (car field)) (cdr field))))
         #f]
        [(= (hash-ref r 'utility) (step-utility m))
         ;; Equal utility, different body: a real tie.  Stop here; everything
         ;; downstream is comparing two different (equally good) answers.
         (set! tie-note
               (format "TIE at abstraction ~a (utility ~a): real ~s, mini ~s"
                       i (hash-ref r 'utility) (hash-ref r 'body) (step-body m)))
         #t]
        [else
         (note! "abstraction ~a: real ~s (utility ~a), mini ~s (utility ~a)"
                i (hash-ref r 'body) (hash-ref r 'utility)
                (step-body m) (step-utility m))
         #f])))

  ;; Whole-run comparisons only make sense when the two agreed all the way.
  (unless tie?
    (unless (= (length real-abs) (length mini-abs))
      (note! "number of abstractions: real ~a, mini ~a"
             (length real-abs) (length mini-abs)))
    (unless (= (hash-ref real 'final_cost) (result-final-cost mini))
      (note! "final_cost: real ~a, mini ~a"
             (hash-ref real 'final_cost) (result-final-cost mini)))
    (unless (equal? (hash-ref real 'rewritten) (result-programs mini))
      (note! "rewritten programs differ:\n    real ~s\n    mini ~s"
             (hash-ref real 'rewritten) (result-programs mini))))

  ;; A tie excuses its own note and no other: any mismatch recorded before the
  ;; tie point -- a drifting original_cost, or a field of an earlier abstraction
  ;; whose body did match -- still fails the run.
  (define verdict
    (cond [(pair? notes) 'fail]
          [tie? 'tie]
          [else 'match]))
  ;; The notes, in the order they were recorded; the tie note (if any) is last,
  ;; since the lockstep walk stops there and nothing is compared after it.  A
  ;; 'tie outcome therefore carries exactly one note, its own; a 'fail carries
  ;; every mismatch, plus the tie note when it also tied.
  (outcome name max-arity iterations verdict
           (append (reverse notes) (if tie-note (list tie-note) '()))))

;; check-corpus : String Path Natural Natural -> Outcome
;; Run both systems on one corpus in one configuration and compare.
(define (check-corpus name file max-arity iterations)
  (define programs (read-corpus file))
  (define real (run-real file max-arity iterations
                         (format "~a-a~a-i~a" name max-arity iterations)))
  (define mini (compress programs #:max-arity max-arity #:iterations iterations))
  (compare-run name max-arity iterations real mini))

;; ---------------------------------------------------------------------------
;; The suite
;; ---------------------------------------------------------------------------

;; basic-corpora : -> (Listof (cons String Path))
;; The readable corpora of stitch/data/basic, by name.
(define (basic-corpora)
  (for*/list ([f (in-list (sort (map path->string (directory-list basic-dir)) string<?))]
              #:when (regexp-match? #rx"[.]json$" f)
              [name (in-value (regexp-replace #rx"[.]json$" f ""))]
              #:unless (member name skipped-corpora))
    (cons name (build-path basic-dir f))))

;; verdict-label : Verdict -> String
(define (verdict-label v)
  (case v [(match) "MATCH"] [(tie) "TIE  "] [else "FAIL "]))

;; unexpected-tie? : Outcome -> Boolean
;; A tie on a combination nobody has signed off on in `known-ties`.
(define (unexpected-tie? o)
  (and (eq? (outcome-verdict o) 'tie)
       (not (member (cons (outcome-corpus o) (outcome-max-arity o)) known-ties))))

;; failing? : Outcome -> Boolean
;; Does this run fail the suite?  Outright mismatches do, and so do unexpected
;; ties: the tie verdict is an excuse the known-ties list has to grant.
(define (failing? o)
  (or (eq? (outcome-verdict o) 'fail) (unexpected-tie? o)))

;; print-summary : (Listof Outcome) -> Void
;; The table the whole module exists to produce.
(define (print-summary outcomes)
  (printf "\n~a\n" (make-string 62 #\=))
  (printf "~a  ~a\n" (~a "corpus" #:min-width 26) "arity/iters -> verdict")
  (printf "~a\n" (make-string 62 #\-))
  (for ([o (in-list outcomes)])
    (printf "~a  a~a i~a -> ~a\n"
            (~a (outcome-corpus o) #:min-width 26)
            (outcome-max-arity o) (outcome-iterations o)
            (verdict-label (outcome-verdict o)))
    (for ([n (in-list (outcome-notes o))]) (printf "      ~a\n" n)))
  (printf "~a\n" (make-string 62 #\-))
  (printf "~a runs: ~a match, ~a tie, ~a fail\n"
          (length outcomes)
          (count (lambda (o) (eq? (outcome-verdict o) 'match)) outcomes)
          (count (lambda (o) (eq? (outcome-verdict o) 'tie)) outcomes)
          (count (lambda (o) (eq? (outcome-verdict o) 'fail)) outcomes))
  (for ([o (in-list outcomes)] #:when (eq? (outcome-verdict o) 'tie))
    (printf "~a tie: ~a at arity ~a, iterations ~a~a\n"
            (if (unexpected-tie? o) "UNEXPECTED" "known")
            (outcome-corpus o) (outcome-max-arity o) (outcome-iterations o)
            (if (unexpected-tie? o) " -- FAILS the suite" ""))))

(module+ test
  (make-directory* out-dir)

  (test-case "mini-stitch agrees with the real binary on stitch/data/basic"
    (check-true (file-exists? real-binary)
                (format "the real binary is not built: ~a" real-binary))
    (define outcomes
      (for*/list ([corpus (in-list (basic-corpora))]
                  [max-arity (in-list '(2 3))]
                  [iterations (in-list '(1 3))])
        (check-corpus (car corpus) (cdr corpus) max-arity iterations)))

    ;; And three runs at realistic scale, from stitch's cogsci domains:
    ;; nuts-bolts is 250 programs through three iterations; wheels (1035
    ;; programs) and dials (207) are one iteration each, and are here because
    ;; the repo claims parity on them and a claim nobody can re-run is not a
    ;; claim.
    (define start (current-inexact-milliseconds))
    (define big
      (list (check-corpus "nuts-bolts" nuts-bolts 2 3)
            (check-corpus "wheels" wheels 2 1)
            (check-corpus "dials" dials 2 1)))
    (define elapsed (- (current-inexact-milliseconds) start))

    (define all (append outcomes big))
    (print-summary all)
    (printf "cogsci runs (nuts-bolts a2 i3, wheels a2 i1, dials a2 i1): ~a ms for both systems\n"
            (inexact->exact (round elapsed)))

    (define failures (filter failing? all))
    (check-equal? (map outcome-corpus failures) '()
                  "see the summary table above for the differences")))
