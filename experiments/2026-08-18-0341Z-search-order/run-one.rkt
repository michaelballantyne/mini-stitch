#lang racket

;; run-one.rkt --- run one (corpus, mode, max-arity) search and print a CSV row
;;
;;   racket run-one.rkt CORPUS.json MODE MAX-ARITY
;;
;; MODE is best | fifo | lifo.  Prints exactly one CSV line to stdout:
;;
;;   corpus,mode,max-arity,status,pops-expanded,pushed,considered,finished,utility,wall-ms,body
;;
;; status is ok | none (search found no abstraction) | error (parse/search
;; raised; message in the body field).  Run under `timeout` by the sweep
;; script so a blowup costs one row, not the sweep.

(require json
         "src-instr/expr.rkt"
         "src-instr/search.rkt")

(define args (current-command-line-arguments))
(define file (vector-ref args 0))
(define mode (string->symbol (vector-ref args 1)))
(define max-arity (string->number (vector-ref args 2)))

;; corpus name = basename without .json
(define corpus-name
  (let-values ([(_dir base _dir?) (split-path file)])
    (regexp-replace #rx"\\.json$" (path->string base) "")))

;; escape : String -> String  -- make a string safe as the final CSV field
(define (escape s)
  (regexp-replace* #rx"[,\n\r]" s ";"))

(define (row status pops pushed considered finished utility wall-ms body)
  (printf "~a,~a,~a,~a,~a,~a,~a,~a,~a,~a,~a\n"
          corpus-name mode max-arity status
          pops pushed considered finished utility wall-ms (escape body)))

(with-handlers ([exn:fail?
                 (lambda (e) (row "error" "" "" "" "" "" "" (exn-message e)))])
  (define programs (call-with-input-file file read-json))
  (unless (and (list? programs) (andmap string? programs))
    (error 'run-one "~a: expected a JSON array of program strings" file))
  (define c (corpus-from-programs programs))
  (define t0 (current-inexact-milliseconds))
  (define a (search c max-arity #:mode mode))
  (define t1 (current-inexact-milliseconds))
  (define stats (search-stats))
  (row (if a "ok" "none")
       (hash-ref stats 'pops-expanded)
       (hash-ref stats 'pushed)
       (hash-ref stats 'considered)
       (hash-ref stats 'finished)
       (if a (abstraction-utility a) "")
       (~r (- t1 t0) #:precision 1)
       (if a (abstraction-body a) "")))
