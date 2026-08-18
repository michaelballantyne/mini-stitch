#lang racket

;; aggregate.rkt --- turn results.csv into the markdown tables for results.md
;;
;;   racket aggregate.rkt [ARITY]     (default: both 2 and 3)
;;
;; Prints, per arity: a corpus x mode table of pops-expanded (with fifo/best
;; and lifo/best ratios), the same for considered, totals, wall-clock totals,
;; and a utility-parity check (winner utilities must agree across modes;
;; bodies may differ on ties, which are flagged).

(define rows
  (for/list ([line (in-list (rest (file->lines "results.csv")))])
    ;; body may contain no commas (escaped by run-one), so a plain split works
    (string-split line "," #:trim? #f)))

(define (field r i) (list-ref r i))
(define (num r i) (string->number (field r i)))
;; columns: 0 corpus 1 mode 2 arity 3 status 4 pops 5 pushed 6 considered
;;          7 finished 8 utility 9 wall-ms 10 body

(define (rows-at arity)
  (filter (lambda (r) (equal? (field r 2) (number->string arity))) rows))

(define (fmt-ratio a b)
  (if (and a b (> b 0)) (~r (/ (exact->inexact a) b) #:precision '(= 2)) "-"))

(define (report arity)
  (define rs (rows-at arity))
  (when (pair? rs)
    (define corpora (remove-duplicates (map (lambda (r) (field r 0)) rs)))
    (define (get corpus mode)
      (findf (lambda (r) (and (equal? (field r 0) corpus) (equal? (field r 1) mode))) rs))
    (printf "\n## max-arity ~a\n\n" arity)
    (printf "| corpus | pops best | pops fifo | pops lifo | fifo/best | lifo/best | considered best | considered fifo | considered lifo | ms best | ms fifo | ms lifo | utility |\n")
    (printf "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n")
    (define totals (make-hash))
    (for ([corpus (in-list corpora)])
      (define b (get corpus "best"))
      (define f (get corpus "fifo"))
      (define l (get corpus "lifo"))
      (define (v r i) (and r (member (field r 3) '("ok" "none")) (num r i)))
      (for ([m (list b f l)] [tag '(best fifo lifo)])
        (when (v m 4)
          (hash-update! totals (cons tag 'pops) (lambda (x) (+ x (v m 4))) 0)
          (hash-update! totals (cons tag 'considered) (lambda (x) (+ x (v m 6))) 0)
          (hash-update! totals (cons tag 'ms) (lambda (x) (+ x (v m 9))) 0.0)))
      (define (cell r i) (cond [(not r) "?"] [(v r i) => values] [else (field r 3)]))
      (printf "| ~a | ~a | ~a | ~a | ~a | ~a | ~a | ~a | ~a | ~a | ~a | ~a | ~a |\n"
              corpus (cell b 4) (cell f 4) (cell l 4)
              (fmt-ratio (v f 4) (v b 4)) (fmt-ratio (v l 4) (v b 4))
              (cell b 6) (cell f 6) (cell l 6)
              (cell b 9) (cell f 9) (cell l 9)
              (if (and b (equal? (field b 3) "ok")) (field b 8) "-"))
      ;; utility parity check
      (define utils (for/list ([r (list b f l)] #:when (and r (member (field r 3) '("ok" "none"))))
                      (field r 8)))
      (unless (or (null? utils) (for/and ([u (cdr utils)]) (equal? u (car utils))))
        (printf "UTILITY MISMATCH at ~a arity ~a: ~a\n" corpus arity utils))
      ;; body tie check
      (define bodies (for/list ([r (list b f l)] #:when (and r (equal? (field r 3) "ok")))
                       (field r 10)))
      (unless (or (null? bodies) (for/and ([b (cdr bodies)]) (equal? b (car bodies))))
        (printf "  (tie: bodies differ at ~a arity ~a: ~a)\n" corpus arity bodies)))
    (printf "\nTOTALS arity ~a: " arity)
    (for ([tag '(best fifo lifo)])
      (printf "~a pops=~a considered=~a ms=~a;  "
              tag
              (hash-ref totals (cons tag 'pops) 0)
              (hash-ref totals (cons tag 'considered) 0)
              (~r (hash-ref totals (cons tag 'ms) 0.0) #:precision 0)))
    (newline)))

(report 2)
(report 3)
