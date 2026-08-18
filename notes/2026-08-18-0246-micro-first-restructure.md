# Restructure: micro as a standalone learning artifact

Michael's direction (2026-08-18): micro was developed after mini and read like
a delta on it; a learner wants the opposite. Micro must present NOTHING about
mini, contain no parsing/printing or test-harness infrastructure, and express
its examples directly as Racket AST values. Comparisons and I/O belong in
separate files.

Changes:
- NEW src/ast.rkt: the five AST structs + six cost constants, extracted from
  expr.rkt — the one thing the two implementations share. Read first.
- src/micro.rkt: requires only ast.rkt + racket/set. parse/term->string
  removed (micro-compress now takes/returns terms; learned-body holds the
  pattern, not a string). All mini references scrubbed (grep-proven). Inline
  examples rewritten as AST values. Comparison tests, canonical, and the
  over-count story evicted. Header rewritten to state the paper relationship
  precisely: micro does NOT implement the paper's Algorithm 1 (which has
  branch-and-bound, upper-bound pruning, dominance pruning and best-first
  ordering built in from the start); it implements the paper's OBJECTIVE
  (Eq. 8 utility + the semantic filters incl. footnote-2 argument capture),
  reached by the enumeration the paper itself describes and discards as "A
  Naive Approach" (§3.1), with §4.4's rewrite DP as the *definition* of
  utility, and the one deliberate deviation (cost_{alpha=0} penalty,
  following the real implementation).
- Knowledge from the old "how this differs" comments moved into the mini
  modules as "WHAT WE DO DIFFERENTLY FROM micro.rkt" header sections
  (expr.rkt, pattern.rkt, search.rkt, rewrite.rkt).
- NEW tests/support.rkt (parse, term->string, canonical — comparison and
  corpus-file infrastructure); NEW tests/micro-test.rkt (micro-vs-mini,
  vs-real-binary, and the over-count disagreement regression); tests/fuzz.rkt
  re-pointed at support.rkt.
- walkthrough.md: §§1-2 mini-free; §2.1 gains the naive-approach honesty
  note; the micro/mini timing comparison moved from §2.7 into §3's opening;
  intro states the reading order (ast.rkt -> micro.rkt -> §§1-2 -> mini).
- README: ast.rkt listed first with reading order; micro described
  standalone; "share only the parser and printer" -> "share only the AST and
  cost model".

Verification: suite green, 83 tests (was 81; micro's 16 split 10 inline + 6
relocated, +2 support self-tests); differential tally unchanged (87 runs: 85
MATCH / 2 TIE / 0 FAIL); fuzz tallies unchanged on the same seed; compress
CLI output byte-identical on hof.json.
