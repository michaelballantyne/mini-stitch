#lang racket

;; ---------------------------------------------------------------------------
;; ast.rkt --- the language, and what a program costs
;; ---------------------------------------------------------------------------
;;
;; The shared definition of the object language: the lambda calculus with de
;; Bruijn indices and named primitives, which is what stitch compresses, plus
;; stitch's cost model, which is what "compresses" means.  Both implementations
;; in src/ are built on this file.
;;
;; DATA DEFINITIONS
;;
;; A Node is one of
;;   (prim s)     a DSL primitive named by the symbol s ("+", "cons", "3", ...)
;;   (var i)      a de Bruijn variable, written $i in stitch's surface syntax;
;;                i >= 0 counts binders outward from the variable, so $0 is the
;;                innermost enclosing lambda
;;   (ivar i)     an abstraction variable, written #i: a parameter of an
;;                abstraction.  Programs never contain these; they appear in the
;;                body of an abstraction being learned
;;   (app f x)    an application of f to x
;;   (lam b)      a lambda with body b
;;
;; Applications are binary and curried: the surface form (a b c) denotes
;; ((a b) c).  There is no n-ary application node.
;;
;; The child fields -- an app's `fun` and `arg`, a lam's `body` -- hold whatever
;; the program representation at hand puts there: a nested Node, or an integer
;; naming a Node in some table.
;;
;; A Cost is an integer, in the cost model below.
;; ---------------------------------------------------------------------------

(provide
 ;; nodes
 (struct-out prim) (struct-out var) (struct-out ivar)
 (struct-out app) (struct-out lam)
 ;; cost model constants
 COST-APP COST-LAM COST-VAR COST-PRIM COST-NEW-PRIM)

;; ---------------------------------------------------------------------------
;; Nodes
;; ---------------------------------------------------------------------------

;; Transparent structs so that equal? and equal-hash-code are structural.
(struct prim (name) #:transparent)   ; Symbol
(struct var  (i)    #:transparent)   ; Natural
(struct ivar (i)    #:transparent)   ; Natural
(struct app  (fun arg) #:transparent)
(struct lam  (body) #:transparent)

;; ---------------------------------------------------------------------------
;; Cost model
;; ---------------------------------------------------------------------------

;; stitch's default (dreamcoder) cost model: structure is nearly free, leaves
;; are expensive.  The cost of a corpus is the sum over its programs, and
;; compression is exactly the reduction of that number.  (compression.rs:367-430,
;; lambdas expr.rs:560-569.)
(define COST-APP 1)
(define COST-LAM 1)
(define COST-VAR 100)
(define COST-PRIM 100)

;; There is deliberately no COST-IVAR.  An abstraction variable has two prices
;; depending on where it is priced, and neither is a constant worth naming:
;; in the body of an abstraction being learned it costs 0 -- variables are
;; parameters, not structure (the paper's cost_{alpha=0}, and the price both
;; implementations charge for an abstraction's own size) -- and nothing in
;; either pipeline ever prices one anywhere else.  (Real stitch's config does
;; carry a cost_ivar = 100 default, but its accounting likewise never routes
;; an abstraction body through the generic cost function; the constant is
;; inert there too.)

;; The name of a freshly invented abstraction is a primitive like any other, so
;; it costs the same (`compute_cost_new_prim`, lambdas expr.rs:555-558).
(define COST-NEW-PRIM COST-PRIM)
