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
;; the program representation at hand puts there: a nested Node, or an index
;; into an arena of Nodes.
;;
;; A Cost is an integer, in the cost model below.
;; ---------------------------------------------------------------------------

(provide
 ;; nodes
 (struct-out prim) (struct-out var) (struct-out ivar)
 (struct-out app) (struct-out lam)
 ;; cost model constants
 COST-APP COST-LAM COST-VAR COST-IVAR COST-PRIM COST-NEW-PRIM)

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
(define COST-IVAR 100)
(define COST-PRIM 100)

;; The name of a freshly invented abstraction is a primitive like any other, so
;; it costs the same (`compute_cost_new_prim`, lambdas expr.rs:555-558).
(define COST-NEW-PRIM COST-PRIM)
