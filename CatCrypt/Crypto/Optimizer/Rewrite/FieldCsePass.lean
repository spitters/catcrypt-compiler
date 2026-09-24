/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Verified common-subexpression elimination (CSE) for a let-binding field IR

A straight-line, *let-binding* field-arithmetic IR `FLet R` over a generic
commutative ring `R`, together with a verified common-subexpression-elimination
(CSE) rewrite, proved denotation-preserving. Because the development is
parametric in `[CommRing R]`, the same proved rewrite runs at every ModArith
dialect level (`ZMod p`, `ℤ`, …). This complements the bottom-up algebraic
constant folder in `FieldConstFoldPass.lean` and the dead-binding eliminator in
`FieldLetDcePass.lean`: there the rewrites drop work that is never used; here the
rewrite *shares* work that is computed twice.

## The CSE idea and the verified core

In a let-binding program, if the same expression `e` is recomputed where a
variable `v` is already bound to its value, the recomputation can be replaced by
a reference to `v`. The verified core is the **substitution-correctness lemma**
(`FExpr.substExpr_denote`):

> replacing every syntactic occurrence of a sub-expression `e` by a variable
> `v`, *given* that the current environment binds `v` to the value of `e`
> (`env v = e.denote env`), preserves the denotation.

That equation — "a variable bound to `e` can stand in for `e`" — is exactly the
content of CSE. We then lift it to the
**single-binding CSE step** on programs (`cseLet_denote`):

> `ret t  ↦  letB x e (ret (substExpr x e t))` is denotation-preserving — bind
> the shared subexpression `e` to a fresh name `x`, then reference `x` wherever
> `e` was recomputed.

This is the CSE transformation: it introduces the sharing let-binding
and rewrites the body, with the binding invariant `env' x = e.denote env`
established *by the very `letB` it introduces*. Working one binding deep sidesteps
the variable-capture bookkeeping (an inner `letB` could re-bind `x` and break the
invariant); the introduced binding is the clean, capture-free unit of CSE.

## The IR (shared shape with `FieldLetDcePass`)

* `FExpr R` — `const / var / add / sub / mul`, variables are `String`s resolved
  against an environment `env : String → R`.
* `FLet R` — a chain of `let`s ending in a `ret`. We keep a self-contained copy
  of the IR (no import of `FieldLetDcePass`) so the pass stands alone;
  `DecidableEq (FExpr R)` is derived (needs `DecidableEq R`) to drive the
  *syntactic* match against the shared sub-expression.

## Scope

The deliverable is the verified CSE *core*: the expression-level substitution
lemma plus the single-binding CSE step on programs, both denotation-preserving
over any `[CommRing R]`. A whole-program CSE pass that threads the sharing
invariant through arbitrarily many nested `letB`s additionally needs a
freshness/capture-avoidance discipline on the introduced names; that bookkeeping
is orthogonal to the algebraic content proved here and is deliberately left out.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.FieldCsePass

variable {R : Type*} [CommRing R]

/-! ## A straight-line let-binding field IR (named variables) -/

/-- A field-arithmetic expression with named (`String`) variables over `R`. -/
inductive FExpr (R : Type*) : Type _
  | const : R → FExpr R
  | var : String → FExpr R
  | add : FExpr R → FExpr R → FExpr R
  | sub : FExpr R → FExpr R → FExpr R
  | mul : FExpr R → FExpr R → FExpr R
  deriving Repr, DecidableEq

/-- A straight-line let-binding program: a chain of named `let`s ending in a
return. -/
inductive FLet (R : Type*) : Type _
  | ret : FExpr R → FLet R
  | letB : String → FExpr R → FLet R → FLet R
  deriving Repr, DecidableEq

namespace FExpr

/-- Denotation of an `FExpr` against an environment `env : String → R`. -/
def denote (env : String → R) : FExpr R → R
  | const c => c
  | var x => env x
  | add a b => denote env a + denote env b
  | sub a b => denote env a - denote env b
  | mul a b => denote env a * denote env b

@[simp] theorem denote_const (env : String → R) (c : R) :
    denote env (const c) = c := rfl

@[simp] theorem denote_var (env : String → R) (x : String) :
    denote env (var x) = env x := rfl

@[simp] theorem denote_add (env : String → R) (a b : FExpr R) :
    denote env (add a b) = denote env a + denote env b := rfl

@[simp] theorem denote_sub (env : String → R) (a b : FExpr R) :
    denote env (sub a b) = denote env a - denote env b := rfl

@[simp] theorem denote_mul (env : String → R) (a b : FExpr R) :
    denote env (mul a b) = denote env a * denote env b := rfl

/-! ### Free-variable test and the irrelevance lemma -/

/-- Whether the name `x` occurs in an expression. -/
def freeInExpr (x : String) : FExpr R → Bool
  | const _ => false
  | var y => x = y
  | add a b => freeInExpr x a || freeInExpr x b
  | sub a b => freeInExpr x a || freeInExpr x b
  | mul a b => freeInExpr x a || freeInExpr x b

/-- **Irrelevance lemma.** If a name `x` is not free in an expression, then
updating the environment at `x` with *any* value `v` leaves the denotation
unchanged: the binding for `x` is unobservable. -/
theorem denote_update_of_not_free (env : String → R) (x : String) (v : R) :
    ∀ e : FExpr R, freeInExpr x e = false →
      denote (Function.update env x v) e = denote env e
  | const _, _ => rfl
  | var y, h => by
      simp only [freeInExpr, decide_eq_false_iff_not] at h
      simp [denote, Function.update_of_ne (Ne.symm h)]
  | add a b, h => by
      simp only [freeInExpr, Bool.or_eq_false_iff] at h
      simp [denote, denote_update_of_not_free env x v a h.1,
        denote_update_of_not_free env x v b h.2]
  | sub a b, h => by
      simp only [freeInExpr, Bool.or_eq_false_iff] at h
      simp [denote, denote_update_of_not_free env x v a h.1,
        denote_update_of_not_free env x v b h.2]
  | mul a b, h => by
      simp only [freeInExpr, Bool.or_eq_false_iff] at h
      simp [denote, denote_update_of_not_free env x v a h.1,
        denote_update_of_not_free env x v b h.2]

/-! ### Sub-expression substitution and the CSE substitution lemma -/

variable [DecidableEq R]

/-- Replace every syntactic occurrence of the sub-expression `e` inside `t` by
the variable `var v`. The match is *syntactic equality* on `FExpr` (decidable
because `R` is); a matched node is short-circuited to `var v`, otherwise we
recurse structurally. This is the rewrite that *shares* a common subexpression
already bound to `v`. -/
def substExpr (v : String) (e : FExpr R) : FExpr R → FExpr R
  | const c => if const c = e then var v else const c
  | var x => if var x = e then var v else var x
  | add a b => if add a b = e then var v else add (substExpr v e a) (substExpr v e b)
  | sub a b => if sub a b = e then var v else sub (substExpr v e a) (substExpr v e b)
  | mul a b => if mul a b = e then var v else mul (substExpr v e a) (substExpr v e b)

/-- **CSE substitution lemma (expression level).** If the environment binds `v`
to the value of `e` (`env v = e.denote env`), then replacing every occurrence of
`e` by `var v` leaves the denotation unchanged: a variable bound to `e` can
stand in for `e`. Proved by structural induction; the matched-node case is closed
by the binding hypothesis, the rest by the recursion. -/
theorem substExpr_denote (env : String → R) (v : String) (e : FExpr R)
    (hv : env v = e.denote env) :
    ∀ t : FExpr R, denote env (substExpr v e t) = denote env t
  | const c => by
      unfold substExpr; split
      · rename_i ht; rw [ht]; simp [denote, hv]
      · rfl
  | var x => by
      unfold substExpr; split
      · rename_i ht; rw [ht]; simp [denote, hv]
      · rfl
  | add a b => by
      unfold substExpr; split
      · rename_i ht; rw [ht]; simp [denote, hv]
      · simp only [denote_add, substExpr_denote env v e hv a,
          substExpr_denote env v e hv b]
  | sub a b => by
      unfold substExpr; split
      · rename_i ht; rw [ht]; simp [denote, hv]
      · simp only [denote_sub, substExpr_denote env v e hv a,
          substExpr_denote env v e hv b]
  | mul a b => by
      unfold substExpr; split
      · rename_i ht; rw [ht]; simp [denote, hv]
      · simp only [denote_mul, substExpr_denote env v e hv a,
          substExpr_denote env v e hv b]

end FExpr

open FExpr

namespace FLet

/-- Denotation of a let-binding program: each `letB x e` updates the environment
at `x` with the value of `e` before running the body. -/
def denote (env : String → R) : FLet R → R
  | ret e => e.denote env
  | letB x e body => denote (Function.update env x (e.denote env)) body

@[simp] theorem denote_ret (env : String → R) (e : FExpr R) :
    denote env (ret e) = e.denote env := rfl

@[simp] theorem denote_letB (env : String → R) (x : String) (e : FExpr R)
    (body : FLet R) :
    denote env (letB x e body)
      = denote (Function.update env x (e.denote env)) body := rfl

/-! ## The single-binding CSE step

`cseLet x e t` is the CSE transformation on a returned expression: bind
the shared subexpression `e` to a fresh name `x`, then rewrite every
recomputation of `e` in `t` to `var x`. The introduced `letB` establishes the
binding invariant `env' x = e.denote env` *by construction*, so its soundness
needs no external freshness hypothesis on the environment. -/

variable [DecidableEq R]

/-- The single-binding CSE step on a returned expression: introduce
`let x := e` and share `e` across the body by rewriting it to `var x`. -/
def cseLet (x : String) (e t : FExpr R) : FLet R :=
  letB x e (ret (FExpr.substExpr x e t))

/-- **Single-binding CSE soundness.** Introducing a sharing binding `x := e` and
rewriting every recomputation of `e` to `var x` is denotation-preserving,
*provided* the binding name `x` does not already occur in `e` (so that binding
`x` does not change the value of `e`). The invariant `env' x = e.denote env'` is
discharged from the introduced `letB` together with `denote_update_of_not_free`,
and then fed to `FExpr.substExpr_denote`. -/
theorem cseLet_denote (env : String → R) (x : String) (e t : FExpr R)
    (hxe : FExpr.freeInExpr x e = false) (hxt : FExpr.freeInExpr x t = false) :
    denote env (cseLet x e t) = denote env (ret t) := by
  simp only [cseLet, denote_letB, denote_ret]
  set env' : String → R := Function.update env x (e.denote env) with henv'
  -- The introduced binding makes `env'` map `x` to the value of `e`; and since
  -- `x` is not free in `e`, that value is `e.denote env'` as well.
  have hbind : env' x = e.denote env' := by
    rw [henv', Function.update_self,
      FExpr.denote_update_of_not_free env x (e.denote env) e hxe]
  -- Sharing `e` through `x` in the body preserves its denotation under `env'`,
  -- and `x` not free in `t` means the introduced binding does not change `t`.
  rw [FExpr.substExpr_denote env' x e hbind t, henv',
    FExpr.denote_update_of_not_free env x (e.denote env) t hxt]

/-! ## Worked example

`a*b + a*b` shares the repeated product `a*b`. The single-binding CSE step
introduces `let t := a*b` and rewrites both occurrences to `var t`, yielding
`let t := a*b in t + t`, with equal denotation under any environment over any
ring. The free-variable side-condition `t ∉ a*b` holds for the fresh name `"t"`
(its operands are `"a"`, `"b"`). -/

namespace Example

open FExpr FLet

/-- The shared subexpression `a*b`. -/
def ab : FExpr ℤ := mul (var "a") (var "b")

/-- `a*b + a*b` — the product `a*b` is recomputed. -/
def prog : FExpr ℤ := add ab ab

/-- The single-binding CSE step rewrites `a*b + a*b` into
`let t := a*b in t + t`: both occurrences of the product are shared through `t`. -/
theorem cseLet_prog :
    FLet.cseLet "t" ab prog
      = letB "t" ab (ret (add (var "t") (var "t"))) := by
  rfl

/-- CSE preserves the denotation of the worked example under any environment over
`ℤ`. The fresh name `"t"` is not free in `a*b`, discharging the side-condition. -/
theorem cseLet_prog_denote (env : String → ℤ) :
    FLet.denote env (FLet.cseLet "t" ab prog) = FLet.denote env (ret prog) :=
  FLet.cseLet_denote env "t" ab prog (by decide) (by decide)

/-- Denotation preservation is characteristic-free: it holds over every `ZMod p`
as well, by the same `cseLet_denote` theorem. -/
theorem cseLet_prog_denote_zmod (p : Nat) (env : String → ZMod p) :
    FLet.denote env
        (FLet.cseLet "t" (mul (var "a") (var "b"))
          (add (mul (var "a") (var "b")) (mul (var "a") (var "b"))))
      = FLet.denote env
          (ret (add (mul (var "a") (var "b")) (mul (var "a") (var "b")))) :=
  FLet.cseLet_denote env "t" (mul (var "a") (var "b"))
    (add (mul (var "a") (var "b")) (mul (var "a") (var "b")))
    (by rfl) (by rfl)

end Example

end FLet

end CatCrypt.Crypto.Optimizer.Rewrite.FieldCsePass
