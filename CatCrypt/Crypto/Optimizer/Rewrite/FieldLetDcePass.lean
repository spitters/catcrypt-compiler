/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Verified dead-let-elimination (DCE) for a let-binding field IR

A straight-line, *let-binding* field-arithmetic IR `FLet R` over a generic
commutative ring `R`, together with a verified dead-binding-elimination pass
`dce`, proved denotation-preserving. Because the development is parametric in
`[CommRing R]`, the same proved pass runs at every ModArith dialect level
(`ZMod p`, `ℤ`, …). This complements the bottom-up algebraic constant folder in
`FieldConstFoldPass.lean`: there the rewrites are *intra-expression*; here the
rewrite eliminates a whole `let`-binding whose result is never consumed.

## Named-variable choice

The IR uses **named** variables (`String`), not De Bruijn indices. Both are
standard; for a DCE pass — whose whole content is *"the value of an unused
binding is irrelevant"* — names sidestep the index-renumbering bookkeeping that
De Bruijn forces on every `let` removal (decrementing all outer indices). With
names, dropping a binding `x := e` leaves the rest of the program textually
unchanged, so the irrelevance lemma is a clean statement about variable
environments. The environment is a function `String → R`; updating it at one
name is `Function.update`.

## The IR

* `FExpr R` — `const / var / add / sub / mul`, variables are `String`s resolved
  against an environment `env : String → R`.
* `FLet R` — a chain of `let`s ending in a `ret`:
  * `ret e`        — return the value of `e`;
  * `letB x e body` — bind name `x` to the value of `e`, then run `body` under
    the updated environment.

## The pass

`freeInExpr x e` / `freeIn x p` decide whether a variable name `x` occurs in an
expression / program. When a `letB x e body` has `x` *not* free in `body`, the
binding is dead: `dce` drops it, keeping `body` (recursively cleaned) verbatim.
The main theorem `dce_denote` shows the single-pass DCE is denotation-preserving.

The real content is the **irrelevance lemma** `denote_update_of_not_free`: if a
name `x` is not free in a body, then updating the environment at `x` with *any*
value `v` leaves the body's denotation unchanged — the dropped binding's value
cannot be observed. It is proved by structural induction, threading the
`freeIn x _ = false` hypothesis through each subterm.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.FieldLetDcePass

variable {R : Type*} [CommRing R]

/-! ## A straight-line let-binding field IR (named variables) -/

/-- A field-arithmetic expression with named (`String`) variables over `R`. -/
inductive FExpr (R : Type*) : Type _
  | const : R → FExpr R
  | var : String → FExpr R
  | add : FExpr R → FExpr R → FExpr R
  | sub : FExpr R → FExpr R → FExpr R
  | mul : FExpr R → FExpr R → FExpr R
  deriving Repr

/-- A straight-line let-binding program: a chain of named `let`s ending in a
return. -/
inductive FLet (R : Type*) : Type _
  | ret : FExpr R → FLet R
  | letB : String → FExpr R → FLet R → FLet R
  deriving Repr

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

/-- Whether the name `x` occurs anywhere in a program (in any bound expression or
the returned expression). A bound name *shadowing* `x` does not stop `x` from
being "free" by this test — but for the DCE soundness argument we only ever query
`freeIn x body` for the `x` *just bound* by the enclosing `letB`, and use it to
justify that the bound value is irrelevant; correctness holds regardless of
shadowing because the irrelevance lemma is about a single environment update. -/
def freeIn (x : String) : FLet R → Bool
  | ret e => e.freeInExpr x
  | letB _ e body => e.freeInExpr x || freeIn x body

end FLet

/-! ## The DCE pass

`dce` walks the `let`-chain. At a `letB x e body`, it first DCE-cleans `body`. If
`x` is not free in the cleaned body, the binding is dead and is dropped (the body
stays textually identical); otherwise the binding is kept. Single-pass / bounded:
one structural recursion through the program. -/

namespace FLet

/-- Single-pass dead-let elimination. -/
def dce : FLet R → FLet R
  | ret e => ret e
  | letB x e body =>
      let body' := dce body
      if freeIn x body' then letB x e body' else body'

end FLet

/-! ## Soundness -/

namespace FLet

/-- Program-level irrelevance: if `x` is not free in a program `p`, then updating
the environment at `x` with *any* value `v` leaves `p`'s denotation unchanged.
This lifts `FExpr.denote_update_of_not_free` over the `let`-chain. The `letB`
case re-establishes the hypothesis after the inner `Function.update` by a
commuting-updates argument. -/
theorem denote_update_of_not_free (x : String) (v : R) :
    ∀ (env : String → R) (p : FLet R), freeIn x p = false →
      denote (Function.update env x v) p = denote env p
  | env, ret e, h => FExpr.denote_update_of_not_free env x v e h
  | env, letB y e body, h => by
      simp only [freeIn, Bool.or_eq_false_iff] at h
      obtain ⟨he, hbody⟩ := h
      simp only [denote_letB]
      -- The bound expression `e` is not free in `x`, so its value is the same
      -- under the `x`-update.
      rw [FExpr.denote_update_of_not_free env x v e he]
      -- Now relate `update (update env x v) y w` to `update env y w`.
      by_cases hxy : x = y
      · subst hxy
        -- Updating at `x` then overwriting at `x` (= `y`) erases the `v`-update.
        rw [Function.update_idem]
      · -- Distinct names: the two updates commute, then peel the outer
        -- `x`-update using the body hypothesis.
        rw [Function.update_comm hxy]
        exact denote_update_of_not_free x v
          (Function.update env y (e.denote env)) body hbody

/-- **Soundness.** Single-pass DCE is denotation-preserving under any
environment: dropping dead `let`-bindings never changes a program's value. -/
theorem dce_denote :
    ∀ (env : String → R) (p : FLet R), denote env (dce p) = denote env p
  | _, ret _ => rfl
  | env, letB x e body => by
      simp only [dce]
      split
      · -- binding kept: recurse on the cleaned body.
        simp only [denote_letB, dce_denote (Function.update env x (e.denote env)) body]
      · -- binding dropped: `x` not free in the cleaned body, so the bound value
        -- is irrelevant; combine the recursion with the irrelevance lemma.
        rename_i hx
        simp only [Bool.not_eq_true] at hx
        rw [denote_letB,
          ← denote_update_of_not_free x (e.denote env) env (dce body) hx,
          dce_denote (Function.update env x (e.denote env)) body]

end FLet

/-! ## Worked example

Two bindings, one dead. `x := 5` is *used* (it feeds `y`), but `y := x + 1` is
*dead* — the program returns `x`, never `y`. DCE removes the `y` binding while
preserving the (constant) `let x := 5`, and the denotation is unchanged. The
example is over `ℤ` so the syntactic result is unambiguous; denotation
preservation, proved by `dce_denote`, holds over every ring. -/

namespace Example

open FExpr FLet

/-- `let x := 5 in let y := x + 1 in x` — the `y` binding is dead. -/
def prog : FLet ℤ :=
  letB "x" (const 5)
    (letB "y" (add (var "x") (const 1))
      (ret (var "x")))

/-- After DCE the dead `y`-binding is gone; only `let x := 5 in x` remains. -/
theorem dce_prog :
    FLet.dce prog = letB "x" (const 5) (ret (var "x")) := by
  rfl

/-- Both the original and the DCE'd program return `5` under any environment. -/
theorem prog_value (env : String → ℤ) :
    FLet.denote env prog = 5 := by
  simp [prog, FLet.denote, FExpr.denote, Function.update_self]

/-- DCE preserves the denotation of the worked example under any environment over
any ring `ZMod p` — denotation preservation is characteristic-free. -/
theorem dce_prog_denote_preserved (p : Nat) (env : String → ZMod p) :
    FLet.denote env
        (FLet.dce
          (letB "x" (const 5)
            (letB "y" (add (var "x") (const 1)) (ret (var "x")))))
      = FLet.denote env
          (letB "x" (const 5)
            (letB "y" (add (var "x") (const 1)) (ret (var "x")))) :=
  FLet.dce_denote env _

end Example

end CatCrypt.Crypto.Optimizer.Rewrite.FieldLetDcePass
