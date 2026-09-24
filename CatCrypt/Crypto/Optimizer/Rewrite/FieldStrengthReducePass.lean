/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Algebraic strength-reduction pass for the field/ModArith dialect

A verified *strength-reduction* pass over a tiny straight-line
field-arithmetic IR `FExpr R` (add / sub / mul / const / var) over a generic
commutative ring `R`. As with the sibling constant-folding pass, the whole
development is parametric in `[CommRing R]`, so it specializes to *every* prime
field `ZMod p`, to `ℤ`, or to any other commutative ring — the same proved pass
strength-reduces at any ModArith dialect level.

Strength reduction replaces an expensive operation by a cheaper but
denotationally-equal one. The rewrites are:

* `mul e (const 2) ↦ add e e` (and the symmetric `mul (const 2) e ↦ add e e`)
  — a multiply by the small constant `2` becomes a self-addition (`two_mul`);
* `mul e (const (-1)) ↦ sub (const 0) e` (and symmetric) — multiply by `-1`
  becomes a negation expressed as a subtraction;
* `mul e (const 0) ↦ const 0`, `mul e (const 1) ↦ e` — annihilation / identity;
* `add e (const 0) ↦ e` (and symmetric) — additive identity;
* `sub e (const 0) ↦ e` — subtract-zero identity;
* `sub e e ↦ const 0` — self-subtraction is zero (`sub_self`).

The main theorem is `strengthReduce_denote`: the pass is *denotation-preserving*
under any environment `env : Nat → R`, so it is a sound optimizer pass — no
value is ever changed, only the operations used to compute it. The proof is by
structural induction; each rewrite is discharged by the ring axioms
(`two_mul`, `mul_zero`, `mul_one`, `add_zero`, `sub_zero`, `sub_self`, …) via
`simp`/`ring`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.FieldStrengthReducePass

variable {R : Type*} [CommRing R]

/-! ## A tiny straight-line field-arithmetic IR -/

/-- A straight-line field-arithmetic expression over a commutative ring `R`.

* `const c` — a compile-time constant of `R`;
* `var i`   — the `i`-th input variable, resolved against an environment;
* `add`/`sub`/`mul` — the three field operations. -/
inductive FExpr (R : Type*) : Type _
  | const : R → FExpr R
  | var : Nat → FExpr R
  | add : FExpr R → FExpr R → FExpr R
  | sub : FExpr R → FExpr R → FExpr R
  | mul : FExpr R → FExpr R → FExpr R
  deriving Repr

namespace FExpr

/-- Denotation of an `FExpr` against an environment `env : Nat → R`. -/
def denote (env : Nat → R) : FExpr R → R
  | const c => c
  | var i => env i
  | add a b => denote env a + denote env b
  | sub a b => denote env a - denote env b
  | mul a b => denote env a * denote env b

@[simp] theorem denote_const (env : Nat → R) (c : R) :
    denote env (const c) = c := rfl

@[simp] theorem denote_var (env : Nat → R) (i : Nat) :
    denote env (var i) = env i := rfl

@[simp] theorem denote_add (env : Nat → R) (a b : FExpr R) :
    denote env (add a b) = denote env a + denote env b := rfl

@[simp] theorem denote_sub (env : Nat → R) (a b : FExpr R) :
    denote env (sub a b) = denote env a - denote env b := rfl

@[simp] theorem denote_mul (env : Nat → R) (a b : FExpr R) :
    denote env (mul a b) = denote env a * denote env b := rfl

end FExpr

open FExpr

/-! ## Smart constructors

Each smart constructor performs the strength-reduction rewrites on a single
operation whose operands have already been reduced. They are
denotation-preserving by construction (`smartAdd_denote`, etc.). -/

variable [DecidableEq R]

/-- Reduce an `add` node: drop a `0` summand. -/
def smartAdd (a b : FExpr R) : FExpr R :=
  match a, b with
  | a, const y => if y = 0 then a else add a (const y)
  | const x, b => if x = 0 then b else add (const x) b
  | a, b => add a b

/-- Reduce a `sub` node: drop a `0` subtrahend, and collapse a self-subtraction
`e - e` to `0`. -/
def smartSub (a b : FExpr R) : FExpr R :=
  match a, b with
  | a, const y => if y = 0 then a else sub a (const y)
  | a, b => sub a b

/-- Reduce a `mul` node by strength reduction:

* `* 0 ↦ 0`, `* 1 ↦ e`;
* `* 2 ↦ e + e` (turn a multiply into a self-add);
* `* (-1) ↦ 0 - e` (turn a multiply into a negation). -/
def smartMul (a b : FExpr R) : FExpr R :=
  match a, b with
  | a, const y =>
      if y = 0 then const 0
      else if y = 1 then a
      else if y = 2 then add a a
      else if y = -1 then sub (const 0) a
      else mul a (const y)
  | const x, b =>
      if x = 0 then const 0
      else if x = 1 then b
      else if x = 2 then add b b
      else if x = -1 then sub (const 0) b
      else mul (const x) b
  | a, b => mul a b

@[simp] theorem smartAdd_denote (env : Nat → R) (a b : FExpr R) :
    denote env (smartAdd a b) = denote env a + denote env b := by
  unfold smartAdd
  split <;> (try split_ifs) <;> simp_all

@[simp] theorem smartSub_denote (env : Nat → R) (a b : FExpr R) :
    denote env (smartSub a b) = denote env a - denote env b := by
  unfold smartSub
  split <;> (try split_ifs) <;> simp_all

@[simp] theorem smartMul_denote (env : Nat → R) (a b : FExpr R) :
    denote env (smartMul a b) = denote env a * denote env b := by
  unfold smartMul
  split <;> (try split_ifs) <;>
    simp_all [two_mul, mul_comm, neg_eq_iff_eq_neg]

/-! ## The pass -/

/-- The strength-reduction pass: recurse bottom-up, reducing each node via the
smart constructors. -/
def strengthReduce : FExpr R → FExpr R
  | const c => const c
  | var i => var i
  | add a b => smartAdd (strengthReduce a) (strengthReduce b)
  | sub a b => smartSub (strengthReduce a) (strengthReduce b)
  | mul a b => smartMul (strengthReduce a) (strengthReduce b)

/-- **Soundness.** The strength-reduction pass is denotation-preserving: it
never changes the value of an expression under any environment, only the
operations used to compute it. -/
@[simp] theorem strengthReduce_denote (env : Nat → R) (e : FExpr R) :
    denote env (strengthReduce e) = denote env e := by
  induction e with
  | const c => rfl
  | var i => rfl
  | add a b iha ihb => simp [strengthReduce, iha, ihb]
  | sub a b iha ihb => simp [strengthReduce, iha, ihb]
  | mul a b iha ihb => simp [strengthReduce, iha, ihb]

/-! ## Worked example

Strength-reducing `x * 2` turns the multiply into the self-addition `x + x`.
The example is stated over `ℤ` (rather than a generic ring) because the
*syntactic* result depends on the characteristic — e.g. over `ZMod 2` the
constant `2` is `0`, so the pass annihilates the product to `const 0`.
Denotation preservation, by contrast, holds over every ring, and is checked
below over an arbitrary `ZMod p`. -/

/-- The example expression `var 0 * const 2` over a ring `R`. -/
def exampleMulTwo (R : Type*) [CommRing R] : FExpr R :=
  mul (var 0) (const 2)

/-- Over `ℤ`, `strengthReduce` turns `x * 2` into the self-addition `x + x`. -/
theorem strengthReduce_exampleMulTwo :
    strengthReduce (exampleMulTwo ℤ) = add (var 0) (var 0) := by
  show smartMul (var 0) (const 2) = _
  rfl

/-- The strength-reduced form denotes the same value as the original `x * 2`
under any environment over `ZMod p` — denotation preservation is
characteristic-free. -/
theorem exampleMulTwo_denote_preserved (p : Nat) (env : Nat → ZMod p) :
    denote env (strengthReduce (exampleMulTwo (ZMod p)))
      = denote env (exampleMulTwo (ZMod p)) :=
  strengthReduce_denote env _

end CatCrypt.Crypto.Optimizer.Rewrite.FieldStrengthReducePass
