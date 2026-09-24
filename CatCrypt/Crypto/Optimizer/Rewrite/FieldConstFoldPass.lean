/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Algebraic constant-folding pass for the field/ModArith dialect

A verified constant-folding pass over a tiny straight-line field-arithmetic IR
`FExpr R` (add / sub / mul / const / var) over a generic commutative ring `R`.
Because the whole development is parametric in `[CommRing R]`, it specializes to
*every* prime field `ZMod p`, and indeed to `ℤ` or any other commutative ring —
the same proved pass folds constants at any ModArith dialect level.

The pass `constFold` performs two kinds of bottom-up rewrites:

* **constant propagation** — an operation whose operands are both `const` is
  evaluated at compile time (`add (const a) (const b) ↦ const (a + b)`, and
  similarly for `sub`/`mul`);
* **algebraic identities** — `add e (const 0) ↦ e`, `mul e (const 1) ↦ e`,
  `mul e (const 0) ↦ const 0` and their symmetric variants.

The main theorem is `constFold_denote`: the pass is *denotation-preserving* under any
environment `env : Nat → R`, so it is a sound optimizer pass — no value is ever
changed, only its representation is shrunk. The proof is by structural induction;
each fold case is discharged by the ring axioms (`add_zero`, `mul_one`,
`mul_zero`, …) via `simp`/`ring`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.FieldConstFoldPass

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

Each smart constructor folds a single operation on already-folded operands. They
are denotation-preserving by construction (`smartAdd_denote`, etc.). -/

variable [DecidableEq R]

/-- Fold an `add` node: evaluate two constants, drop a `0` summand. -/
def smartAdd (a b : FExpr R) : FExpr R :=
  match a, b with
  | const x, const y => const (x + y)
  | a, const y => if y = 0 then a else add a (const y)
  | const x, b => if x = 0 then b else add (const x) b
  | a, b => add a b

/-- Fold a `sub` node: evaluate two constants, drop a `0` subtrahend. -/
def smartSub (a b : FExpr R) : FExpr R :=
  match a, b with
  | const x, const y => const (x - y)
  | a, const y => if y = 0 then a else sub a (const y)
  | a, b => sub a b

/-- Fold a `mul` node: evaluate two constants, apply the `0`/`1` identities. -/
def smartMul (a b : FExpr R) : FExpr R :=
  match a, b with
  | const x, const y => const (x * y)
  | a, const y =>
      if y = 0 then const 0 else if y = 1 then a else mul a (const y)
  | const x, b =>
      if x = 0 then const 0 else if x = 1 then b else mul (const x) b
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
  split <;> (try split_ifs) <;> simp_all

/-! ## The pass -/

/-- The constant-folding pass: recurse bottom-up, folding each node via the
smart constructors. -/
def constFold : FExpr R → FExpr R
  | const c => const c
  | var i => var i
  | add a b => smartAdd (constFold a) (constFold b)
  | sub a b => smartSub (constFold a) (constFold b)
  | mul a b => smartMul (constFold a) (constFold b)

/-- **Soundness.** The constant-folding pass is denotation-preserving: it never
changes the value of an expression under any environment, only its
representation. -/
@[simp] theorem constFold_denote (env : Nat → R) (e : FExpr R) :
    denote env (constFold e) = denote env e := by
  induction e with
  | const c => rfl
  | var i => rfl
  | add a b iha ihb => simp [constFold, iha, ihb]
  | sub a b iha ihb => simp [constFold, iha, ihb]
  | mul a b iha ihb => simp [constFold, iha, ihb]

/-! ## Worked example

Folding `(3 + 4) * x` collapses the constant subterm to `7 * x`. The example is
stated over `ℤ` (rather than a generic ring) because the *syntactic* result
depends on the characteristic — e.g. over `ZMod 7` the subterm `3 + 4` is `0`,
so the pass folds the whole product to `const 0`. Denotation preservation, by
contrast, holds over every ring, and is checked below over an arbitrary
`ZMod p`. -/

/-- The example expression `(const 3 + const 4) * var 0` over a ring `R`. -/
def example347 (R : Type*) [CommRing R] : FExpr R :=
  mul (add (const 3) (const 4)) (var 0)

/-- Over `ℤ`, `constFold` collapses the constant subexpression `3 + 4` to `7`,
leaving `7 * x`. -/
theorem constFold_example347 :
    constFold (example347 ℤ) = mul (const (7 : ℤ)) (var 0) := by
  show smartMul (smartAdd (const 3) (const 4)) (var 0) = _
  rfl

/-- The folded form denotes the same value as the original `(3 + 4) * x` under
any environment over `ZMod p` — denotation preservation is characteristic-free. -/
theorem example347_denote_preserved (p : Nat) (env : Nat → ZMod p) :
    denote env (constFold (example347 (ZMod p))) = denote env (example347 (ZMod p)) :=
  constFold_denote env _

end CatCrypt.Crypto.Optimizer.Rewrite.FieldConstFoldPass
