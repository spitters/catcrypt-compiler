/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# MLIR `vector` dialect — Types

The element-and-length parameterised type of a vector dialect value, mirroring
MLIR's `vector<n × α>` shape. We deliberately use a **lane-function** model

```
VectorTy α n := Fin n → α
```

over the heavier Mathlib `Vector α n` (`List`-backed) because:

* every op we model here is per-lane (`add`, `mul`, `broadcast`, `extract`,
  `shuffle`, `reduce`) — a function `Fin n → α` is the cleanest carrier;
* it sidesteps Mathlib `Vector`-vs-`List.Vector`-vs-`Array` churn that has
  bitten previous refactors (cf. the upgrade notes in the private companion
  repo);
* downstream lowerings that target `BitVec`-shaped lanes can specialise
  `α := BitVec w` without touching the type structure.

A future Phase-2 may swap in Mathlib `Vector` if a particular consumer needs
list-style operations; the current ops do not.

This is the first file of the new MLIR-style **VectorDialect** scaffolding
(task #183). See `README.md` in the same directory for the progressive-lowering
plan and the relationship with the existing `VIR/MlirVectorDialect.lean`
(BitVec-lane, already-denoting analogue).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-- A length-indexed vector of elements of type `α`. Modelled as a total
    lane-function `Fin n → α` (cf. file docstring). -/
@[reducible] def VectorTy (α : Type) (n : Nat) : Type := Fin n → α

namespace VectorTy

variable {α : Type} {n : Nat}

/-- The constant vector with `x` in every lane. The denotation of
    `VectorOp.broadcast`. -/
@[reducible] def replicate (x : α) : VectorTy α n := fun _ => x

/-- Set the `i`-th lane of `v` to `x`, leaving every other lane untouched.
    Used to denote `VectorOp.insert` (the "splat into one lane" op). -/
def insert (v : VectorTy α n) (i : Fin n) (x : α) : VectorTy α n :=
  fun j => if _ : j = i then x else v j

/-- Read the `i`-th lane. The denotation of `VectorOp.extract`. -/
@[reducible] def get (v : VectorTy α n) (i : Fin n) : α := v i

/-- Pointwise apply a binary `α`-operation `op` to two vectors. The shared
    shape of `VectorOp.add`, `VectorOp.mul`, etc. -/
@[reducible] def map₂ (op : α → α → α) (v w : VectorTy α n) : VectorTy α n :=
  fun i => op (v i) (w i)

/-- Pointwise apply a unary `α`-operation. -/
@[reducible] def map₁ (op : α → α) (v : VectorTy α n) : VectorTy α n :=
  fun i => op (v i)

/-- Pointwise apply a unary `α`-operation that carries an immediate `Nat`
    parameter (the shape of `shiftL`/`shiftR`'s lane op `α → Nat → α`). -/
@[reducible] def map₁imm (op : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    VectorTy α n :=
  fun i => op (v i) m

/-- Apply a permutation `π : Fin n → Fin n` to the lanes (shuffle). -/
@[reducible] def shuffle (π : Fin n → Fin n) (v : VectorTy α n) : VectorTy α n :=
  fun i => v (π i)

/-- Fold the lanes left-to-right with `op` starting from `init`. -/
def reduce (op : α → α → α) (init : α) (v : VectorTy α n) : α :=
  (List.finRange n).foldl (fun acc i => op acc (v i)) init

theorem get_replicate (x : α) (i : Fin n) :
    (replicate (n := n) x).get i = x := rfl

theorem map₂_apply (op : α → α → α) (v w : VectorTy α n) (i : Fin n) :
    (map₂ op v w) i = op (v i) (w i) := rfl

theorem replicate_apply (x : α) (i : Fin n) :
    (replicate (n := n) x : VectorTy α n) i = x := rfl

end VectorTy

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
