/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Logic.Equiv.Defs

/-!
# Representation transfer for verified native compute (the `@[implemented_by]` /
  `@[csimp]` connection)

The `ReprTransfer` commuting square `enc (op a b) = bop (enc a) (enc b)` is
exactly the correspondence `@[implemented_by]` *asserts but never checks*: that a
fast/native `bop` computes the abstract `op`. So a realization is the **verified
analogue of `@[implemented_by]`** — it carries the proof that attribute omits.

Two regimes, matching Lean's two impl-swap mechanisms:

* **Representation-changing** (`enc` a non-identity `Equiv`, the CoqEAL "refinement for
  compute" pattern): compute on the concrete representation with `bop`, then
  decode. `EndoOpRefinement.compute_via` is the proved justification for an
  `@[implemented_by fun a b => decode (bop (encode a) (encode b))]`.
* **Same-representation** (`enc = id`): the square collapses to function equality
  `op = bop`, which `@[csimp]` consumes to replace `op` by `bop` in compiled code
  — soundly, *because we proved it*. `EndoOpRefinement.funEq` produces exactly
  such a lemma. This is the verified counterpart of `@[implemented_by]`
  (which is trusted: the kernel never sees a proof).

## Scope

This makes verified native compute available **only when the concrete `bop` is an
actual computable Lean function** (e.g. the emitted `BitVec` field kernels
`bbMul`/`bbAdd`/`barrettReduceMU`). It does **not** make the BLS12-381
`prims.pairing` run: that is an opaque `BlsPrimitives` field (a hypothesis), not a
computable definition — so the pairing bridges stay *specification* transfers, not
executable ones. The boundary is: a realization is verified-`@[csimp]` material
**iff** its `bop` is computable. The worked example below demonstrates the
mechanism end-to-end.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.ReprTransfer

universe u

/-- An **operation refinement** along an equivalence: the abstract `op` and a
    (typically faster, computable) `bop` tied by a bijective encoding + a
    commuting square. The verified analogue of `@[implemented_by]` — it carries
    the proof that the impl computes the spec. -/
structure EndoOpRefinement {A α : Type u} (op : A → A → A) (bop : α → α → α) where
  /-- The bijective encoding between abstract and concrete representations. -/
  equiv : A ≃ α
  /-- The commuting square tying `op` to `bop`. -/
  commutes : ∀ a b, equiv (op a b) = bop (equiv a) (equiv b)

namespace EndoOpRefinement
variable {A α : Type u} {op : A → A → A} {bop : α → α → α}

/-- **Refinement native compute.** Compute on the concrete representation with the
    fast `bop`, then decode: `op a b = decode (bop (encode a) (encode b))`. This is
    the proved justification for an `@[implemented_by]` that runs `bop` — unlike a
    bare `@[implemented_by]`, the correspondence is a theorem. -/
theorem compute_via (R : EndoOpRefinement op bop) (a b : A) :
    op a b = R.equiv.symm (bop (R.equiv a) (R.equiv b)) := by
  rw [← R.commutes, Equiv.symm_apply_apply]

/-- **Same-representation refinement ⇒ `@[csimp]`-eligible equality.** When the
    abstract and concrete representations coincide and the square holds pointwise,
    it collapses to the function equality `op = bop` that `@[csimp]` uses to
    soundly replace `op` by `bop` in compiled code. -/
theorem funEq {B : Type u} {f g : B → B → B} (commutes : ∀ a b, f a b = g a b) :
    f = g := by
  funext a b; exact commutes a b

end EndoOpRefinement

/-! ## Worked example: a verified `@[csimp]` replacement

A "spec" multiply (Peano-style, slow) replaced by native `*` — the swap
`@[implemented_by]` would make *without* a proof, here made *with* one via
`@[csimp]`. -/

/-- A specification-style multiply: structurally recursive, slow. -/
def slowMul : Nat → Nat → Nat
  | _, 0 => 0
  | a, (n + 1) => slowMul a n + a

/-- `slowMul` computes ordinary multiplication. -/
theorem slowMul_eq (a b : Nat) : slowMul a b = a * b := by
  induction b with
  | zero => simp [slowMul]
  | succ n ih => simp [slowMul, ih, Nat.mul_succ]

/-- **Verified compiled-code replacement.** `@[csimp]` swaps `slowMul` for native
    `Nat.mul` in compiled output — and unlike `@[implemented_by]`, the swap is
    proof-carrying (this lemma), so it is sound by construction. (`@[csimp]`
    requires a constant on the right, so we target `Nat.mul` rather than the
    lambda `(· * ·)`; `EndoOpRefinement.funEq` gives the pointwise version.) -/
@[csimp] theorem slowMul_csimp : slowMul = Nat.mul := by
  funext a b; rw [slowMul_eq]; rfl

/-- `slowMul` computes (small kernel check). After `@[csimp]`, the *compiled*
    `slowMul` runs as native `*` (e.g. `#eval slowMul 123456 654321`), while this
    proof and `slowMul_eq` certify the spec — the verified impl swap. -/
example : slowMul 7 6 = 42 := by decide

end CatCrypt.Crypto.Bridges.ReprTransfer
