/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Bridges.ReprTransfer
public import CatCrypt.Hax.Runtime

/-!
# Array-of-encoded-values transfer

`ReprTransfer` relates a single abstract value to its computational encoding.
An extraction bridge needs the same relation *pointwise over a state array*: a
haxpipe extraction carries state as `Array γ` (γ = `Int` for the width-tagged
`Hax.*_w` operators) while the reference carries it as `Fin n → C` (C = `BitVec
64` lanes for Keccak, `ZMod 2` coefficients for a GF(2) ring, a field element
per limb for a curve). `ArrayAgree` is that pointwise relation, and the lemmas
here are the read/write primitives every such bridge uses.

The layer is generic in the embedding, so one set of lemmas serves each
representation: instantiate `ReprEmbedding C γ` and the array reasoning follows.

## Main definitions

* `UnOpRealization` — the unary counterpart of `BinOpRealization` (rotations,
  complements, and per-element maps are unary).
* `ArrayAgree e n arr f` — `arr` represents `f` lane-by-lane along `e`.
* `ArrayAgree.get` / `getI` — reading a represented lane.
* `ArrayAgree.update` / `updateI` — writing one through `Hax.array_update`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.ReprTransfer

universe u

/-! ## Unary operation realization -/

/-- A **unary-operation realization**: the abstract `op : A → C` is realized by
    the computational `uop : α → γ` along a domain encoding and a codomain
    embedding. The unary counterpart of `BinOpRealization`; rotations,
    complements and per-element maps take this form. -/
structure UnOpRealization {A C : Type u} {α γ : Type u}
    (op : A → C) (uop : α → γ) where
  /-- Encoding of the operand. -/
  encA : A → α
  /-- Equality-reflecting encoding of the result. -/
  cod : ReprEmbedding C γ
  /-- The commuting square tying `op` to `uop`. -/
  commutes : ∀ a : A, cod.enc (op a) = uop (encA a)

namespace UnOpRealization
variable {A C : Type u} {α γ : Type u} {op : A → C} {uop : α → γ}

/-- An abstract equation between `op` applications holds iff `uop` agrees on the
    encoded operands. -/
theorem eq_transfer (R : UnOpRealization op uop) (a a' : A) :
    op a = op a' ↔ uop (R.encA a) = uop (R.encA a') := by
  rw [← R.commutes, ← R.commutes]
  exact ⟨fun h => by rw [h], fun h => R.cod.enc_inj h⟩

end UnOpRealization

/-! ## Array agreement -/

variable {C γ : Type}

/-- `arr` represents the indexed family `f` along the embedding `e`: it has
    length `n`, and every position holds the encoding of the corresponding
    abstract value. This is the state relation an extraction bridge threads
    through its loops. -/
def ArrayAgree [Inhabited γ] (e : ReprEmbedding C γ) (n : Nat)
    (arr : Array γ) (f : Fin n → C) : Prop :=
  arr.size = n ∧ ∀ k : Fin n, Hax.index arr (k.val : Int) = e.enc (f k)

namespace ArrayAgree
variable [Inhabited γ] {e : ReprEmbedding C γ} {n : Nat} {arr : Array γ} {f : Fin n → C}

theorem size (h : ArrayAgree e n arr f) : arr.size = n := h.1

/-- Read a represented position at a `Fin` index. -/
theorem get (h : ArrayAgree e n arr f) (k : Fin n) :
    Hax.index arr (k.val : Int) = e.enc (f k) := h.2 k

/-- Read a represented position at an in-range `Int` index. -/
theorem getI (h : ArrayAgree e n arr f) (k : Int) (hk0 : 0 ≤ k) (hk : k < n) :
    Hax.index arr k = e.enc (f ⟨k.toNat, by omega⟩) := by
  have hval : ((k.toNat : Nat) : Int) = k := Int.toNat_of_nonneg hk0
  have hh := h.2 ⟨k.toNat, by omega⟩
  simpa [hval] using hh

end ArrayAgree

/-! ## `Hax.index` / `Hax.array_update` interaction

These are representation-independent facts about the extraction's array
primitives; the agreement lemmas below are stated in terms of them. -/

@[simp] theorem array_update_size {α : Type} (arr : Array α) (i : Int) (v : α) :
    (Hax.array_update arr i v).size = arr.size := by
  simp only [Hax.array_update]; split <;> simp

/-- Reading the position just written by an in-bounds `array_update`. -/
theorem index_array_update_self {α : Type} [Inhabited α] (a : Array α) (i : Int) (v : α)
    (hi : i.toNat < a.size) : Hax.index (Hax.array_update a i v) i = v := by
  simp only [Hax.array_update, Hax.index, dif_pos hi, Array.size_set, Array.getElem_set_self]

/-- Reading a different, in-bounds position of an `array_update` passes through. -/
theorem index_array_update_ne {α : Type} [Inhabited α] (a : Array α) (i k : Int) (v : α)
    (hik : k.toNat ≠ i.toNat) (hk : k.toNat < a.size) :
    Hax.index (Hax.array_update a i v) k = Hax.index a k := by
  by_cases hi : i.toNat < a.size
  · simp only [Hax.index, Hax.array_update, dif_pos hi, Array.size_set, dif_pos hk]
    rw [Array.getElem_set_ne _ _ (by omega)]
  · simp only [Hax.array_update, dif_neg hi]

/-- Reading an `Int` index into an array through `Hax.index`. -/
theorem index_fin {α : Type} [Inhabited α] {n : Nat} (a : Array α) (m : Fin n)
    (h : m.val < a.size) : Hax.index a (m.val : Int) = a[m.val] := by
  simp only [Hax.index, Int.toNat_natCast]; rw [dif_pos h]

namespace ArrayAgree
variable [Inhabited γ] {e : ReprEmbedding C γ} {n : Nat} {arr : Array γ} {f : Fin n → C}

/-- Writing one position through `Hax.array_update` preserves representation,
    updating the abstract family at that index. -/
theorem update (h : ArrayAgree e n arr f) (k : Fin n) (v : C) :
    ArrayAgree e n (Hax.array_update arr (k.val : Int) (e.enc v)) (Function.update f k v) := by
  obtain ⟨hsz, hidx⟩ := h
  have hk : k.val < arr.size := by rw [hsz]; exact k.isLt
  have hupd : Hax.array_update arr (k.val : Int) (e.enc v) = arr.set k.val (e.enc v) hk := by
    simp only [Hax.array_update, Int.toNat_natCast]; rw [dif_pos hk]
  refine ⟨by rw [hupd, Array.size_set, hsz], ?_⟩
  intro m
  have hm : m.val < (arr.set k.val (e.enc v) hk).size := by
    rw [Array.size_set, hsz]; exact m.isLt
  rw [hupd, index_fin _ m hm, Array.getElem_set, Function.update_apply]
  by_cases hkm : k = m
  · subst hkm; simp
  · have hne : k.val ≠ m.val := fun hc => hkm (Fin.ext hc)
    rw [if_neg hne, if_neg (fun hc : m = k => hkm hc.symm),
        ← index_fin arr m (by rw [hsz]; exact m.isLt)]
    exact hidx m

/-- Writing at an in-range `Int` index. -/
theorem updateI (h : ArrayAgree e n arr f) (k : Int) (kf : Fin n)
    (hk0 : 0 ≤ k) (hkeq : k.toNat = kf.val) (v : C) :
    ArrayAgree e n (Hax.array_update arr k (e.enc v)) (Function.update f kf v) := by
  have hval : ((k.toNat : Nat) : Int) = k := Int.toNat_of_nonneg hk0
  have hidxeq : ((kf.val : Nat) : Int) = k := by rw [← hkeq]; exact hval
  have hupd := h.update kf v
  rwa [hidxeq] at hupd

end ArrayAgree

end CatCrypt.Crypto.Bridges.ReprTransfer
