/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.BatchInverse


@[expose] public section
set_option autoImplicit false

/-!
# Montgomery's batch inversion as a generic optimizer rewrite (array form)

Montgomery's trick replaces `n` independent field inverses by **one** inverse
plus `3·(n−1)` multiplies. The correctness core — the scan identity over any
`Field F` (`batchInv as = as.map (·⁻¹)` when every entry is nonzero) and the
operation counts — is already proved list-generically in
`CatCrypt.Crypto.Pairing.BatchInverse`. **This file does not re-prove that
core.** It packages it as a reusable *optimizer rewrite*:

* an **`Array`-valued** entry point `batchInvArray`, the shape an
  affine-conversion / MSM pass actually threads (slope and z-coordinate batches
  are arrays/vectors, not cons-lists), proved bit-identical to the per-element
  `Array.map (·⁻¹)` it rewrites away;
* the **EC-MSM amortized-inverse tie** `affineBatchConvert`: converting a batch
  of `(num, den)` field pairs `numᵢ / denᵢ` (the chord/tangent-slope or
  projective→affine `x = X·Z⁻¹` shape) using a single shared inverse, proved
  equal to the naive per-point division;
* the op-count comparison re-exported in array terms (`mulCount`, `invCount`,
  `arrayBatchInv_invCount_lt_naive`), quantifying the win for `n ≥ 2`.

A peephole pass that recognises a `map (·⁻¹)` over an array of provably-nonzero
field elements may rewrite it to `batchInvArray`; the equality lemma here is its
soundness certificate. All goals are discharged by reduction to the list core
and standard automation; only the standard `propext`/`Classical.choice`/
`Quot.sound` axioms are used.
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.BatchInverseGeneric

open CatCrypt.Crypto.Pairing.BatchInverse (batchInv batchInv_eq_map_inv
  invCount mulCount invCount_lt_naive)

variable {F : Type*} [Field F]

/-! ## 1. Array entry point

The pass operates on arrays. `batchInvArray` runs the proven list-form
`batchInv` through `Array.toList` / `List.toArray`, so its correctness is a
direct corollary of `batchInv_eq_map_inv` — no new induction. -/

/-- Montgomery's batch inversion on an `Array`: returns the array of
element-wise inverses, computed with **one** field inversion (of the total
product) plus multiplies. Defined via the proven list core `batchInv`. -/
def batchInvArray (xs : Array F) : Array F :=
  (batchInv xs.toList).toArray

@[simp] theorem batchInvArray_empty : batchInvArray (#[] : Array F) = #[] := rfl

theorem batchInvArray_size (xs : Array F) :
    (batchInvArray xs).size = xs.size := by
  simp [batchInvArray, CatCrypt.Crypto.Pairing.BatchInverse.batchInv_length]

/-- **Correctness (array form).** When all entries are nonzero, the array batch
inversion equals the naive element-wise inverse `xs.map (·⁻¹)` — bit-identical
to `n` independent inversions, using only one. This is the soundness
certificate for a `map (·⁻¹) → batchInvArray` peephole rewrite. -/
theorem batchInvArray_eq_map_inv (xs : Array F) (h : ∀ x ∈ xs, x ≠ 0) :
    batchInvArray xs = xs.map (·⁻¹) := by
  have hlist : ∀ x ∈ xs.toList, x ≠ 0 := by
    intro x hx; exact h x (by simpa using hx)
  apply Array.toList_inj.mp
  rw [batchInvArray, List.toList_toArray, batchInv_eq_map_inv xs.toList hlist,
    Array.toList_map]

/-! ## 2. EC-MSM amortized-inverse tie

Affine conversion / MSM slope batches compute `numᵢ · denᵢ⁻¹` for a batch of
`(num, den)` pairs (e.g. `x = X · Z⁻¹` for projective→affine, or a
chord/tangent slope `Δy · Δx⁻¹`). Amortizing the inverse over the batch
shares the single `batchInv` inverse across all points. -/

/-- Batched affine conversion: for pairs `(numᵢ, denᵢ)`, return `numᵢ · denᵢ⁻¹`
using a single shared inverse over the whole denominator batch (Montgomery's
trick), instead of one inverse per point. -/
def affineBatchConvert (ps : List (F × F)) : List F :=
  (ps.map Prod.fst).zipWith (· * ·) (batchInv (ps.map Prod.snd))

/-- **Correctness of the amortized affine conversion.** When every denominator
is nonzero, the batched conversion equals the naive per-point division
`numᵢ · denᵢ⁻¹` — but uses one inverse for the whole batch instead of `n`. -/
theorem affineBatchConvert_eq (ps : List (F × F))
    (h : ∀ p ∈ ps, p.2 ≠ 0) :
    affineBatchConvert ps = ps.map (fun p => p.1 * p.2⁻¹) := by
  have hden : ∀ x ∈ ps.map Prod.snd, x ≠ 0 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact h p hp
  unfold affineBatchConvert
  rw [batchInv_eq_map_inv _ hden]
  clear hden h
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.cons.injEq, true_and]
    exact ih

theorem affineBatchConvert_length (ps : List (F × F)) :
    (affineBatchConvert ps).length = ps.length := by
  simp [affineBatchConvert, CatCrypt.Crypto.Pairing.BatchInverse.batchInv_length]

/-! ## 3. Operation counts (the win, array terms)

Re-export the list-core counts in terms of the array size. `batchInvArray` of an
`n`-entry array still uses exactly **one** inversion and `3·(n−1)` multiplies,
versus the naive `n` inversions of `Array.map (·⁻¹)`. -/

omit [Field F] in
theorem arrayBatchInv_invCount (xs : Array F) :
    invCount xs.size = if xs.size = 0 then 0 else 1 := rfl

omit [Field F] in
theorem arrayBatchInv_mulCount (xs : Array F) :
    mulCount xs.size = 3 * (xs.size - 1) := rfl

/-- The headline comparison in array terms: for `n ≥ 2` entries, the batched
inversion uses strictly fewer inversions (`1`) than the naive per-element path
(`n`). Directly re-exports `invCount_lt_naive`. -/
theorem arrayBatchInv_invCount_lt_naive (n : ℕ) (hn : 2 ≤ n) :
    invCount n < n :=
  invCount_lt_naive n hn

end CatCrypt.Crypto.Optimizer.Rewrite.BatchInverseGeneric
