/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.Core

/-!
# Arrays of little-endian cells in byte memory

`arrAt n a xs` is the big separating conjunction of the points-to assertions
`ptsLE n (a + n * i) xs[i]`: the list `xs` of `8 * n`-bit values stored in consecutive
`n`-byte cells from address `a`.

## Main definitions

* `arrAt`: an array of `n`-byte cells.

## Main results

* `arrAt_nil`, `arrAt_cons`: the empty array, and an array as its first cell and the rest.
* `arrAt_append`: an array of `xs ++ ys` splits into, and merges from, the arrays of `xs`
  and of `ys`.
* `arrAt_cell`: an array is its prefix, the cell `j`, and its suffix.
* `ptsLE_le_arrAt`, `arrAt_cells_disj`, `arrAt_sep_disj`: the footprint of a cell lies in that
  of its array; two cells of an array, and two cells of separated arrays, have disjoint
  ranges.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

open SAssert

variable {A : Nat}

/-- The array `xs` of `n`-byte little-endian cells from address `a`: the big separating
    conjunction of `ptsLE n (a + n * i) xs[i]`. -/
def arrAt (n : Nat) (a : BitVec A) (xs : List (BitVec (8 * n))) : SAssert (MemW A) (BitVec A) :=
  bigSep (xs.mapIdx fun i x => ptsLE n (a + BitVec.ofNat A (n * i)) x)

@[simp] theorem arrAt_nil (n : Nat) (a : BitVec A) : arrAt n a [] = emp := rfl

private theorem add_ofNat_mul_add (n i k : Nat) (a : BitVec A) :
    a + BitVec.ofNat A (n * (i + k)) = a + BitVec.ofNat A (n * k) + BitVec.ofNat A (n * i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add, Nat.add_comm (n * k)]

/-- An array of `xs ++ ys` splits into, and merges from, the array of `xs` and the array of
    `ys` that starts after it. -/
theorem arrAt_append (n : Nat) (a : BitVec A) (xs ys : List (BitVec (8 * n))) :
    arrAt n a (xs ++ ys) ⊣⊢ₛ
      arrAt n a xs ∗ arrAt n (a + BitVec.ofNat A (n * xs.length)) ys := by
  unfold arrAt
  rw [List.mapIdx_append]
  simp only [add_ofNat_mul_add]
  exact bigSep_append _ _

/-- An array is its first cell and the array of the rest. -/
theorem arrAt_cons (n : Nat) (a : BitVec A) (x : BitVec (8 * n)) (xs : List (BitVec (8 * n))) :
    arrAt n a (x :: xs) = ptsLE n a x ∗ arrAt n (a + BitVec.ofNat A n) xs := by
  unfold arrAt
  rw [List.mapIdx_cons, bigSep_cons]
  congr 2
  · simp
  · simp only [add_ofNat_mul_add _ _ 1, Nat.mul_one]

/-- An array is its prefix of `j` cells, the cell `j`, and its suffix. -/
theorem arrAt_cell (n : Nat) (a : BitVec A) (xs : List (BitVec (8 * n))) (j : Nat)
    (hj : j < xs.length) :
    arrAt n a xs ⊣⊢ₛ
      arrAt n a (xs.take j) ∗ ptsLE n (a + BitVec.ofNat A (n * j)) xs[j] ∗
        arrAt n (a + BitVec.ofNat A (n * (j + 1))) (xs.drop (j + 1)) := by
  have e : xs = xs.take j ++ xs[j] :: xs.drop (j + 1) := by simp
  have hl : (xs.take j).length = j := List.length_take_of_le hj.le
  have h := arrAt_append n a (xs.take j) (xs[j] :: xs.drop (j + 1))
  have ea : a + BitVec.ofNat A (n * (j + 1)) = a + BitVec.ofNat A (n * j) + BitVec.ofNat A n := by
    rw [Nat.add_comm j 1, add_ofNat_mul_add n 1 j a, Nat.mul_one]
  rw [← e, hl, arrAt_cons] at h
  rw [ea]
  exact h

/-- The footprint of a cell lies in the footprint of its array. -/
theorem ptsLE_le_arrAt (n : Nat) (a : BitVec A) (xs : List (BitVec (8 * n))) (j : Nat)
    (hj : j < xs.length) :
    (ptsLE n (a + BitVec.ofNat A (n * j)) xs[j]).fp ⊆ (arrAt n a xs).fp :=
  fun _ hx => mem_fp_bigSep.2
    ⟨_, List.mem_mapIdx.2 ⟨j, hj, rfl⟩, hx⟩

/-- Two distinct cells of a satisfied array of nonempty cells have disjoint ranges. -/
theorem arrAt_cells_disj {n : Nat} {a : BitVec A} {xs : List (BitVec (8 * n))} {m : MemW A}
    (h : (arrAt n a xs).holds m) (hn : 0 < n) {i j : Nat} (hij : i < j) (hj : j < xs.length) :
    (⟨a + BitVec.ofNat A (n * i), n⟩ : Rng A).Disj ⟨a + BitVec.ofNat A (n * j), n⟩ := by
  have h' := (arrAt_cell n a xs j hj).1 m h
  have hi : i < (xs.take j).length := by simp [List.length_take_of_le hj.le, hij]
  have hc := ptsLE_le_arrAt n a (xs.take j) i hi
  refine Rng.disj_of_disjoint hn hn ?_
  exact (h'.1.1.mono_left hc).mono_right Set.subset_union_left

/-- Two cells of two separated arrays of nonempty cells have disjoint ranges. -/
theorem arrAt_sep_disj {n k : Nat} {a b : BitVec A} {xs : List (BitVec (8 * n))}
    {ys : List (BitVec (8 * k))} {m : MemW A} (h : (arrAt n a xs ∗ arrAt k b ys).holds m)
    (hn : 0 < n) (hk : 0 < k) {i j : Nat} (hi : i < xs.length) (hj : j < ys.length) :
    (⟨a + BitVec.ofNat A (n * i), n⟩ : Rng A).Disj ⟨b + BitVec.ofNat A (k * j), k⟩ :=
  Rng.disj_of_disjoint hn hk
    ((h.1.mono_left (ptsLE_le_arrAt n a xs i hi)).mono_right (ptsLE_le_arrAt k b ys j hj))

end CatCrypt.Crypto.SecureCompilation.SepLogic
