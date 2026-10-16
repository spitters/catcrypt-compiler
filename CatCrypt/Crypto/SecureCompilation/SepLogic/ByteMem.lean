/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.BitVec
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Tactic.Abel

/-!
# Byte memory with `A`-bit addresses

`MemW A` is a total byte memory indexed by `A`-bit addresses. `readLE n m a` reads the
`n` bytes at `a, a + 1, …, a + n - 1` (addresses modulo `2^A`) as a little-endian
`8 * n`-bit value, and `writeLE n m a v` stores `v` there. Both are defined by recursion on
`n`: the read concatenates the read of the upper `n` bytes with the byte at `a`, the write
stores the low byte at `a` and writes the remaining `8 * n` bits at `a + 1`.

`Rng A` is a byte range `base, …, base + len - 1` modulo `2^A`; `Rng.Disj` is disjointness in
the arithmetic form of the 64-bit `Footprint.Rng.Disj`, so that at `A = 64` the two
definitions agree by `Iff.rfl`.

## Main definitions

* `MemW`, `readLE`, `writeLE`: byte memory, little-endian read and write.
* `Rng`, `Rng.toSet`, `Rng.Disj`: byte ranges, their address sets, and disjointness.

## Main results

* `readLE_writeLE_same`: reading back an `n`-byte write returns the written value when
  `n ≤ 2^A`.
* `readLE_writeLE_disj`: a write to a disjoint range does not change a read.
* `readLE_congr`: a read depends only on the bytes of its range.
* `writeLE_outside`: a write changes no byte outside its range.
* `Rng.Disj.not_mem`, `Rng.Disj.disjoint`, `Rng.disj_iff_disjoint`: disjoint ranges share no
  address, and for nonempty ranges disjointness is disjointness of the address sets.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

/-- A total byte memory with `A`-bit addresses. -/
abbrev MemW (A : Nat) := BitVec A → BitVec 8

variable {A : Nat}

/-- The natural-number value of a difference of `A`-bit vectors, without `%`. -/
private theorem toNat_sub_eq_ite (x y : BitVec A) :
    (x - y).toNat =
      if y.toNat ≤ x.toNat then x.toNat - y.toNat else 2 ^ A + x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]
  have hx := x.isLt
  have hy := y.isLt
  split_ifs with h
  · rw [show 2 ^ A - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ A by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## Byte ranges -/

/-- The byte range `base, base + 1, …, base + len - 1`, modulo `2^A`. -/
structure Rng (A : Nat) where
  /-- The first address. -/
  base : BitVec A
  /-- The number of bytes. -/
  len : Nat
  deriving DecidableEq

namespace Rng

instance : Membership (BitVec A) (Rng A) := ⟨fun r x => (x - r.base).toNat < r.len⟩

theorem mem_def {r : Rng A} {x : BitVec A} : x ∈ r ↔ (x - r.base).toNat < r.len := Iff.rfl

instance (r : Rng A) (x : BitVec A) : Decidable (x ∈ r) :=
  inferInstanceAs (Decidable ((x - r.base).toNat < r.len))

/-- The set of addresses of a range. -/
def toSet (r : Rng A) : Set (BitVec A) := {x | x ∈ r}

@[simp] theorem mem_toSet {r : Rng A} {x : BitVec A} : x ∈ r.toSet ↔ x ∈ r := Iff.rfl

/-- Two ranges are disjoint: the offset of each base from the other is at least the length
    of the other range. -/
def Disj (r s : Rng A) : Prop :=
  r.len ≤ (s.base - r.base).toNat ∧ s.len ≤ (r.base - s.base).toNat

instance (r s : Rng A) : Decidable (r.Disj s) :=
  inferInstanceAs
    (Decidable (r.len ≤ (s.base - r.base).toNat ∧ s.len ≤ (r.base - s.base).toNat))

theorem Disj.symm {r s : Rng A} (h : r.Disj s) : s.Disj r := ⟨h.2, h.1⟩

/-- The base of a nonempty range lies in the range. -/
theorem base_mem {r : Rng A} (h : 0 < r.len) : r.base ∈ r := by
  simp [mem_def, h]

/-- A byte of the range of length `n` at `a + 1` lies in the range of length `n + 1` at `a`. -/
theorem mem_succ {a x : BitVec A} {n : Nat} (hx : x ∈ (⟨a + 1, n⟩ : Rng A)) :
    x ∈ (⟨a, n + 1⟩ : Rng A) := by
  simp only [mem_def] at hx ⊢
  have e : x - a = (x - (a + 1)) + 1 := by abel
  rw [e, BitVec.toNat_add]
  exact lt_of_le_of_lt (Nat.mod_le _ _)
    (Nat.add_lt_add_of_lt_of_le hx (Nat.mod_le 1 _))

/-- The base `a` does not lie in the range of length `n < 2^A` at `a + 1`. -/
theorem not_mem_succ_base {a : BitVec A} {n : Nat} (hn : n < 2 ^ A) :
    a ∉ (⟨a + 1, n⟩ : Rng A) := by
  simp only [mem_def, not_lt]
  have e : a - (a + 1) = -1 := by abel
  rw [e, BitVec.toNat_neg, show (1 : BitVec A).toNat = 1 % 2 ^ A from rfl]
  rcases Nat.lt_or_ge 1 (2 ^ A) with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
    omega
  · omega

/-- Disjoint ranges share no byte. -/
theorem Disj.not_mem {r s : Rng A} {x : BitVec A} (h : r.Disj s) (hx : x ∈ r) : x ∉ s := by
  obtain ⟨rb, rl⟩ := r
  obtain ⟨sb, sl⟩ := s
  intro hs
  simp only [Disj, mem_def, toNat_sub_eq_ite] at h hx hs
  have := x.isLt
  have := rb.isLt
  have := sb.isLt
  generalize 2 ^ A = N at *
  split_ifs at h hx hs <;> omega

/-- Disjoint ranges have disjoint address sets. -/
theorem Disj.disjoint {r s : Rng A} (h : r.Disj s) : Disjoint r.toSet s.toSet :=
  Set.disjoint_left.2 fun _ hx => h.not_mem hx

/-- Nonempty ranges with disjoint address sets are disjoint. -/
theorem disj_of_disjoint {r s : Rng A} (hr : 0 < r.len) (hs : 0 < s.len)
    (h : Disjoint r.toSet s.toSet) : r.Disj s := by
  refine ⟨Nat.le_of_not_lt fun hlt => ?_, Nat.le_of_not_lt fun hlt => ?_⟩
  · exact Set.disjoint_left.1 h (show s.base ∈ r from hlt) (base_mem hs)
  · exact Set.disjoint_left.1 h (base_mem hr) (show r.base ∈ s from hlt)

/-- For nonempty ranges, disjointness is disjointness of the address sets. -/
theorem disj_iff_disjoint {r s : Rng A} (hr : 0 < r.len) (hs : 0 < s.len) :
    r.Disj s ↔ Disjoint r.toSet s.toSet :=
  ⟨Disj.disjoint, disj_of_disjoint hr hs⟩

end Rng

/-! ## Little-endian read and write -/

/-- The little-endian value of the `n` bytes at `a, a + 1, …, a + n - 1`. -/
def readLE : (n : Nat) → MemW A → BitVec A → BitVec (8 * n)
  | 0, _, _ => 0#0
  | n + 1, m, a => readLE n m (a + 1) ++ m a

/-- The memory `m` with the little-endian bytes of `v` stored at `a, a + 1, …, a + n - 1`. -/
def writeLE : (n : Nat) → MemW A → BitVec A → BitVec (8 * n) → MemW A
  | 0, m, _, _ => m
  | n + 1, m, a, v =>
      writeLE n (Function.update m a (v.setWidth 8)) (a + 1) (v.extractLsb' 8 (8 * n))

/-- A read depends only on the bytes of its range. -/
theorem readLE_congr {m m' : MemW A} (n : Nat) (a : BitVec A)
    (h : ∀ x ∈ (⟨a, n⟩ : Rng A), m x = m' x) : readLE n m a = readLE n m' a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [readLE]
    rw [ih (a + 1) fun x hx => h x (Rng.mem_succ hx), h a (Rng.base_mem (Nat.succ_pos n))]

/-- A write changes no byte outside its range. -/
theorem writeLE_outside (n : Nat) (m : MemW A) (a : BitVec A) (v : BitVec (8 * n))
    {x : BitVec A} (hx : x ∉ (⟨a, n⟩ : Rng A)) : writeLE n m a v x = m x := by
  induction n generalizing m a with
  | zero => rfl
  | succ n ih =>
    simp only [writeLE]
    rw [ih _ _ _ fun h => hx (Rng.mem_succ h), Function.update_of_ne]
    rintro rfl
    exact hx (Rng.base_mem (Nat.succ_pos n))

/-- The low byte and the upper `8 * n` bits of an `8 * (n + 1)`-bit value concatenate back
    to the value. -/
private theorem extractLsb'_append_setWidth (n : Nat) (v : BitVec (8 * (n + 1))) :
    v.extractLsb' 8 (8 * n) ++ v.setWidth 8 = v := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb', BitVec.getElem_setWidth]
  rw [← BitVec.getLsbD_eq_getElem]
  split
  · rfl
  · congr 1
    omega

/-- Reading back an `n`-byte write returns the written value when `n ≤ 2^A`. -/
theorem readLE_writeLE_same (n : Nat) (m : MemW A) (a : BitVec A) (v : BitVec (8 * n))
    (hn : n ≤ 2 ^ A) : readLE n (writeLE n m a v) a = v := by
  induction n generalizing m a with
  | zero => exact (BitVec.of_length_zero).symm
  | succ n ih =>
    simp only [readLE, writeLE]
    rw [ih _ _ _ (by omega), writeLE_outside _ _ _ _ (Rng.not_mem_succ_base (by omega)),
      Function.update_self]
    exact extractLsb'_append_setWidth n v

/-- A write to a range disjoint from the read range does not change the read. -/
theorem readLE_writeLE_disj {n k : Nat} (m : MemW A) {a b : BitVec A} (v : BitVec (8 * k))
    (h : (⟨a, n⟩ : Rng A).Disj ⟨b, k⟩) : readLE n (writeLE k m b v) a = readLE n m a :=
  readLE_congr n a fun _ hx => writeLE_outside k m b v (h.not_mem hx)

end CatCrypt.Crypto.SecureCompilation.SepLogic
