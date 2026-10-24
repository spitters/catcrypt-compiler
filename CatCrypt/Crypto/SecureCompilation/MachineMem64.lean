/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import Std.Tactic.BVDecide

/-!
# Byte-addressed machine memory with 64-bit little-endian words

The data memory of the AArch64 and RV64 machine models: a total map from 64-bit byte
addresses to bytes. `read64 m a` is the little-endian doubleword at the bytes `a … a + 7`
(the access of A64 `LDR Xt` and RV64 `LD`), and `write64 m a v` writes the eight bytes of
`v` there (A64 `STR Xt`, RV64 `SD`). Addresses wrap modulo `2⁶⁴`.

`MemSep a b` says the doublewords at `a` and `b` share no byte. `ArrAt m base n arr` says the
`n` doublewords at `base, base + 8, …` hold the array `arr`; this is the machine image of a
word array of the `Lprog` memory.

## Main results

* `read64_write64_same`, `read64_write64_sep`: reading back a write, and reading a separated
  doubleword after a write.
* `memSep_cells`: distinct cells of an array of at most `2⁶¹` words are separated.
* `ArrAt_write_cell`, `ArrAt_write_sep`: a write to a cell of an array updates that cell, and
  a write separated from every cell leaves the array unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MachineMem64

/-- A byte-addressed data memory over 64-bit addresses. -/
abbrev Mem64 : Type := BitVec 64 → BitVec 8

/-- The little-endian doubleword at the bytes `a … a + 7`. -/
def read64 (m : Mem64) (a : BitVec 64) : BitVec 64 :=
  (m (a + 7) ++ m (a + 6) ++ m (a + 5) ++ m (a + 4) ++ m (a + 3) ++ m (a + 2) ++ m (a + 1)
    ++ m a).cast rfl

/-- Write the doubleword `v` little-endian at the bytes `a … a + 7`. -/
def write64 (m : Mem64) (a v : BitVec 64) : Mem64 :=
  fun x => if (x - a).toNat < 8 then v.extractLsb' (8 * (x - a).toNat) 8 else m x

/-- The doublewords at `a` and `b` share no byte (modulo `2⁶⁴`). -/
def MemSep (a b : BitVec 64) : Prop := 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat

/-- Reading back the doubleword just written returns it. -/
theorem read64_write64_same (m : Mem64) (a v : BitVec 64) : read64 (write64 m a v) a = v := by
  have h : ∀ i : BitVec 64, a + i - a = i := fun i => by bv_omega
  have k : ∀ i : BitVec 64, i.toNat < 8 →
      write64 m a v (a + i) = v.extractLsb' (8 * i.toNat) 8 :=
    fun i hi => by simp only [write64, h, ite_eq_left hi]
  have k0 : write64 m a v a = v.extractLsb' 0 8 := by
    have := k 0 (by decide); simpa using this
  simp only [read64, k0, k 1 (by decide), k 2 (by decide), k 3 (by decide), k 4 (by decide),
    k 5 (by decide), k 6 (by decide), k 7 (by decide)]
  simp only [show (1 : BitVec 64).toNat = 1 from rfl, show (2 : BitVec 64).toNat = 2 from rfl,
    show (3 : BitVec 64).toNat = 3 from rfl, show (4 : BitVec 64).toNat = 4 from rfl,
    show (5 : BitVec 64).toNat = 5 from rfl, show (6 : BitVec 64).toNat = 6 from rfl,
    show (7 : BitVec 64).toNat = 7 from rfl]
  bv_decide

/-- A write leaves a separated doubleword unchanged. -/
theorem read64_write64_sep (m : Mem64) {a b : BitVec 64} (v : BitVec 64) (h : MemSep a b) :
    read64 (write64 m a v) b = read64 m b := by
  obtain ⟨h1, h2⟩ := h
  have e : ∀ i : BitVec 64, i.toNat < 8 → write64 m a v (b + i) = m (b + i) := by
    intro i hi
    have : ¬ ((b + i - a).toNat < 8) := by bv_omega
    simp only [write64, ite_eq_right this]
  have e0 : write64 m a v b = m b := by
    have := e 0 (by decide); simpa using this
  simp only [read64, e0, e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]

/-- Distinct cells `j ≠ k` of an array of `n ≤ 2⁶¹` doublewords are separated. -/
theorem memSep_cells (base : BitVec 64) (j k n : Nat) (hj : j < n) (hk : k < n)
    (hn : 8 * n ≤ 2 ^ 64) (hjk : j ≠ k) :
    MemSep (base + BitVec.ofNat 64 (8 * k)) (base + BitVec.ofNat 64 (8 * j)) := by
  have e1 : base + BitVec.ofNat 64 (8 * j) - (base + BitVec.ofNat 64 (8 * k))
      = BitVec.ofNat 64 (8 * j) - BitVec.ofNat 64 (8 * k) := by bv_omega
  have e2 : base + BitVec.ofNat 64 (8 * k) - (base + BitVec.ofNat 64 (8 * j))
      = BitVec.ofNat 64 (8 * k) - BitVec.ofNat 64 (8 * j) := by bv_omega
  unfold MemSep
  rw [e1, e2]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega)]
  omega

/-- The `n` doublewords at `base, base + 8, …, base + 8 (n - 1)` hold the array `arr`. -/
def ArrAt (m : Mem64) (base : BitVec 64) (n : Nat) (arr : Fin n → BitVec 64) : Prop :=
  ∀ k : Fin n, read64 m (base + BitVec.ofNat 64 (8 * k.val)) = arr k

/-- A write to cell `k` of an array of `n ≤ 2⁶¹` doublewords updates that cell only. -/
theorem ArrAt_write_cell {m : Mem64} {base : BitVec 64} {n : Nat} {arr : Fin n → BitVec 64}
    (h : ArrAt m base n arr) (hn : 8 * n ≤ 2 ^ 64) (k : Nat) (hk : k < n) (v : BitVec 64) :
    ArrAt (write64 m (base + BitVec.ofNat 64 (8 * k)) v) base n
      (fun j => if j.val = k then v else arr j) := by
  intro j
  by_cases hjk : j.val = k
  · simp only [hjk, ite_true, read64_write64_same]
  · simp only [hjk, ite_false]
    rw [read64_write64_sep m v (memSep_cells base j.val k n j.isLt hk hn hjk)]
    exact h j

/-- A write separated from every cell of an array leaves the array unchanged. -/
theorem ArrAt_write_sep {m : Mem64} {base : BitVec 64} {n : Nat} {arr : Fin n → BitVec 64}
    (h : ArrAt m base n arr) (a v : BitVec 64)
    (hs : ∀ j : Fin n, MemSep a (base + BitVec.ofNat 64 (8 * j.val))) :
    ArrAt (write64 m a v) base n arr := by
  intro j
  rw [read64_write64_sep m v (hs j)]
  exact h j

end CatCrypt.Crypto.SecureCompilation.MachineMem64
