/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# A byte memory over the 64-bit address space

The memory model shared by the x86 address-memory machine (`Ascent.AddrMem`) and the RV64
load/store layer (`RISCVBackend.RiscvMem64`): `AMem` maps each 64-bit address to a byte,
and a 64-bit word occupies the eight bytes from its address, little-endian. Addresses wrap
modulo `2^64`. The model has no alignment requirement and no notion of an invalid address.

## Main definitions

* `AMem`: the byte memory.
* `read64`, `write64`: eight-byte little-endian access.
* `InRange8`, `Disjoint8`: membership in, and disjointness of, eight-byte ranges modulo
  `2^64`.

## Main results

* `read64_write64_same`, `read64_write64_of_disjoint`: the byte-memory laws.
* `disjoint8_add_ofInt`: two displacements from one base at least eight apart give
  disjoint ranges.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Memory64

/-- A byte memory over the 64-bit address space. -/
abbrev AMem := BitVec 64 → BitVec 8

/-- The little-endian word stored in the eight bytes from address `a`. -/
def read64 (m : AMem) (a : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((m a).toNat + 2 ^ 8 * (m (a + BitVec.ofNat 64 1)).toNat
    + 2 ^ 16 * (m (a + BitVec.ofNat 64 2)).toNat + 2 ^ 24 * (m (a + BitVec.ofNat 64 3)).toNat
    + 2 ^ 32 * (m (a + BitVec.ofNat 64 4)).toNat + 2 ^ 40 * (m (a + BitVec.ofNat 64 5)).toNat
    + 2 ^ 48 * (m (a + BitVec.ofNat 64 6)).toNat + 2 ^ 56 * (m (a + BitVec.ofNat 64 7)).toNat)

/-- `x` lies in the eight bytes from `a`, modulo `2^64`. -/
def InRange8 (a x : BitVec 64) : Prop := (x - a).toNat < 8

instance (a x : BitVec 64) : Decidable (InRange8 a x) :=
  inferInstanceAs (Decidable ((x - a).toNat < 8))

/-- Store the word `v` little-endian in the eight bytes from address `a`: the byte at
    `a + k` is byte `k` of `v`. -/
def write64 (m : AMem) (a v : BitVec 64) : AMem := fun x =>
  if InRange8 a x then BitVec.ofNat 8 (v.toNat / 2 ^ (8 * (x - a).toNat)) else m x

/-- The eight-byte ranges from `a` and from `b` are disjoint modulo `2^64`. -/
def Disjoint8 (a b : BitVec 64) : Prop := 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat

theorem write64_of_not_inRange (m : AMem) (a v x : BitVec 64) (h : ¬ InRange8 a x) :
    write64 m a v x = m x := by
  simp only [write64, if_neg h]

theorem toNat_add_sub_self (a : BitVec 64) (k : Nat) (hk : k < 8) :
    (a + BitVec.ofNat 64 k - a).toNat = k := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem write64_add (m : AMem) (a v : BitVec 64) (k : Nat) (hk : k < 8) :
    write64 m a v (a + BitVec.ofNat 64 k) = BitVec.ofNat 8 (v.toNat / 2 ^ (8 * k)) := by
  simp only [write64, InRange8, toNat_add_sub_self a k hk, if_pos hk]

/-- Reading back the eight bytes just written returns the stored word. -/
theorem read64_write64_same (m : AMem) (a v : BitVec 64) : read64 (write64 m a v) a = v := by
  have h0 : write64 m a v a = BitVec.ofNat 8 (v.toNat / 2 ^ (8 * 0)) := by
    simpa using write64_add m a v 0 (by decide)
  simp only [read64, h0, write64_add m a v 1 (by decide), write64_add m a v 2 (by decide),
    write64_add m a v 3 (by decide), write64_add m a v 4 (by decide),
    write64_add m a v 5 (by decide), write64_add m a v 6 (by decide),
    write64_add m a v 7 (by decide)]
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp only [BitVec.toNat_ofNat, Nat.reduceMul, Nat.reducePow, Nat.div_one]
  omega

theorem not_inRange_of_disjoint (a b : BitVec 64) (k : Nat) (h : Disjoint8 a b) (hk : k < 8) :
    ¬ InRange8 a (b + BitVec.ofNat 64 k) := by
  obtain ⟨h1, h2⟩ := h
  simp only [InRange8, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h1 h2 ⊢
  have := a.isLt
  have := b.isLt
  omega

/-- A write to a disjoint eight-byte range does not change the word read at `b`. -/
theorem read64_write64_of_disjoint (m : AMem) (a b v : BitVec 64) (h : Disjoint8 a b) :
    read64 (write64 m a v) b = read64 m b := by
  have h0 : ¬ InRange8 a b := by
    simpa using not_inRange_of_disjoint a b 0 h (by decide)
  simp only [read64, write64_of_not_inRange _ _ _ _ h0,
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 1 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 2 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 3 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 4 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 5 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 6 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 7 h (by decide))]

theorem Disjoint8.symm {a b : BitVec 64} (h : Disjoint8 a b) : Disjoint8 b a := ⟨h.2, h.1⟩

/-- Two displacements from one base, at least eight apart and at most `2^64 - 8` apart,
    give disjoint eight-byte ranges. -/
theorem disjoint8_add_ofInt (p : BitVec 64) (o o' : Int) (h : 8 ≤ (o - o').natAbs)
    (h' : (o - o').natAbs ≤ 2 ^ 64 - 8) :
    Disjoint8 (p + BitVec.ofInt 64 o) (p + BitVec.ofInt 64 o') := by
  have := p.isLt
  simp only [Disjoint8, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt]
  constructor <;> omega

end CatCrypt.Crypto.SecureCompilation.Memory64
