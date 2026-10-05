/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
public import CatCrypt.Crypto.SecureCompilation.MachineMem64

/-!
# Byte ranges modulo `2^64`

`Rng` is a byte range `base, base + 1, …, base + len - 1` modulo `2^64`. `Rng.Disj` is
disjointness of two ranges in the arithmetic form of `MachineMem64.MemSep`: at the word
ranges `Rng.word a` and `Rng.word b` it is `MemSep a b`, which is `AddrMem.Disjoint8 a b`.
`Rng.Pairwise` is the pairwise disjointness of a list of ranges.

## Main definitions

* `Rng`, `Rng.word`, `Rng.Disj`, `Rng.Pairwise`: byte ranges and their disjointness.

## Main results

* `Rng.Disj.not_mem`: disjoint ranges share no byte.
* `Rng.disj_word_iff_memSep`, `Rng.disj_word_iff_disjoint8`, `Rng.pairwise_pair_word`:
  `MemSep` and `Disjoint8` as disjointness of word ranges.
* `Rng.Disj.shorten`, `Rng.mem_buf_of_mem_limb`: a shorter range, and a limb of a buffer.
* `Rng.Pairwise.disj_of_ne`: two distinct members of a pairwise disjoint enumeration are
  disjoint.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Footprint

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-! ## Byte ranges -/

/-- The byte range `base, base + 1, …, base + len - 1`, modulo `2^64`. -/
structure Rng where
  /-- The first address. -/
  base : BitVec 64
  /-- The number of bytes. -/
  len : Nat
  deriving DecidableEq

namespace Rng

instance : Membership (BitVec 64) Rng := ⟨fun r x => (x - r.base).toNat < r.len⟩

theorem mem_def {r : Rng} {x : BitVec 64} : x ∈ r ↔ (x - r.base).toNat < r.len := Iff.rfl

instance (r : Rng) (x : BitVec 64) : Decidable (x ∈ r) :=
  inferInstanceAs (Decidable ((x - r.base).toNat < r.len))

/-- The eight bytes of the word at `a`. -/
def word (a : BitVec 64) : Rng := ⟨a, 8⟩

/-- Two ranges are disjoint: the offset of each base from the other is at least the length
    of the other range. -/
def Disj (r s : Rng) : Prop :=
  r.len ≤ (s.base - r.base).toNat ∧ s.len ≤ (r.base - s.base).toNat

instance (r s : Rng) : Decidable (r.Disj s) :=
  inferInstanceAs
    (Decidable (r.len ≤ (s.base - r.base).toNat ∧ s.len ≤ (r.base - s.base).toNat))

/-- A list of pairwise disjoint ranges. -/
def Pairwise (L : List Rng) : Prop := L.Pairwise Disj

instance (L : List Rng) : Decidable (Pairwise L) :=
  inferInstanceAs (Decidable (L.Pairwise Disj))

theorem mem_word {a x : BitVec 64} : x ∈ word a ↔ InRange8 a x := Iff.rfl

/-- Disjointness of two word ranges is `MachineMem64.MemSep`. -/
theorem disj_word_iff_memSep {a b : BitVec 64} :
    (word a).Disj (word b) ↔ MachineMem64.MemSep a b := Iff.rfl

/-- Disjointness of two word ranges is `AddrMem.Disjoint8`. -/
theorem disj_word_iff_disjoint8 {a b : BitVec 64} :
    (word a).Disj (word b) ↔ Disjoint8 a b := Iff.rfl

theorem Disj.symm {r s : Rng} (h : r.Disj s) : s.Disj r := ⟨h.2, h.1⟩

/-- Disjoint ranges share no byte. -/
theorem Disj.not_mem {r s : Rng} {x : BitVec 64} (h : r.Disj s) (hx : x ∈ r) : x ∉ s := by
  obtain ⟨rb, rl⟩ := r
  obtain ⟨sb, sl⟩ := s
  intro hs
  simp only [Disj, mem_def, BitVec.toNat_sub] at h hx hs
  have := x.isLt
  have := rb.isLt
  have := sb.isLt
  omega

/-- A range disjoint from `s` stays disjoint from a shorter range at the base of `s`. -/
theorem Disj.shorten {r s : Rng} (h : r.Disj s) {n : Nat} (hn : n ≤ s.len) :
    r.Disj ⟨s.base, n⟩ :=
  ⟨h.1, Nat.le_trans hn h.2⟩

/-- Limb `k` of an `n`-limb buffer lies in the buffer. -/
theorem mem_buf_of_mem_limb {a x : BitVec 64} {n k : Nat} (hn : 8 * n ≤ 2 ^ 64) (hk : k < n)
    (hx : x ∈ word (a + BitVec.ofNat 64 (8 * k))) : x ∈ (⟨a, 8 * n⟩ : Rng) := by
  simp only [mem_def, word, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx ⊢
  have := x.isLt
  have := a.isLt
  omega

/-- `MachineMem64.MemSep` is the disjoint conjunction of two word ranges. -/
theorem pairwise_pair_word {a b : BitVec 64} :
    Pairwise [word a, word b] ↔ MachineMem64.MemSep a b := by
  simp only [Pairwise, List.pairwise_pair]
  exact disj_word_iff_memSep

/-- Two members of a pairwise disjoint list at distinct positions of a duplicate-free
    enumeration are disjoint: the list form of `AddrMem.Separated`. -/
theorem Pairwise.disj_of_ne {α : Type} {f : α → Rng} {K : List α}
    (h : Pairwise (K.map f)) {k k' : α} (hk : k ∈ K) (hk' : k' ∈ K) (hne : k ≠ k') :
    (f k).Disj (f k') := by
  unfold Pairwise at h
  rw [List.pairwise_map] at h
  induction K with
  | nil => cases hk
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hk with e | hkt
    · rcases List.mem_cons.1 hk' with e' | hkt'
      · exact absurd (e.trans e'.symm) hne
      · exact e ▸ h.1 _ hkt'
    · rcases List.mem_cons.1 hk' with e' | hkt'
      · exact e' ▸ (h.1 _ hkt).symm
      · exact ih h.2 hkt hkt'

end Rng

end CatCrypt.Crypto.SecureCompilation.Ascent.Footprint
