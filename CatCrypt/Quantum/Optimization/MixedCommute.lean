/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.Optimization.DisjointCommute

/-!
# Mixed single-qubit / two-qubit embedding commutation

Two general matrix lemmas bridging the `embedGate1` (single-qubit) and
`embedGate2` (two-qubit) bit-decompositions, supplying exactly the commutation
facts the `commuteAndMerge` / `notProp` / `rotMerge` optimizer-soundness proofs
need when a single-qubit gate is threaded past a `CNOT`/`CZ`:

1. **Disjoint** (`embedGate1_embedGate2_disjoint_comm`): the single qubit `k`
   is distinct from both qubits `i, j` of the two-qubit gate, so the two
   embeddings act on disjoint bit positions and commute.

2. **Diagonal-shared** (`embedGate1_embedGate2_diag_comm`): both gates are
   diagonal in the computational basis (`G`, `H` `IsDiag`), so both embeddings
   are diagonal matrices, which commute regardless of which qubits they touch.
   This covers `Rz`/`Z`/`S`/`T`/`Tdg` (diagonal) commuting with `CZ` (`czGate`
   is diagonal) even on a shared qubit.

## Main results

* `IsDiagonal` — a square matrix whose off-diagonal entries are all zero.
* `isDiagonal_mul_comm` — two diagonal matrices over a commutative semiring commute.
* `embedGate1_isDiagonal` — the `embedGate1` embedding of a diagonal one-qubit gate is
  diagonal.
* `embedGate2_isDiagonal` — the `embedGate2` embedding of a diagonal two-qubit gate is
  diagonal.
* `embedGate1_embedGate2_diag_comm` — the embeddings of a diagonal one-qubit gate and a
  diagonal two-qubit gate commute on any qubits.
* `embedGate1_embedGate2_disjoint_comm` — the embeddings of a one-qubit gate on `k` and
  a two-qubit gate on `i, j` commute when `k` differs from `i` and from `j`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity

noncomputable section

namespace CatCrypt.Quantum.Optimization.MixedCommute

open scoped Matrix
open CatCrypt.Quantum.Optimization.DisjointCommute

variable {n : ℕ}

/-! ## Diagonal matrices commute

We use a self-contained predicate `IsDiagonal M := ∀ r c, r ≠ c → M r c = 0`
(definitionally the unfolding of `Matrix.IsDiag`) to avoid pulling in the
`Matrix.IsDiag` Mathlib import; the two are interchangeable. -/

/-- A square matrix is diagonal: every off-diagonal entry is zero. -/
def IsDiagonal {m : Type*} {R : Type*} [Zero R] (M : Matrix m m R) : Prop :=
  ∀ r c, r ≠ c → M r c = 0

/-- Two diagonal matrices over a commutative semiring commute. -/
theorem isDiagonal_mul_comm {m : Type*} [Fintype m] [DecidableEq m]
    {R : Type*} [NonUnitalCommSemiring R] {A B : Matrix m m R}
    (hA : IsDiagonal A) (hB : IsDiagonal B) : A * B = B * A := by
  ext r c
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases eq_or_ne r c with rfl | hrc
  · refine Finset.sum_congr rfl ?_
    intro k _
    rcases eq_or_ne r k with rfl | hrk
    · rw [mul_comm]
    · rw [hA r k hrk, hB r k hrk, zero_mul, zero_mul]
  · -- off-diagonal: both products vanish term-by-term
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro k _
      rcases eq_or_ne r k with rfl | hrk
      · rw [hA r c hrc, mul_zero]
      · rw [hB r k hrk, zero_mul]
    · intro k _
      rcases eq_or_ne r k with rfl | hrk
      · rw [hB r c hrc, mul_zero]
      · rw [hA r k hrk, zero_mul]

/-! ## `embedGate1` / `embedGate2` are diagonal when the gate is -/

/-- `testBit` equality from `(·/2^p)%2` equality. -/
theorem testBit_eq_of_div_mod_eq {a b p : ℕ}
    (h : (a / 2 ^ p) % 2 = (b / 2 ^ p) % 2) : a.testBit p = b.testBit p := by
  have h2 : (a.testBit p).toNat = (b.testBit p).toNat := by
    rw [Nat.toNat_testBit, Nat.toNat_testBit]; exact h
  cases ha : a.testBit p <;> cases hb : b.testBit p <;> simp_all

/-- If the 1-qubit gate `G` is diagonal, so is its embedding `embedGate1 n k G`. -/
theorem embedGate1_isDiagonal (k : Fin n) {G : Matrix (Fin 2) (Fin 2) ℂ}
    (hG : IsDiagonal G) : IsDiagonal (embedGate1 n k G) := by
  intro r c hrc
  rw [embedGate1_apply]
  by_cases hM : Match n k r.val c.val
  · rw [ite_eq_left hM]
    -- `r ≠ c`, but they agree off `pos n k`; hence they must differ AT `pos n k`,
    -- so the two gate bits differ and `G` (diagonal) vanishes there.
    apply hG
    intro hbit
    apply hrc
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p = pos n k
    · subst hp
      have hb : (gbit n k r.val).val = (gbit n k c.val).val := by rw [hbit]
      rw [gbit_val, gbit_val] at hb
      exact testBit_eq_of_div_mod_eq hb
    · exact hM p hp
  · rw [ite_eq_right hM]

/-- If the 2-qubit gate `H` is diagonal, so is its embedding `embedGate2 n i j H`. -/
theorem embedGate2_isDiagonal {i j : Fin n} (hij : i ≠ j)
    {H : Matrix (Fin 4) (Fin 4) ℂ} (hH : IsDiagonal H) :
    IsDiagonal (embedGate2 n i j H hij) := by
  intro r c hrc
  simp only [embedGate2, Matrix.of_apply]
  by_cases hobm :
      (∀ k : Fin n, k ≠ i → k ≠ j →
        (⟨(r.val / 2 ^ (n - 1 - k.val)) % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) =
        ⟨(c.val / 2 ^ (n - 1 - k.val)) % 2, Nat.mod_lt _ (by omega)⟩)
  · rw [ite_eq_left hobm]
    -- the 2-bit subindices must differ, else `r = c`.
    apply hH
    intro h2q
    apply hrc
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro p
    -- decode the 2-bit index equality into per-bit equalities at pos i and pos j
    have hbit_i : r.val.testBit (pos n i) = c.val.testBit (pos n i) ∧
                  r.val.testBit (pos n j) = c.val.testBit (pos n j) := by
      have hval := congrArg Fin.val h2q
      simp only at hval
      -- hval : r_i*2 + r_j = c_i*2 + c_j, all bits 0/1
      have hri : (r.val / 2 ^ (n - 1 - i.val)) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hrj : (r.val / 2 ^ (n - 1 - j.val)) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hci : (c.val / 2 ^ (n - 1 - i.val)) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hcj : (c.val / 2 ^ (n - 1 - j.val)) % 2 < 2 := Nat.mod_lt _ (by omega)
      refine ⟨?_, ?_⟩
      · exact testBit_eq_of_div_mod_eq (p := pos n i) (by simp only [pos]; omega)
      · exact testBit_eq_of_div_mod_eq (p := pos n j) (by simp only [pos]; omega)
    by_cases hpi : p = pos n i
    · subst hpi; exact hbit_i.1
    by_cases hpj : p = pos n j
    · subst hpj; exact hbit_i.2
    · -- `p` is read by some qubit `q ≠ i, j`; off-bits match by `hobm`
      rcases lt_or_ge p n with hpn | hge
      · -- the qubit reading position `p` is `q := n - 1 - p`
        have hqval : (⟨n - 1 - p, by omega⟩ : Fin n).val = n - 1 - p := rfl
        set q : Fin n := ⟨n - 1 - p, by omega⟩ with hq
        have hqi : q ≠ i := by
          intro h
          apply hpi
          have : q.val = i.val := by rw [h]
          rw [hqval] at this
          simp only [pos]; omega
        have hqj : q ≠ j := by
          intro h
          apply hpj
          have : q.val = j.val := by rw [h]
          rw [hqval] at this
          simp only [pos]; omega
        have hmatch := hobm q hqi hqj
        have hval := congrArg Fin.val hmatch
        simp only at hval
        have hpq : n - 1 - q.val = p := by rw [hqval]; omega
        exact testBit_eq_of_div_mod_eq (a := r.val) (b := c.val) (p := p)
          (by rw [show p = n - 1 - q.val from hpq.symm]; exact hval)
      · -- bits at positions `≥ n` are all `false` for both `r, c < 2^n`
        rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow]
        · exact lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by omega) hge)
        · exact lt_of_lt_of_le r.isLt (Nat.pow_le_pow_right (by omega) hge)
  · rw [ite_eq_right hobm]

/-! ## A `testBit` entry formula for `embedGate2` -/

/-- The qubit index whose bit position is `p` (for `p < n`). -/
private def qOf (n : ℕ) (p : ℕ) (h : p < n) : Fin n := ⟨n - 1 - p, by omega⟩

private theorem pos_qOf (n : ℕ) (p : ℕ) (h : p < n) : pos n (qOf n p h) = p := by
  simp only [pos, qOf]; omega

/-- The `embedGate2` off-bit predicate (quantified over **qubit indices**) equals
    the per-position `Match2` predicate (quantified over **bit positions**), for
    indices `r, c < 2^n`. -/
theorem embedGate2_obm_iff {i j : Fin n} {r c : ℕ}
    (hr : r < 2 ^ n) (hc : c < 2 ^ n) :
    (∀ k : Fin n, k ≠ i → k ≠ j →
        (gbit n k r = gbit n k c)) ↔ Match2 n i j r c := by
  constructor
  · intro h p hpi hpj
    rcases lt_or_ge p n with hp | hp
    · have hq := h (qOf n p hp)
        (by intro he; exact hpi (by rw [← pos_qOf n p hp, he]))
        (by intro he; exact hpj (by rw [← pos_qOf n p hp, he]))
      have hqv : (gbit n (qOf n p hp) r).val = (gbit n (qOf n p hp) c).val := by rw [hq]
      rw [gbit_eq_testBit, gbit_eq_testBit, pos_qOf n p hp] at hqv
      cases hbr : r.testBit p <;> cases hbc : c.testBit p <;> simp_all
    · rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow]
      · exact lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hp)
      · exact lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) hp)
  · intro h k hki hkj
    apply Fin.ext
    rw [gbit_eq_testBit, gbit_eq_testBit, h (pos n k) (pos_ne hki) (pos_ne hkj)]

/-- The 4×4 subindex `embedGate2` reads at row/col value `v`: qubit `i` is the
    high bit, qubit `j` the low bit. -/
def idx4 (n : ℕ) (i j : Fin n) (v : ℕ) : Fin 4 :=
  ⟨(gbit n i v).val * 2 + (gbit n j v).val, by
    have := (gbit n i v).isLt; have := (gbit n j v).isLt; omega⟩

/-- Clean entry formula for `embedGate2`: it is `H (idx4 r) (idx4 c)` when `r`
    and `c` agree off the two qubit bits, and `0` otherwise. -/
theorem embedGate2_apply {i j : Fin n} (hij : i ≠ j)
    (H : Matrix (Fin 4) (Fin 4) ℂ) (r c : Fin (2 ^ n)) :
    embedGate2 n i j H hij r c =
      if Match2 n i j r.val c.val then H (idx4 n i j r.val) (idx4 n i j c.val) else 0 := by
  simp only [embedGate2, Matrix.of_apply, idx4, gbit, pos]
  have key : (∀ k : Fin n, k ≠ i → k ≠ j →
        (⟨(r.val / 2 ^ (n - 1 - k.val)) % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) =
        ⟨(c.val / 2 ^ (n - 1 - k.val)) % 2, Nat.mod_lt _ (by omega)⟩)
      ↔ Match2 n i j r.val c.val :=
    embedGate2_obm_iff (i := i) (j := j) r.isLt c.isLt
  split_ifs with hobm hM hM
  · rfl
  · exact absurd (key.mp hobm) hM
  · exact absurd (key.mpr hM) hobm
  · rfl

/-! ## Disjoint product-entry formulas -/

/-- `r` and `c` agree at every bit position except the three read by qubits
    `k`, `i`, `j`. -/
def Match3 (n : ℕ) (k i j : Fin n) (r c : ℕ) : Prop :=
  ∀ p, p ≠ pos n k → p ≠ pos n i → p ≠ pos n j → r.testBit p = c.testBit p

/-- `idx4` depends only on the bits at `pos n i` / `pos n j`, hence is preserved
    by a `Match n k` for `k ≠ i, j`. -/
theorem idx4_eq_of_match {k i j : Fin n} (hki : k ≠ i) (hkj : k ≠ j) {r m : ℕ}
    (h : Match n k r m) : idx4 n i j r = idx4 n i j m := by
  have hi : gbit n i r = gbit n i m := gbit_eq_of_match (Ne.symm hki) h
  have hj : gbit n j r = gbit n j m := gbit_eq_of_match (Ne.symm hkj) h
  simp only [idx4, hi, hj]

open Classical in
noncomputable instance instDecidableMatch3 (k i j : Fin n) (r c : ℕ) :
    Decidable (Match3 n k i j r c) := Classical.dec _

/-- Entry of `embedGate1 k G * embedGate2 i j H` with `k` disjoint from `i, j`:
    the intermediate sum collapses to the unique surviving index
    `m = setBit n k r c`. -/
theorem embedGate1_mul_embedGate2_apply {k i j : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (H : Matrix (Fin 4) (Fin 4) ℂ)
    (r c : Fin (2 ^ n)) :
    (embedGate1 n k G * embedGate2 n i j H hij) r c =
      if Match3 n k i j r.val c.val then
        G (gbit n k r.val) (gbit n k c.val) * H (idx4 n i j r.val) (idx4 n i j c.val)
      else 0 := by
  rw [Matrix.mul_apply]
  set m0 : Fin (2 ^ n) := ⟨setBit n k r.val c.val, setBit_lt k r.isLt⟩ with hm0
  simp only [embedGate1_apply, embedGate2_apply hij]
  by_cases hM3 : Match3 n k i j r.val c.val
  · rw [ite_eq_left hM3, Finset.sum_eq_single m0]
    · -- value at m0
      have hMk : Match n k r.val m0.val := fun p hp => by
        simp only [hm0, setBit_testBit_ne k r.val c.val hp]
      have hM2 : Match2 n i j m0.val c.val := by
        intro p hpi hpj
        by_cases hpk : p = pos n k
        · subst hpk; simp only [hm0, setBit_testBit_self]
        · simp only [hm0, setBit_testBit_ne k r.val c.val hpk]
          exact hM3 p hpk hpi hpj
      rw [ite_eq_left hMk, ite_eq_left hM2]
      have hgk : gbit n k m0.val = gbit n k c.val := by
        apply Fin.ext
        rw [gbit_eq_testBit, gbit_eq_testBit, hm0, setBit_testBit_self]
      have hidx : idx4 n i j m0.val = idx4 n i j r.val :=
        (idx4_eq_of_match hki hkj hMk).symm
      rw [hgk, hidx]
    · -- every other index contributes 0
      intro m _ hmne
      by_cases hMk : Match n k r.val m.val
      · by_cases hM2 : Match2 n i j m.val c.val
        · exfalso; apply hmne
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro p
          by_cases hpk : p = pos n k
          · subst hpk
            rw [hm0, setBit_testBit_self]
            exact hM2 (pos n k) (pos_ne hki) (pos_ne hkj)
          · rw [hm0, setBit_testBit_ne k r.val c.val hpk]
            exact (hMk p hpk).symm
        · rw [ite_eq_left hMk, ite_eq_right hM2, mul_zero]
      · rw [ite_eq_right hMk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ m0) h
  · rw [ite_eq_right hM3]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hMk : Match n k r.val m.val
    · by_cases hM2 : Match2 n i j m.val c.val
      · exfalso; apply hM3
        intro p hpk hpi hpj
        rw [hMk p hpk, hM2 p hpi hpj]
      · rw [ite_eq_left hMk, ite_eq_right hM2, mul_zero]
    · rw [ite_eq_right hMk, zero_mul]

/-- Entry of `embedGate2 i j H * embedGate1 k G` with `k` disjoint from `i, j`:
    the intermediate sum collapses to the unique surviving index
    `m = setBit n k c r`. -/
theorem embedGate2_mul_embedGate1_apply {k i j : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (H : Matrix (Fin 4) (Fin 4) ℂ)
    (r c : Fin (2 ^ n)) :
    (embedGate2 n i j H hij * embedGate1 n k G) r c =
      if Match3 n k i j r.val c.val then
        H (idx4 n i j r.val) (idx4 n i j c.val) * G (gbit n k r.val) (gbit n k c.val)
      else 0 := by
  rw [Matrix.mul_apply]
  set m0 : Fin (2 ^ n) := ⟨setBit n k c.val r.val, setBit_lt k c.isLt⟩ with hm0
  simp only [embedGate1_apply, embedGate2_apply hij]
  by_cases hM3 : Match3 n k i j r.val c.val
  · rw [ite_eq_left hM3, Finset.sum_eq_single m0]
    · -- value at m0
      have hMk : Match n k m0.val c.val := fun p hp => by
        simp only [hm0, setBit_testBit_ne k c.val r.val hp]
      have hM2 : Match2 n i j r.val m0.val := by
        intro p hpi hpj
        by_cases hpk : p = pos n k
        · subst hpk; simp only [hm0, setBit_testBit_self]
        · simp only [hm0, setBit_testBit_ne k c.val r.val hpk]
          exact hM3 p hpk hpi hpj
      rw [ite_eq_left hM2, ite_eq_left hMk]
      have hgk : gbit n k m0.val = gbit n k r.val := by
        apply Fin.ext
        rw [gbit_eq_testBit, gbit_eq_testBit, hm0, setBit_testBit_self]
      have hidx : idx4 n i j m0.val = idx4 n i j c.val :=
        (idx4_eq_of_match hki hkj hMk)
      rw [hgk, hidx]
    · -- every other index contributes 0
      intro m _ hmne
      by_cases hM2 : Match2 n i j r.val m.val
      · by_cases hMk : Match n k m.val c.val
        · exfalso; apply hmne
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro p
          by_cases hpk : p = pos n k
          · subst hpk
            rw [hm0, setBit_testBit_self]
            exact (hM2 (pos n k) (pos_ne hki) (pos_ne hkj)).symm
          · rw [hm0, setBit_testBit_ne k c.val r.val hpk]
            exact (hMk p hpk)
        · rw [ite_eq_left hM2, ite_eq_right hMk, mul_zero]
      · rw [ite_eq_right hM2, zero_mul]
    · intro h; exact absurd (Finset.mem_univ m0) h
  · rw [ite_eq_right hM3]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hM2 : Match2 n i j r.val m.val
    · by_cases hMk : Match n k m.val c.val
      · exfalso; apply hM3
        intro p hpk hpi hpj
        rw [hM2 p hpi hpj, hMk p hpk]
      · rw [ite_eq_left hM2, ite_eq_right hMk, mul_zero]
    · rw [ite_eq_right hM2, zero_mul]

/-! ## Lemma 2: diagonal-shared commutation -/

/-- **Diagonal-shared commutation.** If a single-qubit gate `G` and a two-qubit
    gate `H` are both diagonal in the computational basis, their embeddings
    commute for **any** qubits `k`, `i`, `j` — even when `k ∈ {i, j}`. Two
    diagonal matrices always commute. This covers `Rz`/`Z`/`S`/`T`/`Tdg`
    (diagonal) commuting with `CZ` (`czGate` is diagonal). -/
theorem embedGate1_embedGate2_diag_comm {k i j : Fin n} (hij : i ≠ j)
    {G : Matrix (Fin 2) (Fin 2) ℂ} {H : Matrix (Fin 4) (Fin 4) ℂ}
    (hG : IsDiagonal G) (hH : IsDiagonal H) :
    embedGate1 n k G * embedGate2 n i j H hij
      = embedGate2 n i j H hij * embedGate1 n k G :=
  isDiagonal_mul_comm (embedGate1_isDiagonal k hG) (embedGate2_isDiagonal hij hH)

/-! ## Lemma 1: disjoint-qubit commutation -/

/-- **Disjoint-qubit commutation.** A single-qubit gate `G` on qubit `k` and a
    two-qubit gate `H` on qubits `i, j` commute as matrices whenever `k` is
    distinct from both `i` and `j`: the embeddings act on disjoint bit positions
    of the `2^n`-dimensional space, so the order of multiplication is
    irrelevant. -/
theorem embedGate1_embedGate2_disjoint_comm {k i j : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (H : Matrix (Fin 4) (Fin 4) ℂ) :
    embedGate1 n k G * embedGate2 n i j H hij
      = embedGate2 n i j H hij * embedGate1 n k G := by
  ext r c
  rw [embedGate1_mul_embedGate2_apply hki hkj hij G H r c,
      embedGate2_mul_embedGate1_apply hki hkj hij G H r c]
  by_cases hM : Match3 n k i j r.val c.val
  · rw [ite_eq_left hM, ite_eq_left hM, mul_comm]
  · rw [ite_eq_right hM, ite_eq_right hM]

end CatCrypt.Quantum.Optimization.MixedCommute
