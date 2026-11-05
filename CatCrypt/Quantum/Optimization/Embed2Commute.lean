/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.Optimization.DisjointCommute
public import CatCrypt.Quantum.Optimization.MixedCommute

/-!
# Two-qubit / two-qubit disjoint embedding commutation

Two two-qubit gate embeddings acting on **disjoint** pairs of qubits commute as
matrices:

`embedGate2 n i j G * embedGate2 n k l H = embedGate2 n k l H * embedGate2 n i j G`

whenever `{i, j} ∩ {k, l} = ∅`. This is the recurring obstacle blocking
`EGraphRuleSound` and the general two-qubit commute cases.

## Proof outline

This mirrors `MixedCommute.embedGate1_mul_embedGate2_apply` exactly, one level
up: both factors are now `embedGate2`. The matrix product
`(embedGate2 i j G * embedGate2 k l H)(r,c)` is a sum over the intermediate
index `m`. A summand is nonzero only when `r, m` agree off `{pos i, pos j}`
**and** `m, c` agree off `{pos k, pos l}`. With all four positions distinct this
pins `m` uniquely — it is `r` with its bits at `pos k` and `pos l` overwritten
by `c`'s bits there (`setBit2`). The sum then collapses via
`Finset.sum_eq_single` to `G(idx4 i j r, idx4 i j c) · H(idx4 k l r, idx4 k l c)`.
The opposite order collapses to `H(...) · G(...)` at the same `(r, c)`, and the
two agree by commutativity of `ℂ`.

## Main results

* `setBit2` — the index `r` with its bits for qubits `i`, `j` set to those of `c`.
* `embedGate2_mul_embedGate2_apply` — an entry of the product of two-qubit embeddings on
  disjoint pairs is the product of the two gate entries.
* `embedGate2_embedGate2_disjoint_comm` — two-qubit embeddings on disjoint qubit pairs
  commute as matrices.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity

noncomputable section

namespace CatCrypt.Quantum.Optimization.Embed2Commute

open scoped Matrix
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute

variable {n : ℕ}

/-! ## `idx4` from per-bit agreement -/

/-- `idx4 n i j` depends only on the bits at `pos n i` and `pos n j`. -/
theorem idx4_eq_of_testBit {i j : Fin n} {r m : ℕ}
    (hi : r.testBit (pos n i) = m.testBit (pos n i))
    (hj : r.testBit (pos n j) = m.testBit (pos n j)) :
    idx4 n i j r = idx4 n i j m := by
  have hgi : gbit n i r = gbit n i m := by
    apply Fin.ext; rw [gbit_eq_testBit, gbit_eq_testBit, hi]
  have hgj : gbit n j r = gbit n j m := by
    apply Fin.ext; rw [gbit_eq_testBit, gbit_eq_testBit, hj]
  simp only [idx4, hgi, hgj]

/-! ## The unique intermediate index: overwrite two bits -/

/-- `r` with its bits at `pos n i` and `pos n j` overwritten by `c`'s bits there.
    This is the unique intermediate index that survives in the product
    `embedGate2 i j G * embedGate2 k l H` at entry `(r, c)`. -/
def setBit2 (n : ℕ) (i j : Fin n) (r c : ℕ) : ℕ :=
  setBit n i (setBit n j r c) c

theorem setBit2_lt (i j : Fin n) {r c : ℕ} (hr : r < 2 ^ n) :
    setBit2 n i j r c < 2 ^ n :=
  setBit_lt i (setBit_lt j hr)

/-- At `pos n i`, `setBit2` agrees with `c`. -/
theorem setBit2_testBit_i (i j : Fin n) (r c : ℕ) :
    (setBit2 n i j r c).testBit (pos n i) = c.testBit (pos n i) := by
  simp only [setBit2, setBit_testBit_self]

/-- At `pos n j`, `setBit2` agrees with `c` (using `i ≠ j`). -/
theorem setBit2_testBit_j {i j : Fin n} (hij : i ≠ j) (r c : ℕ) :
    (setBit2 n i j r c).testBit (pos n j) = c.testBit (pos n j) := by
  simp only [setBit2, setBit_testBit_ne i _ c (pos_ne hij).symm, setBit_testBit_self]

/-- Off `{pos n i, pos n j}`, `setBit2` agrees with `r`. -/
theorem setBit2_testBit_ne {i j : Fin n} (r c : ℕ) {p : ℕ}
    (hpi : p ≠ pos n i) (hpj : p ≠ pos n j) :
    (setBit2 n i j r c).testBit p = r.testBit p := by
  simp only [setBit2, setBit_testBit_ne i _ c hpi, setBit_testBit_ne j r c hpj]

/-! ## The four-position match predicate -/

/-- `r` and `c` agree at every bit position except the four read by qubits
    `i`, `j`, `k`, `l`. -/
def Match4 (n : ℕ) (i j k l : Fin n) (r c : ℕ) : Prop :=
  ∀ p, p ≠ pos n i → p ≠ pos n j → p ≠ pos n k → p ≠ pos n l →
    r.testBit p = c.testBit p

open Classical in
noncomputable instance instDecidableMatch4 (i j k l : Fin n) (r c : ℕ) :
    Decidable (Match4 n i j k l r c) := Classical.dec _

/-! ## Product-entry formula -/

/-- Entry of `embedGate2 i j G * embedGate2 k l H` with `{i,j}` disjoint from
    `{k,l}`: the intermediate sum collapses to the unique surviving index
    `m = setBit2 n k l r c`. -/
theorem embedGate2_mul_embedGate2_apply {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (G H : Matrix (Fin 4) (Fin 4) ℂ) (r c : Fin (2 ^ n)) :
    (embedGate2 n i j G hij * embedGate2 n k l H hkl) r c =
      if Match4 n i j k l r.val c.val then
        G (idx4 n i j r.val) (idx4 n i j c.val) *
          H (idx4 n k l r.val) (idx4 n k l c.val)
      else 0 := by
  rw [Matrix.mul_apply]
  set m0 : Fin (2 ^ n) := ⟨setBit2 n i j r.val c.val, setBit2_lt i j r.isLt⟩ with hm0
  simp only [embedGate2_apply hij, embedGate2_apply hkl]
  by_cases hM4 : Match4 n i j k l r.val c.val
  · rw [ite_eq_left hM4, Finset.sum_eq_single m0]
    · -- value at m0
      have hMij : Match2 n i j r.val m0.val := by
        intro p hpi hpj
        simp only [hm0, setBit2_testBit_ne r.val c.val hpi hpj]
      have hMkl : Match2 n k l m0.val c.val := by
        intro p hpk hpl
        by_cases hpi : p = pos n i
        · subst hpi; simp only [hm0, setBit2_testBit_i]
        · by_cases hpj : p = pos n j
          · subst hpj; simp only [hm0, setBit2_testBit_j hij]
          · simp only [hm0, setBit2_testBit_ne r.val c.val hpi hpj]
            exact hM4 p hpi hpj hpk hpl
      rw [ite_eq_left hMij, ite_eq_left hMkl]
      have hidx_ij : idx4 n i j m0.val = idx4 n i j c.val := by
        apply idx4_eq_of_testBit
        · simp only [hm0, setBit2_testBit_i]
        · simp only [hm0, setBit2_testBit_j hij]
      have hidx_kl : idx4 n k l m0.val = idx4 n k l r.val := by
        apply (idx4_eq_of_testBit _ _).symm
        · simp only [hm0, setBit2_testBit_ne r.val c.val (pos_ne hik).symm (pos_ne hjk).symm]
        · simp only [hm0, setBit2_testBit_ne r.val c.val (pos_ne hil).symm (pos_ne hjl).symm]
      rw [hidx_ij, hidx_kl]
    · -- every other index contributes 0
      intro m _ hmne
      by_cases hMij : Match2 n i j r.val m.val
      · by_cases hMkl : Match2 n k l m.val c.val
        · exfalso; apply hmne
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro p
          by_cases hpi : p = pos n i
          · subst hpi
            rw [hm0, setBit2_testBit_i]
            exact hMkl (pos n i) (pos_ne hik) (pos_ne hil)
          · by_cases hpj : p = pos n j
            · subst hpj
              rw [hm0, setBit2_testBit_j hij]
              exact hMkl (pos n j) (pos_ne hjk) (pos_ne hjl)
            · rw [hm0, setBit2_testBit_ne r.val c.val hpi hpj]
              exact (hMij p hpi hpj).symm
        · rw [ite_eq_left hMij, ite_eq_right hMkl, mul_zero]
      · rw [ite_eq_right hMij, zero_mul]
    · intro h; exact absurd (Finset.mem_univ m0) h
  · rw [ite_eq_right hM4]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hMij : Match2 n i j r.val m.val
    · by_cases hMkl : Match2 n k l m.val c.val
      · exfalso; apply hM4
        intro p hpi hpj hpk hpl
        rw [hMij p hpi hpj, hMkl p hpk hpl]
      · rw [ite_eq_left hMij, ite_eq_right hMkl, mul_zero]
    · rw [ite_eq_right hMij, zero_mul]

/-- The opposite-order product, collapsing to the same scalars with `H · G`. -/
theorem embedGate2_mul_embedGate2_apply' {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (G H : Matrix (Fin 4) (Fin 4) ℂ) (r c : Fin (2 ^ n)) :
    (embedGate2 n k l H hkl * embedGate2 n i j G hij) r c =
      if Match4 n i j k l r.val c.val then
        H (idx4 n k l r.val) (idx4 n k l c.val) *
          G (idx4 n i j r.val) (idx4 n i j c.val)
      else 0 := by
  rw [embedGate2_mul_embedGate2_apply hkl hij hik.symm hjk.symm hil.symm hjl.symm
        H G r c]
  -- `Match4 n k l i j` is the same predicate as `Match4 n i j k l`
  have hswap : Match4 n k l i j r.val c.val ↔ Match4 n i j k l r.val c.val :=
    ⟨fun h p hpi hpj hpk hpl => h p hpk hpl hpi hpj,
     fun h p hpk hpl hpi hpj => h p hpi hpj hpk hpl⟩
  by_cases hM : Match4 n i j k l r.val c.val
  · rw [ite_eq_left (hswap.mpr hM), ite_eq_left hM]
  · rw [ite_eq_right (fun hc => hM (hswap.mp hc)), ite_eq_right hM]

/-! ## Main result -/

/-- **Disjoint two-qubit commutation.** Two two-qubit gate embeddings on disjoint
    qubit pairs `{i, j}` and `{k, l}` commute as matrices: the embeddings act on
    disjoint bit positions of the `2^n`-dimensional space, so the order of
    multiplication is irrelevant. -/
theorem embedGate2_embedGate2_disjoint_comm {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (G H : Matrix (Fin 4) (Fin 4) ℂ) :
    embedGate2 n i j G hij * embedGate2 n k l H hkl
      = embedGate2 n k l H hkl * embedGate2 n i j G hij := by
  ext r c
  rw [embedGate2_mul_embedGate2_apply hij hkl hik hil hjk hjl G H r c,
      embedGate2_mul_embedGate2_apply' hij hkl hik hil hjk hjl G H r c]
  by_cases hM : Match4 n i j k l r.val c.val
  · rw [ite_eq_left hM, ite_eq_left hM, mul_comm]
  · rw [ite_eq_right hM, ite_eq_right hM]

end CatCrypt.Quantum.Optimization.Embed2Commute
