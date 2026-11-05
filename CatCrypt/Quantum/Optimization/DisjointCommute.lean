/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity

/-!
# Disjoint-qubit commutation for `embedGate1`

Single-qubit gate embeddings on **distinct** qubits commute as matrices:

`embedGate1 n i G * embedGate1 n j H = embedGate1 n j H * embedGate1 n i G`  (for `i ≠ j`).

This is the one remaining gap in `Optimization/CommuteSound.lean`; closing it
unblocks the `commuteAndMerge` optimizer soundness.

## Encoding

`embedGate1 n i G` (in `QCircuit.lean`) acts on the basis index `r : Fin (2^n)`
by reading the bit at position `pᵢ := n - 1 - i` (qubit `0` is the MSB). Its
entry `(r, c)` is `G (bit r i) (bit c i)` when `r` and `c` agree at every other
bit position, and `0` otherwise.

## Proof outline

We re-express `embedGate1` via a `testBit` characterisation
(`embedGate1_apply_testBit`): the "left/right match" predicate of the raw
`div`/`mod` form is exactly "`r` and `c` agree at all bit positions `≠ pᵢ`".

The matrix product `(embedGate1 i G * embedGate1 j H)(r,c)` is a sum over the
intermediate index `k`. A summand is nonzero only when `r,k` agree off `pᵢ`
**and** `k,c` agree off `pⱼ`. Since `i ≠ j` forces `pᵢ ≠ pⱼ`, this pins `k`
uniquely (it equals `r` flipped to `c`'s value at `pᵢ`), so the sum collapses
via `Finset.sum_eq_single` to `G(rᵢ,cᵢ) · H(rⱼ,cⱼ)`. The opposite order
collapses to `H(rⱼ,cⱼ) · G(rᵢ,cᵢ)` at the same `(r,c)`, and the two agree by
commutativity of `ℂ`.

## Main results

* `embedGate1_apply` — an entry of `embedGate1 n i G` is the entry of `G` at the bits of
  qubit `i` when the indices agree at every other bit, and `0` otherwise.
* `embedGate1_mul_apply` — an entry of the product of one-qubit embeddings on distinct
  qubits is the product of the two gate entries at the corresponding bits.
* `setBit` — the index `r` with its bit for qubit `i` set to that of `c`.
* `embedGate1_disjoint_comm` — one-qubit embeddings on distinct qubits commute as matrices.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity

noncomputable section

namespace CatCrypt.Quantum.Optimization.DisjointCommute

open scoped Matrix

variable {n : ℕ}

/-! ## Bit-position characterisation of `embedGate1` -/

/-- The bit position (from the LSB) that qubit `i` reads in the `2^n` basis
    index. Qubit `0` is the most-significant bit. -/
def pos (n : ℕ) (i : Fin n) : ℕ := n - 1 - i.val

theorem pos_lt (i : Fin n) : pos n i < n := by
  have := i.isLt; unfold pos; omega

/-- Distinct qubits read distinct bit positions. -/
theorem pos_ne {i j : Fin n} (h : i ≠ j) : pos n i ≠ pos n j := by
  have hi := i.isLt; have hj := j.isLt
  unfold pos
  intro hpos
  apply h
  apply Fin.ext
  omega

/-- The "gate bit" of `embedGate1` as a `Fin 2`. -/
def gbit (n : ℕ) (i : Fin n) (v : ℕ) : Fin 2 :=
  ⟨(v / 2 ^ pos n i) % 2, Nat.mod_lt _ (by omega)⟩

theorem gbit_val (i : Fin n) (v : ℕ) :
    (gbit n i v).val = (v / 2 ^ pos n i) % 2 := rfl

/-- `gbit` is exactly `testBit` (as a `Fin 2`). -/
theorem gbit_eq_testBit (i : Fin n) (v : ℕ) :
    (gbit n i v).val = (v.testBit (pos n i)).toNat := by
  rw [gbit_val, Nat.toNat_testBit]

/-- `r` and `c` agree at every bit position except the one read by qubit `i`. -/
def Match (n : ℕ) (i : Fin n) (r c : ℕ) : Prop :=
  ∀ p, p ≠ pos n i → r.testBit p = c.testBit p

/-- `a / 2 ^ m = b / 2 ^ m` iff `a` and `b` agree on all bits `≥ m`. -/
theorem div_eq_iff_testBit (a b m : ℕ) :
    a / 2 ^ m = b / 2 ^ m ↔ ∀ p, m ≤ p → a.testBit p = b.testBit p := by
  constructor
  · intro h p hp
    have := congrArg (fun x => Nat.testBit x (p - m)) h
    simpa only [Nat.testBit_div_two_pow, Nat.sub_add_cancel hp] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact h (q + m) (by omega)

/-- `a % 2 ^ m = b % 2 ^ m` iff `a` and `b` agree on all bits `< m`. -/
theorem mod_eq_iff_testBit (a b m : ℕ) :
    a % 2 ^ m = b % 2 ^ m ↔ ∀ p, p < m → a.testBit p = b.testBit p := by
  constructor
  · intro h p hp
    have := congrArg (fun x => Nat.testBit x p) h
    simpa only [Nat.testBit_mod_two_pow, decide_eq_true hp, Bool.true_and] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hq : q < m
    · simp only [decide_eq_true hq, Bool.true_and]; exact h q hq
    · simp only [decide_eq_false hq, Bool.false_and]

/-- The raw `div`/`mod` "off-bit match" predicate of `embedGate1` is exactly the
    per-position `Match` predicate. -/
theorem embedGate1_cond_iff (i : Fin n) (r c : ℕ) :
    (r / 2 ^ (pos n i + 1) = c / 2 ^ (pos n i + 1) ∧
       r % 2 ^ pos n i = c % 2 ^ pos n i) ↔ Match n i r c := by
  rw [div_eq_iff_testBit, mod_eq_iff_testBit]
  constructor
  · rintro ⟨hhi, hlo⟩ p hp
    rcases lt_trichotomy p (pos n i) with h | h | h
    · exact hlo p h
    · exact absurd h hp
    · exact hhi p (by omega)
  · intro h
    exact ⟨fun p hp => h p (by omega), fun p hp => h p (by omega)⟩

instance instDecidableMatch (i : Fin n) (r c : ℕ) : Decidable (Match n i r c) :=
  decidable_of_iff _ (embedGate1_cond_iff i r c)

/-- Clean entry formula for `embedGate1`: it is `G (gbit r) (gbit c)` when `r`
    and `c` agree off the qubit-`i` bit, and `0` otherwise. -/
theorem embedGate1_apply (i : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (r c : Fin (2 ^ n)) :
    embedGate1 n i G r c =
      if Match n i r.val c.val then G (gbit n i r.val) (gbit n i c.val) else 0 := by
  simp only [embedGate1, Matrix.of_apply, gbit, pos]
  by_cases h : Match n i r.val c.val
  · have hc := (embedGate1_cond_iff i r.val c.val).mpr h
    simp only [pos] at hc
    rw [ite_eq_left h, ite_eq_left hc]
  · have hc : ¬ _ := fun hc => h ((embedGate1_cond_iff i r.val c.val).mp (by
      simp only [pos]; exact hc))
    rw [ite_eq_right h, ite_eq_right hc]

/-! ## Helper facts about `Match` and `gbit` -/

theorem Match.symm {i : Fin n} {r c : ℕ} (h : Match n i r c) : Match n i c r :=
  fun p hp => (h p hp).symm

/-- `gbit` depends only on the bit at `pos n i`, so it is preserved by any
    `Match n j` with `j ≠ i`. -/
theorem gbit_eq_of_match {i j : Fin n} (hij : i ≠ j) {r k : ℕ}
    (h : Match n j r k) : gbit n i r = gbit n i k := by
  apply Fin.ext
  rw [gbit_eq_testBit, gbit_eq_testBit, h (pos n i) (pos_ne hij)]

/-! ## The unique intermediate index -/

/-- `r` with its bit at `pos n i` overwritten by `c`'s bit there. This is the
    unique intermediate index that survives in the product
    `embedGate1 i G * embedGate1 j H` at entry `(r, c)`. -/
def setBit (n : ℕ) (i : Fin n) (r c : ℕ) : ℕ :=
  r ^^^ (if r.testBit (pos n i) = c.testBit (pos n i) then 0 else 2 ^ pos n i)

theorem setBit_lt (i : Fin n) {r c : ℕ} (hr : r < 2 ^ n) :
    setBit n i r c < 2 ^ n := by
  unfold setBit
  split
  · simpa using hr
  · exact Nat.xor_lt_two_pow hr (Nat.pow_lt_pow_right (by omega) (pos_lt i))

theorem setBit_testBit_self (i : Fin n) (r c : ℕ) :
    (setBit n i r c).testBit (pos n i) = c.testBit (pos n i) := by
  unfold setBit
  rw [Nat.testBit_xor]
  split
  next h => simp [h]
  next h =>
    rw [Nat.testBit_two_pow]
    simp only [decide_true, Bool.xor_true]
    rcases Bool.eq_false_or_eq_true (r.testBit (pos n i)) with hr | hr <;>
      rcases Bool.eq_false_or_eq_true (c.testBit (pos n i)) with hc | hc <;>
      simp_all

theorem setBit_testBit_ne (i : Fin n) (r c : ℕ) {p : ℕ} (hp : p ≠ pos n i) :
    (setBit n i r c).testBit p = r.testBit p := by
  unfold setBit
  rw [Nat.testBit_xor]
  split
  · simp
  · rw [Nat.testBit_two_pow, decide_eq_false (by omega : ¬ pos n i = p)]
    simp

/-! ## The product-entry formula -/

/-- `r` and `c` agree at every bit position except the two read by qubits
    `i` and `j`. -/
def Match2 (n : ℕ) (i j : Fin n) (r c : ℕ) : Prop :=
  ∀ p, p ≠ pos n i → p ≠ pos n j → r.testBit p = c.testBit p

open Classical in
noncomputable instance instDecidableMatch2 (i j : Fin n) (r c : ℕ) :
    Decidable (Match2 n i j r c) := Classical.dec _

/-- Entry of the product `embedGate1 i G * embedGate1 j H` at `(r, c)`: the
    sum over intermediate indices collapses to a single surviving term at
    `k = setBit n i r c`. -/
theorem embedGate1_mul_apply {i j : Fin n} (hij : i ≠ j)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) (r c : Fin (2 ^ n)) :
    (embedGate1 n i G * embedGate1 n j H) r c =
      if Match2 n i j r.val c.val then
        G (gbit n i r.val) (gbit n i c.val) * H (gbit n j r.val) (gbit n j c.val)
      else 0 := by
  rw [Matrix.mul_apply]
  -- the witness index, as an element of `Fin (2^n)`
  set k0 : Fin (2 ^ n) := ⟨setBit n i r.val c.val, setBit_lt i r.isLt⟩ with hk0
  -- rewrite every summand via `embedGate1_apply`
  simp only [embedGate1_apply]
  by_cases hM2 : Match2 n i j r.val c.val
  · rw [ite_eq_left hM2]
    -- only k0 survives
    rw [Finset.sum_eq_single k0]
    · -- value at k0
      have hMi : Match n i r.val k0.val := by
        intro p hp
        simp only [hk0, setBit_testBit_ne i r.val c.val hp]
      have hMj : Match n j k0.val c.val := by
        intro p hp
        by_cases hpi : p = pos n i
        · subst hpi; simp only [hk0, setBit_testBit_self]
        · simp only [hk0, setBit_testBit_ne i r.val c.val hpi]
          exact hM2 p hpi hp
      rw [ite_eq_left hMi, ite_eq_left hMj]
      -- gbit i k0 = gbit i c, gbit j r = gbit j k0
      have hgi : gbit n i k0.val = gbit n i c.val := by
        apply Fin.ext
        rw [gbit_eq_testBit, gbit_eq_testBit, hk0, setBit_testBit_self]
      have hgj : gbit n j k0.val = gbit n j r.val :=
        (gbit_eq_of_match (Ne.symm hij) hMi).symm
      rw [hgi, hgj]
    · -- every other k contributes 0
      intro k _ hkne
      by_cases hMi : Match n i r.val k.val
      · by_cases hMj : Match n j k.val c.val
        · -- both hold ⇒ k = k0, contradiction
          exfalso; apply hkne
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro p
          by_cases hpi : p = pos n i
          · subst hpi
            rw [hk0, setBit_testBit_self]
            exact (hMj (pos n i) (pos_ne hij))
          · rw [hk0, setBit_testBit_ne i r.val c.val hpi]
            exact (hMi p hpi).symm
        · rw [ite_eq_left hMi, ite_eq_right hMj, mul_zero]
      · rw [ite_eq_right hMi, zero_mul]
    · intro hk0notin; exact absurd (Finset.mem_univ k0) hk0notin
  · rw [ite_eq_right hM2]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hMi : Match n i r.val k.val
    · by_cases hMj : Match n j k.val c.val
      · -- both ⇒ Match2 r c, contradicting hM2
        exfalso; apply hM2
        intro p hpi hpj
        rw [hMi p hpi, hMj p hpj]
      · rw [ite_eq_left hMi, ite_eq_right hMj, mul_zero]
    · rw [ite_eq_right hMi, zero_mul]

/-- `Match2` is symmetric in the two excluded qubit positions. -/
theorem match2_swap (i j : Fin n) (r c : ℕ) :
    Match2 n i j r c ↔ Match2 n j i r c :=
  ⟨fun h p hpj hpi => h p hpi hpj, fun h p hpi hpj => h p hpj hpi⟩

/-! ## Main result: disjoint-qubit commutation -/

/-- **Disjoint-qubit commutation** at the `embedGate1` matrix level.

    Single-qubit gate embeddings on **distinct** qubits `i ≠ j` commute as
    matrices: they act on disjoint tensor factors of the `2^n`-dimensional
    space, so the order of multiplication is irrelevant. -/
theorem embedGate1_disjoint_comm {i j : Fin n} (h : i ≠ j)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i G * embedGate1 n j H = embedGate1 n j H * embedGate1 n i G := by
  ext r c
  rw [embedGate1_mul_apply h G H r c, embedGate1_mul_apply (Ne.symm h) H G r c]
  by_cases hM : Match2 n i j r.val c.val
  · rw [ite_eq_left hM, ite_eq_left ((match2_swap i j r.val c.val).mp hM), mul_comm]
  · rw [ite_eq_right hM, ite_eq_right (fun hc => hM ((match2_swap i j r.val c.val).mpr hc))]

end CatCrypt.Quantum.Optimization.DisjointCommute
