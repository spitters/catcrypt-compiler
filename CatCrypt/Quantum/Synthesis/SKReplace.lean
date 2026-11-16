/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.HTWord
public import CatCrypt.Quantum.Synthesis.SolovayKitaev

/-!
# Solovay–Kitaev replacement of the one-qubit gates of a circuit

The producer `skProducer ε` reads the word of `exists_htWord_approx` at precision `ε` through
choice. It is sound at precision `ε` for `0 < ε < 1` and its words have the Solovay–Kitaev
length `KHT · log (1/ε) ^ skExp + KHT`. With the pass `skReplace` of `HTWord` it gives, for
every gate list, a replacement whose one-qubit gates are `H`, `T`, `T†`, within `k ε` of the
list up to a global phase, `k` the number of replaced gates.

## Main definitions

* `KHT` — the constant of `exists_htWord_approx`.
* `skProducer` — the choice producer.

## Main statements

* `producerSound_skProducer` — the producer is sound.
* `length_skProducer` — the length bound of its words.
* `exists_skReplace_approx` — **Solovay–Kitaev replacement** at a per-gate precision.
* `exists_skReplace_total` — the same at a total precision.
-/

@[expose] public section

set_option autoImplicit false

open Complex
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QFT (listMatrix)
open scoped Matrix.Norms.L2Operator

namespace CatCrypt.Quantum.Synthesis.SK

variable {n : ℕ}

/-- The constant of `exists_htWord_approx`. -/
noncomputable def KHT : ℝ := exists_htWord_approx.choose

/-- The word of `exists_htWord_approx` at precision `ε`, read through `Classical.choose`;
`[]` off the unitary group and for `ε ∉ (0, 1)`. -/
noncomputable def skProducer (ε : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) : List (Gate 1) :=
  open Classical in
  if h : U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ 0 < ε ∧ ε < 1 then
    (exists_htWord_approx.choose_spec U h.1 ε h.2.1 h.2.2).choose
  else []

/-- The properties of the word of `skProducer` on a unitary. -/
theorem skProducer_spec {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ c : ℂ, (∀ g ∈ skProducer ε U, g = .H 0 ∨ g = .T 0 ∨ g = .Tdg 0) ∧ ‖c‖ = 1 ∧
      ‖U - c • listMatrix (skProducer ε U)‖ ≤ ε ∧
      ((skProducer ε U).length : ℝ) ≤
        KHT * Real.log (1 / ε) ^ (Real.log 5 / Real.log (3 / 2)) + KHT := by
  have h : U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ 0 < ε ∧ ε < 1 := ⟨hU, hε, hε1⟩
  simp only [skProducer, h, and_self, ↓reduceDIte]
  exact (exists_htWord_approx.choose_spec U h.1 ε h.2.1 h.2.2).choose_spec

/-- The producer is sound at precision `ε`. -/
theorem producerSound_skProducer {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ProducerSound (skProducer ε) ε := by
  intro U hU
  obtain ⟨c, hw, hc1, hc, -⟩ := skProducer_spec hε hε1 hU
  refine ⟨fun g hg => ?_, c⁻¹, by rw [norm_inv, hc1, inv_one], ?_⟩
  · rcases hw g hg with h | h | h <;> subst h <;> rfl
  · have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc1
    have he : listMatrix (skProducer ε U) - c⁻¹ • U =
        (-c⁻¹) • (U - c • listMatrix (skProducer ε U)) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc0]
      simp only [neg_smul, one_smul]
      abel
    rw [he, norm_smul, norm_neg, norm_inv, hc1, inv_one, one_mul]
    exact hc

/-- The length bound of the words of `skProducer`. -/
theorem length_skProducer {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ((skProducer ε U).length : ℝ) ≤ KHT * Real.log (1 / ε) ^ SolovayKitaev.skExp + KHT := by
  obtain ⟨-, -, -, -, h⟩ := skProducer_spec hε hε1 hU
  exact h

/-- **Solovay–Kitaev replacement of a circuit.** Every gate list has a replacement whose
one-qubit gates are `H`, `T`, `T†`, within `k ε` up to a global phase, `k` the number of
replaced gates, of length at most `|L| + k (KHT log(1/ε)^c + KHT)`. -/
theorem exists_skReplace_approx {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (L : List (Gate n)) :
    ∃ L' : List (Gate n), (∀ g ∈ L', isRot g = false) ∧
      (∃ c : ℂ, ‖c‖ = 1 ∧ ‖listMatrix L' - c • listMatrix L‖ ≤ (L.countP isRot : ℝ) * ε) ∧
      (L'.length : ℝ) ≤ L.length +
        L.countP isRot * (KHT * Real.log (1 / ε) ^ SolovayKitaev.skExp + KHT) := by
  set B : ℝ := KHT * Real.log (1 / ε) ^ SolovayKitaev.skExp + KHT with hB
  have hB0 : 0 ≤ B := le_trans (Nat.cast_nonneg _)
    (length_skProducer hε hε1 (one_mem (Matrix.unitaryGroup (Fin 2) ℂ)))
  have hl : ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, (skProducer ε U).length ≤ ⌊B⌋₊ :=
    fun U hU => Nat.le_floor (length_skProducer hε hε1 hU)
  refine ⟨skReplace (skProducer ε) L, isRot_skReplace (producerSound_skProducer hε hε1) L,
    listMatrix_skReplace_approx (producerSound_skProducer hε hε1) L, ?_⟩
  have h := length_skReplace hl L
  calc ((skReplace (skProducer ε) L).length : ℝ)
      ≤ ((L.length + L.countP isRot * ⌊B⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
    _ ≤ L.length + L.countP isRot * B := by
      push_cast
      gcongr
      exact Nat.floor_le hB0

/-- The same at a total precision `δ`, each gate at `δ / k`. -/
theorem exists_skReplace_total {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (L : List (Gate n)) :
    ∃ L' : List (Gate n), (∀ g ∈ L', isRot g = false) ∧
      (∃ c : ℂ, ‖c‖ = 1 ∧ ‖listMatrix L' - c • listMatrix L‖ ≤ δ) ∧
      (L'.length : ℝ) ≤ L.length + L.countP isRot *
        (KHT * Real.log (L.countP isRot / δ) ^ SolovayKitaev.skExp + KHT) := by
  rcases Nat.eq_zero_or_pos (L.countP isRot) with hk | hk
  · refine ⟨L, ?_, ⟨1, by simp, by simpa using hδ.le⟩, ?_⟩
    · simpa using List.countP_eq_zero.mp hk
    · simp [hk]
  · have hk1 : (1 : ℝ) ≤ L.countP isRot := by exact_mod_cast hk
    have hε : 0 < δ / L.countP isRot := by positivity
    have hε1 : δ / L.countP isRot < 1 :=
      lt_of_le_of_lt (div_le_self hδ.le hk1) hδ1
    obtain ⟨L', h1, ⟨c, hc1, hc⟩, h3⟩ := exists_skReplace_approx hε hε1 L
    refine ⟨L', h1, ⟨c, hc1, ?_⟩, ?_⟩
    · rwa [mul_div_cancel₀ _ (by positivity)] at hc
    · rwa [one_div_div] at h3

end CatCrypt.Quantum.Synthesis.SK
