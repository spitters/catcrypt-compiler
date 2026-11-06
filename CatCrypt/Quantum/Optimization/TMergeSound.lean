/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySound
public import CatCrypt.Quantum.Optimization.TCountOpt
public import CatCrypt.Quantum.Optimization.MatrixCorrect

/-!
# Real-semantics soundness of the T-count merge pass

`TCountOpt.tMerge` flattens a circuit to a gate list, merges maximal runs of
consecutive `T` gates on a single qubit into the minimal Clifford+T residue
(`tPowerToGates`, using `T² = S`, `T⁴ = Z`, `T⁸ = I`), and rebuilds the circuit.

The pass is stated against the unitary-channel semantics
`GateUnitarity.unitaryDenote` (ρ ↦ UρU†).

## Strategy

The list denotation `unitaryDenote ∘ Circuit.ofList` is the unitary channel of
the product (in reverse, head-applied-first order) of the per-gate embeddings.
We package this product as `gateProdU` and reduce the whole pass to two facts:

* a run of `m` consecutive `T q` gates and its merged form `tPowerToGates q m`
  have the same `gateProdU` (both equal `Tᵐ` in the unitary group, which is
  `8`-periodic with `T² = S`, `T⁴ = Z`, `T⁸ = I`); and
* `countConsecutiveT q rest` exposes its prefix as `replicate count (.T q)`.

The main result is `tMerge_unitaryCorrect : UnitaryCorrectQ tMerge`.

## Main results

* `gateProdU` — the product of the per-gate embeddings of a gate list in application
  order, the unitary realized by `Circuit.ofList`.
* `gateProdU_tPowerToGates` — the residue `tPowerToGates q m` realizes `Tᵐ`.
* `countConsecutiveT_decomp` — `countConsecutiveT q gs` splits `gs` into a run of
  `T q` gates followed by the remaining gates.
* `gateProdU_tMergeList` — `tMergeList` leaves `gateProdU` unchanged.
* `tMerge_matrixCorrect` — `tMerge` preserves `circuitUnitary`.
* `tMerge_unitaryCorrect` — `tMerge` is `UnitaryCorrectQ`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.TCountOpt
open CatCrypt.Quantum.Optimization.UnitarySound
open CatCrypt.Quantum.Optimization.RoutingPerm (circuitUnitary)
open CatCrypt.Quantum.Optimization.MatrixSound

namespace CatCrypt.Quantum.Optimization.TMergeSound

noncomputable section

variable {n : ℕ}

/-! ## Gate-list unitary product -/

/-- The product of per-gate embeddings of a gate list, in the order they are
applied (the head gate is applied first, so it sits on the *right* of the
matrix product). This is the unitary realised by `Circuit.ofList`. -/
def gateProdU : List (Gate n) → Matrix.unitaryGroup (Fin (2 ^ n)) ℂ
  | []      => 1
  | g :: gs => gateProdU gs * gateEmbedding_unitaryGroup g

/-- The unitary of a gate list is `gateProdU`. -/
theorem circuitUnitary_ofList_eq_gateProdU (l : List (Gate n)) :
    circuitUnitary (Circuit.ofList l) = gateProdU l := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [circuitUnitary_ofList_cons, ih]; rfl

/-- `unitaryDenote ∘ Circuit.ofList` is the unitary channel of `gateProdU`. -/
theorem unitaryDenote_ofList_eq_channel (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList gs) = unitaryChannel (gateProdU gs) := by
  rw [RoutingPerm.unitaryDenote_eq_channel, circuitUnitary_ofList_eq_gateProdU]

/-- `gateProdU` turns append into a reversed product. -/
theorem gateProdU_append (xs ys : List (Gate n)) :
    gateProdU (xs ++ ys) = gateProdU ys * gateProdU xs := by
  simp only [← circuitUnitary_ofList_eq_gateProdU, PhasePolySemantics.circuitUnitary_ofList_append]

/-! ## T-power group identities

All at the level of `gateEmbedding_unitaryGroup` (the unitary group, a monoid),
lifted from the public `2×2` matrix identities in `GateUnitarity` via
`embedGate1_mul`. `T` denotes `gateEmbedding_unitaryGroup (.T q)`. -/

/-- `T · T = S`. -/
theorem ug_TT (q : Fin n) :
    gateEmbedding_unitaryGroup (.T q) * gateEmbedding_unitaryGroup (.T q) =
      gateEmbedding_unitaryGroup (.S q : Gate n) := by
  apply Subtype.ext
  show embedGate1 n q _ * embedGate1 n q _ = embedGate1 n q _
  rw [embedGate1_mul, tGate_sq_eq_phaseS]

/-- `S · S = Z`. -/
theorem ug_SS (q : Fin n) :
    gateEmbedding_unitaryGroup (.S q) * gateEmbedding_unitaryGroup (.S q) =
      gateEmbedding_unitaryGroup (.Z q : Gate n) := by
  apply Subtype.ext
  show embedGate1 n q _ * embedGate1 n q _ = embedGate1 n q _
  rw [embedGate1_mul, phaseS_sq_eq_pauliZ]

/-- `Z · Z = 1`. -/
theorem ug_ZZ (q : Fin n) :
    gateEmbedding_unitaryGroup (.Z q) * gateEmbedding_unitaryGroup (.Z q) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext
  show embedGate1 n q _ * embedGate1 n q _ = (1 : Matrix _ _ ℂ)
  rw [embedGate1_mul, Programs.Qubit.pauliZ_sq, embedGate1_one]

/-- `T · Tdg = 1`. -/
theorem ug_TTdg (q : Fin n) :
    gateEmbedding_unitaryGroup (.T q) * gateEmbedding_unitaryGroup (.Tdg q) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext
  show embedGate1 n q _ * embedGate1 n q _ = (1 : Matrix _ _ ℂ)
  rw [embedGate1_mul, tGate_mul_tDaggerGate, embedGate1_one]

/-- `T² = S` as a power. -/
theorem ug_Tpow2 (q : Fin n) :
    (gateEmbedding_unitaryGroup (.T q)) ^ 2 = gateEmbedding_unitaryGroup (.S q : Gate n) := by
  rw [pow_two]; exact ug_TT q

/-- `T⁴ = Z` as a power. -/
theorem ug_Tpow4 (q : Fin n) :
    (gateEmbedding_unitaryGroup (.T q)) ^ 4 = gateEmbedding_unitaryGroup (.Z q : Gate n) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ug_Tpow2, pow_two, ug_SS]

/-- `T⁸ = 1`: the `T` gate has order dividing 8. -/
theorem ug_Tpow8 (q : Fin n) :
    (gateEmbedding_unitaryGroup (.T q)) ^ 8 = (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, ug_Tpow4, pow_two, ug_ZZ]

/-- `T` is `8`-periodic: `Tᵐ = T^(m % 8)`. -/
theorem ug_Tpow_mod (q : Fin n) (m : ℕ) :
    (gateEmbedding_unitaryGroup (.T q)) ^ m =
      (gateEmbedding_unitaryGroup (.T q)) ^ (m % 8) := by
  conv_lhs => rw [← Nat.div_add_mod m 8, pow_add, pow_mul, ug_Tpow8, one_pow, one_mul]

/-- `Tdg = T⁷` in the unitary group (`T` has order `8`, so `Tdg = T⁻¹ = T⁷`). -/
theorem ug_Tdg_eq_Tpow7 (q : Fin n) :
    gateEmbedding_unitaryGroup (.Tdg q : Gate n) =
      (gateEmbedding_unitaryGroup (.T q)) ^ 7 := by
  have hinv : gateEmbedding_unitaryGroup (.Tdg q : Gate n) =
      (gateEmbedding_unitaryGroup (.T q))⁻¹ :=
    eq_inv_of_mul_eq_one_right (ug_TTdg q)
  have h7 : (gateEmbedding_unitaryGroup (.T q)) ^ 7 =
      (gateEmbedding_unitaryGroup (.T q))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, ug_Tpow8]
  rw [hinv, h7]

/-- **Core merge identity.** The merged residue `tPowerToGates q m` realises the
same unitary as a run of `m` consecutive `T q` gates, namely `Tᵐ`. -/
theorem gateProdU_tPowerToGates (q : Fin n) (m : ℕ) :
    gateProdU (tPowerToGates q m) = (gateEmbedding_unitaryGroup (.T q)) ^ m := by
  rw [ug_Tpow_mod]
  unfold tPowerToGates
  have hlt : m % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (m % 8) <;>
    simp only [gateProdU, one_mul, pow_zero, pow_one,
      ug_Tpow2, ug_Tpow4, ug_Tdg_eq_Tpow7] <;>
    first
      | rw [← ug_Tpow2, ← pow_succ]            -- T³ = S·T
      | rw [← ug_Tpow4, ← pow_succ]            -- T⁵ = Z·T
      | rw [← ug_Tpow4, ← ug_Tpow2, ← pow_add] -- T⁶ = Z·S

/-- `gateProdU` of a `T`-run is the corresponding power of `T`. -/
theorem gateProdU_replicate_T (q : Fin n) (k : ℕ) :
    gateProdU (List.replicate k (Gate.T q)) = (gateEmbedding_unitaryGroup (.T q)) ^ k := by
  induction k with
  | zero => simp only [List.replicate, gateProdU, pow_zero]
  | succ k ih =>
    simp only [List.replicate_succ, gateProdU, ih, pow_succ]

/-! ## `countConsecutiveT` exposes a `T`-run prefix -/

/-- A successful `countConsecutiveT q gs` decomposes `gs` into a maximal run
of `count` copies of `T q` followed by the remainder:
`gs = replicate count (T q) ++ remaining`. -/
theorem countConsecutiveT_decomp (q : Fin n) :
    ∀ (gs : List (Gate n)),
      gs = List.replicate (countConsecutiveT q gs).1 (Gate.T q) ++
        (countConsecutiveT q gs).2 := by
  intro gs
  induction gs with
  | nil => simp [countConsecutiveT]
  | cons g rest ih =>
    cases g with
    | T i =>
      by_cases hiq : i = q
      · subst hiq
        simp only [countConsecutiveT, decide_true, ite_true]
        rcases hct : countConsecutiveT i rest with ⟨c, r⟩
        simp only [hct] at ih ⊢
        simp only [List.replicate_succ, List.cons_append]
        rw [← ih]
      · simp only [countConsecutiveT, hiq, decide_false, Bool.false_eq_true,
          ite_false, List.replicate_zero, List.nil_append]
    | H i => simp [countConsecutiveT]
    | X i => simp [countConsecutiveT]
    | Y i => simp [countConsecutiveT]
    | Z i => simp [countConsecutiveT]
    | S i => simp [countConsecutiveT]
    | Tdg i => simp [countConsecutiveT]
    | Rz i θ => simp [countConsecutiveT]
    | RzQ i q => simp [countConsecutiveT]
    | CNOT i j => simp [countConsecutiveT]
    | CZ i j => simp [countConsecutiveT]

/-- The remainder of `countConsecutiveT` is at most as long as the input. -/
theorem countConsecutiveT_remaining_length_le (q : Fin n) (gs : List (Gate n)) :
    (countConsecutiveT q gs).2.length ≤ gs.length := by
  conv_rhs => rw [countConsecutiveT_decomp q gs]
  simp only [List.length_append, List.length_replicate]
  omega

/-! ## `tMergeList` preserves the gate-list unitary -/

/-- On a non-`T` head, `tMergeList` simply keeps the gate and recurses. -/
theorem tMergeList_cons_nonT (g : Gate n) (rest : List (Gate n)) (fuel' : ℕ)
    (hg : ∀ q, g ≠ Gate.T q) :
    tMergeList (g :: rest) (fuel' + 1) = g :: tMergeList rest fuel' := by
  cases g with
  | T q => exact absurd rfl (hg q)
  | _ => rfl

/-- **`tMergeList` is unitary-preserving.** With enough fuel it leaves the
realised unitary product unchanged: each merged `T`-run `tPowerToGates q (k+1)`
realises `T^(k+1)`, exactly the product of the `k+1` consecutive `T q` gates it
replaces. -/
theorem gateProdU_tMergeList :
    ∀ (fuel : ℕ) (gs : List (Gate n)), gs.length < fuel →
      gateProdU (tMergeList gs fuel) = gateProdU gs := by
  intro fuel
  induction fuel with
  | zero => intro gs h; exact absurd h (Nat.not_lt_zero _)
  | succ fuel' ih =>
    intro gs hlen
    have hrest_fuel : ∀ (g : Gate n) (rest : List (Gate n)),
        gs = g :: rest → rest.length < fuel' := by
      intro g rest hgs; rw [hgs] at hlen
      simp only [List.length_cons] at hlen; omega
    cases gs with
    | nil => rfl
    | cons g rest =>
      have hrf : rest.length < fuel' := hrest_fuel g rest rfl
      -- Non-T heads: tMergeList (g :: rest) (fuel'+1) = g :: tMergeList rest fuel'.
      have other : (∀ q', g ≠ Gate.T q') →
          gateProdU (tMergeList (g :: rest) (fuel' + 1)) = gateProdU (g :: rest) := by
        intro hne
        rw [tMergeList_cons_nonT g rest fuel' hne]
        simp only [gateProdU, ih rest hrf]
      cases g with
      | T q =>
        rcases hct : countConsecutiveT q rest with ⟨count, remaining⟩
        have hrem_len : remaining.length ≤ rest.length := by
          have := countConsecutiveT_remaining_length_le q rest
          rw [hct] at this; exact this
        have hrem_fuel : remaining.length < fuel' := by omega
        have hdec : rest = List.replicate count (Gate.T q) ++ remaining := by
          have := countConsecutiveT_decomp q rest
          rw [hct] at this; exact this
        have hunfold : tMergeList (Gate.T q :: rest) (fuel' + 1)
            = tPowerToGates q (count + 1) ++ tMergeList remaining fuel' := by
          conv_lhs => rw [tMergeList]
          rw [hct]
        rw [hunfold, gateProdU_append, gateProdU_tPowerToGates, ih remaining hrem_fuel]
        conv_rhs => rw [gateProdU, hdec, gateProdU_append, gateProdU_replicate_T]
        rw [pow_succ, mul_assoc]
      | H i => exact other (by simp)
      | X i => exact other (by simp)
      | Y i => exact other (by simp)
      | Z i => exact other (by simp)
      | S i => exact other (by simp)
      | Tdg i => exact other (by simp)
      | Rz i θ => exact other (by simp)
      | RzQ i q => exact other (by simp)
      | CNOT i j => exact other (by simp)
      | CZ i j => exact other (by simp)

/-- `tMerge` preserves `circuitUnitary`. -/
theorem tMerge_matrixCorrect : MatrixCorrect (tMerge : Circuit n → Circuit n) := by
  intro c
  unfold tMerge
  rw [circuitUnitary_ofList_eq_gateProdU,
    gateProdU_tMergeList _ _ (Nat.lt_succ_self _),
    ← circuitUnitary_ofList_eq_gateProdU, circuitUnitary_ofList_circuitToList]

/-! ## Main result -/

/-- `tMerge` preserves the real unitary semantics: for every circuit `c`,
`unitaryDenote (tMerge c) = unitaryDenote c`. -/
theorem unitaryDenote_tMerge (c : Circuit n) :
    unitaryDenote (tMerge c) = unitaryDenote c :=
  unitaryDenote_eq_of_circuitUnitary_eq (tMerge_matrixCorrect c)

/-- **The T-count merge pass is semantics-preserving.** `tMerge` preserves the
unitary-channel denotation `unitaryDenote`; this is `UnitaryCorrectQ` in the
sense of `GateUnitarity`. -/
theorem tMerge_unitaryCorrect : UnitaryCorrectQ (tMerge : Circuit n → Circuit n) :=
  tMerge_matrixCorrect.unitaryCorrectQ

end

end CatCrypt.Quantum.Optimization.TMergeSound
