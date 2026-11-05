/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySound
public import CatCrypt.Quantum.Optimization.MatrixCorrect

/-!
# Full real-semantics soundness of `optimizeLevel1`

Discharges the two templates `UnitarySound` left open and assembles them with
the single-qubit set to certify the **complete** Level-1 template optimizer
against the real unitary semantics `unitaryDenote`:

* `cancelCNOT_correctU` — `CNOT;CNOT = I` (two-qubit), via `embedGate2_mul` +
  `cnot_sq` + `embedGate2_one` (needs `c ≠ t`, which the optimizer's `i ≠ j`
  guard provides).
* `tdgTdg_unitaryDenote`, `mergeTdgTdg_correctU` — `Tdg;Tdg = Rz(-π/2) = RzQ(-1/2)`.
  With `rzGate θ = diag(1, eⁱᶿ)`, `Tdg² = diag(1, e^{-iπ/2}) = rzGate(-π/2)` exactly
  (no global phase).
* `optimizeLevel1_unitaryCorrect` — `UnitaryCorrectQ (optimizeLevel1)`: the whole
  Level-1 pass (single-qubit template sweep + CNOT cancellation over all
  distinct pairs) preserves the channel semantics.

## Main results

* `cancelCNOT_correctU` — the template `CNOT(c, t); CNOT(c, t)` to the empty circuit is
  `CorrectU` for `c ≠ t`.
* `mergeTdgTdg_correctU` — the template `Tdg; Tdg` to `RzQ(-1/2)` is `CorrectU`.
* `CorrectM` — a template whose pattern and replacement realize the same unitary;
  `CorrectM.correctU` derives `CorrectU` from it.
* `standardTemplates_correctU` — every standard single-qubit template is `CorrectU`.
* `cnotTemplates_correctU` — every CNOT-cancellation template on distinct qubits is
  `CorrectU`.
* `optimizeLevel1_unitaryCorrect` — `optimizeLevel1` is `UnitaryCorrectQ`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.TemplateMatching
open CatCrypt.Quantum.Optimization.FullOptimizer
open CatCrypt.Quantum.Optimization.UnitarySound
open CatCrypt.Quantum.Optimization.RoutingPerm (circuitUnitary)
open CatCrypt.Quantum.Optimization.PhasePolySemantics (circuitUnitary_ofList_single)
open CatCrypt.Quantum.Optimization.MatrixSound (circuitUnitary_single)

namespace CatCrypt.Quantum.Optimization.UnitarySoundFull

variable {n : ℕ}

/-- `Tdg² = Rz(-π/2)` as a `2×2` matrix: both are `diag(1, e^{-iπ/2})`. -/
theorem tDaggerGate_sq :
    tDaggerGate * tDaggerGate = rzGate (-(Real.pi / 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tDaggerGate, rzGate, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- `CNOT;CNOT = I` under the real unitary semantics (for distinct qubits). -/
theorem cancelCNOT_correctU {c t : Fin n} (h : c ≠ t) :
    CorrectU (cancelCNOT c t) := by
  show unitaryDenote
      (Circuit.seq (Circuit.single (Gate.CNOT c t)) (Circuit.single (Gate.CNOT c t)))
    = unitaryDenote Circuit.empty
  simp only [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_empty]
  have heta : (fun (_ : Unit) => denoteGateU (Gate.CNOT c t : Gate n))
            = (fun () => denoteGateU (Gate.CNOT c t)) := funext (fun () => rfl)
  rw [heta, denoteGateU_compose]
  have hmat : gateEmbedding (Gate.CNOT c t : Gate n) * gateEmbedding (Gate.CNOT c t) = 1 := by
    simp only [gateEmbedding, dite_eq_right h]
    rw [embedGate2_mul, cnot_sq, embedGate2_one]
  rw [show gateEmbedding_unitaryGroup (Gate.CNOT c t : Gate n)
        * gateEmbedding_unitaryGroup (Gate.CNOT c t) = 1 from Subtype.ext hmat,
    unitaryChannel_one_eq_qpure]

/-- `Tdg;Tdg = Rz(-π/2)` under the real unitary semantics. -/
theorem tdgTdg_unitaryDenote (q : Fin n) :
    unitaryDenote
      (Circuit.seq (Circuit.single (Gate.Tdg q)) (Circuit.single (Gate.Tdg q)))
    = unitaryDenote (Circuit.single (Gate.Rz q (-(Real.pi / 2)))) := by
  simp only [unitaryDenote_seq, unitaryDenote_single]
  have heta : (fun (_ : Unit) => denoteGateU (Gate.Tdg q : Gate n))
            = (fun () => denoteGateU (Gate.Tdg q)) := funext (fun () => rfl)
  rw [heta, denoteGateU_compose]
  simp only [denoteGateU]
  congr 1
  apply Subtype.ext
  change gateEmbedding (Gate.Tdg q : Gate n) * gateEmbedding (Gate.Tdg q)
    = gateEmbedding (Gate.Rz q (-(Real.pi / 2)))
  simp only [gateEmbedding]
  rw [embedGate1_mul, tDaggerGate_sq]

/-- The angle `-(1/2)` denotes `-(π/2)`. -/
theorem toReal_neg_half : PiLin.toReal (-(1 / 2)) = -(Real.pi / 2) := by
  simp only [PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi, PiLin.neg_ofPi,
    PiLin.toReal_ofPi]
  push_cast
  ring

/-- `Tdg;Tdg = RzQ(-1/2)` under the real unitary semantics. -/
theorem mergeTdgTdg_correctU (q : Fin n) : CorrectU (mergeTdgTdg q) := by
  refine (tdgTdg_unitaryDenote q).trans ?_
  change unitaryDenote (Circuit.single (Gate.Rz q (-(Real.pi / 2))))
    = unitaryDenote (Circuit.single (Gate.RzQ q (-(1 / 2))))
  have hemb : gateEmbedding_unitaryGroup (Gate.Rz q (-(Real.pi / 2)))
      = gateEmbedding_unitaryGroup (Gate.RzQ q (-(1 / 2))) := by
    refine Subtype.ext ?_
    change embedGate1 n q (rzGate (-(Real.pi / 2)))
      = embedGate1 n q (rzGate (PiLin.toReal (-(1 / 2))))
    rw [toReal_neg_half]
  simp only [Circuit.single, unitaryDenote, denoteGateU, hemb]

/-! ## The templates at the unitary -/

section Matrix

open CatCrypt.Quantum.Programs.Qubit

/-- A template is matrix-correct when its pattern and its replacement realize one
unitary. -/
def CorrectM (t : Template n) : Prop :=
  circuitUnitary t.pattern = circuitUnitary t.replacement

/-- A matrix-correct template is `CorrectU`. -/
theorem CorrectM.correctU {t : Template n} (h : CorrectM t) : CorrectU t :=
  MatrixSound.unitaryDenote_eq_of_circuitUnitary_eq h

/-- The unitary of the two-gate circuit `a; b`. -/
theorem circuitUnitary_pair (a b : Gate n) :
    circuitUnitary (Circuit.seq (Circuit.single a) (Circuit.single b)) =
      gateEmbedding_unitaryGroup b * gateEmbedding_unitaryGroup a := by
  change circuitUnitary (Circuit.single b) * circuitUnitary (Circuit.single a) = _
  rw [circuitUnitary_single, circuitUnitary_single]

/-- The unitary of the three-gate circuit `a; b; c`. -/
theorem circuitUnitary_triple (a b c : Gate n) :
    circuitUnitary (Circuit.seq (Circuit.single a)
        (Circuit.seq (Circuit.single b) (Circuit.single c))) =
      gateEmbedding_unitaryGroup c * gateEmbedding_unitaryGroup b *
        gateEmbedding_unitaryGroup a := by
  change circuitUnitary (Circuit.seq (Circuit.single b) (Circuit.single c)) *
    circuitUnitary (Circuit.single a) = _
  rw [circuitUnitary_pair, circuitUnitary_single]

/-- Every standard single-qubit template is matrix-correct. -/
theorem standardTemplates_correctM (q : Fin n) :
    ∀ t ∈ standardTemplates q, CorrectM t := by
  intro t ht
  fin_cases ht
  · simp only [CorrectM, cancelHH, circuitUnitary_pair]
    apply Subtype.ext
    change embedGate1 n q hadamard * embedGate1 n q hadamard = 1
    rw [embedGate1_mul, hadamard_sq, embedGate1_one]
  · simp only [CorrectM, cancelXXTemplate, circuitUnitary_pair]
    apply Subtype.ext
    change embedGate1 n q pauliX * embedGate1 n q pauliX = 1
    rw [embedGate1_mul, pauliX_sq, embedGate1_one]
  · simp only [CorrectM, cancelYY, circuitUnitary_pair]
    apply Subtype.ext
    change embedGate1 n q pauliY * embedGate1 n q pauliY = 1
    rw [embedGate1_mul, pauliY_sq, embedGate1_one]
  · simp only [CorrectM, cancelZZ, circuitUnitary_pair]
    apply Subtype.ext
    change embedGate1 n q pauliZ * embedGate1 n q pauliZ = 1
    rw [embedGate1_mul, pauliZ_sq, embedGate1_one]
  · simp only [CorrectM, cancelTTdg, circuitUnitary_pair]
    apply Subtype.ext
    change embedGate1 n q tDaggerGate * embedGate1 n q tGate = 1
    rw [embedGate1_mul, tDaggerGate_mul_tGate, embedGate1_one]
  · simp only [CorrectM, cancelTdgT, circuitUnitary_pair]
    apply Subtype.ext
    change embedGate1 n q tGate * embedGate1 n q tDaggerGate = 1
    rw [embedGate1_mul, tGate_mul_tDaggerGate, embedGate1_one]
  · simp only [CorrectM, mergeTT, circuitUnitary_pair, circuitUnitary_single]
    apply Subtype.ext
    change embedGate1 n q tGate * embedGate1 n q tGate = embedGate1 n q phaseS
    rw [embedGate1_mul, tGate_sq_eq_phaseS]
  · simp only [CorrectM, mergeTdgTdg, circuitUnitary_pair, circuitUnitary_single]
    apply Subtype.ext
    change embedGate1 n q tDaggerGate * embedGate1 n q tDaggerGate =
      embedGate1 n q (rzGate (PiLin.toReal (-(1 / 2))))
    rw [embedGate1_mul, tDaggerGate_sq, toReal_neg_half]
  · simp only [CorrectM, hxh_to_z, circuitUnitary_triple, circuitUnitary_single]
    apply Subtype.ext
    change embedGate1 n q hadamard * embedGate1 n q pauliX * embedGate1 n q hadamard =
      embedGate1 n q pauliZ
    rw [embedGate1_mul, embedGate1_mul, hadamard_pauliX_hadamard]
  · simp only [CorrectM, hzh_to_x, circuitUnitary_triple, circuitUnitary_single]
    apply Subtype.ext
    change embedGate1 n q hadamard * embedGate1 n q pauliZ * embedGate1 n q hadamard =
      embedGate1 n q pauliX
    rw [embedGate1_mul, embedGate1_mul, hadamard_pauliZ_hadamard]
  · simp only [CorrectM, mergeSS, circuitUnitary_pair, circuitUnitary_single]
    apply Subtype.ext
    change embedGate1 n q phaseS * embedGate1 n q phaseS = embedGate1 n q pauliZ
    rw [embedGate1_mul, phaseS_sq_eq_pauliZ]

/-- The CNOT-cancellation templates on distinct qubits are matrix-correct. -/
theorem cnotTemplates_correctM {i j : Fin n} (h : i ≠ j) :
    ∀ t ∈ cnotTemplates i j, CorrectM t := by
  intro t ht
  fin_cases ht
  simp only [CorrectM, cancelCNOT, circuitUnitary_pair]
  apply Subtype.ext
  change gateEmbedding (Gate.CNOT i j : Gate n) * gateEmbedding (Gate.CNOT i j) = 1
  simp only [gateEmbedding, dite_eq_right h]
  rw [embedGate2_mul, cnot_sq, embedGate2_one]

end Matrix

/-! ## Full Level-1 template set is unitary-correct -/

/-- Every standard single-qubit template is `CorrectU`. -/
theorem standardTemplates_correctU (q : Fin n) :
    ∀ t ∈ standardTemplates q, CorrectU t :=
  fun t ht => (standardTemplates_correctM q t ht).correctU

/-- The CNOT-cancellation template set is `CorrectU` for distinct qubits. -/
theorem cnotTemplates_correctU {i j : Fin n} (h : i ≠ j) :
    ∀ t ∈ cnotTemplates i j, CorrectU t :=
  fun t ht => (cnotTemplates_correctM h t ht).correctU

/-- `unitaryDenote` is preserved by any `Fin.foldl` whose step preserves it. -/
theorem unitaryDenote_finFoldl :
    ∀ {m : ℕ} (f : Circuit n → Fin m → Circuit n),
      (∀ acc q, unitaryDenote (f acc q) = unitaryDenote acc) →
      ∀ c, unitaryDenote (Fin.foldl m f c) = unitaryDenote c
  | 0, _, _, c => by rw [Fin.foldl_zero]
  | m + 1, f, hf, c => by
      rw [Fin.foldl_succ,
        unitaryDenote_finFoldl (fun acc i => f acc i.succ)
          (fun acc i => hf acc i.succ) (f c 0)]
      exact hf c 0

/-- **The full Level-1 optimizer preserves the real unitary semantics.** -/
theorem optimizeLevel1_unitaryCorrect :
    UnitaryCorrectQ (optimizeLevel1 : Circuit n → Circuit n) := by
  intro c
  show unitaryDenote c = unitaryDenote (optimizeLevel1 c)
  symm
  unfold optimizeLevel1
  rw [unitaryDenote_finFoldl _ (fun acc i => by
        refine unitaryDenote_finFoldl _ (fun acc₂ j => ?_) acc
        split
        · rfl
        · next hne =>
          exact applyTemplates_correctU _ (cnotTemplates_correctU (by simpa using hne)) acc₂ 100),
    unitaryDenote_finFoldl _ (fun acc q =>
      applyTemplates_correctU _ (standardTemplates_correctU q) acc 100)]

end CatCrypt.Quantum.Optimization.UnitarySoundFull
