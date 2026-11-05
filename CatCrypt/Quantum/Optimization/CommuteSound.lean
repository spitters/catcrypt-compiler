/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.Optimization.DisjointCommute

/-!
# Gate-commutation soundness under the real unitary semantics

Gate-commutation lemmas stated against the unitary-channel semantics
`unitaryDenote` rather than the `qpure ()` denotation. They carry the quantum
optimizer's soundness at Levels 2 and 3: a peephole pass that reorders
commuting gates preserves `unitaryDenote`.

## Same-qubit diagonal commutation (proved)

`Z`, `S`, `T`, `Tdg`, and `Rz θ` all embed as `embedGate1 n q (diag 1 b)`
for some `b : ℂ`. Two such diagonal single-qubit gates on the **same** qubit
`q` commute:

`unitaryDenote (seq (single g₁) (single g₂)) = unitaryDenote (seq (single g₂) (single g₁))`.

The route mirrors `UnitarySoundFull.mergeTdgTdg_correctU`:
`denoteGateU_compose` reduces the two orders to
`gateEmbedding_unitaryGroup g₂ * gateEmbedding_unitaryGroup g₁` versus
`gateEmbedding_unitaryGroup g₁ * gateEmbedding_unitaryGroup g₂`; `Subtype.ext`
drops to `embedGate1 n q D₂ * embedGate1 n q D₁ = embedGate1 n q D₁ * embedGate1 n q D₂`,
which `embedGate1_mul` (both directions) reduces to `D₂ * D₁ = D₁ * D₂` for the
two `2×2` diagonal matrices — `diag(1,a) * diag(1,b) = diag(1,a*b) = diag(1,b) * diag(1,a)`.

Single-qubit gates on distinct qubits commute by `DisjointCommute.embedGate1_disjoint_comm`.

## Main results

* `IsDiagOn` — a gate embeds as a diagonal one-qubit matrix `diag(1, b)` on qubit `q`.
* `gateEmbedding_unitaryGroup_diag_comm` — the unitary embeddings of two gates diagonal on
  the same qubit commute.
* `diag_same_qubit_commuteU` — two gates diagonal on the same qubit commute under
  `unitaryDenote`.
* `TS_commuteU`, `ZRz_commuteU` — the instances `T; S = S; T` and `Z; Rz θ = Rz θ; Z`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity

noncomputable section

namespace CatCrypt.Quantum.Optimization.CommuteSound

open scoped Matrix

variable {n : ℕ}

/-! ## Diagonal `2×2` gate matrices commute -/

/-- A `2×2` diagonal matrix `diag(1, b)`. All of `Z`, `S`, `T`, `Tdg`, `Rz θ`
    embed as `embedGate1 n q (diagB b)` for the appropriate `b`. -/
def diagB (b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, b]]

@[simp] theorem pauliZ_eq_diagB :
    CatCrypt.Quantum.Programs.Qubit.pauliZ = diagB (-1) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CatCrypt.Quantum.Programs.Qubit.pauliZ, diagB]

@[simp] theorem phaseS_eq_diagB :
    CatCrypt.Quantum.Programs.Qubit.phaseS = diagB Complex.I := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CatCrypt.Quantum.Programs.Qubit.phaseS, diagB]

@[simp] theorem tGate_eq_diagB :
    CatCrypt.Quantum.Programs.Qubit.tGate
      = diagB (Complex.exp (Complex.I * ↑(Real.pi / 4))) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CatCrypt.Quantum.Programs.Qubit.tGate, diagB]

@[simp] theorem tDaggerGate_eq_diagB :
    tDaggerGate = diagB (Complex.exp (-Complex.I * ↑(Real.pi / 4))) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tDaggerGate, diagB]

@[simp] theorem rzGate_eq_diagB (θ : ℝ) :
    rzGate θ = diagB (Complex.exp (Complex.I * ↑θ)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rzGate, diagB]

/-- Two diagonal `2×2` matrices commute: `diag(1,a) * diag(1,b) = diag(1,b) * diag(1,a)`
    (both equal `diag(1, a*b)`). -/
theorem diagB_comm (a b : ℂ) : diagB a * diagB b = diagB b * diagB a := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagB, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Same-qubit commutation at the `embedGate1` matrix level for diagonal gates. -/
theorem embedGate1_diagB_comm (q : Fin n) (a b : ℂ) :
    embedGate1 n q (diagB a) * embedGate1 n q (diagB b)
      = embedGate1 n q (diagB b) * embedGate1 n q (diagB a) := by
  rw [embedGate1_mul, embedGate1_mul, diagB_comm]

/-! ## Same-qubit diagonal gates: classification and commutation -/

/-- A gate is a *diagonal single-qubit gate on qubit `q`* if its matrix
    embedding is `embedGate1 n q (diagB b)` for some `b`. Covers `Z`, `S`,
    `T`, `Tdg`, `Rz θ`. -/
def IsDiagOn (q : Fin n) (g : Gate n) : Prop :=
  ∃ b : ℂ, gateEmbedding g = embedGate1 n q (diagB b)

theorem isDiagOn_Z (q : Fin n) : IsDiagOn q (Gate.Z q) :=
  ⟨-1, by simp only [gateEmbedding, pauliZ_eq_diagB]⟩

theorem isDiagOn_S (q : Fin n) : IsDiagOn q (Gate.S q) :=
  ⟨Complex.I, by simp only [gateEmbedding, phaseS_eq_diagB]⟩

theorem isDiagOn_T (q : Fin n) : IsDiagOn q (Gate.T q) :=
  ⟨Complex.exp (Complex.I * ↑(Real.pi / 4)), by simp only [gateEmbedding, tGate_eq_diagB]⟩

theorem isDiagOn_Tdg (q : Fin n) : IsDiagOn q (Gate.Tdg q) :=
  ⟨Complex.exp (-Complex.I * ↑(Real.pi / 4)), by simp only [gateEmbedding, tDaggerGate_eq_diagB]⟩

theorem isDiagOn_Rz (q : Fin n) (θ : ℝ) : IsDiagOn q (Gate.Rz q θ) :=
  ⟨Complex.exp (Complex.I * ↑θ), by simp only [gateEmbedding, rzGate_eq_diagB]⟩

/-- `RzQ` is diagonal on its own qubit, like `Rz`. -/
theorem isDiagOn_RzQ (q : Fin n) (a : PiLin) : IsDiagOn q (Gate.RzQ q a) :=
  ⟨Complex.exp (Complex.I * ↑(PiLin.toReal a)), by
    simp only [gateEmbedding, rzGate_eq_diagB]⟩

/-- **Same-qubit diagonal commutation** at the unitary-group level: for two
    diagonal single-qubit gates on the same qubit `q`, the order of
    multiplication is irrelevant. -/
theorem gateEmbedding_unitaryGroup_diag_comm {q : Fin n} {g₁ g₂ : Gate n}
    (h₁ : IsDiagOn q g₁) (h₂ : IsDiagOn q g₂) :
    gateEmbedding_unitaryGroup g₂ * gateEmbedding_unitaryGroup g₁
      = gateEmbedding_unitaryGroup g₁ * gateEmbedding_unitaryGroup g₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  apply Subtype.ext
  show gateEmbedding g₂ * gateEmbedding g₁ = gateEmbedding g₁ * gateEmbedding g₂
  rw [ha, hb, embedGate1_diagB_comm]

/-- **Same-qubit diagonal commutation under the real unitary semantics.**

    For two diagonal single-qubit gates (`Z`, `S`, `T`, `Tdg`, `Rz`) on the
    same qubit `q`, swapping their order preserves `unitaryDenote`. -/
theorem diag_same_qubit_commuteU {q : Fin n} {g₁ g₂ : Gate n}
    (h₁ : IsDiagOn q g₁) (h₂ : IsDiagOn q g₂) :
    unitaryDenote (Circuit.seq (Circuit.single g₁) (Circuit.single g₂))
      = unitaryDenote (Circuit.seq (Circuit.single g₂) (Circuit.single g₁)) := by
  simp only [unitaryDenote_seq, unitaryDenote_single]
  have heta₁ : (fun (_ : Unit) => denoteGateU (n := n) g₂)
             = (fun () => denoteGateU g₂) := funext (fun () => rfl)
  have heta₂ : (fun (_ : Unit) => denoteGateU (n := n) g₁)
             = (fun () => denoteGateU g₁) := funext (fun () => rfl)
  rw [heta₁, denoteGateU_compose, heta₂, denoteGateU_compose,
    gateEmbedding_unitaryGroup_diag_comm h₁ h₂]

/-- Concrete instance: `T q ; S q = S q ; T q` under the real unitary semantics. -/
theorem TS_commuteU (q : Fin n) :
    unitaryDenote (Circuit.seq (Circuit.single (Gate.T q)) (Circuit.single (Gate.S q)))
      = unitaryDenote (Circuit.seq (Circuit.single (Gate.S q)) (Circuit.single (Gate.T q))) :=
  diag_same_qubit_commuteU (isDiagOn_T q) (isDiagOn_S q)

/-- Concrete instance: `Z q ; Rz q θ = Rz q θ ; Z q` under the real unitary semantics. -/
theorem ZRz_commuteU (q : Fin n) (θ : ℝ) :
    unitaryDenote (Circuit.seq (Circuit.single (Gate.Z q)) (Circuit.single (Gate.Rz q θ)))
      = unitaryDenote (Circuit.seq (Circuit.single (Gate.Rz q θ)) (Circuit.single (Gate.Z q))) :=
  diag_same_qubit_commuteU (isDiagOn_Z q) (isDiagOn_Rz q θ)

end CatCrypt.Quantum.Optimization.CommuteSound
