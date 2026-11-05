/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.NotPropSound

/-!
# Diagonal gates on the control of a CNOT

A single-qubit gate that is diagonal in the computational basis commutes with a
`CNOT` when it sits on the **control** wire. Structurally: a diagonal
`D = diag(d₀, d₁)` on the high qubit embeds to `embedHigh D = diag(d₀, d₀, d₁, d₁)`,
and `CNOT` permutes only the two control-`1` basis states (rows and columns 2, 3),
which carry the same value `d₁`; so the two 4×4 matrices commute. The bridge
`embedGate1_eq_embedGate2_high` together with `embedGate2_mul` lifts the 4×4 fact
to the `2^n`-dimensional embeddings.

## Main results

* `cnot_embedHigh_diag_comm` — the 4×4 fact.
* `embedGate2_cnot_embedGate1_diag_control_comm` — the `embedGate1`/`embedGate2` form.
* `embedGate1_embedGate2_control_comm` — the `rzGate` instance.
* `gateEmbedding_cnot_diag_control_comm` — the `gateEmbedding` form.

The dual fact for a diagonal gate on the **target** does not hold (`CNOT` mixes
the two target basis states); the target-wire commutation available there is
`NotPropSound.embedGate1_X_cnot_target_comm`, for `X` rather than a diagonal gate.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.Optimization.NotPropSound

noncomputable section

namespace CatCrypt.Quantum.Optimization.ControlCommute

variable {n : ℕ}

/-- `CNOT · embedHigh D = embedHigh D · CNOT` for any diagonal `D`. -/
theorem cnot_embedHigh_diag_comm {D : Matrix (Fin 2) (Fin 2) ℂ}
    (hD : IsDiagonal D) :
    cnot * embedHigh D = embedHigh D * cnot := by
  have h01 : D 0 1 = 0 := hD 0 1 (by decide)
  have h10 : D 1 0 = 0 := hD 1 0 (by decide)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cnot, embedHigh, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.of_apply, h01, h10]

/-- A diagonal single-qubit gate on the **control** `c` of `CNOT c t` commutes
past the CNOT (`embedGate2`/`embedGate1` form). -/
theorem embedGate2_cnot_embedGate1_diag_control_comm {c t : Fin n} (hct : c ≠ t)
    {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsDiagonal D) :
    embedGate2 n c t cnot hct * embedGate1 n c D
      = embedGate1 n c D * embedGate2 n c t cnot hct := by
  rw [embedGate1_eq_embedGate2_high hct D, embedGate2_mul, embedGate2_mul,
    cnot_embedHigh_diag_comm hD]

/-- An `Rz` rotation on the **control** `c` of `CNOT c t` commutes past the CNOT:
both are diagonal in the computational basis on that wire. -/
theorem embedGate1_embedGate2_control_comm {c t : Fin n} (hct : c ≠ t) (θ : ℝ) :
    embedGate1 n c (rzGate θ) * embedGate2 n c t cnot hct
      = embedGate2 n c t cnot hct * embedGate1 n c (rzGate θ) := by
  have hrz : IsDiagonal (rzGate θ) := by
    intro r c hrc; fin_cases r <;> fin_cases c <;> simp_all [rzGate]
  exact (embedGate2_cnot_embedGate1_diag_control_comm hct hrz).symm

/-- A diagonal single-qubit gate on the control `c` of `CNOT c t` commutes past
the CNOT, in `gateEmbedding` form. -/
theorem gateEmbedding_cnot_diag_control_comm {c t : Fin n} (hct : c ≠ t)
    {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsDiagonal D) :
    gateEmbedding (Gate.CNOT c t : Gate n) * embedGate1 n c D
      = embedGate1 n c D * gateEmbedding (Gate.CNOT c t) := by
  rw [show gateEmbedding (Gate.CNOT c t : Gate n) = embedGate2 n c t cnot hct from by
      simp [gateEmbedding, hct]]
  exact embedGate2_cnot_embedGate1_diag_control_comm hct hD

end CatCrypt.Quantum.Optimization.ControlCommute
