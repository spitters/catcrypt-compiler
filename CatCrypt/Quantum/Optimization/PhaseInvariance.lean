/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySoundFull

/-!
# Global-phase channel invariance and the X-Rz conjugation identity

A unitary channel `ρ ↦ U ρ U†` is invariant under multiplying `U` by a global
phase `c` with `c · conj c = 1`: the two phases cancel in `(cU) ρ (cU)†`
(`UnitaryChannel.conjugate_smul_unit`, `UnitaryChannel.unitaryChannel_eq_of_conjugate`).
This file uses that invariance to discharge the global phase that appears when
conjugating an `Rz` rotation by `X`:

* `pauliX_rzGate_conj` — `X · Rz(θ) · X = e^{iθ} · Rz(−θ)` (a 2×2 identity).
* `xRzx_correctU` — under the real unitary semantics `unitaryDenote`, the circuit
  `X; Rz(θ); X` equals `Rz(−θ)`: the global phase `e^{iθ}` is invisible to the
  channel.

This unblocks NOT-propagation soundness (commuting an `X` through an `Rz`).

## Main results

* `pauliX_rzGate_conj` — `X · Rz(θ) · X = e^{iθ} · Rz(−θ)` as 2×2 matrices.
* `gateEmbedding_XRzX_eq_smul` — the same identity for the `gateEmbedding` of the three
  gates on qubit `q` of an `n`-qubit register.
* `xRzx_correctU` — under `unitaryDenote`, the circuit `X; Rz(θ); X` equals `Rz(−θ)`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit

namespace CatCrypt.Quantum.Optimization.PhaseInvariance

/-! ## The X-Rz conjugation identity -/

/-- `X · Rz(θ) · X = e^{iθ} · Rz(−θ)` as a `2×2` matrix.
    Both sides are `diag(e^{iθ}, 1)`. -/
theorem pauliX_rzGate_conj (θ : ℝ) :
    pauliX * rzGate θ * pauliX
      = (Complex.exp (Complex.I * (θ : ℂ))) • rzGate (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, rzGate, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Complex.exp_neg, mul_neg]

/-! ## The X-Rz conjugation under the real channel semantics -/

/-- `X · Rz(θ) · X = e^{iθ} · Rz(−θ)` at the `gateEmbedding` level, packaged so
    the global phase is exposed for `conjugate_smul_unit`. -/
theorem gateEmbedding_XRzX_eq_smul {n : ℕ} (q : Fin n) (θ : ℝ) :
    gateEmbedding (Gate.X q : Gate n) * gateEmbedding (Gate.Rz q θ)
        * gateEmbedding (Gate.X q)
      = (Complex.exp (Complex.I * (θ : ℂ)))
        • gateEmbedding (Gate.Rz q (-θ)) := by
  show embedGate1 n q pauliX * embedGate1 n q (rzGate θ) * embedGate1 n q pauliX
      = (Complex.exp (Complex.I * (θ : ℂ))) • embedGate1 n q (rzGate (-θ))
  rw [embedGate1_mul, embedGate1_mul, pauliX_rzGate_conj, embedGate1_smul]

/-- **NOT-propagation through `Rz`.** Under the unitary channel
    semantics `unitaryDenote`, the circuit `X; Rz(θ); X` equals `Rz(−θ)`: the
    global phase `e^{iθ}` from `X·Rz(θ)·X = e^{iθ}·Rz(−θ)` is invisible to the
    channel `ρ ↦ U ρ U†`. -/
theorem xRzx_correctU {n : ℕ} (q : Fin n) (θ : ℝ) :
    unitaryDenote (Circuit.seq (Circuit.single (Gate.X q))
        (Circuit.seq (Circuit.single (Gate.Rz q θ)) (Circuit.single (Gate.X q))))
      = unitaryDenote (Circuit.single (Gate.Rz q (-θ)) : Circuit n) := by
  simp only [unitaryDenote_seq, unitaryDenote_single]
  -- Compose the three gates into a single unitary channel.
  have hinner : (fun (_ : Unit) => denoteGateU (n := n) (Gate.X q))
      = (fun () => denoteGateU (Gate.X q)) := funext (fun () => rfl)
  rw [hinner, denoteGateU_compose,
    show denoteGateU (Gate.X q)
      = unitaryChannel (gateEmbedding_unitaryGroup (Gate.X q)) from rfl,
    unitaryChannel_compose]
  -- Now: unitaryChannel ((X * Rz θ) * X) = denoteGateU (Rz (-θ)).
  -- Discharge the global phase via conjugate invariance.
  show unitaryChannel _ = unitaryChannel (gateEmbedding_unitaryGroup (Gate.Rz q (-θ)))
  apply unitaryChannel_eq_of_conjugate
  rw [UnitaryGroup.mul_val, UnitaryGroup.mul_val]
  have hmat : ((gateEmbedding_unitaryGroup (Gate.X q) :
          Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
          * gateEmbedding_unitaryGroup (Gate.Rz q θ))
        * gateEmbedding_unitaryGroup (Gate.X q)
      = (Complex.exp (Complex.I * (θ : ℂ)))
        • (gateEmbedding_unitaryGroup (Gate.Rz q (-θ)) :
            Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
    gateEmbedding_XRzX_eq_smul q θ
  rw [hmat]
  exact conjugate_smul_unit _ (by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    rw [show Complex.I * (θ : ℂ) + (starRingEnd ℂ) (Complex.I * (θ : ℂ)) = 0 from by
      simp [Complex.conj_I]]
    exact Complex.exp_zero) _

end CatCrypt.Quantum.Optimization.PhaseInvariance
