/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySoundFull
public import CatCrypt.Quantum.Optimization.NotPropagation

/-!
# Real-semantics soundness of Rz-fusion and NOT-propagation rewrites

This file discharges gate-conjugation / gate-fusion identities against the
unitary-channel semantics `unitaryDenote` (rather than the trivial
`qpure ()` denotation), to support the quantum optimizer's real-semantics
soundness at Levels 2-3.

## Rz fusion (fully proved)

* `mergeRzRz_correctU` — `Rz(α); Rz(β) = Rz(α + β)` under `unitaryDenote`.
  This is the exact analogue of `mergeTdgTdg_correctU`
  (`UnitarySoundFull.lean`): both reduce to a `2×2` diagonal-matrix fact,
  here `rzGate α * rzGate β = rzGate (α + β)`, whose only nontrivial entry is
  `e^{iα}·e^{iβ} = e^{i(α+β)}` (`← Complex.exp_add`).
* `rzGate_mul` — the underlying `2×2` matrix identity.
* `mergeRzRzInv_correctU` — bonus: `Rz(θ); Rz(-θ) = empty` (Rz is invertible).

## NOT propagation (`NotPropagation.notPropagationPass`)

`notPropagationPass` rewrites X (NOT) gates rightward.  The rules it applies
(see `propagateX`) and their `unitaryDenote` soundness status:

* `X(q); X(q) = empty` — already `UnitarySoundFull`-adjacent
  (`GateUnitarity.templateXX_correct`); re-exported here as
  `xx_cancel_correctU`.
* `H; X; H = Z` and `H; Z; H = X` — the Hadamard-conjugation rules that turn
  an X commuting past an H into a Z (and back); already proved in
  `GateUnitarity` as `templateHXH_correct` / `templateHZH_correct` and
  re-exported as `hxh_correctU` / `hzh_correctU`.

## Main results

* `rzGate_mul` — `rzGate α * rzGate β = rzGate (α + β)`.
* `mergeRzRz_correctU` — `Rz(α); Rz(β)` and `Rz(α + β)` have the same `unitaryDenote`.
* `mergeRzRzInv_correctU` — `Rz(θ); Rz(-θ)` and the empty circuit have the same
  `unitaryDenote`.
* `xx_cancel_correctU` — `X; X` and the empty circuit have the same `unitaryDenote`.
* `hxh_correctU`, `hzh_correctU` — `H; X; H = Z` and `H; Z; H = X` under `unitaryDenote`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.UnitarySoundFull

namespace CatCrypt.Quantum.Optimization.FusionSound

variable {n : ℕ}

/-! ## (a) Rz fusion -/

/-- `Rz(α) · Rz(β) = Rz(α + β)` as a `2×2` matrix: both are `diag(1, e^{i·})`,
    and the `(1,1)` entry is `e^{iα}·e^{iβ} = e^{i(α+β)}`.

    Exact analogue of `tDaggerGate_sq`. -/
theorem rzGate_mul (α β : ℝ) :
    rzGate α * rzGate β = rzGate (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzGate, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | rfl
    | (rw [← Complex.exp_add]; congr 1; push_cast; ring)

/-- `Rz(α); Rz(β) = Rz(α + β)` under the real unitary semantics.

    Exact analogue of `mergeTdgTdg_correctU` (which is the `α = β = -π/2`
    instance via `Tdg = Rz(-π/4)` up to global phase).  Routes the gate-level
    statement through `denoteGateU_compose` + `Subtype.ext` + `embedGate1_mul`,
    closing with `rzGate_mul`. -/
theorem mergeRzRz_correctU (q : Fin n) (α β : ℝ) :
    unitaryDenote (Circuit.seq (Circuit.single (Gate.Rz q α))
        (Circuit.single (Gate.Rz q β)))
      = unitaryDenote (Circuit.single (Gate.Rz q (α + β))) := by
  simp only [unitaryDenote_seq, unitaryDenote_single]
  have heta : (fun (_ : Unit) => denoteGateU (Gate.Rz q β : Gate n))
            = (fun () => denoteGateU (Gate.Rz q β)) := funext (fun () => rfl)
  rw [heta, denoteGateU_compose]
  simp only [denoteGateU]
  congr 1
  apply Subtype.ext
  show gateEmbedding (Gate.Rz q β : Gate n) * gateEmbedding (Gate.Rz q α)
    = gateEmbedding (Gate.Rz q (α + β))
  simp only [gateEmbedding]
  rw [embedGate1_mul, rzGate_mul, add_comm]

/-- Bonus: `Rz(θ); Rz(-θ) = empty` — `Rz` is invertible, `Rz(θ)·Rz(-θ) = Rz(0) = I`. -/
theorem mergeRzRzInv_correctU (q : Fin n) (θ : ℝ) :
    unitaryDenote (Circuit.seq (Circuit.single (Gate.Rz q θ))
        (Circuit.single (Gate.Rz q (-θ))))
      = unitaryDenote (Circuit.empty : Circuit n) := by
  rw [mergeRzRz_correctU q θ (-θ)]
  have hθ : θ + -θ = (0 : ℝ) := by ring
  have h1 : gateEmbedding_unitaryGroup (Gate.Rz q (0 : ℝ))
      = (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
    apply Subtype.ext
    show gateEmbedding (Gate.Rz q (0 : ℝ)) = 1
    simp only [gateEmbedding]
    have hrz : rzGate (0 : ℝ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [rzGate, Matrix.one_apply]
    rw [hrz, embedGate1_one]
  rw [hθ, unitaryDenote_single, unitaryDenote_empty, denoteGateU, h1,
    unitaryChannel_one_eq_qpure]

/-! ## (b) NOT-propagation conjugation identities -/

/-- `X; X = empty` under the real unitary semantics — the self-inverse rule
    `propagateX` applies when it meets an X on the same qubit.  Re-export of
    `GateUnitarity.templateXX_correct`. -/
theorem xx_cancel_correctU (q : Fin n) :
    unitaryDenote (Circuit.seq (Circuit.single (Gate.X q)) (Circuit.single (Gate.X q)))
      = unitaryDenote (Circuit.empty : Circuit n) :=
  templateXX_correct q

/-- `H; X; H = Z` under the real unitary semantics — Hadamard conjugation
    turns an X into a Z.  Re-export of `GateUnitarity.templateHXH_correct`. -/
theorem hxh_correctU (q : Fin n) :
    unitaryDenote (Circuit.seq (Circuit.single (Gate.H q))
        (Circuit.seq (Circuit.single (Gate.X q)) (Circuit.single (Gate.H q))))
      = unitaryDenote (Circuit.single (Gate.Z q)) :=
  templateHXH_correct q

/-- `H; Z; H = X` under the real unitary semantics — Hadamard conjugation
    turns a Z back into an X.  Re-export of `GateUnitarity.templateHZH_correct`. -/
theorem hzh_correctU (q : Fin n) :
    unitaryDenote (Circuit.seq (Circuit.single (Gate.H q))
        (Circuit.seq (Circuit.single (Gate.Z q)) (Circuit.single (Gate.H q))))
      = unitaryDenote (Circuit.single (Gate.X q)) :=
  templateHZH_correct q

-- The X-conjugation rule `X; Rz(θ); X = Rz(-θ)` holds only up to the global
-- phase `e^{iθ}`, so it needs a `unitaryChannel (c • U) = unitaryChannel U`
-- (‖c‖=1) phase-invariance lemma not yet in the GateUnitarity layer. Deferred
-- to the gate-commutation/phase infrastructure task (#46/#47 follow-up).

end CatCrypt.Quantum.Optimization.FusionSound
