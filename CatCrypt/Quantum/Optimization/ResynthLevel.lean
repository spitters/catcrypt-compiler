/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.MatrixSound
public import CatCrypt.Quantum.Synthesis.QrunchFit

/-!
# The resynthesis level: Level 2, then checked KAK and ZYZ resynthesis

The resynthesis level `resynth` runs the pass list of Level 2 (`levelPasses .Level2`,
`fullOptimize`), then replaces the two-qubit blocks of the result by KAK templates
(`KAKPassSmall.kakEmit`) and its one-qubit runs by ZYZ or XYX templates (`ZYZPass.zyzEmit`),
both at the fits of `QrunchFit` behind the verified checker (`qrunchFitChecked`,
`qrunchZFitChecked`). Its value `Resynth` records the gate lists of the three stages and the
payloads of the replaced blocks and runs, from which `Resynth.phase` and `Resynth.eps` are
the sums of the recorded phases and bounds.

Level 2 preserves `circuitUnitary` exactly (`fullOptimize_level2_circuitUnitary`); the two
resynthesis stages each move the matrix by at most the sum of their bounds, up to the sum of
their phases (`listMatrix_kakEmit_checkedFit`, `listMatrix_zyzEmit_checkedZFit`); the errors
of the stages add (`norm_sub_smul_trans_le`). So the output of the level is within `eps` of
the circuit, up to the phase `e^{i·phase}`, with no hypothesis on the fits.

The level is a definition of its own, beside the pass list of `PassPipeline`, not a
`NamedPass`: a named pass is a map `Circuit n → Circuit n` that preserves `unitaryDenote`
exactly (`NamedPass.run_unitaryCorrect`, on which `runNamed_unitaryCorrect` rests), and the
resynthesis neither preserves it exactly nor returns only a circuit (its phase and bound are
part of the result).

## Main definitions

* `Resynth` — the value of the level: the gate lists of its stages and their payloads.
* `Resynth.phase`, `Resynth.eps` — the sums of the recorded phases and bounds.
* `level2Gates`, `Resynth.ofKak` — the stages.
* `resynthAt` — the level at a pair of fits; `resynth` — the level at the checked fits.

## Main results

* `norm_listMatrix_resynth_sub_le` — `‖M(resynth c) - e^{i·phase} M(c)‖ ≤ eps` in the `ℓ²`
  operator norm, `M` the unitary of a circuit.
* `cnotCount_resynth_out_le` — the output has at most as many CNOTs as Level 2.
-/

@[expose] public section

set_option autoImplicit false

open Complex
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QFT (listMatrix)
open CatCrypt.Quantum.Optimization.FullOptimizer
open CatCrypt.Quantum.Synthesis.KAKPass (cnotCount)
open CatCrypt.Quantum.Synthesis.KAKPassSmall (kakEmit)
open CatCrypt.Quantum.Synthesis.QrunchFit
open scoped Matrix.Norms.L2Operator

namespace CatCrypt.Quantum.Optimization.ResynthLevel

variable {n : ℕ}

/-- A payload of a replaced block or run behind the checker: the floating-point phase of the
fit, the exact phase `φ` and the bound `ε` of the checker. -/
abbrev Payload : Type := Float × PiLin × ℚ

/-- The value of the resynthesis level on a circuit: the gates after Level 2, after the
checked KAK pass and after the checked ZYZ pass, with the payloads of the replaced blocks and
of the replaced runs. -/
structure Resynth (n : ℕ) where
  /-- The gates of the circuit after Level 2. -/
  l2 : List (Gate n)
  /-- The gates after the checked KAK pass. -/
  kak : List (Gate n)
  /-- The payloads of the blocks the KAK pass replaced. -/
  kakPay : List Payload
  /-- The gates after the checked ZYZ pass: the output of the level. -/
  out : List (Gate n)
  /-- The payloads of the runs the ZYZ pass replaced. -/
  zyzPay : List Payload

namespace Resynth

/-- The payloads of all replaced blocks and runs. -/
def payloads (r : Resynth n) : List Payload := r.kakPay ++ r.zyzPay

/-- The global phase of the level: the sum of the exact phases of the payloads. -/
noncomputable def phase (r : Resynth n) : ℝ := (r.payloads.map fun b => PiLin.toReal b.2.1).sum

/-- The error bound of the level: the sum of the bounds of the payloads. -/
def eps (r : Resynth n) : ℚ := (r.payloads.map fun b => b.2.2).sum

/-- The resynthesis stages after the KAK pass: the ZYZ pass at the fit `zf` on the gates `k.1`
of a KAK result `k`, with the axes `runAxes` of the runs of `k.1`; `l2` is recorded as the
input of the KAK pass. -/
def ofKak (zf : Array Synthesis.ZYZPass.Axis → Synthesis.ZYZPass.ZFit n Payload)
    (l2 : List (Gate n)) (k : List (Gate n) × List Payload) : Resynth n :=
  let z := Synthesis.ZYZPass.zyzEmit (zf (runAxes (Synthesis.ZYZPass.collectRuns k.1).toArray)) k.1
  { l2, kak := k.1, kakPay := k.2, out := z.1, zyzPay := z.2 }

end Resynth

/-- The gates of Level 2 on `c`. -/
def level2Gates (c : Circuit n) : List (Gate n) := OpenQASM.toGateList (fullOptimize .Level2 c)

/-- The resynthesis level at a pair of fits: Level 2, then the KAK pass at `kf`, then the ZYZ
pass at `zf`. The executable runs it at the checked fits (`resynth`, whose bound
`norm_listMatrix_resynth_sub_le` proves) or, without `--check`, at the unchecked fits
`qrunchFitUnchecked`, `qrunchZFitUnchecked`, which give the same gates when every fit passes
the checker. -/
def resynthAt (kf : Synthesis.KAKPassSmall.BlockFit n Payload)
    (zf : Array Synthesis.ZYZPass.Axis → Synthesis.ZYZPass.ZFit n Payload) (c : Circuit n) :
    Resynth n :=
  Resynth.ofKak zf (level2Gates c) (kakEmit kf (level2Gates c))

/-- **The resynthesis level.** Level 2, then the checked KAK pass, then the checked ZYZ
pass. -/
def resynth (c : Circuit n) : Resynth n := resynthAt qrunchFitChecked qrunchZFitChecked c

/-- Errors of two approximations add: if `‖B - c₁ A‖ ≤ ε₁` and `‖C - c₂ B‖ ≤ ε₂` with
`‖c₂‖ = 1`, then `‖C - (c₂ c₁) A‖ ≤ ε₁ + ε₂`. -/
theorem norm_sub_smul_trans_le {m : Type*} [Fintype m] [DecidableEq m]
    {A B C : Matrix m m ℂ} {c₁ c₂ : ℂ} {ε₁ ε₂ : ℝ} (hc₂ : ‖c₂‖ = 1)
    (h₁ : ‖B - c₁ • A‖ ≤ ε₁) (h₂ : ‖C - c₂ • B‖ ≤ ε₂) :
    ‖C - (c₂ * c₁) • A‖ ≤ ε₁ + ε₂ := by
  have h : C - (c₂ * c₁) • A = (C - c₂ • B) + c₂ • (B - c₁ • A) := by
    rw [smul_sub, smul_smul]; abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, hc₂, one_mul]
  linarith

/-- The matrix of the gates of Level 2 is the unitary of the circuit. -/
theorem listMatrix_level2Gates (c : Circuit n) :
    listMatrix (level2Gates c) = (RoutingPerm.circuitUnitary c).val := by
  rw [level2Gates, Synthesis.KAKPass.listMatrix_toGateList,
    MatrixSound.fullOptimize_level2_circuitUnitary]

/-- **Approximate correctness of the resynthesis level.** The matrix of the output of
`resynth c` is within `eps` of the unitary of `c` in the `ℓ²` operator norm, up to the global
phase `e^{i·phase}`. -/
theorem norm_listMatrix_resynth_sub_le (c : Circuit n) :
    ‖listMatrix (resynth c).out -
        exp (I * ((resynth c).phase : ℂ)) • (RoutingPerm.circuitUnitary c).val‖ ≤
      ((resynth c).eps : ℝ) := by
  have hk := listMatrix_kakEmit_qrunchFitChecked (level2Gates c)
  have hz := listMatrix_zyzEmit_qrunchZFitChecked
    (runAxes (Synthesis.ZYZPass.collectRuns (kakEmit qrunchFitChecked (level2Gates c)).1).toArray)
    (kakEmit qrunchFitChecked (level2Gates c)).1
  rw [listMatrix_level2Gates] at hk
  have h := norm_sub_smul_trans_le (Complex.norm_exp_I_mul_ofReal _) hk hz
  have he : ∀ x y : ℝ,
      exp (I * (y : ℂ)) * exp (I * (x : ℂ)) = exp (I * ((x + y : ℝ) : ℂ)) := by
    intro x y; rw [← Complex.exp_add]; push_cast; ring_nf
  rw [he] at h
  simp only [resynth, resynthAt, Resynth.ofKak, Resynth.phase, Resynth.eps, Resynth.payloads,
    List.map_append, List.sum_append, Rat.cast_add, Rat.cast_list_sum, List.map_map]
  exact h.trans_eq (by simp [Function.comp_def])

/-- **The CNOT bound of the resynthesis level.** The output of `resynth c` has at most as many
CNOTs as the gates of Level 2: the KAK pass does not add any (`cnotCount_kakEmit_le`) and the
ZYZ pass keeps their number (`cnotCount_zyzEmit`). -/
theorem cnotCount_resynth_out_le (c : Circuit n) :
    cnotCount (resynth c).out ≤ cnotCount (resynth c).l2 := by
  simp only [resynth, resynthAt, Resynth.ofKak, Synthesis.ZYZPass.cnotCount_zyzEmit]
  exact Synthesis.KAKPassSmall.cnotCount_kakEmit_le _ _

end CatCrypt.Quantum.Optimization.ResynthLevel
