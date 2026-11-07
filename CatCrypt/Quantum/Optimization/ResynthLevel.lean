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
* `gateTCostG`, `tCostG` — the T-cost of a gate and of a gate list.
* `tGuardFit`, `tGuardZFit` — the fits under the T-cost guard, which drop a template that
  raises the T-cost of its block or run; `resynthT` — the level at the guarded checked fits.

## Main results

* `norm_listMatrix_resynth_sub_le` — `‖M(resynth c) - e^{i·phase} M(c)‖ ≤ eps` in the `ℓ²`
  operator norm, `M` the unitary of a circuit.
* `cnotCount_resynth_out_le` — the output has at most as many CNOTs as Level 2.
* `norm_listMatrix_resynthT_sub_le`, `cnotCount_resynthT_out_le` — the same at the guarded
  fits, guard on or off.
* `tCostG_resynthT_out_le` — under the guard the output has at most the T-cost of Level 2
  (`tCostG_kakEmit_tGuardFit_le`, `tCostG_zyzEmit_tGuardZFit_le`).
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
the checker. Under the T-cost the fits are guarded by `tGuardFit`, `tGuardZFit`. -/
def resynthAt (kf : Synthesis.KAKPassSmall.BlockFit n Payload)
    (zf : Array Synthesis.ZYZPass.Axis → Synthesis.ZYZPass.ZFit n Payload) (c : Circuit n) :
    Resynth n :=
  Resynth.ofKak zf (level2Gates c) (kakEmit kf (level2Gates c))

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

/-! ## The T-cost guard -/

section TGuard

open Synthesis.KAKPass Synthesis.ZYZPass Synthesis.KAKPassSmall

variable {β : Type}

/-- The T-cost of a gate: `TCountOpt.gateTCost` where it is determined (`0` for a Clifford
gate, `1` for `T`, `Tdg` and an `RzQ` at an odd multiple of `π/4`), and `100` for an `Rz` and
for an `RzQ` at any other angle, the estimate of the T gates of a Clifford+T synthesis. -/
def gateTCostG (g : Gate n) : ℕ := (TCountOpt.gateTCost g).getD 100

/-- The T-cost of a gate list: the sum of the T-costs `gateTCostG` of its gates. -/
def tCostG (l : List (Gate n)) : ℕ := (l.map gateTCostG).sum

/-- The empty list has T-cost `0` (an unfolding lemma of `tCostG`). -/
theorem tCostG_nil : tCostG ([] : List (Gate n)) = 0 := rfl

/-- The T-cost of a cons is the T-cost of its head plus that of its tail. -/
theorem tCostG_cons (g : Gate n) (l : List (Gate n)) :
    tCostG (g :: l) = gateTCostG g + tCostG l := by
  simp [tCostG]

/-- The T-cost is additive over concatenation. -/
theorem tCostG_append (l l' : List (Gate n)) : tCostG (l ++ l') = tCostG l + tCostG l' := by
  simp [tCostG]

/-- The T-cost of a flat map is the sum of the T-costs of its pieces. -/
theorem tCostG_flatMap {α : Type} (L : List α) (F : α → List (Gate n)) :
    tCostG (L.flatMap F) = (L.map fun x => tCostG (F x)).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [List.flatMap_cons, tCostG_append, ih]

/-- The T-cost of the open blocks splits along a filter. -/
theorem tCostG_stGates_filter (p : OpenBlk n → Bool) (os : List (OpenBlk n)) :
    tCostG (stGates os) =
      tCostG (stGates (os.filter p)) + tCostG (stGates (os.filter fun b => !p b)) := by
  induction os with
  | nil => simp [stGates, tCostG]
  | cons x r ih =>
    by_cases hpx : p x = true <;>
      simp only [List.filter_cons, hpx, Bool.not_true, Bool.not_false, ite_true, ite_false,
        Bool.false_eq_true, stGates_cons, tCostG_append] at ih ⊢ <;> omega

/-- The block scan keeps the T-cost of the open blocks and the input. -/
theorem tCostG_collectAux (l : List (Gate n)) :
    ∀ os : List (OpenBlk n),
      tCostG ((collectAux os l).flatMap Block.gates) = tCostG (stGates os ++ l) := by
  induction l with
  | nil => intro os; simp [collectAux, flatMap_emit]
  | cons g gs ih =>
    intro os
    have hpart := tCostG_stGates_filter (OpenBlk.touches g) os
    simp only [collectAux]
    split
    · next b hj =>
      obtain ⟨hT, _⟩ := joinable_spec hj
      rw [ih]
      rw [hT] at hpart
      simp only [stGates_append, stGates_cons, stGates_nil, List.append_nil,
        List.reverse_cons, tCostG_append, tCostG_cons, tCostG_nil] at hpart ⊢
      omega
    · split
      · next a b' _ =>
        have ih' := ih (os.filter (fun c => !c.touches g) ++ [⟨a, b', [g]⟩])
        rw [List.flatMap_append, flatMap_emit]
        simp only [stGates_append, stGates_cons, stGates_nil, List.append_nil,
          List.reverse_cons, List.reverse_nil, List.nil_append, tCostG_append, tCostG_cons,
          tCostG_nil] at hpart ih' ⊢
        omega
      · have ih' := ih (os.filter (fun c => !c.touches g))
        rw [List.flatMap_append, List.flatMap_cons, flatMap_emit]
        simp only [Block.gates, tCostG_append, tCostG_cons, tCostG_nil] at hpart ih' ⊢
        omega

/-- The blocks of `collectBlocks l` have the T-cost of `l`. -/
theorem tCostG_collectBlocks (l : List (Gate n)) :
    tCostG ((collectBlocks l).flatMap Block.gates) = tCostG l := by
  rw [collectBlocks, tCostG_collectAux]
  simp [stGates]

/-- The T-cost of the open runs splits along a filter of the qubits. -/
theorem tCostG_stGatesOn_filter (F : Fin n → List (Gate n)) (p : Fin n → Bool)
    (L : List (Fin n)) :
    tCostG (stGatesOn F L) =
      tCostG (stGatesOn F (L.filter p)) + tCostG (stGatesOn F (L.filter fun q => !p q)) := by
  induction L with
  | nil => simp [stGatesOn, tCostG]
  | cons x r ih =>
    by_cases hpx : p x = true <;>
      simp only [stGatesOn, List.filter_cons, hpx, Bool.not_true, Bool.not_false, ite_true,
        ite_false, Bool.false_eq_true, List.flatMap_cons, tCostG_append] at ih ⊢ <;> omega

/-- The run scan keeps the T-cost of the open runs and the input. -/
theorem tCostG_runAux (l : List (Gate n)) :
    ∀ v : Vector (List (Gate n)) n,
      tCostG ((runAux v l).flatMap Seg.gates) =
        tCostG (stGatesOn (stFun v) (List.finRange n)) + tCostG l := by
  induction l with
  | nil => intro v; simp [runAux, flatMap_emitRuns, tCostG_nil]
  | cons g gs ih =>
    intro v
    simp only [runAux]
    split
    · next q hq =>
      rw [ih, stFun_set, show v[q] = stFun v q from rfl,
        tCostG_stGatesOn_filter _ (fun p => decide (p = q)),
        tCostG_stGatesOn_filter (stFun v) (fun p => decide (p = q)), filter_finRange_eq]
      have hB : stGatesOn (fun p => if p = q then g :: stFun v q else stFun v p)
          ((List.finRange n).filter fun p => !decide (p = q)) =
          stGatesOn (stFun v) ((List.finRange n).filter fun p => !decide (p = q)) := by
        simp only [stGatesOn]
        refine List.flatMap_congr fun p hp => ?_
        simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not] at hp
        simp [hp.2]
      rw [hB]
      simp only [stGatesOn, List.flatMap_cons, List.flatMap_nil, ite_true, List.reverse_cons,
        List.append_nil, tCostG_append, tCostG_cons, tCostG_nil]
      omega
    · rw [emitRunsL_qubitsAsc, List.flatMap_append, List.flatMap_cons, flatMap_emitRuns,
        tCostG_append, tCostG_append, ih,
        stFun_clearOn_qubitsAsc, stGatesOn_ite]
      have hp := tCostG_stGatesOn_filter (stFun v)
        (fun p => decide (p ∈ CommutationRules.targetQubits g)) (List.finRange n)
      simp only [Seg.gates, tCostG_cons, tCostG_nil]
      omega

/-- The segments of `collectRuns l` have the T-cost of `l`. -/
theorem tCostG_collectRuns (l : List (Gate n)) :
    tCostG ((collectRuns l).flatMap Seg.gates) = tCostG l := by
  rw [collectRuns, tCostG_runAux,
    show stGatesOn (stFun (Vector.replicate n [])) (List.finRange n) = [] by
      simp [stGatesOn, stFun, List.flatMap_eq_nil_iff]]
  simp [tCostG_nil]

/-- A block fitter under the T-cost guard: under `tSafe`, a proposal `(k, θ, b)` of `fit` on a
block `gs` on `(i, j)` is kept when the template `tmplGatesQ k i j θ` has at most the T-cost
of `gs`, and otherwise dropped, so that `blockEmit` keeps the block; without `tSafe` it is
`fit`. -/
def tGuardFit (tSafe : Bool) (fit : BlockFit n β) : BlockFit n β := fun i j gs =>
  if tSafe then
    (fit i j gs).filter fun x => decide (tCostG (tmplGatesQ x.1 i j x.2.1) ≤ tCostG gs)
  else fit i j gs

/-- A run fitter under the T-cost guard: under `tSafe`, a proposal `(a, θ, b)` of `fit` on a
run `gs` on `q` is kept when the template `runTemplate a q θ` has at most the T-cost of `gs`,
and otherwise dropped, so that `segEmit` keeps the run; without `tSafe` it is `fit`. -/
def tGuardZFit (tSafe : Bool) (fit : ZFit n β) : ZFit n β := fun i q gs =>
  if tSafe then
    (fit i q gs).filter fun x => decide (tCostG (runTemplate x.1 q x.2.1) ≤ tCostG gs)
  else fit i q gs

/-- A proposal of the guarded block fitter is one of `fit`, and under `tSafe` its template
does not raise the T-cost of the block. -/
theorem tGuardFit_eq_some {tSafe : Bool} {fit : BlockFit n β} {i j : Fin n}
    {gs : List (Gate n)} {x : Fin 4 × (Fin 15 → PiLin) × β}
    (h : tGuardFit tSafe fit i j gs = some x) :
    fit i j gs = some x ∧ (tSafe = true → tCostG (tmplGatesQ x.1 i j x.2.1) ≤ tCostG gs) := by
  unfold tGuardFit at h
  cases tSafe <;> simp_all [Option.filter_eq_some_iff]

/-- A proposal of the guarded run fitter is one of `fit`, and under `tSafe` its template does
not raise the T-cost of the run. -/
theorem tGuardZFit_eq_some {tSafe : Bool} {fit : ZFit n β} {i : ℕ} {q : Fin n}
    {gs : List (Gate n)} {x : Axis × (Fin 3 → PiLin) × β}
    (h : tGuardZFit tSafe fit i q gs = some x) :
    fit i q gs = some x ∧ (tSafe = true → tCostG (runTemplate x.1 q x.2.1) ≤ tCostG gs) := by
  unfold tGuardZFit at h
  cases tSafe <;> simp_all [Option.filter_eq_some_iff]

/-- The guard keeps the checked hypothesis of the KAK pass. -/
theorem kFitChecked_tGuardFit {fit : BlockFit n β} {ph : β → PiLin} {ep : β → ℚ}
    {l : List (Gate n)} (h : Synthesis.IntervalArith.KFitChecked fit ph ep l) (tSafe : Bool) :
    Synthesis.IntervalArith.KFitChecked (tGuardFit tSafe fit) ph ep l :=
  fun i j gs k θ b hb hf hk => h i j gs k θ b hb (tGuardFit_eq_some hf).1 hk

/-- The guard keeps the checked hypothesis of the run pass. -/
theorem zFitChecked_tGuardZFit {fit : ZFit n β} {ph : β → PiLin} {ep : β → ℚ}
    {l : List (Gate n)} (h : Synthesis.IntervalArith.ZFitChecked fit ph ep l) (tSafe : Bool) :
    Synthesis.IntervalArith.ZFitChecked (tGuardZFit tSafe fit) ph ep l :=
  fun i q gs a θ b hi hf => h i q gs a θ b hi (tGuardZFit_eq_some hf).1

/-- **The guarded KAK pass does not raise the T-cost.** -/
theorem tCostG_kakEmit_tGuardFit_le (fit : BlockFit n β) (l : List (Gate n)) :
    tCostG (kakEmit (tGuardFit true fit) l).1 ≤ tCostG l := by
  rw [← tCostG_collectBlocks l, kakEmit_fst, tCostG_flatMap, tCostG_flatMap]
  refine List.sum_le_sum fun b _ => ?_
  cases b with
  | gate g => exact le_rfl
  | pair i j gs =>
    rcases h : tGuardFit true fit i j gs with _ | ⟨k, θ, p⟩
    · simp [blockEmit, h, Block.gates]
    · have ht := (tGuardFit_eq_some h).2 rfl
      by_cases hk : k.val < cnotCount gs
      · simpa [blockEmit, h, hk, Block.gates] using ht
      · simp [blockEmit, h, hk, Block.gates]

/-- **The guarded run pass does not raise the T-cost.** -/
theorem tCostG_zyzEmit_tGuardZFit_le (fit : ZFit n β) (l : List (Gate n)) :
    tCostG (zyzEmit (tGuardZFit true fit) l).1 ≤ tCostG l := by
  have h0 : (collectRuns l).flatMap Seg.gates =
      (collectRuns l).zipIdx.flatMap fun si => Seg.gates si.1 := by
    rw [← List.flatMap_map (f := Prod.fst) (g := Seg.gates), List.zipIdx_map_fst]
  rw [← tCostG_collectRuns l, h0, zyzEmit_fst, tCostG_flatMap, tCostG_flatMap]
  refine List.sum_le_sum fun si _ => ?_
  obtain ⟨s, i⟩ := si
  cases s with
  | gate g => exact le_rfl
  | run q gs =>
    rcases h : tGuardZFit true fit i q gs with _ | ⟨a, θ, p⟩
    · simp [segEmit, h, Seg.gates]
    · simpa [segEmit, h, Seg.gates] using (tGuardZFit_eq_some h).2 rfl

end TGuard

/-- The resynthesis level at the checked fits under the T-cost guard `tSafe` (`tGuardFit`,
`tGuardZFit`): under `tSafe` a block or run is replaced by its template only when the template
does not raise its T-cost `tCostG`; without `tSafe` every checked fit is used. -/
def resynthT (tSafe : Bool) (c : Circuit n) : Resynth n :=
  resynthAt (tGuardFit tSafe qrunchFitChecked) (fun ax => tGuardZFit tSafe (qrunchZFitChecked ax))
    c

/-- **The resynthesis level.** Level 2, then the checked KAK pass, then the checked ZYZ
pass, without the T-cost guard. -/
def resynth (c : Circuit n) : Resynth n := resynthT false c

/-- **Approximate correctness of the guarded resynthesis level.** The matrix of the output of
`resynthT tSafe c` is within `eps` of the unitary of `c` in the `ℓ²` operator norm, up to the
global phase `e^{i·phase}`. -/
theorem norm_listMatrix_resynthT_sub_le (tSafe : Bool) (c : Circuit n) :
    ‖listMatrix (resynthT tSafe c).out -
        exp (I * ((resynthT tSafe c).phase : ℂ)) • (RoutingPerm.circuitUnitary c).val‖ ≤
      ((resynthT tSafe c).eps : ℝ) := by
  have hk := Synthesis.IntervalArith.listMatrix_kakEmit_approx
    (tGuardFit tSafe qrunchFitChecked) _ _ (level2Gates c)
    (kFitChecked_tGuardFit (Synthesis.IntervalArith.kFitChecked_checkedFit qrunchFit phaseQ
      checkBound (level2Gates c)) tSafe)
  have hz := Synthesis.IntervalArith.listMatrix_zyzEmit_approx
    (tGuardZFit tSafe (qrunchZFitChecked (runAxes (Synthesis.ZYZPass.collectRuns
        (kakEmit (tGuardFit tSafe qrunchFitChecked) (level2Gates c)).1).toArray))) _ _
    (kakEmit (tGuardFit tSafe qrunchFitChecked) (level2Gates c)).1
    (zFitChecked_tGuardZFit (Synthesis.IntervalArith.zFitChecked_checkedZFit
      (qrunchZFit (runAxes (Synthesis.ZYZPass.collectRuns
        (kakEmit (tGuardFit tSafe qrunchFitChecked) (level2Gates c)).1).toArray))
      phaseQ checkBound _) tSafe)
  rw [listMatrix_level2Gates] at hk
  have h := norm_sub_smul_trans_le (Complex.norm_exp_I_mul_ofReal _) hk hz
  have he : ∀ x y : ℝ,
      exp (I * (y : ℂ)) * exp (I * (x : ℂ)) = exp (I * ((x + y : ℝ) : ℂ)) := by
    intro x y; rw [← Complex.exp_add]; push_cast; ring_nf
  rw [he] at h
  simp only [resynthT, resynthAt, Resynth.ofKak, Resynth.phase, Resynth.eps, Resynth.payloads,
    List.map_append, List.sum_append, Rat.cast_add, Rat.cast_list_sum, List.map_map]
  exact h.trans_eq (by simp [Function.comp_def])

/-- **The CNOT bound of the guarded resynthesis level.** The output of `resynthT tSafe c` has
at most as many CNOTs as the gates of Level 2. -/
theorem cnotCount_resynthT_out_le (tSafe : Bool) (c : Circuit n) :
    cnotCount (resynthT tSafe c).out ≤ cnotCount (resynthT tSafe c).l2 := by
  simp only [resynthT, resynthAt, Resynth.ofKak, Synthesis.ZYZPass.cnotCount_zyzEmit]
  exact Synthesis.KAKPassSmall.cnotCount_kakEmit_le _ _

/-- **The T-cost bound of the guarded resynthesis level.** The output of `resynthT true c` has
at most the T-cost `tCostG` of the gates of Level 2: under the guard the KAK and ZYZ passes
replace a block or run only by a template of at most its T-cost. -/
theorem tCostG_resynthT_out_le (c : Circuit n) :
    tCostG (resynthT true c).out ≤ tCostG (resynthT true c).l2 := by
  simp only [resynthT, resynthAt, Resynth.ofKak]
  exact (tCostG_zyzEmit_tGuardZFit_le _ _).trans (tCostG_kakEmit_tGuardFit_le _ _)

/-- **Approximate correctness of the resynthesis level.** The matrix of the output of
`resynth c` is within `eps` of the unitary of `c` in the `ℓ²` operator norm, up to the global
phase `e^{i·phase}`. -/
theorem norm_listMatrix_resynth_sub_le (c : Circuit n) :
    ‖listMatrix (resynth c).out -
        exp (I * ((resynth c).phase : ℂ)) • (RoutingPerm.circuitUnitary c).val‖ ≤
      ((resynth c).eps : ℝ) :=
  norm_listMatrix_resynthT_sub_le false c

/-- **The CNOT bound of the resynthesis level.** The output of `resynth c` has at most as many
CNOTs as the gates of Level 2: the KAK pass does not add any (`cnotCount_kakEmit_le`) and the
ZYZ pass keeps their number (`cnotCount_zyzEmit`). -/
theorem cnotCount_resynth_out_le (c : Circuit n) :
    cnotCount (resynth c).out ≤ cnotCount (resynth c).l2 :=
  cnotCount_resynthT_out_le false c

end CatCrypt.Quantum.Optimization.ResynthLevel
