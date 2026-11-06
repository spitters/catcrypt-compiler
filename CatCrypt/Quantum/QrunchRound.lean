/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.ResynthLevel
public import CatCrypt.Quantum.QrunchBasis
public import CatCrypt.Quantum.QrunchFuse
public import CatCrypt.Quantum.QrunchCommute

/-!
# One round of the Qrunch pipeline and its iteration to a fixed point

A round `round stage qs` maps a list of qelib1 statements to a list of qelib1 statements: it
lowers the statements (`OpenQASMImport.lowerQ`), runs a stage `stage : Circuit n → Resynth n`
(Level 1, Level 2 or the resynthesis level of `ResynthLevel`), translates the gates of the
stage to the basis `{rx, ry, cx, p}` (`QrunchBasis.toQelib`) and runs `fuseQ`, the backward
commutation pass `commuteQ`, the Pauli frame pass `pauliQ` and `fuseQ` again. It refuses
(`none`) an input with a statement whose operands are not distinct (`Qelib.Distinct`) and a
stage output with a real-angle `Rz`, which has no exact statement.

The round records an exact phase `RoundOut.phase` (a `PiLin`) and a bound `RoundOut.eps`.
**The round theorem** `norm_round_sub_le`: when the stage satisfies its bound (`StageBound`,
proved for `resynth` by `norm_listMatrix_resynth_sub_le`), the qelib1 matrix of the output is
within the bound of `e^{iφ}` times the qelib1 matrix of the input, in the `ℓ²` operator norm.

The iteration `runRounds stage k qs` runs one round, then further rounds while a round lowers
the CX count of its input, or keeps it and lowers the statement count (`Better`), at most `k`
rounds in all: it stops at a fixed point of the round up to this order or at the fuel.
**The iteration theorem** `norm_runRounds_sub_le`: the bound of the iteration is the sum of
the bounds of its rounds and its phase the sum of their phases, since every phase factor has
norm one and errors of approximations add (`ResynthLevel.norm_sub_smul_trans_le`). The CX
count never rises after the first round (`cxCount_runRounds_le`).

## Main definitions

* `round` — one round of the pipeline, with its phase and bound (`RoundOut`).
* `runRounds` — the iteration of the round to a fixed point, at most `k` rounds.
* `finalOut` — the statements after a list of rounds.

## Main results

* `norm_round_sub_le` — the round theorem.
* `norm_runRounds_sub_le` — the iteration theorem.
* `cxCount_runRounds_le` — the CX count of the iteration is at most that of its first round.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QFT (listMatrix)
open CatCrypt.Quantum.OpenQASMImport (QGate lowerQ)
open CatCrypt.Quantum.Qelib (qelibListMatrix listPhase Distinct)
open CatCrypt.Quantum.QrunchFuse (fuseQ pauliQ cxCount)
open CatCrypt.Quantum.QrunchCommute (commuteQ)
open CatCrypt.Quantum.QrunchBasis (toQelib NoRz)
open CatCrypt.Quantum.Optimization.ResynthLevel
open scoped Matrix.Norms.L2Operator

namespace CatCrypt.Quantum.QrunchRound

variable {n : ℕ}

/-- Whether a gate is the real-angle `Gate.Rz`, which has no exact OpenQASM statement. -/
def isRealRz : Gate n → Bool
  | .Rz _ _ => true
  | _ => false

/-- A gate other than the real-angle `Rz` satisfies `NoRz`. -/
theorem noRz_of_isRealRz {g : Gate n} (h : isRealRz g = false) : NoRz g := by
  cases g <;> simp_all [isRealRz, NoRz]

/-- The exact phase of a stage value: the sum of the exact phases of its payloads. -/
def stagePhase (r : Resynth n) : PiLin := (r.payloads.map fun b => b.2.1).sum

/-- The exact phase of a stage value denotes its real phase `Resynth.phase`. -/
theorem toReal_stagePhase (r : Resynth n) : (stagePhase r).toReal = r.phase := by
  unfold stagePhase Resynth.phase
  induction r.payloads with
  | nil => simp
  | cons b l ih => simp [ih]

/-- A stage satisfies its bound: the matrix of its output is within `eps` of the unitary of
its input, up to the phase `e^{i·phase}`, in the `ℓ²` operator norm. -/
def StageBound (stage : Circuit n → Resynth n) : Prop :=
  ∀ c, ‖listMatrix (stage c).out -
      Complex.exp (Complex.I * ((stage c).phase : ℂ)) •
        (Optimization.RoutingPerm.circuitUnitary c).val‖ ≤
    ((stage c).eps : ℝ)

/-- The resynthesis level satisfies its bound (`norm_listMatrix_resynth_sub_le`). -/
theorem stageBound_resynth : StageBound (resynth (n := n)) :=
  norm_listMatrix_resynth_sub_le

/-- The value of one round: the stage value, the output statements, the exact phase and the
bound. -/
structure RoundOut (n : ℕ) where
  /-- The value of the stage on the lowered input. -/
  stage : Resynth n
  /-- The output statements, over `{rx, ry, cx, p}`. -/
  out : List (QGate n)
  /-- The exact phase of the round. -/
  phase : PiLin
  /-- The bound of the round. -/
  eps : ℚ

/-- The output statements and phase of the basis passes on the gates `l`: `toQelib`, `fuseQ`,
`commuteQ`, `pauliQ`, `fuseQ`. -/
def basisPasses (l : List (Gate n)) : List (QGate n) × PiLin :=
  let t := toQelib l
  let p := pauliQ (commuteQ (fuseQ t.1))
  (fuseQ p.1, t.2 + p.2)

/-- **One round** of the pipeline on the statements `qs`, with the stage `stage`; `none` when
a statement has operands that are not distinct or the stage outputs a real-angle `Rz`. -/
def round (stage : Circuit n → Resynth n) (qs : List (QGate n)) : Option (RoundOut n) :=
  if qs.all (fun g => decide (Distinct g)) then
    let r := stage (Circuit.ofList (qs.flatMap lowerQ))
    if r.out.all (fun g => !isRealRz g) then
      let b := basisPasses r.out
      some ⟨r, b.1, listPhase qs + stagePhase r + b.2, r.eps⟩
    else none
  else none

/-- The basis passes realise the gates up to their phase, for gates without the real-angle
`Rz`. -/
theorem qelibListMatrix_basisPasses (l : List (Gate n)) (hl : ∀ g ∈ l, NoRz g) :
    qelibListMatrix (basisPasses l).1 =
      Complex.exp (Complex.I * (basisPasses l).2.toReal) • listMatrix l := by
  simp only [basisPasses]
  rw [QrunchFuse.qelibListMatrix_fuseQ, QrunchFuse.qelibListMatrix_pauliQ,
    QrunchCommute.qelibListMatrix_commuteQ, QrunchFuse.qelibListMatrix_fuseQ,
    QrunchBasis.qelibListMatrix_toQelib l hl, smul_smul, ← Complex.exp_add, PiLin.toReal_add]
  congr 2
  push_cast
  ring

/-- A phase factor of norm one leaves the distance unchanged. -/
theorem norm_smul_sub_smul_of_norm_eq_one {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m m ℂ} {c : ℂ} (hc : ‖c‖ = 1) : ‖c • A - c • B‖ = ‖A - B‖ := by
  rw [← smul_sub, norm_smul, hc, one_mul]

/-- **The round theorem.** The qelib1 matrix of the output of a round is within the round's
bound of `e^{iφ}` times the qelib1 matrix of its input, `φ` the round's exact phase. -/
theorem norm_round_sub_le {stage : Circuit n → Resynth n} (hS : StageBound stage)
    {qs : List (QGate n)} {o : RoundOut n} (h : round stage qs = some o) :
    ‖qelibListMatrix o.out - Complex.exp (Complex.I * o.phase.toReal) • qelibListMatrix qs‖ ≤
      (o.eps : ℝ) := by
  unfold round at h
  dsimp only at h
  split_ifs at h with h1 h2
  obtain rfl := Option.some.inj h
  simp only [List.all_eq_true, decide_eq_true_eq] at h1
  simp only [List.all_eq_true, Bool.not_eq_true'] at h2
  have hN : ∀ g ∈ (stage (Circuit.ofList (qs.flatMap lowerQ))).out, NoRz g :=
    fun g hg => noRz_of_isRealRz (by simpa using h2 g hg)
  have hb := qelibListMatrix_basisPasses _ hN
  have hs := hS (Circuit.ofList (qs.flatMap lowerQ))
  change ‖listMatrix _ - _ • listMatrix (qs.flatMap lowerQ)‖ ≤ _ at hs
  rw [Qelib.listMatrix_flatMap_lowerQ qs h1, smul_smul, ← Complex.exp_add] at hs
  clear h
  simp only
  rw [hb]
  set r := stage (Circuit.ofList (qs.flatMap lowerQ))
  set β := (basisPasses r.out).2
  have he : Complex.exp (Complex.I * ((listPhase qs + stagePhase r + β).toReal : ℂ)) =
      Complex.exp (Complex.I * (β.toReal : ℂ)) *
        Complex.exp (Complex.I * (r.phase : ℂ) + Complex.I * ((listPhase qs).toReal : ℂ)) := by
    rw [← Complex.exp_add, PiLin.toReal_add, PiLin.toReal_add, toReal_stagePhase]
    push_cast
    ring_nf
  rw [he, ← smul_smul, ← smul_sub, norm_smul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact hs

/-- The order of the iteration: `l'` has fewer CX statements than `l`, or as many and fewer
statements. -/
def Better (l' l : List (QGate n)) : Bool :=
  decide (cxCount l' < cxCount l) ||
    (decide (cxCount l' = cxCount l) && decide (l'.length < l.length))

/-- A `Better` list has at most as many CX statements. -/
theorem cxCount_le_of_better {l' l : List (QGate n)} (h : Better l' l = true) :
    cxCount l' ≤ cxCount l := by
  simp only [Better, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- `Better` is transitive. -/
theorem better_trans {l₁ l₂ l₃ : List (QGate n)} (h₁ : Better l₁ l₂ = true)
    (h₂ : Better l₂ l₃ = true) : Better l₁ l₃ = true := by
  simp only [Better, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
  omega

/-- The rounds after the first: at most `k` more rounds from `l`, each kept only when its
output is `Better` than its input. -/
def iterFrom (stage : Circuit n → Resynth n) : ℕ → List (QGate n) → List (RoundOut n)
  | 0, _ => []
  | k + 1, l =>
    match round stage l with
    | some o => if Better o.out l then o :: iterFrom stage k o.out else []
    | none => []

/-- The statements after a list of rounds from `l`: the output of the last round, or `l`. -/
def finalOut : List (QGate n) → List (RoundOut n) → List (QGate n)
  | l, [] => l
  | _, o :: rs => finalOut o.out rs

/-- **The iteration to a fixed point**: one round, then at most `k - 1` further rounds while
the output improves (`iterFrom`); empty when the first round refuses its input. -/
def runRounds (stage : Circuit n → Resynth n) (k : ℕ) (qs : List (QGate n)) :
    List (RoundOut n) :=
  match round stage qs with
  | some o => o :: iterFrom stage (k - 1) o.out
  | none => []

/-- The sum of the phases of a list of rounds. -/
def sumPhase (rs : List (RoundOut n)) : PiLin := (rs.map (·.phase)).sum

/-- The sum of the bounds of a list of rounds. -/
def sumEps (rs : List (RoundOut n)) : ℚ := (rs.map (·.eps)).sum

/-- A round from `l` followed by rounds from its output: the bounds add and the phases add. -/
theorem norm_finalOut_cons_sub_le {l : List (QGate n)} {o : RoundOut n}
    {rs : List (RoundOut n)}
    (h₁ : ‖qelibListMatrix o.out -
        Complex.exp (Complex.I * o.phase.toReal) • qelibListMatrix l‖ ≤ (o.eps : ℝ))
    (h₂ : ‖qelibListMatrix (finalOut o.out rs) -
        Complex.exp (Complex.I * (sumPhase rs).toReal) • qelibListMatrix o.out‖ ≤
      (sumEps rs : ℝ)) :
    ‖qelibListMatrix (finalOut l (o :: rs)) -
        Complex.exp (Complex.I * (sumPhase (o :: rs)).toReal) • qelibListMatrix l‖ ≤
      (sumEps (o :: rs) : ℝ) := by
  have h := norm_sub_smul_trans_le (Complex.norm_exp_I_mul_ofReal _) h₁ h₂
  have he : Complex.exp (Complex.I * ((sumPhase rs).toReal : ℂ)) *
      Complex.exp (Complex.I * (o.phase.toReal : ℂ)) =
      Complex.exp (Complex.I * ((sumPhase (o :: rs)).toReal : ℂ)) := by
    rw [← Complex.exp_add]
    simp only [sumPhase, List.map_cons, List.sum_cons, PiLin.toReal_add]
    push_cast
    ring_nf
  rw [he] at h
  simpa [finalOut, sumEps, List.map_cons, List.sum_cons, Rat.cast_add] using h

/-- The iteration theorem for the rounds after the first. -/
theorem norm_iterFrom_sub_le {stage : Circuit n → Resynth n} (hS : StageBound stage)
    (k : ℕ) (l : List (QGate n)) :
    ‖qelibListMatrix (finalOut l (iterFrom stage k l)) -
        Complex.exp (Complex.I * (sumPhase (iterFrom stage k l)).toReal) • qelibListMatrix l‖ ≤
      (sumEps (iterFrom stage k l) : ℝ) := by
  induction k generalizing l with
  | zero => simp [iterFrom, finalOut, sumPhase, sumEps]
  | succ k ih =>
    unfold iterFrom
    split
    · rename_i o ho
      split
      · exact norm_finalOut_cons_sub_le (norm_round_sub_le hS ho) (ih o.out)
      · simp [finalOut, sumPhase, sumEps]
    · simp [finalOut, sumPhase, sumEps]

/-- **The iteration theorem.** After the rounds of `runRounds`, the qelib1 matrix of the output
is within the sum of the bounds of the rounds of `e^{iΦ}` times the qelib1 matrix of the input,
`Φ` the sum of their exact phases. -/
theorem norm_runRounds_sub_le {stage : Circuit n → Resynth n} (hS : StageBound stage)
    (k : ℕ) (qs : List (QGate n)) :
    ‖qelibListMatrix (finalOut qs (runRounds stage k qs)) -
        Complex.exp (Complex.I * (sumPhase (runRounds stage k qs)).toReal) • qelibListMatrix qs‖ ≤
      (sumEps (runRounds stage k qs) : ℝ) := by
  unfold runRounds
  split
  · rename_i o ho
    exact norm_finalOut_cons_sub_le (norm_round_sub_le hS ho) (norm_iterFrom_sub_le hS _ o.out)
  · simp [finalOut, sumPhase, sumEps]

/-- The CX count never rises in the rounds after the first. -/
theorem cxCount_iterFrom_le (stage : Circuit n → Resynth n) (k : ℕ) (l : List (QGate n)) :
    cxCount (finalOut l (iterFrom stage k l)) ≤ cxCount l := by
  induction k generalizing l with
  | zero => simp [iterFrom, finalOut]
  | succ k ih =>
    unfold iterFrom
    split
    · split
      · rename_i o _ hb
        exact (ih o.out).trans (cxCount_le_of_better hb)
      · simp [finalOut]
    · simp [finalOut]

/-- **The CX count never rises** after the first round: the output of the iteration has at most
as many CX statements as the output of its first round. -/
theorem cxCount_runRounds_le (stage : Circuit n → Resynth n) (k : ℕ) (qs : List (QGate n))
    {o : RoundOut n} (h : round stage qs = some o) :
    cxCount (finalOut qs (runRounds stage k qs)) ≤ cxCount o.out := by
  simp only [runRounds, h, finalOut]
  exact cxCount_iterFrom_le stage (k - 1) o.out

/-- The output of the rounds after the first is their input or `Better` than it, and it is the
output of each kept round or `Better` than it. -/
theorem better_iterFrom (stage : Circuit n → Resynth n) (k : ℕ) (l : List (QGate n)) :
    (finalOut l (iterFrom stage k l) = l ∨ Better (finalOut l (iterFrom stage k l)) l = true) ∧
    ∀ o' ∈ iterFrom stage k l, finalOut l (iterFrom stage k l) = o'.out ∨
      Better (finalOut l (iterFrom stage k l)) o'.out = true := by
  induction k generalizing l with
  | zero => simp [iterFrom, finalOut]
  | succ k ih =>
    unfold iterFrom
    split
    · split
      · rename_i o _ hb
        obtain ⟨h₁, h₂⟩ := ih o.out
        simp only [finalOut, List.mem_cons, forall_eq_or_imp]
        refine ⟨?_, h₁, h₂⟩
        rcases h₁ with h | h
        · rw [h]; exact Or.inr hb
        · exact Or.inr (better_trans h hb)
      · simp [finalOut]
    · simp [finalOut]

/-- **The best iterate.** The output of the iteration is the output of each of its rounds or
`Better` than it: every kept round is `Better` than its input, and the iteration stops at the
first round whose output is not `Better` than its input, so the returned statements have the
lowest CX count, and then the lowest statement count, of all the iterates it computed. -/
theorem better_runRounds (stage : Circuit n → Resynth n) (k : ℕ) (qs : List (QGate n)) :
    ∀ o' ∈ runRounds stage k qs, finalOut qs (runRounds stage k qs) = o'.out ∨
      Better (finalOut qs (runRounds stage k qs)) o'.out = true := by
  unfold runRounds
  split
  · rename_i o _
    obtain ⟨h₁, h₂⟩ := better_iterFrom stage (k - 1) o.out
    simp only [finalOut, List.mem_cons, forall_eq_or_imp]
    exact ⟨h₁, h₂⟩
  · simp

end CatCrypt.Quantum.QrunchRound
