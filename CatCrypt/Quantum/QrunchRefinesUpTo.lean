/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QrunchRound
public import CatCryptCore.Refinement.RRelWRPQuantumUpTo

/-!
# The Qrunch run as a channel refinement up to an error

The compile theorem `QrunchRound.norm_compileQGates_sub_le` bounds the `ℓ²` operator-norm
distance between the qelib1 matrix of the input of the whole run `compileQGates` and
`wireMatrix π * e^{-iΦ} • M_out`. This module reads that bound as a refinement of unitary
channels up to an error (`ChannelWRP.ChannelRefinesUpTo`): the unitary channel of the input and
the unitary channel of `wireMatrix π * M_out` refine each other up to `2 (ε_snap + Σ ε_round)`.
The global phase `e^{-iΦ}` does not appear in the statement, since a scalar of modulus one does
not change a unitary channel (`ChannelWRP.unitaryChannel_refinesUpTo_of_norm_sub_smul_le`).
The exact counterpart for circuit passes, refinement in both directions with no error, is
`Optimization.PassRefinesWP.PassRefines`.

## Main results

* `qelibListMatrix_mem_unitaryGroup` — a list of statements with distinct operands has a
  unitary qelib1 matrix.
* `qelibListMatrix_mem_unitaryGroup_of_rounds_ne_nil` — the input of a run whose rounds are
  nonempty has a unitary qelib1 matrix.
* `wireMatrix_mul_out_mem_unitaryGroup` — the output matrix `wireMatrix π * M_out` of such a run
  is unitary.
* `unitaryChannel_compileQGates_refinesUpTo` — the input and output channels of the run refine
  each other up to `2 (ε_snap + Σ ε_round)`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QFT (listMatrix)
open CatCrypt.Quantum.OpenQASMImport (QGate lowerQ)
open CatCrypt.Quantum.Qelib (qelibMatrix qelibListMatrix Distinct)
open CatCrypt.Quantum.Optimization.ResynthLevel
open CatCrypt.Quantum.Synthesis.IntervalArith (listMatrix_mem_unitaryGroup)
open CatCrypt.Quantum.QrunchRound
open CatCrypt.Quantum.UnitaryChannel (unitaryChannel)
open CatCrypt.Refinement.ChannelWRP (ChannelRefinesUpTo)
open scoped Matrix.Norms.L2Operator

namespace CatCrypt.Quantum.QrunchRefinesUpTo

variable {n : ℕ}

/-- A phase multiple `e^{ix} • A` of a unitary matrix is unitary. -/
theorem exp_smul_mem_unitaryGroup {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (x : ℝ) (hA : A ∈ Matrix.unitaryGroup m ℂ) :
    Complex.exp (Complex.I * x) • A ∈ Matrix.unitaryGroup m ℂ := by
  refine Unitary.smul_mem_of_mem ?_ hA
  rw [Unitary.mem_iff_star_mul_self]
  simp [← Complex.exp_conj, ← Complex.exp_add]

/-- A matrix whose phase multiple `e^{ix} • A` is unitary is unitary. -/
theorem mem_unitaryGroup_of_exp_smul {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (x : ℝ) (hA : Complex.exp (Complex.I * x) • A ∈ Matrix.unitaryGroup m ℂ) :
    A ∈ Matrix.unitaryGroup m ℂ := by
  have h := exp_smul_mem_unitaryGroup (-x) hA
  rwa [smul_smul, ← Complex.exp_add, Complex.ofReal_neg, mul_neg, neg_add_cancel,
    Complex.exp_zero, one_smul] at h

/-- A statement with distinct operands has a unitary qelib1 matrix. -/
theorem qelibMatrix_mem_unitaryGroup (g : QGate n) (hg : Distinct g) :
    qelibMatrix g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hU := listMatrix_mem_unitaryGroup (lowerQ g)
  rw [Qelib.listMatrix_lowerQ g hg] at hU
  exact mem_unitaryGroup_of_exp_smul _ hU

/-- A list of statements with distinct operands has a unitary qelib1 matrix. -/
theorem qelibListMatrix_mem_unitaryGroup (l : List (QGate n)) (hl : ∀ g ∈ l, Distinct g) :
    qelibListMatrix l ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  induction l with
  | nil => exact Submonoid.one_mem _
  | cons g l ih =>
    exact Submonoid.mul_mem _ (ih fun x hx => hl x (List.mem_cons_of_mem g hx))
      (qelibMatrix_mem_unitaryGroup g (hl g List.mem_cons_self))

/-- Relabelling the qubits of a statement keeps its operands distinct. -/
theorem distinct_relabelQ (σ : Equiv.Perm (Fin n)) (g : QGate n) :
    Distinct (SwapElide.relabelQ σ g) ↔ Distinct g := by
  cases g <;> simp [SwapElide.relabelQ, Distinct]

/-- When the statements of the swap elision have distinct operands, so have its input
statements. -/
theorem distinct_of_elideFrom (σ : Equiv.Perm (Fin n)) (l : List (QGate n))
    (h : ∀ g ∈ (SwapElide.elideFrom σ l).1, Distinct g) : ∀ g ∈ l, Distinct g := by
  induction l generalizing σ with
  | nil => simp
  | cons g l ih =>
    intro x hx
    cases g with
    | swap a b =>
      rcases List.mem_cons.1 hx with rfl | hx
      · trivial
      · exact ih _ (by simpa [SwapElide.elideFrom] using h) x hx
    | _ =>
      simp only [SwapElide.elideFrom, List.mem_cons, forall_eq_or_imp] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact (distinct_relabelQ σ _).1 h.1
      · exact ih σ h.2 x hx

/-- When the prepared statements have distinct operands, so have the input statements. -/
theorem distinct_of_prepQ (elide snap : Bool) (qs : List (QGate n))
    (h : ∀ g ∈ (prepQ elide snap qs).1, Distinct g) : ∀ g ∈ qs, Distinct g := by
  have he : ∀ g ∈ (if elide then SwapElide.elideQ qs else (qs, 1)).1, Distinct g := by
    intro g hg
    cases snap with
    | false => exact h g (by simpa [prepQ] using hg)
    | true =>
      refine (AngleSnap.distinct_snapGate g).1 (h _ ?_)
      simp only [prepQ, ite_true, AngleSnap.snapQ_fst]
      exact List.mem_map_of_mem hg
  cases elide with
  | false => simpa using he
  | true => exact distinct_of_elideFrom 1 qs he

/-- The output statements of a round have a unitary qelib1 matrix. -/
theorem qelibListMatrix_out_mem_unitaryGroup_of_round {stage : Circuit n → Resynth n}
    {qs : List (QGate n)} {o : RoundOut n} (h : QrunchRound.round stage qs = some o) :
    qelibListMatrix o.out ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  unfold QrunchRound.round at h
  dsimp only at h
  split_ifs at h with h1 h2
  obtain rfl := (Option.some.inj h).symm
  rw [qelibListMatrix_basisPasses _ (fun g hg => noRz_of_isRealRz (by
    simpa using List.all_eq_true.1 h2 g hg))]
  exact exp_smul_mem_unitaryGroup _ (listMatrix_mem_unitaryGroup _)

/-- Every round of `iterFrom` has output statements with a unitary qelib1 matrix. -/
theorem out_mem_unitaryGroup_of_mem_iterFrom {stage : Circuit n → Resynth n} (k : ℕ)
    (l : List (QGate n)) (cost : Cost) :
    ∀ o ∈ iterFrom stage k l cost, qelibListMatrix o.out ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  induction k generalizing l with
  | zero => simp [iterFrom]
  | succ k ih =>
    intro o ho
    unfold iterFrom at ho
    split at ho
    · rename_i o' ho'
      split_ifs at ho
      · rcases List.mem_cons.1 ho with rfl | ho
        · exact qelibListMatrix_out_mem_unitaryGroup_of_round ho'
        · exact ih _ o ho
      · simp at ho
    · simp at ho

/-- Every round of `runRounds` has output statements with a unitary qelib1 matrix. -/
theorem out_mem_unitaryGroup_of_mem_runRounds {stage : Circuit n → Resynth n} (k : ℕ)
    (qs : List (QGate n)) (cost : Cost) :
    ∀ o ∈ runRounds stage k qs cost,
      qelibListMatrix o.out ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  intro o ho
  have hd := distinct_of_runRounds_ne_nil (List.ne_nil_of_mem ho)
  unfold runRounds at ho
  split at ho
  · rename_i o' ho'
    split_ifs at ho
    · rcases List.mem_cons.1 ho with rfl | ho
      · exact qelibListMatrix_mem_unitaryGroup qs hd
      · simp at ho
    · rcases List.mem_cons.1 ho with rfl | ho
      · exact qelibListMatrix_out_mem_unitaryGroup_of_round ho'
      · exact out_mem_unitaryGroup_of_mem_iterFrom _ _ _ o ho
  · simp at ho

/-- The statements after a list of rounds are the start or the output of one of the rounds. -/
theorem finalOut_eq_or_mem (l : List (QGate n)) (rs : List (RoundOut n)) :
    finalOut l rs = l ∨ ∃ o ∈ rs, finalOut l rs = o.out := by
  induction rs generalizing l with
  | nil => exact Or.inl rfl
  | cons o rs ih =>
    rcases ih o.out with h | ⟨o', ho', h⟩
    · exact Or.inr ⟨o, List.mem_cons_self, h⟩
    · exact Or.inr ⟨o', List.mem_cons_of_mem o ho', h⟩

/-- The input of a run whose rounds are nonempty has a unitary qelib1 matrix. -/
theorem qelibListMatrix_mem_unitaryGroup_of_rounds_ne_nil {stage : Circuit n → Resynth n}
    {k : ℕ} {elide snap : Bool} {qs : List (QGate n)} {cost : Cost}
    (h : (compileQGates stage k elide snap qs cost).rounds ≠ []) :
    qelibListMatrix qs ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  qelibListMatrix_mem_unitaryGroup qs
    (distinct_of_prepQ elide snap qs (distinct_of_runRounds_ne_nil h))

/-- The output matrix `wireMatrix π * M_out` of a run whose rounds are nonempty is unitary. -/
theorem wireMatrix_mul_out_mem_unitaryGroup {stage : Circuit n → Resynth n}
    {k : ℕ} {elide snap : Bool} {qs : List (QGate n)} {cost : Cost}
    (h : (compileQGates stage k elide snap qs cost).rounds ≠ []) :
    SwapElide.wireMatrix (compileQGates stage k elide snap qs cost).perm *
        qelibListMatrix (compileQGates stage k elide snap qs cost).out ∈
      Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  refine Submonoid.mul_mem _ (Optimization.RoutingPerm.qubitPermUnitary _).prop ?_
  have hd := distinct_of_runRounds_ne_nil h
  simp only [compileQGates] at h hd ⊢
  rcases finalOut_eq_or_mem (prepQ elide snap qs).1
      (runRounds stage k (prepQ elide snap qs).1 cost) with he | ⟨o, ho, he⟩
  · rw [he]; exact qelibListMatrix_mem_unitaryGroup _ hd
  · rw [he]; exact out_mem_unitaryGroup_of_mem_runRounds _ _ _ o ho

/-- **The compile run as a channel refinement up to an error.** For a stage meeting its bound
and a run whose rounds are nonempty, the unitary channel of the input statements and the unitary
channel of `wireMatrix π * M_out` refine each other up to `2 (ε_snap + Σ ε_round)`. -/
theorem unitaryChannel_compileQGates_refinesUpTo {stage : Circuit n → Resynth n}
    (hS : StageBound stage) (k : ℕ) (elide snap : Bool) (qs : List (QGate n)) (cost : Cost)
    (h : (compileQGates stage k elide snap qs cost).rounds ≠ []) :
    ChannelRefinesUpTo
        (ENNReal.ofReal (2 * (((compileQGates stage k elide snap qs cost).snapEps +
          sumEps (compileQGates stage k elide snap qs cost).rounds : ℚ) : ℝ)))
        (unitaryChannel ⟨_, wireMatrix_mul_out_mem_unitaryGroup h⟩)
        (unitaryChannel ⟨_, qelibListMatrix_mem_unitaryGroup_of_rounds_ne_nil h⟩) ∧
      ChannelRefinesUpTo
        (ENNReal.ofReal (2 * (((compileQGates stage k elide snap qs cost).snapEps +
          sumEps (compileQGates stage k elide snap qs cost).rounds : ℚ) : ℝ)))
        (unitaryChannel ⟨_, qelibListMatrix_mem_unitaryGroup_of_rounds_ne_nil h⟩)
        (unitaryChannel ⟨_, wireMatrix_mul_out_mem_unitaryGroup h⟩) := by
  have hb := norm_compileQGates_sub_le hS k elide snap qs cost h
  rw [Matrix.mul_smul] at hb
  refine CatCrypt.Refinement.ChannelWRP.unitaryChannel_refinesUpTo_of_norm_sub_smul_le ?_ hb
  rw [Complex.norm_exp]
  simp

end CatCrypt.Quantum.QrunchRefinesUpTo
