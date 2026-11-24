/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaWP
public import RefinementWP.Tactic

/-!
# Laws of the fuel run `Isa.runM` of an instruction set

One fetched step of a program `P` under an instruction set is the program `Isa.stepM` of
`StateT LstateMF Option`, which returns whether the state is halted. The fuel run
`Isa.runM` at successor fuel is this step followed by the run at the remaining fuel, and at
fuel zero the step followed by a failure when the state is not halted. With the specification
of the step, `wrp_vcgen` reduces a refinement of a run at a numeral fuel to verification
conditions on the fetched instructions and their steps.

## Main definitions

* `VIR.LprogIsa.Isa.stepM`: one fetched step as a program of `StateT LstateMF Option`.

## Main results

* `Isa.runM_zero`, `Isa.runM_succ`: the unfolding of the fuel run.
* `Isa.stepM_spec`: the `Std.WP` specification of one step.
* `Isa.wp_runM_bot_mono`, `Isa.runM_fuel_mono`: the weakest precondition and the triples of
  halting runs are monotone in the fuel, by `Isa.lsemFuelMemF_add`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa

open Std.WP Lean.Order
open JasminLsemMemLoop (LprogM findInstrMem)
open JasminLsemMemFlagGuard (LstateMF)

variable (I : Isa) (P : LprogM)

/-- One fetched step of `P` under `I` as a program of `StateT LstateMF Option`: it returns
    `true` in the same state when no instruction is fetched, returns `false` in the successor
    state after a step, and fails when the step fails. -/
def stepM : StateT LstateMF Option Bool := fun s =>
  match findInstrMem P s.prog with
  | none => some (true, s)
  | some i => (I.step P i s).map (false, ·)

/-- The run at fuel zero returns when the state is halted and fails otherwise. -/
theorem runM_zero :
    I.runM P 0 = I.stepM P >>= fun h => if h then pure () else throw () := by
  funext s
  simp only [runM, stepM, lsemFuelMemF, bind, StateT.bind]
  cases findInstrMem P s.prog with
  | none => rfl
  | some i => dsimp only; cases I.step P i s <;> rfl

/-- The run at successor fuel is one step, followed by the run at the remaining fuel when
    the state was not halted. -/
theorem runM_succ (n : Nat) :
    I.runM P (n + 1) = I.stepM P >>= fun h => if h then pure () else I.runM P n := by
  funext s
  simp only [runM, stepM, lsemFuelMemF, bind, StateT.bind]
  cases findInstrMem P s.prog with
  | none => rfl
  | some i => dsimp only; cases I.step P i s <;> rfl

/-- The specification of one step: at a halted state the postcondition at `true`, after a
    step the postcondition at `false` of the successor, and at a failed step the exception
    postcondition. The three cases are a conjunction of implications, which `vcgen`
    decomposes to continue with the program after the step. -/
@[spec]
theorem stepM_spec (Q : Bool → LstateMF → Prop) (E : Unit → Prop) :
    Triple (I.stepM P)
      (fun s => (findInstrMem P s.prog = none → Q true s) ∧
        ∀ i, findInstrMem P s.prog = some i →
          (∀ s', I.step P i s = some s' → Q false s') ∧ (I.step P i s = none → E ()))
      Q E := by
  refine Triple.intro fun s h => ?_
  simp only [StateT.wp_apply_eq, StateT.run, stepM]
  cases hf : findInstrMem P s.prog with
  | none => exact h.1 hf
  | some i =>
    dsimp only
    cases hs : I.step P i s with
    | none => exact (h.2 i hf).2 hs
    | some s' => exact (h.2 i hf).1 s' hs

/-- The weakest precondition of the run at the exception postcondition `⊥` is monotone in
    the fuel. -/
theorem wp_runM_bot_mono {n m : Nat} (hle : n ≤ m) (Q : Unit → LstateMF → Prop) :
    wp (I.runM P n) Q bot ⊑ wp (I.runM P m) Q bot := by
  intro s h
  rw [Ascent.wp_runM_bot_iff] at h ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  grind [lsemFuelMemF_add]

/-- A triple of the run at the exception postcondition `⊥` holds at every larger fuel. -/
theorem runM_fuel_mono {n m : Nat} (hle : n ≤ m) {R : LstateMF → Prop}
    {Q : Unit → LstateMF → Prop} (h : Triple (I.runM P n) R Q bot) :
    Triple (I.runM P m) R Q bot :=
  Triple.intro (PartialOrder.rel_trans h.le_wp (I.wp_runM_bot_mono P hle Q))

open JasminLprogExport in
/-- A conditional jump to the label after it, run at fuel two under any instruction set,
    refines the update of the program counter from zero to two. -/
example (c : LOperand) (k : LabelKind) (l : LLabel) (t t' : JasminLsemMem.MemTag) :
    RefinementWP.Refines top
      (RefinementWP.Concretization.ofStateRel fun (s : LstateMF) (pc : Nat) =>
        s.prog.lfn = "f" ∧ s.prog.base.lpc = pc)
      (fun _ : Unit => bot)
      (I.runM (JasminLsemMemLoop.singletonProgM "f" [(.Lcond c l, t), (.Llabel k l, t')]) 2)
      (RefinementWP.optD fun pc => if pc = 0 then some ((), 2) else none)
      (fun _ _ _ => True) := by
  have hl : JasminLsemMemLoop.findLabelMem l [(.Lcond c l, t), (.Llabel k l, t')] = some 1 := by
    simp [JasminLsemMemLoop.findLabelMem, JasminLsemLabeled.findLabel,
      JasminLsemLabeled.isLabel, List.findIdx?_cons]
  wrp_vcgen [runM_succ, runM_zero] using [stepM_spec]
  all_goals grind [findInstrMem, JasminLsemMemLoop.singletonProgM,
    JasminLsemMemLoop.evalJumpMem, JasminLsemMem.LstateM.setLpc, JasminLsemMem.LstateM.nextPc,
    JasminLsemMem.LstateM.lpc, JasminLsemWidthN.LstateN.nextPc, step_cond, step_label]

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa

end
