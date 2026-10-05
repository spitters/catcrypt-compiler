/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaData

@[expose] public section

set_option autoImplicit false

/-!
# The instruction-set record of the `Lprog` back end: semantics fields

An `Isa` extends the data record `IsaData` of `VIR.LprogIsaData` (register file, calling convention
and the mnemonic data of the two-address legaliser) by the step semantics of one instruction
set over the flag-extended memref state `LstateMF`: a whole-instruction step `step`, the branch-condition evaluation
`condEval`, and the obligation `step_ctl` that on a control instruction (`Llabel`, `Lcond`,
`Lgoto`) the step is the control step `ctlStep condEval`, shared by every instruction set.
The state types and their flag bits `zf`, `cf`, `of` are fixed; an instruction set decides
through `step` which instructions write them.

The interpreters `Isa.lsemFuelMemF`, `Isa.evalInstrPMemFk`, `Isa.lsemFuelMemFk` and the
predicate `Isa.RunIdxOk` have the recursion of `JasminLsemMemFlagGuard.lsemFuelMemF` and of
the checked machine of `JasminLsemMemChecked`, with the step taken from the record. The x86
instance, whose step is `evalInstrPMemF`, is `X86Backend.X86Isa.x86Isa`; at that instance each
generic interpreter is the existing one by `rfl`.

## Main results

* `ctlStep`, `isCtl`, `Isa`: the shared control step and the record.
* `Isa.lsemFuelMemF_halt`, `Isa.lsemFuelMemF_step`: the run equations.
* `Isa.lsemFuelMemF_add`, `Isa.lsemFuelMemF_of_runL`: a successful run is stable under more
  fuel, and a straight stretch at the end of the body runs as `Isa.runL`.
* `Isa.lsemFuelMemFk_false`, `Isa.lsemFuelMemF_of_checked`, `Isa.lsemFuelMemFk_of_runIdxOk`,
  `Isa.runIdxOk_of_checked`: the checked run against the unchecked one.
* `Isa.step_label`, `Isa.step_cond`, `Isa.step_goto`: the control step of every instance.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked

/-- The control instructions: labels, conditional jumps and gotos. -/
def isCtl : LinstrR → Bool
  | .Llabel _ _ => true
  | .Lcond _ _ => true
  | .Lgoto _ => true
  | _ => false

/-- **The control step**, shared by every instruction set: `Llabel` advances the pc,
    `Lcond c l` jumps to `l` when `condEval s c` and advances the pc otherwise, and
    `Lgoto (fn, l)` jumps to `l` within the function `fn` of the program. Any other
    instruction has no control step. -/
def ctlStep (condEval : LstateMF → LOperand → Bool) (P : LprogM) (i : LinstrRM)
    (s : LstateMF) : Option LstateMF :=
  match i.fst with
  | .Llabel _ _ => some { s with prog := { s.prog with base := s.prog.base.nextPc } }
  | .Lcond c l =>
      if condEval s c then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else some { s with prog := { s.prog with base := s.prog.base.nextPc } }
  | .Lgoto (fn, l) =>
      if fn = P.lfn then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else none
  | _ => none

/-- **The instruction-set record of the `Lprog` back end**: the data `IsaData` (register
    file, calling convention, legaliser mnemonic data), the step of one instruction over the
    flag-extended memref state, the evaluation of a branch condition, and the obligation that
    the step of a control instruction is the shared control step under that evaluation. -/
structure Isa : Type extends IsaData where
  /-- The step of one instruction of the program `P` from a state. -/
  step : LprogM → LinstrRM → LstateMF → Option LstateMF
  /-- Whether the branch condition holds in a state. -/
  condEval : LstateMF → LOperand → Bool
  /-- On a control instruction the step is the shared control step. -/
  step_ctl : ∀ (P : LprogM) (i : LinstrRM) (s : LstateMF), isCtl i.fst = true →
    step P i s = ctlStep condEval P i s

namespace Isa

variable (I : Isa)

/-- The step of a label advances the pc. -/
theorem step_label (P : LprogM) (k : LabelKind) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    I.step P (.Llabel k l, tag) s =
      some { s with prog := { s.prog with base := s.prog.base.nextPc } } :=
  I.step_ctl P _ s rfl

/-- The step of a conditional jump: jump when the condition holds, else advance the pc. -/
theorem step_cond (P : LprogM) (c : LOperand) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    I.step P (.Lcond c l, tag) s =
      if I.condEval s c = true then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else some { s with prog := { s.prog with base := s.prog.base.nextPc } } :=
  I.step_ctl P _ s rfl

/-- The step of a goto: a jump within the function of the program, none otherwise. -/
theorem step_goto (P : LprogM) (x : String) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    I.step P (.Lgoto (x, l), tag) s =
      if x = P.lfn then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else none :=
  I.step_ctl P _ s rfl

/-- The steps of a list of instructions, in order. -/
def runL (P : LprogM) : List LinstrRM → LstateMF → Option LstateMF
  | [], s => some s
  | i :: is, s => (I.step P i s).bind (runL P is)

/-- Fetch and step. -/
def lsemStepPMemF (P : LprogM) (s : LstateMF) : Option LstateMF :=
  match findInstrMem P s.prog with
  | some i => I.step P i s
  | none => none

/-- The fuel-stepped interpreter of the instruction set: iterate `step`, halting
    (returning the state) when `findInstrMem` is `none`. -/
def lsemFuelMemF (P : LprogM) : Nat → LstateMF → Option LstateMF
  | 0, s => match findInstrMem P s.prog with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s.prog with
      | none => some s
      | some i =>
          match I.step P i s with
          | some s' => lsemFuelMemF P fuel s'
          | none => none

/-- A halted state takes no step. -/
theorem lsemFuelMemF_halt (P : LprogM) (fuel : Nat) (s : LstateMF)
    (h : findInstrMem P s.prog = none) : I.lsemFuelMemF P fuel s = some s := by
  cases fuel <;> simp [lsemFuelMemF, h]

/-- One fetched-and-evaluated step under the fuel iterator. -/
theorem lsemFuelMemF_step (P : LprogM) (fuel : Nat) (i : LinstrRM) (s s' : LstateMF)
    (hfetch : findInstrMem P s.prog = some i) (heval : I.step P i s = some s') :
    I.lsemFuelMemF P (fuel + 1) s = I.lsemFuelMemF P fuel s' := by
  simp only [lsemFuelMemF, hfetch, heval]

/-- A successful run returns the same state at every larger fuel. -/
theorem lsemFuelMemF_add (P : LprogM) :
    ∀ (n k : Nat) (s t : LstateMF), I.lsemFuelMemF P n s = some t →
      I.lsemFuelMemF P (n + k) s = some t := by
  intro n
  induction n with
  | zero =>
      intro k s t h
      simp only [lsemFuelMemF] at h
      split at h
      · next hf => cases h; rw [Nat.zero_add]; exact I.lsemFuelMemF_halt P k s hf
      · cases h
  | succ n ih =>
      intro k s t h
      rw [Nat.add_right_comm]
      simp only [lsemFuelMemF] at h ⊢
      cases hf : findInstrMem P s.prog with
      | none => simp only [hf] at h ⊢; exact h
      | some i =>
          simp only [hf] at h ⊢
          cases hs : I.step P i s with
          | none => simp only [hs, reduceCtorEq] at h
          | some s' => simp only [hs] at h ⊢; exact ih k s' t h

/-- **A straight stretch at the end of the body.** When the body of `P` is `pre ++ rest`, the
    state is in the function of `P` at counter `pre.length`, and every step of an instruction
    of `rest` stays in the function and advances the counter by one, the run of `P` with fuel
    `rest.length` is the run `Isa.runL` of the instructions of `rest`. -/
theorem lsemFuelMemF_of_runL (P : LprogM) :
    ∀ (rest pre : List LinstrRM) (s t : LstateMF), P.body = pre ++ rest →
      s.prog.lfn = P.lfn → s.prog.base.lpc = pre.length →
      (∀ i ∈ rest, ∀ u u', I.step P i u = some u' →
        u'.prog.lfn = u.prog.lfn ∧ u'.prog.base.lpc = u.prog.base.lpc + 1) →
      I.runL P rest s = some t → I.lsemFuelMemF P rest.length s = some t := by
  intro rest
  induction rest with
  | nil =>
      intro pre s t hbody hfn hpc _ hrun
      cases hrun
      refine I.lsemFuelMemF_halt P 0 s ?_
      simp only [findInstrMem, hfn, if_true, hbody, List.append_nil, hpc,
        List.getElem?_eq_none (le_refl _)]
  | cons i rest ih =>
      intro pre s t hbody hfn hpc hstep hrun
      simp only [runL, Option.bind_eq_some_iff] at hrun
      obtain ⟨u, hu, hrun⟩ := hrun
      have hfetch : findInstrMem P s.prog = some i := by
        simp only [findInstrMem, hfn, if_true, hbody, hpc, List.getElem?_append_right
          (le_refl _), Nat.sub_self, List.getElem?_cons_zero]
      rw [List.length_cons, I.lsemFuelMemF_step P _ i s u hfetch hu]
      obtain ⟨hufn, hupc⟩ := hstep i (List.mem_cons_self ..) s u hu
      exact ih (pre ++ [i]) u t (by rw [hbody, List.append_assoc]; rfl) (hufn.trans hfn)
        (by rw [hupc, hpc, List.length_append, List.length_singleton])
        (fun j hj => hstep j (List.mem_cons_of_mem i hj)) hrun

/-- The checked step: with `ck`, the step when the instruction is in bounds (`idxOkB`) and
    none otherwise; without `ck`, the step. -/
def evalInstrPMemFk (ck : Bool) (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    Option LstateMF :=
  if ck && !idxOkB i s then none else I.step P i s

/-- The run of the checked step, with the recursion of `lsemFuelMemF`. -/
def lsemFuelMemFk (ck : Bool) (P : LprogM) : Nat → LstateMF → Option LstateMF
  | 0, s => match findInstrMem P s.prog with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s.prog with
      | none => some s
      | some i =>
          match I.evalInstrPMemFk ck P i s with
          | some s' => lsemFuelMemFk ck P fuel s'
          | none => none

@[simp] theorem evalInstrPMemFk_false (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    I.evalInstrPMemFk false P i s = I.step P i s := by
  simp [evalInstrPMemFk]

theorem evalInstrPMemFk_true (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    I.evalInstrPMemFk true P i s = if idxOkB i s then I.step P i s else none := by
  cases h : idxOkB i s <;> simp [evalInstrPMemFk, h]

/-- A checked step is a step. -/
theorem step_of_k {ck : Bool} {P : LprogM} {i : LinstrRM} {s s' : LstateMF}
    (h : I.evalInstrPMemFk ck P i s = some s') : I.step P i s = some s' := by
  unfold evalInstrPMemFk at h
  split at h
  · cases h
  · exact h

/-- A successful checked step is in bounds. -/
theorem idxOkB_of_checked {P : LprogM} {i : LinstrRM} {s s' : LstateMF}
    (h : I.evalInstrPMemFk true P i s = some s') : idxOkB i s = true := by
  rw [evalInstrPMemFk_true] at h
  cases hb : idxOkB i s
  · simp [hb] at h
  · rfl

/-- The unchecked instance of the checked run is the run. -/
theorem lsemFuelMemFk_false (P : LprogM) :
    ∀ (fuel : Nat) (s : LstateMF), I.lsemFuelMemFk false P fuel s = I.lsemFuelMemF P fuel s
  | 0, s => by
      cases hf : findInstrMem P s.prog <;> simp only [lsemFuelMemFk, lsemFuelMemF, hf]
  | fuel + 1, s => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf]
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf, evalInstrPMemFk_false]
          cases I.step P i s with
          | none => rfl
          | some s' => exact lsemFuelMemFk_false P fuel s'

theorem lsemFuelMemFk_halt (ck : Bool) (P : LprogM) (fuel : Nat) (s : LstateMF)
    (h : findInstrMem P s.prog = none) : I.lsemFuelMemFk ck P fuel s = some s := by
  cases fuel <;> simp [lsemFuelMemFk, h]

theorem lsemFuelMemFk_step (ck : Bool) (P : LprogM) (fuel : Nat) (i : LinstrRM)
    (s s' : LstateMF) (hfetch : findInstrMem P s.prog = some i)
    (heval : I.evalInstrPMemFk ck P i s = some s') :
    I.lsemFuelMemFk ck P (fuel + 1) s = I.lsemFuelMemFk ck P fuel s' := by
  simp only [lsemFuelMemFk, hfetch, heval]

/-- A halting checked run is a halting run, to the same state. -/
theorem lsemFuelMemF_of_checked {ck : Bool} (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), I.lsemFuelMemFk ck P fuel s = some t →
      I.lsemFuelMemF P fuel s = some t
  | 0, s, t, h => by
      cases hf : findInstrMem P s.prog <;>
        simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢ <;> exact h
  | fuel + 1, s, t, h => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢; exact h
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢
          cases he : I.evalInstrPMemFk ck P i s with
          | none => simp [he] at h
          | some s' =>
              rw [he] at h
              simp only [I.step_of_k he]
              exact lsemFuelMemF_of_checked P fuel s' t h

/-- Every state that a run of at most `fuel` steps steps from is in bounds at the
    instruction it fetches. -/
def RunIdxOk (P : LprogM) : Nat → LstateMF → Prop
  | 0, _ => True
  | fuel + 1, s =>
      ∀ i, findInstrMem P s.prog = some i →
        idxOkB i s = true ∧ ∀ s', I.step P i s = some s' → RunIdxOk P fuel s'

/-- A halting run whose accesses are in bounds is a halting checked run, to the same
    state. -/
theorem lsemFuelMemFk_of_runIdxOk (ck : Bool) (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), I.lsemFuelMemF P fuel s = some t → I.RunIdxOk P fuel s →
      I.lsemFuelMemFk ck P fuel s = some t
  | 0, s, t, h, _ => by
      cases hf : findInstrMem P s.prog <;>
        simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢ <;> exact h
  | fuel + 1, s, t, h, hok => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢; exact h
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢
          obtain ⟨hi, hnext⟩ := hok i hf
          cases he : I.step P i s with
          | none => simp [he] at h
          | some s' =>
              rw [he] at h
              have hk : I.evalInstrPMemFk ck P i s = some s' := by
                simp [evalInstrPMemFk, hi, he]
              simp only [hk]
              exact lsemFuelMemFk_of_runIdxOk ck P fuel s' t h (hnext s' he)

/-- A halting checked run is in bounds: every state it steps from fetches an instruction
    in bounds. -/
theorem runIdxOk_of_checked (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), I.lsemFuelMemFk true P fuel s = some t →
      I.RunIdxOk P fuel s
  | 0, _, _, _ => trivial
  | fuel + 1, s, t, h => by
      intro i hf
      simp only [lsemFuelMemFk, hf] at h
      cases he : I.evalInstrPMemFk true P i s with
      | none => simp [he] at h
      | some s' =>
          rw [he] at h
          refine ⟨I.idxOkB_of_checked he, fun s'' he' => ?_⟩
          rw [I.step_of_k he] at he'
          cases he'
          exact runIdxOk_of_checked P fuel s' t h

end Isa

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
