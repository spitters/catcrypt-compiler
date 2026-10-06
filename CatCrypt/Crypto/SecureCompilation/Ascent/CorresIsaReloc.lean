/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaRet

/-!
# Relocation of a body inside a larger program

A machine state `LstateMF` holds the name of its function and a program counter; it holds no
program. The state `shiftPc k s` is `s` with the counter advanced by `k`. This module relates
the runs of a body `B`, as the program `singletonProgM fn B`, to the runs of the program
`singletonProgM fn (pre ++ B ++ post)` that contains `B` at the offset `pre.length`: a
segment `IsaCfg.Steps` of `B` from `s` to `t` is a segment of the larger program with the
same number of steps from `shiftPc pre.length s` to `shiftPc pre.length t`.

The fetch at the counter `pre.length + j` of the larger program returns the instruction at
the counter `j` of `B`. The step of an instruction depends on the program through the label
search of a jump only when the instruction is a control instruction (`Isa.step_ctl`), and
the search `findLabelMem` returns the first declaration of a label. The hypothesis
`LabelsFresh pre B` (no label declared in `B` is declared in `pre`) makes every jump of `B`
that resolves at the index `q` of `B` resolve at the index `pre.length + q` of the larger
program; the labels of `post` are unconstrained. `labelsFreshB` is a Boolean check of the
hypothesis.

The step of an instruction other than a control instruction is a field of the record `Isa`
with no equation, so the relocation of such a step is the hypothesis `StepRelocates`: the
branch condition does not read the counter, and a step of a non-control instruction of `B`
from `s` to `u` on `B` is a step from `shiftPc pre.length s` to `shiftPc pre.length u` on the
larger program.

A run of the interpreter `Isa.lsemFuelMemF` on `B` halts when the counter leaves `B`. A
correspondence `CorresIsa` of `B` together with the exit contract `ExitFrame` ends at the
counter `B.length`. In the larger program the counter `pre.length + B.length` is the
position of the first instruction of `post`, where the interpreter does not halt when
`post` is not empty. The relocated statements are therefore segments that reach the counter
`pre.length + B.length`; they do not state that the larger program halts.

A call through the stack stores the counter after the call as a word in memory
(`LprogIsa.retAddr`). The state after a call step of the larger program therefore differs
from the shift of the state after the call step of `B` in that memory cell, and a segment of
`B` under `isa.withCalls` that takes a call is not related to a segment of the larger program
by `shiftPc`. `steps_of_step_rel` transfers segments along a relation between states, and
`steps_call_entry_relocate` gives the call step of the larger program. The statements with
`shiftPc` are for a body without calls, which is the case of a callee `B` followed by its
return.

## Main results

* `shiftPc`: a state with the counter advanced.
* `LabelsFresh`, `labelsFreshB`, `labelsFresh_of_labelsFreshB`: the label hypothesis and its
  Boolean check.
* `findLabelMem_relocate`, `ctlStep_relocate`: a label search and a control step in the
  larger program.
* `StepRelocates`, `step_relocate`, `lsemStepPMemF_relocate`: the hypothesis on the
  non-control steps, the step of every instruction of `B`, and the fetch-and-step function.
* `steps_of_step_rel`, `steps_of_step_sim`: segments along a relation and along a function
  between states.
* `steps_relocate`, `steps_relocate_withCalls`: the relocation of a segment at `isa`, and at
  `isa.withCalls` for a body without calls.
* `atPc_relocate`, `atLabel_relocate`: positions in the larger program.
* `corresIsa_relocate_run`, `corresIsa_relocate_run_withCalls`: the run of the larger program
  from a shifted entry state, from a correspondence of `B`.
* `relocRel`, `relocFrame`, `procSpec_relocate_of_corresIsa`,
  `procSpec_labelled_of_corresIsa`: the procedure specification `IsaCall.ProcSpec` of a
  callee body placed inside a larger program and followed by its return.
* `relocRel_of_atPc`, `relocRel_callEntry`: the relocated relation at a state of the larger
  program, in particular at the state after a call step.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace IsaCall

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LLabel LabelKind LOperand
  LinstrR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM findInstrMem
  findLabelMem evalJumpMem singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa isCall isCtl ctlStep)

/-! ## The shifted state -/

/-- The state `s` with the program counter advanced by `k`. -/
def shiftPc (k : Nat) (s : LstateMF) : LstateMF := goto s (k + s.prog.base.lpc)

@[simp] theorem shiftPc_lfn (k : Nat) (s : LstateMF) :
    (shiftPc k s).prog.lfn = s.prog.lfn := rfl

@[simp] theorem shiftPc_lpc (k : Nat) (s : LstateMF) :
    (shiftPc k s).prog.base.lpc = k + s.prog.base.lpc := rfl

/-- The shift of a state with the counter set to `q` has the counter `k + q`. -/
theorem shiftPc_goto (k q : Nat) (s : LstateMF) :
    shiftPc k (goto s q) = goto (shiftPc k s) (k + q) := rfl

/-- The shift commutes with the advance of the counter by one. -/
theorem shiftPc_next (k : Nat) (s : LstateMF) : shiftPc k (next s) = next (shiftPc k s) :=
  rfl

/-- Setting the counter of a state to its own value changes nothing. -/
theorem goto_lpc_self (s : LstateMF) : goto s s.prog.base.lpc = s := rfl

/-- The return address contract reads the registers and the memory only, so it holds
    between two shifted states when it holds between the states. -/
theorem retFrame_shiftPc (sp : String) (k : Nat) {m m' : LstateMF} (h : RetFrame sp m m') :
    RetFrame sp (shiftPc k m) (shiftPc k m') := h

/-! ## Fetch and labels in the larger program -/

/-- The instruction at the counter `j` of `B` is at the counter `pre.length + j` of
    `pre ++ B ++ post`. -/
theorem getElem?_relocate {pre B : List LinstrRM} (post : List LinstrRM) {j : Nat}
    {i : LinstrRM} (h : B[j]? = some i) : (pre ++ B ++ post)[pre.length + j]? = some i := by
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_append_left hlt]
  exact h

/-- **The label hypothesis of a relocation.** No label declared in `B` is declared in
    `pre`. -/
def LabelsFresh (pre B : List LinstrRM) : Prop :=
  ∀ l q, findLabelMem l B = some q → findLabelMem l pre = none

/-- The Boolean check of `LabelsFresh`: every label declared in `pre` is absent from
    `B`. -/
def labelsFreshB (pre B : List LinstrRM) : Bool :=
  pre.all fun i =>
    match i.fst with
    | .Llabel _ l => (findLabelMem l B).isNone
    | _ => true

/-- The Boolean check `labelsFreshB` is sound for `LabelsFresh`. -/
theorem labelsFresh_of_labelsFreshB {pre B : List LinstrRM}
    (h : labelsFreshB pre B = true) : LabelsFresh pre B := by
  intro l q hq
  unfold findLabelMem VIR.JasminLsemLabeled.findLabel
  rw [List.findIdx?_eq_none_iff]
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  have hc := List.all_eq_true.mp h i hi
  cases hfst : i.fst with
  | Llabel kd l' =>
      rw [hfst] at hc
      by_cases hl : l = l'
      · subst hl
        simp [hq] at hc
      · simp [VIR.JasminLsemLabeled.isLabel, hl]
  | _ => rfl

/-- **A label search in the larger program.** A label absent from `pre` and declared at the
    index `q` of `B` is declared at the index `pre.length + q` of `pre ++ B ++ post`. -/
theorem findLabelMem_relocate {pre B : List LinstrRM} (post : List LinstrRM) {l : LLabel}
    {q : Nat} (hpre : findLabelMem l pre = none) (h : findLabelMem l B = some q) :
    findLabelMem l (pre ++ B ++ post) = some (pre.length + q) := by
  unfold findLabelMem VIR.JasminLsemLabeled.findLabel at hpre h ⊢
  rw [List.map_append, List.map_append, List.findIdx?_append, List.findIdx?_append, hpre, h]
  simp [Nat.add_comm]

/-- A label absent from `pre` and declared right after `pre` is found at the index
    `pre.length`. -/
theorem findLabelMem_append_label {pre : List LinstrRM} (X : List LinstrRM)
    (kind : LabelKind) (l : LLabel) (tag : MemTag) (hpre : findLabelMem l pre = none) :
    findLabelMem l (pre ++ (.Llabel kind l, tag) :: X) = some pre.length := by
  unfold findLabelMem VIR.JasminLsemLabeled.findLabel at hpre ⊢
  rw [List.map_append, List.findIdx?_append, hpre]
  simp [List.findIdx?_cons, VIR.JasminLsemLabeled.isLabel]

/-! ## The control step -/

/-- **A jump in the larger program.** A jump of `B` to the label `l` from `s` to `u` is, in
    `pre ++ B ++ post`, a jump from the shifted state to the shifted state. -/
theorem evalJumpMem_relocate (fn : String) {pre B : List LinstrRM} (post : List LinstrRM)
    (hfresh : LabelsFresh pre B) (l : LLabel) {s u : LstateMF}
    (h : (evalJumpMem (singletonProgM fn B) l s.prog).map (fun p => { s with prog := p }) =
      some u) :
    (evalJumpMem (singletonProgM fn (pre ++ B ++ post)) l (shiftPc pre.length s).prog).map
        (fun p => { shiftPc pre.length s with prog := p }) = some (shiftPc pre.length u) := by
  cases hq : findLabelMem l B with
  | none => simp [evalJumpMem, singletonProgM, hq] at h
  | some q =>
      have hB : findLabelMem l (singletonProgM fn B).body = some q := hq
      rw [evalJumpMem_of_findLabelMem hB s] at h
      cases h
      have hbig : findLabelMem l (singletonProgM fn (pre ++ B ++ post)).body =
          some (pre.length + q) := findLabelMem_relocate post (hfresh l q hq) hq
      rw [evalJumpMem_of_findLabelMem hbig (shiftPc pre.length s)]
      rfl

/-- **The control step in the larger program.** When the branch condition `cond` does not
    read the counter and no label of `B` is declared in `pre`, a control step of `B` from
    `s` to `u` is a control step of `pre ++ B ++ post` from the shifted state to the shifted
    state. -/
theorem ctlStep_relocate (cond : LstateMF → LOperand → Bool) (fn : String)
    {pre B : List LinstrRM} (post : List LinstrRM)
    (hcond : ∀ s c, cond (shiftPc pre.length s) c = cond s c) (hfresh : LabelsFresh pre B)
    (i : LinstrRM) {s u : LstateMF} (h : ctlStep cond (singletonProgM fn B) i s = some u) :
    ctlStep cond (singletonProgM fn (pre ++ B ++ post)) i (shiftPc pre.length s) =
      some (shiftPc pre.length u) := by
  have hfn : ∀ X : List LinstrRM, (singletonProgM fn X).lfn = fn := fun _ => rfl
  obtain ⟨w, t⟩ := i
  cases w with
  | Llabel kd l =>
      simp only [ctlStep] at h ⊢
      cases h
      rfl
  | Lcond c l =>
      simp only [ctlStep, hcond] at h ⊢
      by_cases hc : cond s c = true
      · rw [if_pos hc] at h ⊢
        exact evalJumpMem_relocate fn post hfresh l h
      · rw [if_neg hc] at h ⊢
        cases h
        rfl
  | Lgoto p =>
      obtain ⟨f, l⟩ := p
      simp only [ctlStep, hfn] at h ⊢
      by_cases hf : f = fn
      · rw [if_pos hf] at h ⊢
        exact evalJumpMem_relocate fn post hfresh l h
      · rw [if_neg hf] at h
        cases h
  | _ => simp only [ctlStep, reduceCtorEq] at h

/-! ## One step -/

/-- **The hypothesis on the steps of a relocation.** The branch condition of `isa` does not
    read the counter, and a step of a non-control instruction of `B` from `s` to `u` on `B`
    is a step from the shifted state to the shifted state on `pre ++ B ++ post`. -/
def StepRelocates (isa : Isa) (fn : String) (pre B post : List LinstrRM) : Prop :=
  (∀ s c, isa.condEval (shiftPc pre.length s) c = isa.condEval s c) ∧
    ∀ i ∈ B, isCtl i.fst = false → ∀ s u, isa.step (singletonProgM fn B) i s = some u →
      isa.step (singletonProgM fn (pre ++ B ++ post)) i (shiftPc pre.length s) =
        some (shiftPc pre.length u)

/-- **The step of an instruction in the larger program.** Under `StepRelocates` and
    `LabelsFresh`, a step of any instruction of `B` from `s` to `u` on `B` is a step from
    the shifted state to the shifted state on `pre ++ B ++ post`. -/
theorem step_relocate (isa : Isa) (fn : String) {pre B : List LinstrRM}
    (post : List LinstrRM) (hreloc : StepRelocates isa fn pre B post)
    (hfresh : LabelsFresh pre B) (i : LinstrRM) (hi : i ∈ B) {s u : LstateMF}
    (h : isa.step (singletonProgM fn B) i s = some u) :
    isa.step (singletonProgM fn (pre ++ B ++ post)) i (shiftPc pre.length s) =
      some (shiftPc pre.length u) := by
  cases hc : isCtl i.fst with
  | false => exact hreloc.2 i hi hc s u h
  | true =>
      rw [isa.step_ctl _ i _ hc] at h ⊢
      exact ctlStep_relocate isa.condEval fn post hreloc.1 hfresh i h

/-- **The fetch-and-step function in the larger program.** Let every step of `isa` on an
    instruction of `B` from `s` to `u` on `B` be a step of `isa'` from the shifted state to
    the shifted state on `pre ++ B ++ post`. A fetch and step of `isa` on `B` from `s` to
    `u` is a fetch and step of `isa'` on the larger program from the shifted state to the
    shifted state. -/
theorem lsemStepPMemF_relocate (isa isa' : Isa) (fn : String) {pre B : List LinstrRM}
    (post : List LinstrRM)
    (hstep : ∀ i ∈ B, ∀ s u, isa.step (singletonProgM fn B) i s = some u →
      isa'.step (singletonProgM fn (pre ++ B ++ post)) i (shiftPc pre.length s) =
        some (shiftPc pre.length u))
    {s u : LstateMF} (h : isa.lsemStepPMemF (singletonProgM fn B) s = some u) :
    isa'.lsemStepPMemF (singletonProgM fn (pre ++ B ++ post)) (shiftPc pre.length s) =
      some (shiftPc pre.length u) := by
  unfold Isa.lsemStepPMemF at h ⊢
  cases hf : findInstrMem (singletonProgM fn B) s.prog with
  | none => rw [hf] at h; cases h
  | some i =>
      rw [hf] at h
      unfold findInstrMem at hf
      split at hf
      · next hl =>
          have hfB : B[s.prog.base.lpc]? = some i := hf
          have hf' : findInstrMem (singletonProgM fn (pre ++ B ++ post))
              (shiftPc pre.length s).prog = some i := by
            unfold findInstrMem
            rw [if_pos (show (shiftPc pre.length s).prog.lfn =
              (singletonProgM fn (pre ++ B ++ post)).lfn from hl)]
            exact getElem?_relocate post hfB
          rw [hf']
          exact hstep i (List.mem_of_getElem? hfB) s u h
      · cases hf

/-! ## Segments -/

/-- **Segments along a relation.** When every step of `isa` on `P` from a state related by
    `R` to a state of `P'` is matched by a step of `isa'` on `P'` to a related state, a
    segment of `isa` on `P` from a related state is matched by a segment of `isa'` on `P'`
    with the same number of steps to a related state. -/
theorem steps_of_step_rel (isa isa' : Isa) {P P' : LprogM} (R : LstateMF → LstateMF → Prop)
    (hstep : ∀ s s' u, R s s' → isa.lsemStepPMemF P s = some u →
      ∃ u', isa'.lsemStepPMemF P' s' = some u' ∧ R u u') :
    ∀ (n : Nat) (s s' t : LstateMF), R s s' → Steps isa P n s t →
      ∃ t', Steps isa' P' n s' t' ∧ R t t'
  | 0, s, s', t, hR, h => by
      have hst : s = t := Option.some.inj h
      subst hst
      exact ⟨s', Steps.refl isa' P' s', hR⟩
  | n + 1, s, s', t, hR, h => by
      simp only [Steps, CutPoint.iter, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨u, hu, h⟩ := h
      obtain ⟨u', hu', hR'⟩ := hstep s s' u hR hu
      obtain ⟨t', ht', hRt⟩ := steps_of_step_rel isa isa' R hstep n u u' t hR' h
      exact ⟨t', ⟨u', hu', ht'⟩, hRt⟩

/-- **Segments along a function.** When every step of `isa` on `P` from `s` to `u` is a
    step of `isa'` on `P'` from `f s` to `f u`, a segment of `isa` on `P` from `s` to `t` is
    a segment of `isa'` on `P'` with the same number of steps from `f s` to `f t`. -/
theorem steps_of_step_sim (isa isa' : Isa) {P P' : LprogM} (f : LstateMF → LstateMF)
    (hstep : ∀ s u, isa.lsemStepPMemF P s = some u →
      isa'.lsemStepPMemF P' (f s) = some (f u))
    {n : Nat} {s t : LstateMF} (h : Steps isa P n s t) : Steps isa' P' n (f s) (f t) := by
  obtain ⟨t', ht', rfl⟩ := steps_of_step_rel isa isa' (fun s s' => s' = f s)
    (fun s s' u hR hu => ⟨f u, by rw [hR]; exact hstep s u hu, rfl⟩) n s (f s) t rfl h
  exact ht'

/-- **Relocation of a segment.** Under `StepRelocates` and `LabelsFresh`, a segment of `isa`
    on `B` from `s` to `t` is a segment of `isa` on `pre ++ B ++ post` with the same number
    of steps from `shiftPc pre.length s` to `shiftPc pre.length t`. -/
theorem steps_relocate (isa : Isa) (fn : String) {pre B : List LinstrRM}
    (post : List LinstrRM) (hreloc : StepRelocates isa fn pre B post)
    (hfresh : LabelsFresh pre B) {n : Nat} {s t : LstateMF}
    (h : Steps isa (singletonProgM fn B) n s t) :
    Steps isa (singletonProgM fn (pre ++ B ++ post)) n (shiftPc pre.length s)
      (shiftPc pre.length t) :=
  steps_of_step_sim isa isa (shiftPc pre.length)
    (fun _ _ hu => lsemStepPMemF_relocate isa isa fn post
      (fun i hi _ _ hs => step_relocate isa fn post hreloc hfresh i hi hs) hu) h

/-- **Relocation of a segment of a body without calls, at the instruction set with calls.**
    Let `B` contain no call and no return. Under `StepRelocates` and `LabelsFresh`, a
    segment of `isa` on `B` from `s` to `t` is a segment of `isa.withCalls` on
    `pre ++ B ++ post` with the same number of steps from `shiftPc pre.length s` to
    `shiftPc pre.length t`. -/
theorem steps_relocate_withCalls (isa : Isa) (fn : String) {pre B : List LinstrRM}
    (post : List LinstrRM) (hB : ∀ i ∈ B, isCall i.fst = false)
    (hreloc : StepRelocates isa fn pre B post) (hfresh : LabelsFresh pre B) {n : Nat}
    {s t : LstateMF} (h : Steps isa (singletonProgM fn B) n s t) :
    Steps isa.withCalls (singletonProgM fn (pre ++ B ++ post)) n (shiftPc pre.length s)
      (shiftPc pre.length t) :=
  steps_of_step_sim isa isa.withCalls (shiftPc pre.length)
    (fun _ _ hu => lsemStepPMemF_relocate isa isa.withCalls fn post
      (fun i hi _ _ hs => by
        rw [isa.withCalls_step_of_not_call _ i _ (hB i hi)]
        exact step_relocate isa fn post hreloc hfresh i hi hs) hu) h

/-! ## Positions -/

/-- A state at the counter `q` of `B` is, shifted, at the counter `pre.length + q` of
    `pre ++ B ++ post`. -/
theorem atPc_relocate (fn : String) (pre B post : List LinstrRM) {q : Nat} {s : LstateMF}
    (h : atPc (singletonProgM fn B) q s) :
    atPc (singletonProgM fn (pre ++ B ++ post)) (pre.length + q) (shiftPc pre.length s) :=
  ⟨h.1, congrArg (pre.length + ·) h.2⟩

/-- A state at the label `l` of `B` is, shifted, at the label `l` of `pre ++ B ++ post`
    when no label of `B` is declared in `pre`. -/
theorem atLabel_relocate (fn : String) {pre B : List LinstrRM} (post : List LinstrRM)
    (hfresh : LabelsFresh pre B) {l : LLabel} {s : LstateMF}
    (h : atLabel (singletonProgM fn B) l s) :
    atLabel (singletonProgM fn (pre ++ B ++ post)) l (shiftPc pre.length s) := by
  obtain ⟨q, hq, hat⟩ := h
  exact ⟨pre.length + q, findLabelMem_relocate post (hfresh l q hq) hq,
    atPc_relocate fn pre B post hat⟩

/-- **The call step in the larger program.** Let the counter `j` of `B` hold a call through
    the stack to the label `l`, declared at the index `q` of `B`, and let no label of `B` be
    declared in `pre`. From a state `m` at the counter `pre.length + j` of
    `pre ++ B ++ post` whose stack pointer holds `v`, one step of `isa.withCalls` reaches
    the state `callEntry isa.sp v (pre.length + q) m`, which is at the label `l`. The return
    address it stores is the word of `pre.length + j + 1`. -/
theorem steps_call_entry_relocate (isa : Isa) (fn : String) {pre B : List LinstrRM}
    (post : List LinstrRM) (hfresh : LabelsFresh pre B) {j q : Nat} {l : LLabel}
    {tag : MemTag} {v : BitVec 64} {m : LstateMF}
    (hat : atPc (singletonProgM fn (pre ++ B ++ post)) (pre.length + j) m)
    (hi : B[j]? = some (.Lcall none (fn, l), tag)) (hl : findLabelMem l B = some q)
    (hsp : m.prog.base.reg.getW isa.sp 64 = some v) :
    Steps isa.withCalls (singletonProgM fn (pre ++ B ++ post)) 1 m
        (callEntry isa.sp v (pre.length + q) m) ∧
      atLabel (singletonProgM fn (pre ++ B ++ post)) l
        (callEntry isa.sp v (pre.length + q) m) :=
  steps_call_entry isa (P := singletonProgM fn (pre ++ B ++ post)) hat
    (getElem?_relocate post hi) (findLabelMem_relocate post (hfresh l q hl) hl) hsp

/-! ## The run of the larger program from a correspondence of the body -/

section Generic

variable {A : Type}

/-- **The run of the larger program from a shifted entry state.** Let `B` correspond to
    `fa` at fuel `fuel`. Under `StepRelocates` and `LabelsFresh`, from the shift of a state
    `m` related by `SR` to `a` under `Pre`, the program `pre ++ B ++ post` makes a segment
    of `n ≤ fuel` steps to the shift of a state `m'` that is halted in `B` and related to
    `fa a`. -/
theorem corresIsa_relocate_run (isa : Isa) {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {fuel : Nat} (hreloc : StepRelocates isa fn pre B post) (hfresh : LabelsFresh pre B)
    (h : CorresIsa isa (singletonProgM fn B) SR Pre fa fuel) {m : LstateMF} {a : A}
    (hSR : SR m a) (hPre : Pre a) :
    ∃ n m', n ≤ fuel ∧
      Steps isa (singletonProgM fn (pre ++ B ++ post)) n (shiftPc pre.length m)
        (shiftPc pre.length m') ∧
      Halted (singletonProgM fn B) m' ∧ SR m' (fa a) := by
  obtain ⟨m', hrun, hSR'⟩ := h m a hSR hPre
  obtain ⟨n, hn, hsteps, hhalt⟩ := steps_of_lsemFuelMemF isa _ fuel m m' hrun
  exact ⟨n, m', hn, steps_relocate isa fn post hreloc hfresh hsteps, hhalt, hSR'⟩

/-- **The run of the larger program at the instruction set with calls.** Let `B` contain no
    call and no return, correspond to `fa` at fuel `fuel` and satisfy the exit contract
    `ExitFrame`. Under `StepRelocates` and `LabelsFresh`, from the shift of a state `m`
    related by `SR` to `a` under `Pre`, the program `pre ++ B ++ post` makes at
    `isa.withCalls` a segment of `n ≤ fuel` steps to the shift of a state `m'` related to
    `fa a` and framed against `m`; the end state is at the counter
    `pre.length + B.length`. -/
theorem corresIsa_relocate_run_withCalls (isa : Isa) {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false) (hreloc : StepRelocates isa fn pre B post)
    (hfresh : LabelsFresh pre B) (h : CorresIsa isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame isa fn B SR Pre Frame fuel) {m : LstateMF} {a : A}
    (hSR : SR m a) (hPre : Pre a) :
    ∃ n m', n ≤ fuel ∧
      Steps isa.withCalls (singletonProgM fn (pre ++ B ++ post)) n (shiftPc pre.length m)
        (shiftPc pre.length m') ∧
      atPc (singletonProgM fn (pre ++ B ++ post)) (pre.length + B.length)
        (shiftPc pre.length m') ∧
      SR m' (fa a) ∧ Frame m m' ∧ RetFrame isa.sp m m' := by
  obtain ⟨m', hrun, hSR'⟩ := h m a hSR hPre
  obtain ⟨hend, hF, hRF⟩ := hexit m a m' hSR hPre hrun
  obtain ⟨n, hn, hsteps, _⟩ := steps_of_lsemFuelMemF isa _ fuel m m' hrun
  exact ⟨n, m', hn, steps_relocate_withCalls isa fn post hB hreloc hfresh hsteps,
    atPc_relocate fn pre B post hend, hSR', hF, hRF⟩

/-! ## The procedure specification of a relocated callee -/

/-- The relation `SR` at the offset `k`: the state is the shift by `k` of a state related by
    `SR`. -/
def relocRel (k : Nat) (SR : LstateMF → A → Prop) : LstateMF → A → Prop :=
  fun m a => ∃ m₀, m = shiftPc k m₀ ∧ SR m₀ a

/-- The frame relation `Frame` at the offset `k`: the two states are the shifts by `k` of
    two states related by `Frame`. -/
def relocFrame (k : Nat) (Frame : LstateMF → LstateMF → Prop) :
    LstateMF → LstateMF → Prop :=
  fun m m' => ∃ m₀ m₀', m = shiftPc k m₀ ∧ m' = shiftPc k m₀' ∧ Frame m₀ m₀'

/-- A state at the counter `k + j` is related at the offset `k` when the state with the
    counter `j` is related. -/
theorem relocRel_of_atPc {k j : Nat} {SR : LstateMF → A → Prop} {m : LstateMF} {a : A}
    (hpc : m.prog.base.lpc = k + j) (h : SR (goto m j) a) : relocRel k SR m a := by
  refine ⟨goto m j, ?_, h⟩
  show m = goto m (k + j)
  rw [← hpc]
  exact (goto_lpc_self m).symm

/-- The state after a call step to a label declared at the index `q` is related at the
    offset `q + 1` when the state with the counter `0` is related. -/
theorem relocRel_callEntry {SR : LstateMF → A → Prop} (sp : String) (v : BitVec 64)
    (q : Nat) (m : LstateMF) {a : A} (h : SR (goto (callEntry sp v q m) 0) a) :
    relocRel (q + 1) SR (callEntry sp v q m) a :=
  relocRel_of_atPc (j := 0) rfl h

/-- The return that follows `B` in `pre ++ B ++ Lret :: post` is at the counter
    `pre.length + B.length`. -/
theorem getElem?_relocate_ret (pre B post : List LinstrRM) (tag : MemTag) :
    (pre ++ B ++ (LinstrR.Lret, tag) :: post)[pre.length + B.length]? =
      some (LinstrR.Lret, tag) := by
  rw [← List.length_append, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- **The procedure specification of a relocated callee.** Let `B` contain no call and no
    return, correspond to `fa` at fuel `fuel` and satisfy the exit contract `ExitFrame`, and
    let `StepRelocates` and `LabelsFresh` hold for `B` between `pre` and `Lret :: post`. For
    every label `l`, the program `pre ++ B ++ Lret :: post` satisfies at `isa.withCalls` the
    specification of a procedure at `l` that returns at the counter `pre.length + B.length`,
    with the relation and the frame of the body at the offset `pre.length`, the
    precondition and the abstraction of the body and the step bound `fuel`. The
    specification constrains the states that are shifts by `pre.length` of states related
    by `SR`. -/
theorem procSpec_relocate_of_corresIsa (isa : Isa) {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) (tag : MemTag) (l : LLabel) {SR : LstateMF → A → Prop}
    {Pre : A → Prop} {fa : A → A} {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false)
    (hreloc : StepRelocates isa fn pre B ((.Lret, tag) :: post))
    (hfresh : LabelsFresh pre B) (h : CorresIsa isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame isa fn B SR Pre Frame fuel) :
    ProcSpec isa.withCalls (singletonProgM fn (pre ++ B ++ (.Lret, tag) :: post)) l
      (pre.length + B.length) (relocRel pre.length SR) Pre fa (relocFrame pre.length Frame)
      fuel := by
  intro m a _ hSR hPre
  obtain ⟨m₀, rfl, hSR₀⟩ := hSR
  obtain ⟨n, m', hn, hsteps, hat, hSR', hF, hRF⟩ :=
    corresIsa_relocate_run_withCalls isa ((.Lret, tag) :: post) hB hreloc hfresh h hexit
      hSR₀ hPre
  exact ⟨n, shiftPc pre.length m', hn, hsteps, hat, ⟨m', rfl, hSR'⟩, ⟨m₀, m', rfl, rfl, hF⟩,
    retFrame_shiftPc _ _ hRF⟩

/-- **The procedure specification of a labelled callee inside a larger program.** The
    instance of `procSpec_relocate_of_corresIsa` for a body `B` placed after the declaration
    of the label `l` that follows `pre`: the callee is entered at the counter
    `pre.length + 1`, where a call to `l` lands when `l` is absent from `pre`
    (`findLabelMem_append_label`), and returns at the counter
    `pre.length + 1 + B.length`. -/
theorem procSpec_labelled_of_corresIsa (isa : Isa) {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) (kind : LabelKind) (tagl tag : MemTag) (l : LLabel)
    {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false)
    (hreloc : StepRelocates isa fn (pre ++ [(.Llabel kind l, tagl)]) B
      ((.Lret, tag) :: post))
    (hfresh : LabelsFresh (pre ++ [(.Llabel kind l, tagl)]) B)
    (h : CorresIsa isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame isa fn B SR Pre Frame fuel) :
    ProcSpec isa.withCalls
      (singletonProgM fn (pre ++ [(.Llabel kind l, tagl)] ++ B ++ (.Lret, tag) :: post)) l
      (pre.length + 1 + B.length) (relocRel (pre.length + 1) SR) Pre fa
      (relocFrame (pre.length + 1) Frame) fuel := by
  have hspec := procSpec_relocate_of_corresIsa isa post tag l hB hreloc hfresh h hexit
  rwa [List.length_append, List.length_singleton] at hspec

end Generic

end IsaCall

end CatCrypt.Crypto.SecureCompilation.Ascent
