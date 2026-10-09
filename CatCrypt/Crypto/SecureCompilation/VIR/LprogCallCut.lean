/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaRelocX86
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked

@[expose] public section

set_option autoImplicit false

/-!
# The cut of a body at the shadow instructions of calls

A body `B` with shadow instructions of calls of a procedure table `T` runs on the
instruction set `I.withProcs T`. This module cuts such a run at the shadow instructions: a
run is a chain of segments on the instruction set `I`, each from the entry of the body or
from the position after a shadow instruction to the next shadow instruction or to the end
of the body, and consecutive segments are joined by the step `procStep` of the summary of
the procedure.

Each segment is a halting run from the counter `0` of a cut program. The cut program
`cutAt fn fin B e x` for the entry `e` (`none` is the entry of the body, `some p` the
position after the shadow instruction at `p`) and the exit `x` (`none` is the end of the
body, `some p` the shadow instruction at `p`) is the body rotated so that the entry
position is first, with a jump to the last label `fin` at the exit position, and with the
other shadow instructions unchanged. The position map `cutPos B e` sends a position of
`B` to its position in the cut program. The relation between a body, a cut program and a
position map that the run statement uses is `IsCut`; `isCutB` decides it, and `cutOkB`
checks it for every pair of an entry and an exit of `cutAt`.

## Main definitions

* `isProcB`, `sites`: the recogniser of a shadow instruction of a call of a symbol of the
  table, and the positions of such instructions in a body.
* `SegTo`, `Glue`, `RunChain`: a segment of a body on `I` to a shadow instruction or to a
  halted state, the step of the summary at a shadow instruction, and a chain of segments.
* `PcFree`: the branch condition of an instruction set does not read the counter, and the
  step of a non-control instruction commutes with setting the counter and does not read
  the program.
* `entryPos`, `stopPos`, `IsCut`, `isCutB`: the positions of an entry and of an exit, the
  relation of a body to a cut program along a position map, and its decision procedure.
* `cutAt`, `cutPos`, `cutOkB`: the cut program, its position map and the check of `IsCut`
  on every cut program of a body.
* `CutRun`, `CutChain`: a halting run of a cut program from the counter `0`, and a chain of
  such runs joined by `Glue`.
* `CutSimI`, `CutSim`: a simulation of the cut programs of one body by those of another on
  an instruction set, and at `x86Isa`.
* `CutCheckSoundI`, `CutCheckSound`: the statement of soundness of a validation of the cut
  programs of two bodies, segment by segment, on an instruction set and at `x86Isa`.
* `shadowFreeB`, `poolAbi`, `lfundefPhysAbiOfVirtAt`: the bodies `expandCallShadows` leaves
  in place, the x86 register file at an allocation pool, and the allocation of a virtual
  function at a pool with the shadow instructions expanded after the allocation.
* `movI`, `commonSeq`, `commonCall?`, `commonCalls?`: the form of a shadow instruction on
  the argument and result names of its callee, and the rewriting of a body onto them.
* `runI`, `regUpd`, `movesF`: the run of an instruction list without the counter, a state
  with a new register file and an advanced counter, and the state after a list of copies.
* `offCongrB`, `commonCongrB`: the check that the described step of an instruction reads
  no name of a list, and the same for every instruction and branch condition of a body.
* `commonFreshB`: the check that the common names are distinct, occur in no operation of a
  body, and that the body passes `commonCongrB` at them.
* `setRL`, `OffRel`, `expPos`: a state with a register file and a counter, the relation of
  a state of a body to a state of its rewritten body, and the position map of the rewriting.
* `OffCongr`, `CondCongr`: the step of an instruction commutes with a change of a set of
  names, and a branch condition does not read them.
* `FnStable`, `IsCutRev`, `isCutRevB`: the steps of an instruction set stay in the function,
  a cut program halts only at its exit, and the check of the latter.
* `renFin`: the goto to the last label of a cut program sent to another function.

## Main results

* `runChain_of_run`, `run_of_runChain`: a halting run of `I.withProcs T` is a chain of
  segments of `I`, and conversely when `I` refuses the procedures of `T`.
* `x86Isa_pcFree`, `fnStable_x86Isa`: `PcFree x86Isa` and `FnStable x86Isa`.
* `steps_emb`, `cutRun_of_segTo`: a segment of the body is a run of a cut program.
* `isCut_of_isCutB`: soundness of `isCutB`.
* `withProcs_run_cut`: a halting run of `I.withProcs T` on a body from the counter `0` is
  a chain of halting runs of cut programs on `I`.
* `x86_withProcs_run_cutAt`: the same at `x86Isa` for the cut programs `cutAt` of a body
  that `cutOkB` accepts.
* `expandCallShadows_of_shadowFreeB`, `lfundefPhysAbiOfVirtAt_default`: on a body without
  call shadows the expansion is the identity, and at the pool of `x86Abi` the allocation
  with shadow instructions is `lfundefPhysAbiOfVirt`.
* `shadowCall?_commonCalls?`: every shadow instruction of a rewritten body is a call of the
  callee on its argument names with its result name.
* `commonCall_sim`: the step of the summary at a shadow instruction is the run of its form
  on common names, up to the argument names and the result name.
* `commonFreshB_site`: a body that passes `commonFreshB` meets the side conditions of
  `commonCall_sim` at each of its shadow instructions.
* `findLabelMem_commonCalls?`: a label of the body is declared in the rewritten body at the
  image of its position.
* `step_common`, `commonCalls_run`, `commonCalls_run_obs`: a halting run of the body on the
  x86 instruction set with procedures is a halting run of the rewritten body, the end states
  related by `OffRel`, under `OffCongr` for the operations and `CondCongr` for the branch
  conditions of the body.
* `offCongr_of_offCongrB`, `commonCongrB_offCongr`, `commonCongrB_condCongr`: `OffCongr`
  and `CondCongr` from the checks.
* `run_onCommonNames`, `obs_onCommonNames`: the two run statements for a body that passes
  `commonFreshB`, with no further premise.
* `segTo_of_cutRun`: a halting run of a cut program that halts only at its exit is a
  segment of the body.
* `map_renFin_cutAt`, `IsCut.rename`, `isCut_cutAt_of_cutOkB`, `isCutRev_cutAt_rename`: for a
  body with no jump to the label `fin`, the cut programs at one function name are those at
  another under `renFin`, and the cut checks at one function name give `IsCut` and
  `IsCutRev` at every function name.
* `runChain_of_cutChainI`, `cutCheck_soundI`: `CutCheckSoundI I` for cut programs of the
  second body that halt only at their exits, on an instruction set `I` with `PcFree I`,
  `I.RefusesProcs T` and `FnStable I`.
* `runChain_of_cutChain`, `cutCheck_sound`: the same at `x86Isa`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel findLabel_sound
  findLabel_lt_length isLabel)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (x86Isa_refusesProcs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (steps_of_lsemFuelMemF
  steps_of_step_sim evalInstrPMemF_goto)

/-! ## 1. Shadow instructions of the table -/

/-- The instruction is a shadow instruction of a call of a symbol of the table `T`. -/
def isProcB (T : ProcTable) (i : LinstrRM) : Bool := (procCall? T i.fst).isSome

/-- The positions of the shadow instructions of calls of symbols of `T` in the body `B`. -/
def sites (T : ProcTable) (B : List LinstrRM) : List Nat :=
  (List.range B.length).filter fun p => (B[p]?).any (isProcB T)

/-! ## 2. Segments of the body and their chain -/

/-- **A segment of the program `P` on the instruction set `I`** from `s` to `u`: a run of
    steps of `I` that ends, for `x = none`, in a halted state, and for `x = some p`, at the
    counter `p`, which holds a shadow instruction of a call of a symbol of `T`. -/
def SegTo (I : Isa) (T : ProcTable) (P : LprogM) (s : LstateMF) (x : Option Nat)
    (u : LstateMF) : Prop :=
  ∃ n, Steps I P n s u ∧
    match x with
    | none => Halted P u
    | some p => atPc P p u ∧ ∃ i, P.body[p]? = some i ∧ isProcB T i = true

/-- **The step of the summary at the position `p`**: the instruction of `P` at `p` is a
    shadow instruction of a call of a symbol of `T`, and `v` is the state after the step
    `procStep` of the summary of the symbol from `u`. -/
def Glue (T : ProcTable) (P : LprogM) (p : Nat) (u v : LstateMF) : Prop :=
  ∃ i pr dst srcs, P.body[p]? = some i ∧ procCall? T i.fst = some (pr, dst, srcs) ∧
    procStep pr dst srcs u = some v

/-- **A chain of segments** of `P` on `I` from `s` to `t`: a segment to a halted state `t`,
    or a segment to a shadow instruction, the step of the summary, and a chain from the
    state after it. -/
inductive RunChain (I : Isa) (T : ProcTable) (P : LprogM) : LstateMF → LstateMF → Prop
  | done {s t : LstateMF} : SegTo I T P s none t → RunChain I T P s t
  | call {s u v t : LstateMF} (p : Nat) : SegTo I T P s (some p) u → Glue T P p u v →
      RunChain I T P v t → RunChain I T P s t

/-- A step of `I` in front of a chain. -/
theorem RunChain.step_cons {I : Isa} {T : ProcTable} {P : LprogM} {s u t : LstateMF}
    (h : I.lsemStepPMemF P s = some u) (hc : RunChain I T P u t) : RunChain I T P s t := by
  cases hc with
  | done hseg =>
      obtain ⟨n, hn, hx⟩ := hseg
      exact .done ⟨1 + n, (Steps.one h).trans hn, hx⟩
  | call p hseg hg hrest =>
      obtain ⟨n, hn, hx⟩ := hseg
      exact .call p ⟨1 + n, (Steps.one h).trans hn, hx⟩ hg hrest

/-- A run of steps of `I.withProcs T` to a halted state is a chain of segments of `I`. -/
theorem runChain_of_steps (I : Isa) (T : ProcTable) (P : LprogM) :
    ∀ (n : Nat) (s t : LstateMF), Steps (I.withProcs T) P n s t → Halted P t →
      RunChain I T P s t
  | 0, s, t, h, ht => by
      have hst : s = t := Option.some.inj h
      subst hst
      exact .done ⟨0, Steps.refl I P s, ht⟩
  | n + 1, s, t, h, ht => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨u, hu, h⟩ := h
      have ih := runChain_of_steps I T P n u t h ht
      unfold Isa.lsemStepPMemF at hu
      cases hf : findInstrMem P s.prog with
      | none => rw [hf] at hu; cases hu
      | some i =>
          rw [hf] at hu
          replace hu : (I.withProcs T).step P i s = some u := hu
          cases hq : procCall? T i.fst with
          | none =>
              rw [I.withProcs_step_of_none T P i s hq] at hu
              refine RunChain.step_cons ?_ ih
              unfold Isa.lsemStepPMemF
              rw [hf]
              exact hu
          | some q =>
              obtain ⟨pr, dst, srcs⟩ := q
              have hstep : procStep pr dst srcs s = some u := by
                simpa only [Isa.withProcs, hq] using hu
              unfold findInstrMem at hf
              split at hf
              · rename_i hfn
                exact .call s.prog.base.lpc
                  ⟨0, Steps.refl I P s, ⟨hfn, rfl⟩, i, hf, by simp only [isProcB, hq,
                    Option.isSome_some]⟩
                  ⟨i, pr, dst, srcs, hf, hq, hstep⟩ ih
              · cases hf

/-- **A halting run of `I.withProcs T` is a chain of segments of `I`.** -/
theorem runChain_of_run (I : Isa) (T : ProcTable) (P : LprogM) (n : Nat) (s t : LstateMF)
    (h : (I.withProcs T).lsemFuelMemF P n s = some t) : RunChain I T P s t := by
  obtain ⟨k, -, hk, ht⟩ := steps_of_lsemFuelMemF (I.withProcs T) P n s t h
  exact runChain_of_steps I T P k s t hk ht

/-- **A chain of segments of `I` is a halting run of `I.withProcs T`**, when `I` has no
    step on a shadow instruction of a call of a symbol of `T`. -/
theorem run_of_runChain {I : Isa} {T : ProcTable} {P : LprogM} (hR : I.RefusesProcs T)
    {s t : LstateMF} (h : RunChain I T P s t) :
    ∃ n, ∀ j, (I.withProcs T).lsemFuelMemF P (n + j) s = some t := by
  have hle : ∀ {n : Nat} {a b : LstateMF}, Steps I P n a b →
      Steps (I.withProcs T) P n a b := fun {n a b} hs =>
    steps_of_step_sim I (I.withProcs T) (P := P) (P' := P) id (fun a b hab => by
      simp only [id]
      unfold Isa.lsemStepPMemF at hab ⊢
      cases hf : findInstrMem P a.prog with
      | none => rw [hf] at hab; cases hab
      | some i =>
          rw [hf] at hab
          exact I.withProcs_stepLe hR P i a b hab) hs
  have key : ∃ n, Steps (I.withProcs T) P n s t ∧ Halted P t := by
    induction h with
    | done hseg =>
        obtain ⟨n, hn, hx⟩ := hseg
        exact ⟨n, hle hn, hx⟩
    | call p hseg hg _ ih =>
        obtain ⟨n, hn, hat, -⟩ := hseg
        obtain ⟨i, pr, dst, srcs, hi, hq, hstep⟩ := hg
        obtain ⟨m, hm, ht⟩ := ih
        refine ⟨n + (1 + m), (hle hn).trans ((Steps.one ?_).trans hm), ht⟩
        rw [lsemStepPMemF_of_atPc (I.withProcs T) hat hi]
        simpa only [Isa.withProcs, hq] using hstep
  obtain ⟨n, hn, ht⟩ := key
  exact ⟨n, fun j => lsemFuelMemF_of_steps (I.withProcs T) P hn ht j⟩

/-! ## 3. Instruction sets that do not read the counter -/

/-- **The steps of `I` do not read the counter.** The branch condition at a state with the
    counter set to `q` is the branch condition at the state, and the step of a non-control
    instruction on a program `P'` from a state with the counter set to `q` is the step on
    any program `P` from the state, followed by setting the counter to `q + 1`. -/
structure PcFree (I : Isa) : Prop where
  cond : ∀ (s : LstateMF) (q : Nat) (c : LOperand), I.condEval (goto s q) c = I.condEval s c
  step : ∀ (P P' : LprogM) (i : LinstrRM), isCtl i.fst = false → ∀ (s : LstateMF) (q : Nat),
    I.step P' i (goto s q) = (I.step P i s).map fun u => goto u (q + 1)

/-- The steps of the x86 instruction set do not read the counter. -/
theorem x86Isa_pcFree : PcFree x86Isa :=
  ⟨fun _ _ _ => rfl, fun P P' i hi s q => by
    rw [x86Isa_step]
    exact evalInstrPMemF_goto P P' hi s q⟩

/-- A successful step of a non-control instruction advances the counter by one. -/
theorem PcFree.lpc_succ {I : Isa} (hI : PcFree I) (P : LprogM) {i : LinstrRM}
    (hi : isCtl i.fst = false) {s u : LstateMF} (h : I.step P i s = some u) :
    u = goto u (s.prog.base.lpc + 1) := by
  have hg := hI.step P P i hi s s.prog.base.lpc
  rw [show goto s s.prog.base.lpc = s from rfl, h] at hg
  exact Option.some.inj hg

/-! ## 4. Cut programs -/

/-- The position of an entry: `none` is the entry of the body, `some p` the position after
    the shadow instruction at `p`. -/
def entryPos : Option Nat → Nat
  | none => 0
  | some p => p + 1

/-- The position of an exit of the body `B`: `none` is the end of the body, `some p` the
    shadow instruction at `p`. -/
def stopPos (B : List LinstrRM) : Option Nat → Nat
  | none => B.length
  | some p => p

/-- **The body `C` is a cut of the body `B` along the position map `φ`**, for the entry `e`
    and the exit `x`: the entry position is sent to `0`; an instruction of `B` that is no
    shadow instruction of a call of a symbol of `T` is the instruction of `C` at the image
    of its position, and the image of the next position is the next position; a label
    declared in `B` at `q` is declared in `C` at the image of `q`; and the image of the
    exit position holds a jump to a label declared at the last position of `C`. -/
structure IsCut (T : ProcTable) (fn : String) (B : List LinstrRM) (e x : Option Nat)
    (C : List LinstrRM) (φ : Nat → Nat) : Prop where
  entry : φ (entryPos e) = 0
  instr : ∀ (p : Nat) (i : LinstrRM), B[p]? = some i → procCall? T i.fst = none →
    C[φ p]? = some i ∧ φ (p + 1) = φ p + 1
  label : ∀ (l : LLabel) (q : Nat), findLabelMem l B = some q → findLabelMem l C = some (φ q)
  exit : ∃ (tag : MemTag) (fin : LLabel) (k : Nat),
    C[φ (stopPos B x)]? = some (.Lgoto (fn, fin), tag) ∧ findLabelMem fin C = some k ∧
      k + 1 = C.length

/-- The state `s` at the image of its counter under the position map `φ`. -/
def emb (φ : Nat → Nat) (s : LstateMF) : LstateMF := goto s (φ s.prog.base.lpc)

/-- A label declared in `B` at `q`: `q` is a position of `B`, and the image of the next
    position is the next position. -/
theorem IsCut.label_succ {T : ProcTable} {fn : String} {B : List LinstrRM} {e x : Option Nat}
    {C : List LinstrRM} {φ : Nat → Nat} (hc : IsCut T fn B e x C φ) {l : LLabel} {q : Nat}
    (hl : findLabelMem l B = some q) : q + 1 ≤ B.length ∧ φ (q + 1) = φ q + 1 := by
  unfold findLabelMem at hl
  have hlt := findLabel_lt_length l _ q hl
  rw [List.length_map] at hlt
  obtain ⟨k, hk, hlab⟩ := findLabel_sound l _ q hl
  rw [List.getElem?_map] at hk
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hk
  refine ⟨hlt, (hc.instr q i hi ?_).2⟩
  have hctl : isCtl i.fst = true := by
    cases hi' : i.fst <;> simp_all [isLabel, isCtl]
  simp only [procCall?, shadowCall?_of_isCtl hctl, Option.bind_none]

/-- **One step of the body is one step of a cut program.** A step of `I` on `B` from `s`
    to `u` is a step of `I` on `C` from the image of `s` to the image of `u`, and the
    counter of `u` is at most the length of `B`. -/
theorem step_emb {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {e x : Option Nat} {C : List LinstrRM} {φ : Nat → Nat} (hI : PcFree I)
    (hR : I.RefusesProcs T) (hc : IsCut T fn B e x C φ) {s u : LstateMF}
    (h : I.lsemStepPMemF (singletonProgM fn B) s = some u) :
    I.lsemStepPMemF (singletonProgM fn C) (emb φ s) = some (emb φ u) ∧
      u.prog.base.lpc ≤ B.length := by
  unfold Isa.lsemStepPMemF at h
  cases hf : findInstrMem (singletonProgM fn B) s.prog with
  | none => rw [hf] at h; cases h
  | some i =>
      rw [hf] at h
      replace h : I.step (singletonProgM fn B) i s = some u := h
      unfold findInstrMem at hf
      split at hf
      · rename_i hfn
        replace hf : B[s.prog.base.lpc]? = some i := hf
        have hlt : s.prog.base.lpc < B.length := (List.getElem?_eq_some_iff.mp hf).1
        have hq : procCall? T i.fst = none := by
          by_contra hne
          rw [hR _ i s hne] at h
          cases h
        obtain ⟨hCi, hφ⟩ := hc.instr _ i hf hq
        have hfetch : findInstrMem (singletonProgM fn C) (emb φ s).prog = some i := by
          unfold findInstrMem
          rw [if_pos (show (emb φ s).prog.lfn = (singletonProgM fn C).lfn from hfn)]
          exact hCi
        unfold Isa.lsemStepPMemF
        rw [hfetch]
        show I.step (singletonProgM fn C) i (emb φ s) = some (emb φ u) ∧ _
        cases hctl : isCtl i.fst with
        | false =>
            have hu := hI.lpc_succ _ hctl h
            have hpc : u.prog.base.lpc = s.prog.base.lpc + 1 := by rw [hu]; rfl
            refine ⟨?_, by omega⟩
            rw [emb, hI.step (singletonProgM fn B) (singletonProgM fn C) i hctl s, h, emb, hpc,
              hφ]
            rfl
        | true =>
            rw [I.step_ctl _ i s hctl] at h
            rw [I.step_ctl _ i _ hctl]
            obtain ⟨ir, tag⟩ := i
            cases ir with
            | Llabel k l =>
                simp only [ctlStep, Option.some.injEq] at h ⊢
                subst h
                refine ⟨?_, by
                  simp only [JasminLsemMemLoop.LstateM.lpc_nextPc]; omega⟩
                simp only [emb, goto, JasminLsemMemLoop.LstateM.lpc_nextPc, hφ]
                rfl
            | Lcond c l =>
                simp only [ctlStep] at h ⊢
                rw [show I.condEval (emb φ s) c = I.condEval s c from hI.cond s _ c]
                split at h
                · rw [if_pos (by assumption)]
                  unfold evalJumpMem at h ⊢
                  cases hl : findLabelMem l (singletonProgM fn B).body with
                  | none => rw [hl] at h; cases h
                  | some q =>
                      rw [hl] at h
                      obtain ⟨hql, hqφ⟩ := hc.label_succ hl
                      rw [show findLabelMem l (singletonProgM fn C).body = some (φ q) from
                        hc.label l q hl]
                      simp only [Option.map_some, Option.some.injEq] at h ⊢
                      subst h
                      refine ⟨?_, hql⟩
                      simp only [emb, goto, JasminLsemMemLoop.LstateM.lpc_setLpc, hqφ]
                      rfl
                · rw [if_neg (by assumption)]
                  simp only [Option.some.injEq] at h ⊢
                  subst h
                  refine ⟨?_, by
                    simp only [JasminLsemMemLoop.LstateM.lpc_nextPc]; omega⟩
                  simp only [emb, goto, JasminLsemMemLoop.LstateM.lpc_nextPc, hφ]
                  rfl
            | Lgoto tgt =>
                obtain ⟨f, l⟩ := tgt
                simp only [ctlStep] at h ⊢
                split at h
                · rw [if_pos (by assumption)]
                  unfold evalJumpMem at h ⊢
                  cases hl : findLabelMem l (singletonProgM fn B).body with
                  | none => rw [hl] at h; cases h
                  | some q =>
                      rw [hl] at h
                      obtain ⟨hql, hqφ⟩ := hc.label_succ hl
                      rw [show findLabelMem l (singletonProgM fn C).body = some (φ q) from
                        hc.label l q hl]
                      simp only [Option.map_some, Option.some.injEq] at h ⊢
                      subst h
                      refine ⟨?_, hql⟩
                      simp only [emb, goto, JasminLsemMemLoop.LstateM.lpc_setLpc, hqφ]
                      rfl
                · cases h
            | _ => simp [isCtl] at hctl
      · cases hf

/-- **A run of steps of the body is a run of steps of a cut program**, with the same
    number of steps, from the image of `s` to the image of `u`; the counter of `u` is at
    most the length of `B` when the counter of `s` is. -/
theorem steps_emb {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {e x : Option Nat} {C : List LinstrRM} {φ : Nat → Nat} (hI : PcFree I)
    (hR : I.RefusesProcs T) (hc : IsCut T fn B e x C φ) :
    ∀ (n : Nat) (s u : LstateMF), Steps I (singletonProgM fn B) n s u →
      s.prog.base.lpc ≤ B.length →
      Steps I (singletonProgM fn C) n (emb φ s) (emb φ u) ∧ u.prog.base.lpc ≤ B.length
  | 0, s, u, h, hle => by
      have hst : s = u := Option.some.inj h
      subst hst
      exact ⟨Steps.refl I _ _, hle⟩
  | n + 1, s, u, h, _ => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      obtain ⟨hm', hmle⟩ := step_emb hI hR hc hm
      obtain ⟨ih, hle⟩ := steps_emb hI hR hc n m u h hmle
      refine ⟨?_, hle⟩
      have := (Steps.one hm').trans ih
      rwa [Nat.add_comm] at this

/-- **The exit of a cut program.** From the image of a state of the function `fn` at the
    exit position, one step of `I` on `C` reaches the state with the counter at the length
    of `C`. -/
theorem exit_step {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {e x : Option Nat} {C : List LinstrRM} {φ : Nat → Nat} (hc : IsCut T fn B e x C φ)
    {w : LstateMF} (hfn : w.prog.lfn = fn) (hpc : w.prog.base.lpc = stopPos B x) :
    I.lsemStepPMemF (singletonProgM fn C) (emb φ w) = some (goto w C.length) := by
  obtain ⟨tag, fin, k, hi, hfin, hk⟩ := hc.exit
  have hat : atPc (singletonProgM fn C) (φ (stopPos B x)) (emb φ w) := ⟨hfn, by
    rw [emb, ← hpc]; rfl⟩
  rw [lsemStepPMemF_of_atPc I hat hi, I.step_goto,
    if_pos (show fn = (singletonProgM fn C).lfn from rfl)]
  unfold evalJumpMem
  rw [show findLabelMem fin (singletonProgM fn C).body = some k from hfin, ← hk]
  rfl

/-- **A halting run of the cut program `C` from the counter `0`**, from the state `s` with
    its counter set to `0` to the state `u` with its counter set to some position: the run
    function of `I` returns that state at every fuel from some bound on. -/
def CutRun (I : Isa) (fn : String) (C : List LinstrRM) (s u : LstateMF) : Prop :=
  ∃ k q, ∀ j, I.lsemFuelMemF (singletonProgM fn C) (k + j) (goto s 0) = some (goto u q)

/-- **A segment of the body is a halting run of a cut program.** Let `C` be a cut of `B`
    along `φ` for the entry `e` and the exit `x`. A segment of `B` on `I` from a state at
    the entry position, to the shadow instruction at `x` or to a halted state as `x`
    states, is a halting run of `C` on `I` from the counter `0` to the same state up to
    its counter. -/
theorem cutRun_of_segTo {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {e x : Option Nat} {C : List LinstrRM} {φ : Nat → Nat} (hI : PcFree I)
    (hR : I.RefusesProcs T) (hc : IsCut T fn B e x C φ) {s u : LstateMF}
    (hs : atPc (singletonProgM fn B) (entryPos e) s) (hle : entryPos e ≤ B.length)
    (h : SegTo I T (singletonProgM fn B) s x u) : CutRun I fn C s u := by
  obtain ⟨n, hn, hx⟩ := h
  obtain ⟨hsteps, hule⟩ := steps_emb hI hR hc n s u hn (by rw [hs.2]; exact hle)
  have hs0 : emb φ s = goto s 0 := by rw [emb, hs.2, hc.entry]
  rw [hs0] at hsteps
  have hexit : ∀ (hfn : u.prog.lfn = fn) (hpc : u.prog.base.lpc = stopPos B x),
      CutRun I fn C s u := fun hfn hpc =>
    ⟨n + 1, C.length, fun j => lsemFuelMemF_of_steps I _
      (hsteps.trans (Steps.one (exit_step hc hfn hpc)))
      (halted_of_atPc (P := singletonProgM fn C) ⟨hfn, rfl⟩ (Nat.le_refl _)) j⟩
  cases x with
  | some p => exact hexit hx.1.1 hx.1.2
  | none =>
      by_cases hfn : u.prog.lfn = fn
      · refine hexit hfn (Nat.le_antisymm hule ?_)
        have hh : findInstrMem (singletonProgM fn B) u.prog = none := hx
        unfold findInstrMem at hh
        rw [if_pos (show u.prog.lfn = (singletonProgM fn B).lfn from hfn)] at hh
        exact List.getElem?_eq_none_iff.mp hh
      · refine ⟨n, φ u.prog.base.lpc, fun j => lsemFuelMemF_of_steps I _ hsteps ?_ j⟩
        show findInstrMem (singletonProgM fn C) (emb φ u).prog = none
        unfold findInstrMem
        exact if_neg hfn

/-! ## 5. The chain of runs of cut programs -/

/-- An entry or an exit of the body `B`: `none`, or the position of a shadow instruction of
    a call of a symbol of `T`. -/
def IsSite (T : ProcTable) (B : List LinstrRM) : Option Nat → Prop
  | none => True
  | some p => ∃ i, B[p]? = some i ∧ isProcB T i = true

/-- **A chain of halting runs of cut programs** of the body `B` on `I`, from the state `s`
    at the entry `e` to the state `t`. With `cut e x` the cut program for the entry `e` and
    the exit `x`: a halting run of `cut e none` from `s` to the halted state `t`; or a
    halting run of `cut e (some p)` from `s` to a state `u` at the shadow instruction at
    `p`, the step of the summary from `u` to `v`, and a chain from `v` at the entry
    `some p`. Each run starts at the counter `0`. -/
inductive CutChain (I : Isa) (T : ProcTable) (fn : String) (B : List LinstrRM)
    (cut : Option Nat → Option Nat → List LinstrRM) : Option Nat → LstateMF → LstateMF → Prop
  | done {e : Option Nat} {s t : LstateMF} : CutRun I fn (cut e none) s t →
      Halted (singletonProgM fn B) t → CutChain I T fn B cut e s t
  | call {e : Option Nat} {s u v t : LstateMF} (p : Nat) :
      CutRun I fn (cut e (some p)) s u → atPc (singletonProgM fn B) p u →
      Glue T (singletonProgM fn B) p u v → CutChain I T fn B cut (some p) v t →
      CutChain I T fn B cut e s t

/-- The state after the step of the summary at the position `p` is at the position after
    `p`. -/
theorem Glue.atPc_succ {T : ProcTable} {P : LprogM} {p : Nat} {u v : LstateMF}
    (hu : atPc P p u) (hg : Glue T P p u v) : atPc P (p + 1) v := by
  obtain ⟨i, pr, dst, srcs, -, -, hstep⟩ := hg
  unfold procStep at hstep
  split at hstep
  · obtain ⟨vs, -, hstep⟩ := Option.bind_eq_some_iff.mp hstep
    obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp hstep
    exact ⟨(lfn_retRes dst x u).trans hu.1, by rw [lpc_retRes, hu.2]⟩
  · cases hstep

/-- **A chain of segments of the body is a chain of halting runs of cut programs.** -/
theorem cutChain_of_runChain {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {cut : Option Nat → Option Nat → List LinstrRM} {pos : Option Nat → Option Nat → Nat → Nat}
    (hI : PcFree I) (hR : I.RefusesProcs T)
    (hcut : ∀ e x, IsSite T B e → IsSite T B x → IsCut T fn B e x (cut e x) (pos e x))
    {s t : LstateMF} (h : RunChain I T (singletonProgM fn B) s t) :
    ∀ (e : Option Nat), IsSite T B e → atPc (singletonProgM fn B) (entryPos e) s →
      CutChain I T fn B cut e s t := by
  have hle : ∀ e, IsSite T B e → entryPos e ≤ B.length := by
    intro e he
    cases e with
    | none => exact Nat.zero_le _
    | some p =>
        obtain ⟨i, hi, -⟩ := he
        exact (List.getElem?_eq_some_iff.mp hi).1
  induction h with
  | done hseg =>
      intro e he hs
      exact .done (cutRun_of_segTo hI hR (hcut e none he trivial) hs (hle e he) hseg)
        (by obtain ⟨_, _, hh⟩ := hseg; exact hh)
  | @call s₁ u₁ v₁ t₁ p hseg hg _ ih =>
      intro e he hs
      have hp : IsSite T B (some p) := by
        obtain ⟨_, _, _, hi⟩ := hseg
        exact hi
      have hu : atPc (singletonProgM fn B) p u₁ := by
        obtain ⟨_, _, hat, _⟩ := hseg
        exact hat
      exact .call p (cutRun_of_segTo hI hR (hcut e (some p) he hp) hs (hle e he) hseg) hu hg
        (ih (some p) hp (hg.atPc_succ hu))

/-- **A halting run on the instruction set with procedures is a chain of halting runs of
    cut programs on the plain instruction set.** Let the steps of `I` not read the counter,
    let `I` have no step on a shadow instruction of a call of a symbol of `T`, and let
    `cut e x` be a cut of `B` along `pos e x` for every entry `e` and exit `x` of `B`. A
    halting run of `I.withProcs T` on the body `B` of the function `fn`, from a state `s`
    of `fn` at the counter `0` to `t`, is a chain `CutChain` from `s` at the entry of the
    body to `t`. -/
theorem withProcs_run_cut {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {cut : Option Nat → Option Nat → List LinstrRM} {pos : Option Nat → Option Nat → Nat → Nat}
    (hI : PcFree I) (hR : I.RefusesProcs T)
    (hcut : ∀ e x, IsSite T B e → IsSite T B x → IsCut T fn B e x (cut e x) (pos e x))
    (n : Nat) (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (hrun : (I.withProcs T).lsemFuelMemF (singletonProgM fn B) n s = some t) :
    CutChain I T fn B cut none s t :=
  cutChain_of_runChain hI hR hcut (runChain_of_run I T _ n s t hrun) none trivial ⟨hfn, hpc⟩

/-! ## 6. The decision procedure of `IsCut` -/

section Check

variable [DecidableEq LinstrR]

/-- **The check of `IsCut`**: the entry position is sent to `0`; at every position of `B`
    that holds no shadow instruction of a call of a symbol of `T`, `C` holds the same
    instruction at the image and the image of the next position is the next position; at
    every position of `B` that is the first declaration of its label, `C` declares the
    label first at the image; and the image of the exit position holds a jump, within `fn`,
    to a label first declared at the last position of `C`. -/
def isCutB (T : ProcTable) (fn : String) (B : List LinstrRM) (e x : Option Nat)
    (C : List LinstrRM) (φ : Nat → Nat) : Bool :=
  decide (φ (entryPos e) = 0) &&
  (List.range B.length).all (fun p =>
    match B[p]? with
    | some i => (procCall? T i.fst).isSome ||
        (decide (C[φ p]? = some i) && decide (φ (p + 1) = φ p + 1))
    | none => true) &&
  (List.range B.length).all (fun q =>
    match B[q]? with
    | some (.Llabel _ l, _) =>
        !decide (findLabelMem l B = some q) || decide (findLabelMem l C = some (φ q))
    | _ => true) &&
  (match C[φ (stopPos B x)]? with
    | some (.Lgoto (f, fin), _) =>
        decide (f = fn) && decide ((findLabelMem fin C).map (· + 1) = some C.length)
    | _ => false)

/-- **Soundness of `isCutB`.** -/
theorem isCut_of_isCutB {T : ProcTable} {fn : String} {B : List LinstrRM} {e x : Option Nat}
    {C : List LinstrRM} {φ : Nat → Nat} (h : isCutB T fn B e x C φ = true) :
    IsCut T fn B e x C φ := by
  simp only [isCutB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨he, hi⟩, hl⟩, hx⟩ := h
  refine ⟨he, ?_, ?_, ?_⟩
  · intro p i hp hq
    have hpi := hi p (List.getElem?_eq_some_iff.mp hp).1
    rw [hp] at hpi
    simpa [hq] using hpi
  · intro l q hlq
    have hlq' := hlq
    unfold findLabelMem at hlq'
    have hlt := findLabel_lt_length l _ q hlq'
    rw [List.length_map] at hlt
    obtain ⟨k, hk, hlab⟩ := findLabel_sound l _ q hlq'
    rw [List.getElem?_map] at hk
    obtain ⟨i, hi', rfl⟩ := Option.map_eq_some_iff.mp hk
    have hq := hl q hlt
    rw [hi'] at hq
    obtain ⟨ir, tag⟩ := i
    cases ir with
    | Llabel kd l' =>
        have hll : l = l' := by simpa [isLabel] using hlab
        subst hll
        simpa [hlq] using hq
    | _ => simp [isLabel] at hlab
  · split at hx
    · rename_i f fin tag hC
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      obtain ⟨rfl, hfin⟩ := hx
      obtain ⟨k, hk, hk'⟩ := Option.map_eq_some_iff.mp hfin
      exact ⟨tag, fin, k, hC, hk, hk'⟩
    · cases hx

end Check

/-! ## 7. The cut programs of a body -/

/-- The jump to the label `fin` within the function `fn`. -/
def exitI (fn : String) (fin : LLabel) : LinstrRM := (.Lgoto (fn, fin), .reg none)

/-- The declaration of the label `fin`. -/
def finI (fin : LLabel) : LinstrRM := (.Llabel .internal fin, .reg none)

/-- **The cut program of the body `B`** of the function `fn` for the entry `e` and the exit
    `x`, with the label `fin`. In `B`, the shadow instruction at the exit `x = some p` is
    replaced by the jump to `fin`. For the entry `none` the result is followed by the
    instruction of the end of the body and the declaration of `fin`; for the entry
    `some p` the instructions after `p` come first, then the instruction of the end of the
    body, the instructions before `p`, the instruction at `p`, and the declaration of
    `fin`. The instruction of the end of the body is the jump to `fin` for the exit `none`
    and the shadow instruction of the exit otherwise. -/
def cutAt (fn : String) (fin : LLabel) (B : List LinstrRM) (e x : Option Nat) :
    List LinstrRM :=
  let B' := match x with
    | none => B
    | some p => B.set p (exitI fn fin)
  let O := match x with
    | none => exitI fn fin
    | some p => (B[p]?).getD (exitI fn fin)
  match e with
  | none => B' ++ [O, finI fin]
  | some p => B'.drop (p + 1) ++ [O] ++ B'.take p ++ [(B'[p]?).getD O, finI fin]

/-- **The position map of the cut programs** of `B` for the entry `e`: the identity for the
    entry `none`; for the entry `some p`, a position after `p` moves to the front and a
    position up to `p` moves behind the instructions after `p` and the instruction of the
    end of the body. -/
def cutPos (B : List LinstrRM) : Option Nat → Nat → Nat
  | none, j => j
  | some p, j => if p < j then j - (p + 1) else j + (B.length - p)

section CutOk

variable [DecidableEq LinstrR]

/-- **The check of the cut programs of a body**: `isCutB` accepts `cutAt fn fin B e x`
    along `cutPos B e` for every entry `e` and every exit `x` of `B`. -/
def cutOkB (T : ProcTable) (fn : String) (fin : LLabel) (B : List LinstrRM) : Bool :=
  let es := none :: (sites T B).map some
  es.all fun e => es.all fun x => isCutB T fn B e x (cutAt fn fin B e x) (cutPos B e)

omit [DecidableEq LinstrR] in
/-- An entry or exit of `B` is `none` or a member of `sites T B`. -/
theorem mem_of_isSite {T : ProcTable} {B : List LinstrRM} {e : Option Nat}
    (h : IsSite T B e) : e ∈ none :: (sites T B).map some := by
  cases e with
  | none => exact List.mem_cons_self
  | some p =>
      obtain ⟨i, hi, hp⟩ := h
      refine List.mem_cons_of_mem _ (List.mem_map_of_mem ?_)
      simp only [sites, List.mem_filter, List.mem_range]
      exact ⟨(List.getElem?_eq_some_iff.mp hi).1, by rw [hi]; exact hp⟩

/-- **A halting run of the x86 instruction set with procedures is a chain of halting runs
    of the cut programs `cutAt` on the x86 instruction set**, for a body that `cutOkB`
    accepts. -/
theorem x86_withProcs_run_cutAt {T : ProcTable} {fn : String} {fin : LLabel}
    {B : List LinstrRM} (hok : cutOkB T fn fin B = true) (n : Nat) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (hrun : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) n s = some t) :
    CutChain x86Isa T fn B (cutAt fn fin B) none s t := by
  simp only [cutOkB, List.all_eq_true] at hok
  exact withProcs_run_cut (pos := fun e _ => cutPos B e) x86Isa_pcFree (x86Isa_refusesProcs T)
    (fun e x he hx => isCut_of_isCutB (hok e (mem_of_isSite he) x (mem_of_isSite hx)))
    n s t hfn hpc hrun

end CutOk

/-! ## 8. The statement of soundness of a validation by segments -/

/-- **A simulation of the cut programs of `B` by the cut programs of `B'` on the
    instruction set `I`.** `site` sends an entry or exit of `B` to one of `B'`. `R e`
    relates a state of `B` at the entry `e` to a state of `B'` at the entry `site e`, and
    `Q x` relates the end states of two segments with the exits `x` and `site x`. Equal
    states are related at the entry of the bodies; for an entry `e` and an exit `x` of `B`,
    a halting run on `I` of the cut program of `B` from a state related to a state `s'` of
    `fn` is matched by a halting run on `I` of the cut program of `B'` from `s'` to states
    related by `Q`; states related by `Q` at the end of the bodies agree on the
    registers `outs`, the arrays and the word memory; and from states related by `Q` at a
    shadow instruction, the step of the summary on `B` is matched by the step of the
    summary on `B'` to states related by `R`. -/
structure CutSimI (I : Isa) (T : ProcTable) (outs : List String) (fn : String)
    (B B' : List LinstrRM) (cut cut' : Option Nat → Option Nat → List LinstrRM) : Type where
  site : Option Nat → Option Nat
  R : Option Nat → LstateMF → LstateMF → Prop
  Q : Option Nat → LstateMF → LstateMF → Prop
  site_none : site none = none
  init : ∀ s, R none s s
  seg : ∀ e x s s' u, IsSite T B e → IsSite T B x → s'.prog.lfn = fn → R e s s' →
    CutRun I fn (cut e x) s u →
    ∃ u', CutRun I fn (cut' (site e) (site x)) s' u' ∧ Q x u u'
  fin : ∀ t t', Q none t t' → Obs outs t t'
  glue : ∀ p u u' v, Q (some p) u u' → Glue T (singletonProgM fn B) p u v →
    ∃ q v', site (some p) = some q ∧ Glue T (singletonProgM fn B') q u' v' ∧ R (some p) v v'

/-- **A simulation of the cut programs of `B` by the cut programs of `B'`.** `CutSimI` at
    the x86 instruction set `x86Isa`. -/
abbrev CutSim (T : ProcTable) (outs : List String) (fn : String) (B B' : List LinstrRM)
    (cut cut' : Option Nat → Option Nat → List LinstrRM) : Type :=
  CutSimI x86Isa T outs fn B B' cut cut'

/-- **The statement of soundness of a validation by segments on the instruction set
    `I`.** Under a simulation `CutSimI I` of the cut programs of `B` by those of `B'`,
    every halting run of `I.withProcs T` on `B` from a state of `fn` at the counter `0` is
    matched by a halting run of `I.withProcs T` on `B'` from the same state, the end
    states agreeing on the registers `outs`, the arrays and the word memory. -/
def CutCheckSoundI (I : Isa) (T : ProcTable) (outs : List String) (fn : String)
    (B B' : List LinstrRM) (cut cut' : Option Nat → Option Nat → List LinstrRM) : Prop :=
  CutSimI I T outs fn B B' cut cut' → ∀ (s t : LstateMF), s.prog.lfn = fn →
    s.prog.base.lpc = 0 → ∀ fuel,
      (I.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t →
      ∃ fuel' t', (I.withProcs T).lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧
        Obs outs t t'

/-- **The statement of soundness of a validation by segments.** Under a simulation
    `CutSim` of the cut programs of `B` by those of `B'`, every halting run of
    `x86Isa.withProcs T` on `B` from a state of `fn` at the counter `0` is matched by a
    halting run of `x86Isa.withProcs T` on `B'` from the same state, the end states
    agreeing on the registers `outs`, the arrays and the word memory. -/
def CutCheckSound (T : ProcTable) (outs : List String) (fn : String) (B B' : List LinstrRM)
    (cut cut' : Option Nat → Option Nat → List LinstrRM) : Prop :=
  CutSim T outs fn B B' cut cut' → ∀ (s t : LstateMF), s.prog.lfn = fn →
    s.prog.base.lpc = 0 → ∀ fuel,
      (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t →
      ∃ fuel' t', (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧
        Obs outs t t'

/-! ## 9. The allocation of a body with shadow instructions -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (evalInstrPMemF_movReg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN

/-- The instruction is left in place by `expandCallShadows`: it is no operation with one
    register destination whose mnemonic is a call shadow (`CALLW:`, `CALLNW:`, `CALLN:`,
    `CALL:`). -/
def shadowFreeI (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg _] opn _ =>
      (parseCallW opn).isNone && !hasPrefix opn "CALLN:" && !hasPrefix opn "CALL:"
  | _ => true

/-- Every instruction of the body is left in place by `expandCallShadows`. -/
def shadowFreeB (body : Lcmd) : Bool := body.all shadowFreeI

/-- **`expandCallShadows` is the identity on a body without call shadows.** -/
theorem expandCallShadows_of_shadowFreeB {body : Lcmd} (h : shadowFreeB body = true) :
    expandCallShadows body = body := by
  unfold expandCallShadows
  induction body with
  | nil => rfl
  | cons i B ih =>
    simp only [shadowFreeB, List.all_cons, Bool.and_eq_true] at h
    rw [List.flatMap_cons, ih h.2]
    have hi := h.1
    unfold shadowFreeI at hi
    split at hi
    · rename_i d opn ss heq
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hi
      simp [heq, hi.1.1, hi.1.2, hi.2]
    · rename_i hne
      split
      · rename_i d opn ss heq
        exact absurd heq (hne d opn ss)
      · rfl

/-- The x86 register file with the allocation pool `pool`. -/
def poolAbi (pool : List String) : IsaAbi := { x86Abi with allocPool := pool }

/-- At the allocation pool of `x86Abi` the register file is `x86Abi`. -/
theorem poolAbi_default : poolAbi x86Abi.allocPool = x86Abi := rfl

/-- **The physical-ABI allocation of a virtual function with shadow instructions, at the
    allocation pool `pool`**: `lfundefPhysAbiOfVirt` at the register file `poolAbi pool`,
    with the shadow instructions in the input of the allocation, followed by
    `expandCallShadows` on the allocated body. With `pool` a pool of names kept across the
    call (`Callee.keepPool`), a name live across a shadow instruction is allocated to a
    register the callee keeps or to a frame word, and the marshalling moves of the
    expansion write only argument registers and read the result register. -/
def lfundefPhysAbiOfVirtAt (pool : List String) (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs abiArgs : List String) (abiTyin : List Nat) (posBind : Bool) : Lfundef :=
  let fd := lfundefPhysAbiOfVirt virt0 outArg' inArgs' accRegs (abiArgs := abiArgs)
    (abiTyin := abiTyin) (abi := poolAbi pool) (posBind := posBind)
  { fd with lfd_body := expandCallShadows fd.lfd_body }

/-- **At the pool of `x86Abi`, on an allocated body without call shadows, the allocation
    with shadow instructions is `lfundefPhysAbiOfVirt`.** -/
theorem lfundefPhysAbiOfVirtAt_default (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs abiArgs : List String) (abiTyin : List Nat) (posBind : Bool)
    (h : shadowFreeB (lfundefPhysAbiOfVirt virt0 outArg' inArgs' accRegs (abiArgs := abiArgs)
      (abiTyin := abiTyin) (posBind := posBind)).lfd_body = true) :
    lfundefPhysAbiOfVirtAt x86Abi.allocPool virt0 outArg' inArgs' accRegs abiArgs abiTyin posBind
      = lfundefPhysAbiOfVirt virt0 outArg' inArgs' accRegs (abiArgs := abiArgs)
          (abiTyin := abiTyin) (posBind := posBind) := by
  unfold lfundefPhysAbiOfVirtAt
  rw [poolAbi_default]
  dsimp only
  rw [expandCallShadows_of_shadowFreeB h]

/-! ## 10. Shadow instructions on common names -/

/-- The copy `MOV:64 dst, src`. -/
def movI (dst src : String) : LinstrRM :=
  (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src], .reg none)

/-- A copy is no shadow instruction. -/
theorem shadowCall?_movI (dst src : String) : shadowCall? (movI dst src).fst = none := by
  simp only [movI, shadowCall?]
  rw [if_neg (by decide)]

/-- The names of a list of register operands; `none` when an operand is no register. -/
def regNames? : List LOperand → Option (List String)
  | [] => some []
  | .reg x :: os => (regNames? os).map (x :: ·)
  | _ :: _ => none

/-- Operands with the names `xs` are the registers `xs`. -/
theorem regNames?_eq : ∀ {os : List LOperand} {xs : List String},
    regNames? os = some xs → os = xs.map LOperand.reg
  | [], _, h => by cases h; rfl
  | .reg x :: os, xs, h => by
      obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.map_cons, regNames?_eq hys]
  | .imm _ :: _, _, h => by cases h
  | .arr _ _ :: _, _, h => by cases h
  | .arrIdx _ _ _ :: _, _, h => by cases h

/-- **The call `d ← CALL:f xs` on the common names `args` and `res`**: the copies of the
    operands `xs` into the names `args`, the shadow instruction `res ← CALL:f args`, and
    the copy of `res` into `d`. -/
def commonSeq (f : String) (args : List String) (res d : String) (xs : List String) :
    List LinstrRM :=
  (args.zip xs).map (fun p => movI p.1 p.2)
    ++ [(callShadow res f (args.map LOperand.reg), .reg none), movI d res]

/-- The rewriting of one instruction onto the common names: an instruction that is no
    shadow instruction is kept; a shadow instruction of a call of `f` on as many register
    operands as `args` becomes `commonSeq`; every other shadow instruction is refused. -/
def commonCall? (f : String) (args : List String) (res : String) (i : LinstrRM) :
    Option (List LinstrRM) :=
  match shadowCall? i.fst with
  | none => some [i]
  | some (d, g, srcs) =>
      match regNames? srcs with
      | some xs =>
          if g = f ∧ xs.length = args.length then some (commonSeq f args res d xs) else none
      | none => none

/-- **The rewriting of the shadow instructions of a body onto the common names** `args`
    and `res` of the callee `f`: `commonCall?` at each instruction, in order. -/
def commonCalls? (f : String) (args : List String) (res : String) :
    List LinstrRM → Option (List LinstrRM)
  | [] => some []
  | i :: B => (commonCall? f args res i).bind fun is =>
      (commonCalls? f args res B).map (is ++ ·)

/-- A shadow instruction of `commonSeq` has the destination `res`, the symbol `f` and the
    operands `args` as registers. -/
theorem shadowCall?_commonSeq {f : String} {args : List String} {res d : String}
    {xs : List String} {i : LinstrRM} (hi : i ∈ commonSeq f args res d xs)
    {q : String × String × List LOperand} (hq : shadowCall? i.fst = some q) :
    q = (res, f, args.map LOperand.reg) := by
  simp only [commonSeq, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with ⟨p, -, rfl⟩ | rfl | rfl
  · rw [shadowCall?_movI] at hq; cases hq
  · rw [shadowCall?_callShadow] at hq; exact (Option.some.inj hq).symm
  · rw [shadowCall?_movI] at hq; cases hq

/-- **Every shadow instruction of a rewritten body has the destination `res`, the symbol
    `f` and the operands `args` as registers.** -/
theorem shadowCall?_commonCalls? {f : String} {args : List String} {res : String} :
    ∀ {B B' : List LinstrRM}, commonCalls? f args res B = some B' →
      ∀ i ∈ B', ∀ q, shadowCall? i.fst = some q → q = (res, f, args.map LOperand.reg)
  | [], _, h, i, hi, _, _ => by cases h; cases hi
  | j :: B, _, h, i, hi, q, hq => by
      obtain ⟨is, his, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨B₁, hB₁, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_append.mp hi with hi | hi
      · unfold commonCall? at his
        split at his
        · rename_i hn
          cases his
          rw [List.mem_singleton.mp hi, hn] at hq
          cases hq
        · split at his
          · split at his
            · cases his
              exact shadowCall?_commonSeq hi hq
            · cases his
          · cases his
      · exact shadowCall?_commonCalls? hB₁ i hi q hq

/-- The run of a list of instructions by the steps of `I`, one after the other, without
    reading the counter. -/
def runI (I : Isa) (P : LprogM) : List LinstrRM → LstateMF → Option LstateMF
  | [], s => some s
  | i :: is, s => (I.step P i s).bind (runI I P is)

theorem runI_append (I : Isa) (P : LprogM) (is js : List LinstrRM) (s : LstateMF) :
    runI I P (is ++ js) s = (runI I P is s).bind (runI I P js) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, runI]
    cases I.step P i s with
    | none => rfl
    | some u => exact ih u

/-- The state `s` with the register file `g` of its register file and the counter advanced
    by `k`. -/
def regUpd (g : (String → Σ w, BitVec w) → String → Σ w, BitVec w) (k : Nat) (s : LstateMF) :
    LstateMF :=
  { s with prog := { s.prog with base := { s.prog.base with
      reg := { lvm := g s.prog.base.reg.lvm, lpc := s.prog.base.reg.lpc + k } } } }

theorem regUpd_regUpd (g g' : (String → Σ w, BitVec w) → String → Σ w, BitVec w) (k k' : Nat)
    (s : LstateMF) : regUpd g k (regUpd g' k' s) = regUpd (fun L => g (g' L)) (k' + k) s := by
  simp only [regUpd, Nat.add_assoc]

/-- The state after the copy `MOV:64 dst, src`. -/
def movS (dst src : String) (s : LstateMF) : LstateMF :=
  regUpd (fun L r => if r = dst then L src else L r) 1 s

/-- The step of a copy on the x86 instruction set with procedures. -/
theorem step_movI (T : ProcTable) (P : LprogM) (dst src : String) (s : LstateMF) :
    (x86Isa.withProcs T).step P (movI dst src) s = some (movS dst src s) := by
  show (match procCall? T (movI dst src).fst with
    | some q => procStep q.1 q.2.1 q.2.2 s
    | none => x86Isa.step P (movI dst src) s) = _
  simp only [procCall?, shadowCall?_movI, Option.bind_none]
  rw [x86Isa_step]
  exact evalInstrPMemF_movReg P dst src (.reg none) s

theorem retWord_eq_regUpd (dst : String) (w : BitVec 64) (s : LstateMF) :
    retWord dst w s = regUpd (fun L r => if r = dst then ⟨64, w⟩ else L r) 1 s := rfl

/-- The state after the copies `MOV:64 p.1, p.2` of the pairs `ps`, in order. -/
def movesF : List (String × String) → LstateMF → LstateMF
  | [], s => s
  | p :: ps, s => movesF ps (movS p.1 p.2 s)

theorem runI_moves (T : ProcTable) (P : LprogM) :
    ∀ (ps : List (String × String)) (s : LstateMF),
      runI (x86Isa.withProcs T) P (ps.map fun p => movI p.1 p.2) s = some (movesF ps s)
  | [], _ => rfl
  | p :: ps, s => by
      simp only [List.map_cons, runI, step_movI, Option.bind_some, movesF]
      exact runI_moves T P ps _

theorem lvm_movS (dst src : String) (s : LstateMF) (r : String) :
    (movS dst src s).prog.base.reg.lvm r
      = if r = dst then s.prog.base.reg.lvm src else s.prog.base.reg.lvm r := rfl

theorem movesF_eq_regUpd : ∀ (ps : List (String × String)) (s : LstateMF),
    movesF ps s = regUpd (fun _ => (movesF ps s).prog.base.reg.lvm) ps.length s
  | [], _ => rfl
  | p :: ps, s => by
      show movesF ps (movS p.1 p.2 s)
        = regUpd (fun _ => (movesF ps (movS p.1 p.2 s)).prog.base.reg.lvm) (ps.length + 1) s
      conv_lhs => rw [movesF_eq_regUpd ps (movS p.1 p.2 s)]
      rw [movS, regUpd_regUpd, Nat.add_comm]

/-- The copies keep a name that is no destination. -/
theorem lvm_movesF_of_not_mem : ∀ (ps : List (String × String)) (s : LstateMF) (r : String),
    r ∉ ps.map Prod.fst → (movesF ps s).prog.base.reg.lvm r = s.prog.base.reg.lvm r
  | [], _, _, _ => rfl
  | p :: ps, s, r, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [movesF, lvm_movesF_of_not_mem ps _ r h.2, lvm_movS, if_neg h.1]

/-- After copies with distinct destinations and no source among the destinations, each
    destination holds the entry cell of its source. -/
theorem lvm_movesF_of_mem : ∀ (ps : List (String × String)) (s : LstateMF),
    (ps.map Prod.fst).Nodup → (∀ p ∈ ps, p.2 ∉ ps.map Prod.fst) →
    ∀ p ∈ ps, (movesF ps s).prog.base.reg.lvm p.1 = s.prog.base.reg.lvm p.2
  | [], _, _, _, _, hp => by cases hp
  | q :: ps, s, hnd, hx, p, hp => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [movesF]
      rcases List.mem_cons.mp hp with rfl | hp'
      · rw [lvm_movesF_of_not_mem ps _ _ hnd.1, lvm_movS, if_pos rfl]
      · rw [lvm_movesF_of_mem ps _ hnd.2
          (fun p' hp'' hm => hx p' (List.mem_cons_of_mem _ hp'') (by simp [hm])) p hp',
          lvm_movS, if_neg]
        intro e
        exact hx p (List.mem_cons_of_mem _ hp') (by simp [e])

/-- Register operands read at width `64` in two register files give the same words when
    the files agree on them pairwise. -/
theorem mapM_reg_congr (R R' : LstateN) : ∀ (as xs : List String), as.length = xs.length →
    (∀ p ∈ as.zip xs, R'.lvm p.1 = R.lvm p.2) →
    (as.map LOperand.reg).mapM (evalOperandN R' 64)
      = (xs.map LOperand.reg).mapM (evalOperandN R 64)
  | [], [], _, _ => rfl
  | a :: as, x :: xs, hl, h => by
      have e : R'.lvm a = R.lvm x := h (a, x) (by simp)
      have h0 : evalOperandN R' 64 (.reg a) = evalOperandN R 64 (.reg x) := by
        simp only [evalOperandN, LstateN.getW]
        rw [e]
      simp only [List.map_cons, List.mapM_cons, h0]
      rw [mapM_reg_congr R R' as xs (by simpa using hl) (fun p hp => h p (by simp [hp]))]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **The step of the summary at a shadow instruction is simulated by the run of its form
    on common names.** Let `f` have the summary `pr` on words with a word result in `T`, the
    names `args` be distinct and as many as the operands `xs`, and no operand be a name of
    `args`. When the step of
    the summary at `d ← CALL:f xs` from `s` gives `v`, the run of `commonSeq f args res d
    xs` from `s` on the x86 instruction set with procedures gives `v` with the counter
    advanced by `args.length + 1` and a register file that agrees with the register file of
    `v` at every name outside `args` other than `res`. The arrays, the word memory, the
    zero flag and the function name are those of `v`. -/
theorem commonCall_sim {T : ProcTable} {f : String} {pr : ProcSummary} (hT : T f = some pr)
    (hwo : pr.WordOnly) (hrw : pr.RetWord) (P : LprogM) {args xs : List String}
    (res d : String) (hlen : xs.length = args.length)
    (hnd : args.Nodup) (hx : ∀ x ∈ xs, x ∉ args) {s v : LstateMF}
    (h : procStep pr d (xs.map LOperand.reg) s = some v) :
    ∃ L' : String → Σ w, BitVec w,
      runI (x86Isa.withProcs T) P (commonSeq f args res d xs) s
        = some (regUpd (fun _ => L') (args.length + 1) v)
      ∧ ∀ r, r ∉ args → r ≠ res → L' r = v.prog.base.reg.lvm r := by
  rw [procStep_of_wordOnly hwo hrw] at h
  split at h
  · rename_i har
    obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    have hfst : (args.zip xs).map Prod.fst = args := List.map_fst_zip (by omega)
    obtain ⟨u, hu⟩ : ∃ u, u = movesF (args.zip xs) s := ⟨_, rfl⟩
    have hmap : (args.map LOperand.reg).mapM (evalOperandN u.prog.base.reg 64) = some vs := by
      rw [mapM_reg_congr s.prog.base.reg _ args xs hlen.symm (fun p hp => by
        rw [hu]
        exact lvm_movesF_of_mem _ s (by rw [hfst]; exact hnd)
          (fun q hq => by rw [hfst]; exact hx _ (List.of_mem_zip hq).2) p hp)]
      exact hvs
    have hcall : (x86Isa.withProcs T).step P
        (callShadow res f (args.map LOperand.reg), .reg none) u = some (retWord res w u) := by
      show (match procCall? T (callShadow res f (args.map LOperand.reg)) with
        | some q => procStep q.1 q.2.1 q.2.2 u
        | none => _) = _
      rw [procCall?_callShadow, hT]
      simp only [Option.map_some]
      rw [procStep_of_wordOnly hwo hrw, if_pos (by simpa [hlen] using har), hmap]
      simp only [Option.bind_some, hw, Option.map_some]
    have hreg : u = regUpd (fun _ => u.prog.base.reg.lvm) (args.zip xs).length s := by
      rw [hu]; exact movesF_eq_regUpd _ s
    refine ⟨fun r => if r = d then ⟨64, w⟩ else if r = res then ⟨64, w⟩
      else u.prog.base.reg.lvm r, ?_, ?_⟩
    · rw [commonSeq, runI_append, runI_moves, ← hu]
      simp only [Option.bind_some, runI, hcall, step_movI]
      conv_lhs => rw [hreg]
      rw [movS, retWord_eq_regUpd, retWord_eq_regUpd, regUpd_regUpd, regUpd_regUpd,
        regUpd_regUpd]
      have hl : (args.zip xs).length = args.length := by simp [hlen]
      rw [hl, Nat.add_comm 1 (args.length + 1), Nat.add_assoc]
      congr 2
      funext L r
      by_cases h1 : r = d <;> by_cases h2 : r = res <;> simp [h1, h2]
    · intro r hr hres
      rw [retWord_eq_regUpd]
      show _ = if r = d then _ else _
      by_cases h1 : r = d
      · simp [h1]
      · simp only [h1, hres, if_false]
        rw [hu]
        exact lvm_movesF_of_not_mem _ s r (by rw [hfst]; exact hr)
  · cases h

/-- The names of an operand. -/
def opNames : LOperand → List String
  | .reg r => [r]
  | .imm _ => []
  | .arr b _ => [b]
  | .arrIdx b i _ => [b, i]

/-- The names of the destinations and the sources of an operation; no name for every other
    instruction. -/
def instrNames : LinstrR → List String
  | .Lopn ds _ ss => (ds ++ ss).flatMap opNames
  | _ => []

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV in
/-- **The check that the step of `i` mentions no name of `N`**: the symbolic step of `i`
    from the start state is a description, and no guard, written register, written array
    or flag of the description reads a start register of `N`. -/
def offCongrB (N : List String) (i : LinstrRM) : Bool :=
  match symStep i SSt.start with
  | .ok ss gs =>
      (gs.flatMap SG.vars ++ ss.wr.flatMap (fun r => (ss.regs r).vars) ++ ss.cf.vars
          ++ ss.of.vars ++ ss.zf.vars ++ ss.awr.flatMap fun a => (ss.arrs a).vars).all
        fun r => !N.contains r
  | _ => false

/-- **The check of the instructions of a body against the names `N`**: the condition of
    each conditional jump has no operand name in `N`, and every instruction that is neither
    a control instruction nor a shadow instruction passes `offCongrB N`. -/
def commonCongrB (N : List String) (B : List LinstrRM) : Bool :=
  B.all fun i =>
    match i.fst with
    | .Lcond c _ => (opNames c).all fun n => !N.contains n
    | j => isCtl j || (shadowCall? j).isSome || offCongrB N i

/-- **The check of the common names against a body**: the names `args` are distinct, `res`
    is none of them, no operation of the body has an operand with a name of `args` or
    the name `res`, and the body passes `commonCongrB` at the names `res :: args`. -/
def commonFreshB (args : List String) (res : String) (B : List LinstrRM) : Bool :=
  decide args.Nodup && !args.contains res
    && (B.all fun i => (instrNames i.fst).all fun n => !args.contains n && n != res)
    && commonCongrB (res :: args) B

/-- A body that passes `commonFreshB` passes `commonCongrB` at the common names. -/
theorem commonFreshB_congr {args : List String} {res : String} {B : List LinstrRM}
    (h : commonFreshB args res B = true) : commonCongrB (res :: args) B = true := by
  simp only [commonFreshB, Bool.and_eq_true] at h
  exact h.2

/-- **A shadow instruction of a body that passes `commonFreshB` meets the side conditions
    of `commonCall_sim`**: the names `args` are distinct, no operand of the shadow
    instruction is a name of `args`, and its destination is neither a name of `args` nor
    `res`. -/
theorem commonFreshB_site {args : List String} {res : String} {B : List LinstrRM}
    (h : commonFreshB args res B = true) {i : LinstrRM} (hi : i ∈ B) {d g : String}
    {srcs : List LOperand} (hs : shadowCall? i.fst = some (d, g, srcs)) {xs : List String}
    (hxs : regNames? srcs = some xs) :
    args.Nodup ∧ (∀ x ∈ xs, x ∉ args) ∧ d ∉ args ∧ d ≠ res := by
  simp only [commonFreshB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hnd, -⟩, hall⟩, -⟩ := h
  have hin := hall i hi
  unfold shadowCall? at hs
  split at hs
  · rename_i dst opn ss heq
    split at hs
    · cases hs
      rw [heq, regNames?_eq hxs] at hin
      refine ⟨hnd, fun x hx => ?_, ?_, ?_⟩
      · have := (hin x (by simp [instrNames, opNames, hx])).1
        simpa using this
      · have := (hin d (by simp [instrNames, opNames])).1
        simpa using this
      · exact (hin d (by simp [instrNames, opNames])).2
    · cases hs
  · cases hs

/-- No operand of a shadow instruction of a body that passes `commonFreshB` is the name
    `res`. -/
theorem commonFreshB_site_res {args : List String} {res : String} {B : List LinstrRM}
    (h : commonFreshB args res B = true) {i : LinstrRM} (hi : i ∈ B) {d g : String}
    {srcs : List LOperand} (hs : shadowCall? i.fst = some (d, g, srcs)) {xs : List String}
    (hxs : regNames? srcs = some xs) : ∀ x ∈ xs, x ≠ res := by
  simp only [commonFreshB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  have hin := h.1.2 i hi
  unfold shadowCall? at hs
  split at hs
  · rename_i dst opn ss heq
    split at hs
    · cases hs
      rw [heq, regNames?_eq hxs] at hin
      exact fun x hx => (hin x (by simp [instrNames, opNames, hx])).2
    · cases hs
  · cases hs

/-! ## 11. The run of a body rewritten onto common names -/

/-- The state `s` with the register file `L` and the counter `q`. -/
def setRL (L : String → Σ w, BitVec w) (q : Nat) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := { s.prog.base with reg := { lvm := L, lpc := q } } } }

/-- **The relation of a state of a body to a state of its rewritten body**, for the names
    `N` and the position map `ψ`: the second state is the first with a register file that
    agrees with its register file off `N`, and with the counter at the image of its
    counter. The arrays, the word memory, the flags and the function name are equal. -/
def OffRel (N : List String) (ψ : Nat → Nat) (s s' : LstateMF) : Prop :=
  ∃ L' : String → Σ w, BitVec w, (∀ r, r ∉ N → L' r = s.prog.base.reg.lvm r) ∧
    s' = setRL L' (ψ s.prog.base.reg.lpc) s

/-- **The step of the instruction `i` on the x86 instruction set commutes with a change of
    the names `N`.** A step from `s` to `t` is matched, from `s` with a register file that
    agrees with the register file of `s` off `N`, by a step to `t` with a register file that
    agrees with the register file of `t` off `N`. -/
def OffCongr (N : List String) (i : LinstrRM) : Prop :=
  ∀ (P P' : LprogM) (s t : LstateMF) (L' : String → Σ w, BitVec w),
    (∀ r, r ∉ N → L' r = s.prog.base.reg.lvm r) → x86Isa.step P i s = some t →
    ∃ L'' : String → Σ w, BitVec w, (∀ r, r ∉ N → L'' r = t.prog.base.reg.lvm r) ∧
      x86Isa.step P' i (setRL L' s.prog.base.reg.lpc s) = some (setRL L'' t.prog.base.reg.lpc t)

/-- The branch condition `c` of the x86 instruction set does not read the names `N`. -/
def CondCongr (N : List String) (c : LOperand) : Prop :=
  ∀ (s : LstateMF) (L' : String → Σ w, BitVec w) (q : Nat),
    (∀ r, r ∉ N → L' r = s.prog.base.reg.lvm r) →
    x86Isa.condEval (setRL L' q s) c = x86Isa.condEval s c

/-- A branch condition with no operand name in `N` does not read the names `N`. -/
theorem condCongr_of_names {N : List String} {c : LOperand} (h : ∀ n ∈ opNames c, n ∉ N) :
    CondCongr N c := by
  intro s L' q hL
  show X86Backend.OwnedLprogTV.decC _ c = X86Backend.OwnedLprogTV.decC s c
  unfold X86Backend.OwnedLprogTV.decC
  cases X86Backend.OwnedLprogTV.ccPol c with
  | some pol => rfl
  | none =>
      cases c with
      | reg r =>
          show condNZ _ _ = condNZ _ _
          have e : (setRL L' q s).prog.base.reg.lvm r = s.prog.base.reg.lvm r :=
            hL r (h r (by simp [opNames]))
          simp only [condNZ, evalOperandN, LstateN.getW]
          rw [e]
      | imm v => rfl
      | arr b n => rfl
      | arrIdx b i n => rfl

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV in
/-- **An instruction that passes `offCongrB N` commutes with a change of the names `N`.**
    The description of its step reads no name of `N`, so the step from a register file
    that agrees off `N` succeeds, writes the same words to the registers it writes, and
    gives the same arrays, word memory, flags and counter. -/
theorem offCongr_of_offCongrB {N : List String} {i : LinstrRM} (h : offCongrB N i = true) :
    OffCongr N i := by
  intro P P' s t L' hL hs
  unfold offCongrB at h
  split at h
  · rename_i ss gs heq
    simp only [List.all_eq_true, Bool.not_eq_true'] at h
    have hrd : ∀ r, r ∈ gs.flatMap SG.vars ++ ss.wr.flatMap (fun r => (ss.regs r).vars)
        ++ ss.cf.vars ++ ss.of.vars ++ ss.zf.vars ++ ss.awr.flatMap (fun a => (ss.arrs a).vars) →
        s.prog.base.reg.lvm r = L' r :=
      fun r hr => (hL r (by simpa using h r hr)).symm
    have hg := symStep_good i SSt.good_start heq
    have hD := symStep_sound P i SSt.start s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf
      s.prog.base.of s.zf s (holds_start s)
    have hD' := symStep_sound P' i SSt.start L' s.prog.base.larr s.prog.base.cf
      s.prog.base.of s.zf (setRL L' s.prog.base.reg.lpc s)
      (holds_start (setRL L' s.prog.base.reg.lpc s))
    rw [heq] at hD hD'
    rw [x86Isa_step] at hs ⊢
    obtain ⟨hG, hH, hF⟩ := hD.1 t hs
    have hG' : AllG L' s.prog.base.larr s.prog.base.cf s.prog.base.of gs := by
      intro g hgm
      refine (SG.holds_congr _ g (fun r hr => hrd r ?_) (fun _ => ⟨rfl, rfl⟩)).mp (hG g hgm)
      simp only [List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨g, hgm, hr⟩))))
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hD'.2 hG')
    obtain ⟨-, hH', hF'⟩ := hD'.1 t' ht'
    have e1 : t'.prog.base.reg.lpc = t.prog.base.reg.lpc := by rw [hF'.2.1, hF.2.1]; rfl
    have e2 : t'.prog.base.larr = t.prog.base.larr := by
      funext q
      rw [hH'.2.1 q, hH.2.1 q]
      by_cases hw : q ∈ ss.awr
      · refine (SArr.ev_congr _ _ (fun r hr => hrd r ?_) (fun _ => ⟨rfl, rfl⟩)).symm
        simp only [List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨q, hw, hr⟩
      · rw [hg.2 q hw]
        rfl
    have e3 : t'.prog.base.lmem = t.prog.base.lmem := by rw [hF'.2.2, hF.2.2]; rfl
    have e4 : t'.prog.base.cf = t.prog.base.cf := by
      rw [hH'.2.2.2.1, hH.2.2.2.1]
      congr 1
      refine (STerm.ev_congr _ _ (fun r hr => hrd r ?_) (fun _ => ⟨rfl, rfl⟩)).symm
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr hr)))
    have e5 : t'.prog.base.of = t.prog.base.of := by
      rw [hH'.2.2.2.2, hH.2.2.2.2]
      congr 1
      refine (STerm.ev_congr _ _ (fun r hr => hrd r ?_) (fun _ => ⟨rfl, rfl⟩)).symm
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr hr))
    have e6 : t'.prog.lfn = t.prog.lfn := by rw [hF'.1, hF.1]; rfl
    have e7 : t'.zf = t.zf := by
      rw [hH'.2.2.1, hH.2.2.1]
      refine (SFlag.ev_congr _ ss.zf (fun r hr => hrd r ?_) (fun _ => ⟨rfl, rfl, rfl⟩)).symm
      simp only [List.mem_append]
      exact Or.inl (Or.inr hr)
    refine ⟨t'.prog.base.reg.lvm, fun r hr => ?_, ?_⟩
    · rw [hH'.1 r, hH.1 r]
      by_cases hw : r ∈ ss.wr
      · refine (STerm.ev_congr _ _ (fun q hq => hrd q ?_) (fun _ => ⟨rfl, rfl⟩)).symm
        simp only [List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, hw, hq⟩))))
      · rw [hg.1 r hw]
        exact hL r hr
    · rw [ht']
      clear hH hH' hF hF' hD hD' hs ht'
      obtain ⟨⟨⟨⟨lvm', lpc'⟩, larr', lmem', cf', of'⟩, lfn'⟩, zf'⟩ := t'
      obtain ⟨⟨⟨⟨lvm, lpc⟩, larr, lmem, cf, of⟩, lfn⟩, zf⟩ := t
      dsimp only at e1 e2 e3 e4 e5 e6 e7
      subst e1 e2 e3 e4 e5 e6 e7
      rfl
  · cases h

/-- An instruction of a body that passes `commonCongrB N`, neither a control instruction
    nor a shadow instruction, commutes with a change of the names `N`. -/
theorem commonCongrB_offCongr {N : List String} {B : List LinstrRM}
    (h : commonCongrB N B = true) {i : LinstrRM} (hi : i ∈ B) (hc : isCtl i.fst = false)
    (hs : shadowCall? i.fst = none) : OffCongr N i := by
  have hm := List.all_eq_true.mp h i hi
  split at hm
  · rename_i c l heq
    rw [heq] at hc
    cases hc
  · exact offCongr_of_offCongrB (by simpa [hc, hs] using hm)

/-- The condition of a conditional jump of a body that passes `commonCongrB N` does not
    read the names `N`. -/
theorem commonCongrB_condCongr {N : List String} {B : List LinstrRM}
    (h : commonCongrB N B = true) {c : LOperand} {l : LLabel} {tag : MemTag}
    (hi : (LinstrR.Lcond c l, tag) ∈ B) : CondCongr N c := by
  have hm := List.all_eq_true.mp h _ hi
  dsimp only at hm
  exact condCongr_of_names fun n hn => by simpa using List.all_eq_true.mp hm n hn

/-- The number of instructions of the form of `i` on `n` common argument names. -/
def expLen (n : Nat) (i : LinstrRM) : Nat :=
  if (shadowCall? i.fst).isSome then n + 2 else 1

/-- **The position map of the rewriting onto `n` common argument names**: the number of
    instructions of the forms of the instructions of `B` before the position `p`. -/
def expPos (n : Nat) (B : List LinstrRM) (p : Nat) : Nat := ((B.take p).map (expLen n)).sum

theorem expPos_zero (n : Nat) (B : List LinstrRM) : expPos n B 0 = 0 := by
  simp [expPos]

theorem expPos_cons_succ (n : Nat) (i : LinstrRM) (B : List LinstrRM) (p : Nat) :
    expPos n (i :: B) (p + 1) = expLen n i + expPos n B p := by
  simp [expPos]

theorem expPos_succ (n : Nat) : ∀ {B : List LinstrRM} {p : Nat} {i : LinstrRM},
    B[p]? = some i → expPos n B (p + 1) = expPos n B p + expLen n i
  | [], _, _, h => by simp at h
  | j :: B, 0, i, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [expPos]
  | j :: B, p + 1, i, h => by
      rw [expPos_cons_succ, expPos_cons_succ, expPos_succ n (B := B) (by simpa using h)]
      omega

theorem expPos_of_le (n : Nat) {B : List LinstrRM} {p : Nat} (h : B.length ≤ p) :
    expPos n B p = expPos n B B.length := by
  simp only [expPos, List.take_of_length_le h, List.take_length]

/-- The form of an instruction that is no shadow instruction is the instruction. -/
theorem commonCall?_none {f : String} {args : List String} {res : String} {i : LinstrRM}
    {is : List LinstrRM} (h : commonCall? f args res i = some is)
    (hn : shadowCall? i.fst = none) : is = [i] := by
  unfold commonCall? at h
  rw [hn] at h
  exact (Option.some.inj h).symm

/-- The form of a shadow instruction is `commonSeq` at its register operands. -/
theorem commonCall?_some {f : String} {args : List String} {res : String} {i : LinstrRM}
    {is : List LinstrRM} (h : commonCall? f args res i = some is) {d g : String}
    {srcs : List LOperand} (hs : shadowCall? i.fst = some (d, g, srcs)) :
    ∃ xs, regNames? srcs = some xs ∧ g = f ∧ xs.length = args.length ∧
      is = commonSeq f args res d xs := by
  unfold commonCall? at h
  rw [hs] at h
  dsimp only at h
  split at h
  · rename_i xs hxs
    split at h
    · rename_i hc
      exact ⟨xs, hxs, hc.1, hc.2, (Option.some.inj h).symm⟩
    · cases h
  · cases h

theorem commonCall?_length {f : String} {args : List String} {res : String} {i : LinstrRM}
    {is : List LinstrRM} (h : commonCall? f args res i = some is) :
    is.length = expLen args.length i := by
  cases hs : shadowCall? i.fst with
  | none => rw [commonCall?_none h hs, expLen, hs]; rfl
  | some q =>
      obtain ⟨d, g, srcs⟩ := q
      obtain ⟨xs, -, -, hlen, rfl⟩ := commonCall?_some h hs
      simp [expLen, hs, commonSeq, hlen]

/-- **The rewritten body at a position of the body**: the form of the instruction at `p`
    stands in the rewritten body at the image of `p`. -/
theorem commonCalls?_split {f : String} {args : List String} {res : String} :
    ∀ {B B' : List LinstrRM}, commonCalls? f args res B = some B' →
      ∀ {p : Nat} {i : LinstrRM}, B[p]? = some i →
      ∃ is pre post, commonCall? f args res i = some is ∧ B' = pre ++ is ++ post ∧
        pre.length = expPos args.length B p
  | [], _, _, _, _, hi => by simp at hi
  | j :: B, _, h, p, i, hi => by
      obtain ⟨js, hjs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨B₁, hB₁, rfl⟩ := Option.map_eq_some_iff.mp h
      cases p with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          exact ⟨js, [], B₁, hjs, rfl, by rw [expPos_zero]; rfl⟩
      | succ p =>
          obtain ⟨is, pre, post, his, rfl, hpre⟩ :=
            commonCalls?_split hB₁ (p := p) (i := i) (by simpa using hi)
          refine ⟨is, js ++ pre, post, his, by simp only [List.append_assoc], ?_⟩
          rw [List.length_append, expPos_cons_succ, hpre, commonCall?_length hjs]

theorem commonCalls?_length {f : String} {args : List String} {res : String} :
    ∀ {B B' : List LinstrRM}, commonCalls? f args res B = some B' →
      B'.length = expPos args.length B B.length
  | [], _, h => by cases h; rfl
  | j :: B, _, h => by
      obtain ⟨js, hjs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨B₁, hB₁, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.length_append, List.length_cons, expPos_cons_succ, commonCalls?_length hB₁,
        commonCall?_length hjs]

/-- The form of an instruction that does not declare the label `l` declares no label `l`. -/
theorem commonCall?_noLabel {f : String} {args : List String} {res : String} {i : LinstrRM}
    {is : List LinstrRM} (h : commonCall? f args res i = some is) (l : LLabel)
    (hl : isLabel l i.fst = false) : ∀ j ∈ is, isLabel l j.fst = false := by
  cases hs : shadowCall? i.fst with
  | none =>
      rw [commonCall?_none h hs]
      intro j hj
      rw [List.mem_singleton.mp hj]
      exact hl
  | some q =>
      obtain ⟨d, g, srcs⟩ := q
      obtain ⟨xs, -, -, -, rfl⟩ := commonCall?_some h hs
      intro j hj
      simp only [commonSeq, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      rcases hj with ⟨p, -, rfl⟩ | rfl | rfl <;> rfl

/-- **A label declared in the body at `q` is declared in the rewritten body at the image
    of `q`.** -/
theorem findLabelMem_commonCalls? {f : String} {args : List String} {res : String}
    (l : LLabel) : ∀ {B B' : List LinstrRM}, commonCalls? f args res B = some B' →
      ∀ {q : Nat}, findLabelMem l B = some q →
        findLabelMem l B' = some (expPos args.length B q)
  | [], _, _, _, hq => by simp [findLabelMem, findLabel] at hq
  | j :: B, _, h, q, hq => by
      obtain ⟨js, hjs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨B₁, hB₁, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [findLabelMem, findLabel, List.map_cons, List.findIdx?_cons] at hq
      cases hl : isLabel l j.fst with
      | true =>
          rw [hl] at hq
          simp only [if_true, Option.some.injEq] at hq
          subst hq
          have hctl : isCtl j.fst = true := by
            cases hj : j.fst <;> simp_all [isLabel, isCtl]
          rw [commonCall?_none hjs (shadowCall?_of_isCtl hctl), expPos_zero]
          simp only [findLabelMem, findLabel, List.cons_append, List.nil_append, List.map_cons,
            List.findIdx?_cons, hl, if_true]
      | false =>
          rw [hl] at hq
          simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at hq
          obtain ⟨q₀, hq₀, rfl⟩ := hq
          have ih := findLabelMem_commonCalls? l hB₁ (q := q₀) hq₀
          have hnone : (js.map Prod.fst).findIdx? (isLabel l) = none := by
            rw [List.findIdx?_eq_none_iff]
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            exact commonCall?_noLabel hjs l hl y hy
          simp only [findLabelMem, findLabel] at ih
          simp only [findLabelMem, findLabel, List.map_append, List.findIdx?_append, hnone,
            Option.none_or, ih, Option.map_some, List.length_map, expPos_cons_succ,
            commonCall?_length hjs]
          rw [Nat.add_comm]

/-- The image of the position after a label is the position after the image of the
    label. -/
theorem expPos_label_succ (n : Nat) {l : LLabel} {B : List LinstrRM} {q : Nat}
    (hl : findLabelMem l B = some q) : expPos n B (q + 1) = expPos n B q + 1 := by
  unfold findLabelMem at hl
  obtain ⟨k, hk, hlab⟩ := findLabel_sound l _ q hl
  rw [List.getElem?_map] at hk
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hk
  have hctl : isCtl i.fst = true := by
    cases hi' : i.fst <;> simp_all [isLabel, isCtl]
  rw [expPos_succ n hi, expLen, shadowCall?_of_isCtl hctl]
  rfl

/-- The step of a non-control instruction that commutes with a change of the names `N`,
    from a state with the counter `q`. -/
theorem offCongr_step {N : List String} {i : LinstrRM} (hc : OffCongr N i)
    (hi : isCtl i.fst = false) (P P' : LprogM) {s t : LstateMF}
    {L' : String → Σ w, BitVec w} (q : Nat)
    (hL : ∀ r, r ∉ N → L' r = s.prog.base.reg.lvm r) (h : x86Isa.step P i s = some t) :
    ∃ L'' : String → Σ w, BitVec w, (∀ r, r ∉ N → L'' r = t.prog.base.reg.lvm r) ∧
      x86Isa.step P' i (setRL L' q s) = some (setRL L'' (q + 1) t) := by
  obtain ⟨L'', hL'', h'⟩ := hc P P' s t L' hL h
  refine ⟨L'', hL'', ?_⟩
  have hg := x86Isa_pcFree.step P' P' i hi (setRL L' s.prog.base.reg.lpc s) q
  rw [h'] at hg
  exact hg

/-- Register operands read at width `64` in two register files that agree on them give
    the same words. -/
theorem mapM_regOps_agree (R R' : LstateN) : ∀ (xs : List String),
    (∀ x ∈ xs, R'.lvm x = R.lvm x) →
    (xs.map LOperand.reg).mapM (evalOperandN R' 64)
      = (xs.map LOperand.reg).mapM (evalOperandN R 64)
  | [], _ => rfl
  | x :: xs, h => by
      have e : R'.lvm x = R.lvm x := h x (by simp)
      have h0 : evalOperandN R' 64 (.reg x) = evalOperandN R 64 (.reg x) := by
        simp only [evalOperandN, LstateN.getW]
        rw [e]
      simp only [List.map_cons, List.mapM_cons, h0]
      rw [mapM_regOps_agree R R' xs (fun y hy => h y (by simp [hy]))]

/-- **The step of a summary with a word result commutes with a change of names that are no
    operands.** -/
theorem procStep_setRL {pr : ProcSummary} (hrw : pr.RetWord) {d : String} {xs : List String}
    {s u : LstateMF}
    (L' : String → Σ w, BitVec w) (q : Nat) (hx : ∀ x ∈ xs, L' x = s.prog.base.reg.lvm x)
    (h : procStep pr d (xs.map LOperand.reg) s = some u) :
    ∃ w, u = retWord d w s ∧
      procStep pr d (xs.map LOperand.reg) (setRL L' q s) = some (retWord d w (setRL L' q s)) := by
  rw [procStep_of_retWord hrw] at h ⊢
  split at h
  · rename_i har
    obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨w, rfl, ?_⟩
    rw [if_pos har, argsRead_regs_congr (b := s.prog.base) (b' := (setRL L' q s).prog.base)
      pr.arrArgs rfl 0 hx, hvs]
    simp only [Option.bind_some, hw, Option.map_some]
  · cases h

/-- A step of an instruction of `commonSeq` on the x86 instruction set with procedures
    stays in the function and advances the counter by one. -/
theorem commonSeq_step_pc (T : ProcTable) (P : LprogM) {f : String} {args : List String}
    {res d : String} {xs : List String} {i : LinstrRM} (hi : i ∈ commonSeq f args res d xs)
    {a b : LstateMF} (h : (x86Isa.withProcs T).step P i a = some b) :
    b.prog.lfn = a.prog.lfn ∧ b.prog.base.lpc = a.prog.base.lpc + 1 := by
  simp only [commonSeq, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  have hmov : ∀ x y, (x86Isa.withProcs T).step P (movI x y) a = some b →
      b.prog.lfn = a.prog.lfn ∧ b.prog.base.lpc = a.prog.base.lpc + 1 := by
    intro x y hm
    rw [step_movI] at hm
    cases hm
    exact ⟨rfl, rfl⟩
  rcases hi with ⟨p, -, rfl⟩ | rfl | rfl
  · exact hmov _ _ h
  · replace h : (match procCall? T (callShadow res f (args.map LOperand.reg)) with
        | some q => procStep q.1 q.2.1 q.2.2 a
        | none => x86Isa.step P (callShadow res f (args.map LOperand.reg), .reg none) a)
        = some b := h
    rw [procCall?_callShadow] at h
    cases hT : T f with
    | none =>
        rw [hT] at h
        replace h : x86Isa.step P (callShadow res f (args.map LOperand.reg), .reg none) a
          = some b := h
        rw [x86Isa_refusesProcs
          (fun g => if g = f then some { arity := 0, run := fun _ => none } else none) P
          (callShadow res f (args.map LOperand.reg), .reg none) a
          (by rw [procCall?_callShadow]; simp)] at h
        cases h
    | some pr =>
        rw [hT] at h
        replace h : procStep pr res (args.map LOperand.reg) a = some b := h
        unfold procStep at h
        split at h
        · obtain ⟨vs, -, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨lfn_retRes res x a, lpc_retRes res x a⟩
        · cases h
  · exact hmov _ _ h

theorem runI_eq_runL (I : Isa) (P : LprogM) : ∀ (is : List LinstrRM) (s : LstateMF),
    runI I P is s = I.runL P is s
  | [], _ => rfl
  | i :: is, s => by
      simp only [runI, Isa.runL]
      cases I.step P i s with
      | none => rfl
      | some u => exact runI_eq_runL I P is u

/-- **One step of the body is a run of steps of the rewritten body.** Let `f` have a
    summary on words without a word-array result in `T`, the body `B` pass `commonFreshB`, `B'` be its rewriting onto `args` and
    `res`, every instruction of `B` that is neither a control instruction nor a shadow
    instruction commute with a change of the names `res :: args`, and no branch condition
    of `B` read them. From states related by `OffRel` along `expPos`, a step of the x86
    instruction set with procedures on `B` is matched by a run of steps on `B'` to related
    states. -/
theorem step_common {T : ProcTable} {f : String} {pr : ProcSummary} (hT : T f = some pr)
    (hwo : pr.WordOnly) (hrw : pr.RetWord) {args : List String} {res fn : String} {B B' : List LinstrRM}
    (hB : commonCalls? f args res B = some B') (hf : commonFreshB args res B = true)
    (hcg : ∀ i ∈ B, isCtl i.fst = false → shadowCall? i.fst = none →
      OffCongr (res :: args) i)
    (hcd : ∀ c l tag, (LinstrR.Lcond c l, tag) ∈ B → CondCongr (res :: args) c)
    {s u s' : LstateMF}
    (h : (x86Isa.withProcs T).lsemStepPMemF (singletonProgM fn B) s = some u)
    (hr : OffRel (res :: args) (expPos args.length B) s s') :
    ∃ k u', Steps (x86Isa.withProcs T) (singletonProgM fn B') k s' u' ∧
      OffRel (res :: args) (expPos args.length B) u u' := by
  obtain ⟨L', hL, rfl⟩ := hr
  unfold Isa.lsemStepPMemF at h
  cases hfi : findInstrMem (singletonProgM fn B) s.prog with
  | none => rw [hfi] at h; cases h
  | some i =>
    rw [hfi] at h
    replace h : (x86Isa.withProcs T).step (singletonProgM fn B) i s = some u := h
    unfold findInstrMem at hfi
    split at hfi
    · rename_i hfn
      replace hfi : B[s.prog.base.reg.lpc]? = some i := hfi
      have hmem : i ∈ B := List.mem_of_getElem? hfi
      obtain ⟨is, pre, post, his, hB', hpre⟩ := commonCalls?_split hB hfi
      have hsucc := expPos_succ args.length hfi
      rw [← hpre] at hsucc ⊢
      have hat : atPc (singletonProgM fn B') pre.length (setRL L' pre.length s) := ⟨hfn, rfl⟩
      cases hs : shadowCall? i.fst with
      | none =>
        have hq : procCall? T i.fst = none := by simp only [procCall?, hs, Option.bind_none]
        rw [Isa.withProcs_step_of_none _ T _ i s hq] at h
        have his' := commonCall?_none his hs
        subst his'
        have hget : (singletonProgM fn B').body[pre.length]? = some i := by
          show B'[pre.length]? = some i
          rw [hB']
          simp
        have hlen : expLen args.length i = 1 := by simp [expLen, hs]
        rw [hlen] at hsucc
        suffices hsuff : ∃ u', x86Isa.step (singletonProgM fn B') i (setRL L' pre.length s)
            = some u' ∧ OffRel (res :: args) (expPos args.length B) u u' by
          obtain ⟨u', hu', hrel⟩ := hsuff
          refine ⟨1, u', Steps.one ?_, hrel⟩
          rw [lsemStepPMemF_of_atPc _ hat hget, Isa.withProcs_step_of_none _ T _ i _ hq]
          exact hu'
        cases hctl : isCtl i.fst with
        | false =>
          obtain ⟨L'', hL'', hstep⟩ := offCongr_step (hcg i hmem hctl hs) hctl _
            (singletonProgM fn B') pre.length hL h
          have hpc : u.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 := by
            have hu := x86Isa_pcFree.lpc_succ _ hctl h
            rw [hu]
            rfl
          exact ⟨_, hstep, L'', hL'', by rw [hpc, hsucc]⟩
        | true =>
          rw [x86Isa.step_ctl _ i s hctl] at h
          rw [x86Isa.step_ctl _ i _ hctl]
          obtain ⟨ir, tag⟩ := i
          cases ir with
          | Llabel k l =>
              simp only [ctlStep, Option.some.injEq] at h
              subst h
              refine ⟨_, rfl, L', hL, ?_⟩
              show setRL L' (pre.length + 1) s
                = setRL L' (expPos args.length B (s.prog.base.reg.lpc + 1)) s
              rw [hsucc]
          | Lcond c l =>
              simp only [ctlStep] at h ⊢
              rw [hcd c l tag hmem s L' _ hL]
              split at h
              · rw [if_pos (by assumption)]
                unfold evalJumpMem at h ⊢
                cases hl : findLabelMem l (singletonProgM fn B).body with
                | none => rw [hl] at h; cases h
                | some q =>
                    rw [hl] at h
                    rw [show findLabelMem l (singletonProgM fn B').body
                      = some (expPos args.length B q) from findLabelMem_commonCalls? l hB hl]
                    simp only [Option.map_some, Option.some.injEq] at h
                    subst h
                    refine ⟨_, rfl, L', hL, ?_⟩
                    show setRL L' (expPos args.length B q + 1) s
                      = setRL L' (expPos args.length B (q + 1)) s
                    rw [expPos_label_succ args.length (B := B) hl]
              · rw [if_neg (by assumption)]
                simp only [Option.some.injEq] at h
                subst h
                refine ⟨_, rfl, L', hL, ?_⟩
                show setRL L' (pre.length + 1) s
                  = setRL L' (expPos args.length B (s.prog.base.reg.lpc + 1)) s
                rw [hsucc]
          | Lgoto tgt =>
              obtain ⟨g, l⟩ := tgt
              simp only [ctlStep] at h ⊢
              split at h
              · rw [if_pos (by assumption)]
                unfold evalJumpMem at h ⊢
                cases hl : findLabelMem l (singletonProgM fn B).body with
                | none => rw [hl] at h; cases h
                | some q =>
                    rw [hl] at h
                    rw [show findLabelMem l (singletonProgM fn B').body
                      = some (expPos args.length B q) from findLabelMem_commonCalls? l hB hl]
                    simp only [Option.map_some, Option.some.injEq] at h
                    subst h
                    refine ⟨_, rfl, L', hL, ?_⟩
                    show setRL L' (expPos args.length B q + 1) s
                      = setRL L' (expPos args.length B (q + 1)) s
                    rw [expPos_label_succ args.length (B := B) hl]
              · cases h
          | _ => simp [isCtl] at hctl
      | some q₃ =>
        obtain ⟨d, g, srcs⟩ := q₃
        obtain ⟨xs, hxs, rfl, hlen, rfl⟩ := commonCall?_some his hs
        have hsrcs := regNames?_eq hxs
        subst hsrcs
        have hq : procCall? T i.fst = some (pr, d, xs.map LOperand.reg) := by
          simp only [procCall?, hs, Option.bind_some, hT, Option.map_some]
        have h1 : procStep pr d (xs.map LOperand.reg) s = some u := by
          simpa only [Isa.withProcs, hq] using h
        obtain ⟨hnd, hxa, hda, hdr⟩ := commonFreshB_site hf hmem hs hxs
        have hxr := commonFreshB_site_res hf hmem hs hxs
        obtain ⟨w, rfl, h2⟩ := procStep_setRL hrw L' pre.length
          (fun x hx => hL x (by
            simp only [List.mem_cons, not_or]
            exact ⟨hxr x hx, hxa x hx⟩)) h1
        obtain ⟨L₂, hrun, hL₂⟩ := commonCall_sim hT hwo hrw (singletonProgM fn B') res d hlen hnd hxa
          h2
        rw [runI_eq_runL] at hrun
        obtain ⟨hst, -⟩ := steps_of_runL (x86Isa.withProcs T) (singletonProgM fn B') _ pre post
          _ _ hB' hat (fun j hj a b hab => commonSeq_step_pc T _ hj hab) hrun
        have hlenE : expLen args.length i = args.length + 2 := by simp [expLen, hs]
        rw [hlenE] at hsucc
        refine ⟨_, _, hst, L₂, fun r hr => ?_, ?_⟩
        · simp only [List.mem_cons, not_or] at hr
          rw [hL₂ r hr.2 hr.1, retWord_eq_regUpd, retWord_eq_regUpd]
          show (if r = d then _ else L' r) = (if r = d then _ else s.prog.base.reg.lvm r)
          split
          · rfl
          · exact hL r (by simp only [List.mem_cons, not_or]; exact hr)
        · show setRL L₂ (pre.length + 1 + (args.length + 1)) s
            = setRL L₂ (expPos args.length B (s.prog.base.reg.lpc + 1)) s
          rw [hsucc, Nat.add_assoc, Nat.add_left_comm 1 args.length 1]
    · cases hfi

/-- **A run of steps of the body is a run of steps of the rewritten body**, between states
    related by `OffRel` along `expPos`. -/
theorem steps_common {T : ProcTable} {f : String} {pr : ProcSummary} (hT : T f = some pr)
    (hwo : pr.WordOnly) (hrw : pr.RetWord) {args : List String} {res fn : String} {B B' : List LinstrRM}
    (hB : commonCalls? f args res B = some B') (hf : commonFreshB args res B = true)
    (hcg : ∀ i ∈ B, isCtl i.fst = false → shadowCall? i.fst = none →
      OffCongr (res :: args) i)
    (hcd : ∀ c l tag, (LinstrR.Lcond c l, tag) ∈ B → CondCongr (res :: args) c) :
    ∀ (n : Nat) (s t s' : LstateMF),
      Steps (x86Isa.withProcs T) (singletonProgM fn B) n s t →
      OffRel (res :: args) (expPos args.length B) s s' →
      ∃ n' t', Steps (x86Isa.withProcs T) (singletonProgM fn B') n' s' t' ∧
        OffRel (res :: args) (expPos args.length B) t t'
  | 0, s, t, s', h, hr => by
      have hst : s = t := Option.some.inj h
      subst hst
      exact ⟨0, s', Steps.refl _ _ _, hr⟩
  | n + 1, s, t, s', h, hr => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      obtain ⟨k, m', hk, hr'⟩ := step_common hT hwo hrw hB hf hcg hcd hm hr
      obtain ⟨n', t', hn', hr''⟩ := steps_common hT hwo hrw hB hf hcg hcd n m t m' h hr'
      exact ⟨k + n', t', hk.trans hn', hr''⟩

/-- A halted state of the body is related to halted states of the rewritten body. -/
theorem halted_common {f : String} {args : List String} {res fn : String}
    {B B' : List LinstrRM} (hB : commonCalls? f args res B = some B') {N : List String}
    {t t' : LstateMF} (ht : Halted (singletonProgM fn B) t)
    (hr : OffRel N (expPos args.length B) t t') : Halted (singletonProgM fn B') t' := by
  obtain ⟨L', -, rfl⟩ := hr
  unfold Halted findInstrMem at ht ⊢
  split at ht
  · rename_i hfn
    rw [if_pos (show (setRL L' _ t).prog.lfn = (singletonProgM fn B').lfn from hfn)]
    have hle : B.length ≤ t.prog.base.reg.lpc := List.getElem?_eq_none_iff.mp ht
    show B'[expPos args.length B t.prog.base.reg.lpc]? = none
    rw [expPos_of_le _ hle, ← commonCalls?_length hB]
    exact List.getElem?_eq_none (Nat.le_refl _)
  · rename_i hfn
    exact if_neg hfn

/-- A state at the counter `0` is related to itself. -/
theorem offRel_entry (N : List String) (n : Nat) (B : List LinstrRM) {s : LstateMF}
    (h0 : s.prog.base.reg.lpc = 0) : OffRel N (expPos n B) s s :=
  ⟨s.prog.base.reg.lvm, fun _ _ => rfl, by
    rw [h0, expPos_zero]
    calc s = setRL s.prog.base.reg.lvm s.prog.base.reg.lpc s := rfl
      _ = setRL s.prog.base.reg.lvm 0 s := by rw [h0]⟩

/-- Related states agree on the registers outside `N`, the arrays and the word memory. -/
theorem OffRel.obs {N : List String} {ψ : Nat → Nat} {t t' : LstateMF} (h : OffRel N ψ t t')
    {outs : List String} (ho : ∀ r ∈ outs, r ∉ N) : Obs outs t t' := by
  obtain ⟨L', hL, rfl⟩ := h
  exact ⟨fun r hr => hL r (ho r hr), rfl, rfl⟩

/-- **The rewriting of a body onto common names preserves halting runs.** Let `f` have a
    summary on words in `T`, the body `B` pass `commonFreshB`, `B'` be its rewriting onto `args` and
    `res`, every instruction of `B` that is neither a control instruction nor a shadow
    instruction commute with a change of the names `res :: args`, and no branch condition
    of `B` read them. A halting run of the x86 instruction set with procedures on `B` from
    a state at the counter `0` to `t` is matched by a halting run on `B'` from the same
    state to a state `t'` that is `t` up to the registers `res :: args` and the counter,
    which is at the image of the counter of `t`. -/
theorem commonCalls_run {T : ProcTable} {f : String} {pr : ProcSummary} (hT : T f = some pr)
    (hwo : pr.WordOnly) (hrw : pr.RetWord) {args : List String} {res fn : String} {B B' : List LinstrRM}
    (hB : commonCalls? f args res B = some B') (hf : commonFreshB args res B = true)
    (hcg : ∀ i ∈ B, isCtl i.fst = false → shadowCall? i.fst = none →
      OffCongr (res :: args) i)
    (hcd : ∀ c l tag, (LinstrR.Lcond c l, tag) ∈ B → CondCongr (res :: args) c)
    {fuel : Nat} {s t : LstateMF} (h0 : s.prog.base.reg.lpc = 0)
    (hrun : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧
      OffRel (res :: args) (expPos args.length B) t t' := by
  obtain ⟨n, -, hn, ht⟩ := steps_of_lsemFuelMemF (x86Isa.withProcs T) _ fuel s t hrun
  obtain ⟨n', t', hn', hr⟩ := steps_common hT hwo hrw hB hf hcg hcd n s t s hn
    (offRel_entry _ _ _ h0)
  exact ⟨n' + 0, t', lsemFuelMemF_of_steps _ _ hn' (halted_common hB ht hr) 0, hr⟩

/-- **The end states of the two runs agree on the registers outside the common names, the
    arrays and the word memory.** -/
theorem commonCalls_run_obs {T : ProcTable} {f : String} {pr : ProcSummary}
    (hT : T f = some pr) (hwo : pr.WordOnly) (hrw : pr.RetWord) {args : List String} {res fn : String}
    {B B' : List LinstrRM}
    (hB : commonCalls? f args res B = some B') (hf : commonFreshB args res B = true)
    (hcg : ∀ i ∈ B, isCtl i.fst = false → shadowCall? i.fst = none →
      OffCongr (res :: args) i)
    (hcd : ∀ c l tag, (LinstrR.Lcond c l, tag) ∈ B → CondCongr (res :: args) c)
    {outs : List String} (ho : ∀ r ∈ outs, r ∉ res :: args)
    {fuel : Nat} {s t : LstateMF} (h0 : s.prog.base.reg.lpc = 0)
    (hrun : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  obtain ⟨fuel', t', h', hr⟩ := commonCalls_run hT hwo hrw hB hf hcg hcd h0 hrun
  exact ⟨fuel', t', h', hr.obs ho⟩

/-- **The rewriting of a checked body onto common names preserves halting runs.** Let `f`
    have a summary on words in `T`, the body `B` pass `commonFreshB`, and `B'` be its rewriting onto
    `args` and `res`. A halting run of the x86 instruction set with procedures on `B` from
    a state at the counter `0` to `t` is matched by a halting run on `B'` from the same
    state to a state that is `t` up to the registers `res :: args` and the counter, which
    is at the image of the counter of `t`. -/
theorem run_onCommonNames {T : ProcTable} {f : String} {pr : ProcSummary} (hT : T f = some pr)
    (hwo : pr.WordOnly) (hrw : pr.RetWord) {args : List String} {res fn : String} {B B' : List LinstrRM}
    (hB : commonCalls? f args res B = some B') (hf : commonFreshB args res B = true)
    {fuel : Nat} {s t : LstateMF} (h0 : s.prog.base.reg.lpc = 0)
    (hrun : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧
      OffRel (res :: args) (expPos args.length B) t t' :=
  commonCalls_run hT hwo hrw hB hf
    (fun _ hi hc hs => commonCongrB_offCongr (commonFreshB_congr hf) hi hc hs)
    (fun _ _ _ hi => commonCongrB_condCongr (commonFreshB_congr hf) hi) h0 hrun

/-- **The end states of the two runs of a checked body agree on the registers outside the
    common names, the arrays and the word memory.** -/
theorem obs_onCommonNames {T : ProcTable} {f : String} {pr : ProcSummary}
    (hT : T f = some pr) (hwo : pr.WordOnly) (hrw : pr.RetWord) {args : List String} {res fn : String}
    {B B' : List LinstrRM}
    (hB : commonCalls? f args res B = some B') (hf : commonFreshB args res B = true)
    {outs : List String} (ho : ∀ r ∈ outs, r ∉ res :: args)
    {fuel : Nat} {s t : LstateMF} (h0 : s.prog.base.reg.lpc = 0)
    (hrun : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  obtain ⟨fuel', t', h', hr⟩ := run_onCommonNames hT hwo hrw hB hf h0 hrun
  exact ⟨fuel', t', h', hr.obs ho⟩

/-! ## 12. A halting run of a cut program is a segment of the body -/

/-- A step of `I` stays in the function of its state. -/
def FnStable (I : Isa) : Prop :=
  ∀ (P : LprogM) (i : LinstrRM) (s u : LstateMF), I.step P i s = some u →
    u.prog.lfn = s.prog.lfn

/-- A step of `x86Isa` stays in the function of its state. -/
theorem fnStable_x86Isa : FnStable x86Isa := fun P i s u h =>
  (X86Backend.AllocCheck.LcmdCFG.evalInstrPMemF_next P i s u h).1

/-- A halting run of an instruction set whose steps stay in the function ends in the
    function of its start state. -/
theorem FnStable.lsemFuelMemF_lfn {I : Isa} (hS : FnStable I) (P : LprogM) :
    ∀ (n : Nat) (s t : LstateMF), I.lsemFuelMemF P n s = some t → t.prog.lfn = s.prog.lfn
  | 0, s, t, h => by
      simp only [Isa.lsemFuelMemF] at h
      split at h
      · cases h; rfl
      · cases h
  | n + 1, s, t, h => by
      simp only [Isa.lsemFuelMemF] at h
      split at h
      · cases h; rfl
      · rename_i i _
        split at h
        · rename_i s' hs'
          exact (hS.lsemFuelMemF_lfn P n s' t h).trans (hS P i s s' hs')
        · cases h

/-- The label a conditional jump or a goto jumps to. -/
def jumpLabel? : LinstrR → Option LLabel
  | .Lcond _ l => some l
  | .Lgoto (_, l) => some l
  | _ => none

/-- **The cut `C` of `B` along `φ` for the exit `x` halts only at the exit.** The image of
    the position of a shadow instruction of a call of a symbol of `T` other than the exit
    holds such a shadow instruction; when the exit is a shadow instruction, the image of
    the end of the body holds one; and every label a jump of `B` names is declared in
    `B`. -/
structure IsCutRev (T : ProcTable) (B : List LinstrRM) (x : Option Nat) (C : List LinstrRM)
    (φ : Nat → Nat) : Prop where
  shadow : ∀ (p : Nat) (i : LinstrRM), B[p]? = some i → procCall? T i.fst ≠ none →
    x ≠ some p → ∃ j, C[φ p]? = some j ∧ procCall? T j.fst ≠ none
  stop : ∀ p, x = some p → ∃ j, C[φ B.length]? = some j ∧ procCall? T j.fst ≠ none
  target : ∀ (p : Nat) (i : LinstrRM) (l : LLabel), B[p]? = some i →
    jumpLabel? i.fst = some l → (findLabelMem l B).isSome = true

/-- **The check of `IsCutRev`.** -/
def isCutRevB (T : ProcTable) (B : List LinstrRM) (x : Option Nat) (C : List LinstrRM)
    (φ : Nat → Nat) : Bool :=
  (List.range B.length).all (fun p =>
    match B[p]? with
    | some i =>
        ((procCall? T i.fst).isNone || x == some p || (C[φ p]?).any (isProcB T)) &&
        (match jumpLabel? i.fst with
          | some l => (findLabelMem l B).isSome
          | none => true)
    | none => true) &&
  (x.isNone || (C[φ B.length]?).any (isProcB T))

/-- **Soundness of `isCutRevB`.** -/
theorem isCutRev_of_isCutRevB {T : ProcTable} {B : List LinstrRM} {x : Option Nat}
    {C : List LinstrRM} {φ : Nat → Nat} (h : isCutRevB T B x C φ = true) :
    IsCutRev T B x C φ := by
  simp only [isCutRevB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hall, hstop⟩ := h
  have hany : ∀ {o : Option LinstrRM}, o.any (isProcB T) = true →
      ∃ j, o = some j ∧ procCall? T j.fst ≠ none := by
    intro o ho
    cases o with
    | none => cases ho
    | some j => exact ⟨j, rfl, Option.isSome_iff_ne_none.mp ho⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p i hp hq hx
    have hpi := hall p (List.getElem?_eq_some_iff.mp hp).1
    rw [hp] at hpi
    simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hpi
    rcases hpi.1 with (h1 | h1) | h1
    · exact absurd h1 hq
    · exact absurd h1 hx
    · exact hany h1
  · intro p hx
    subst hx
    simp only [Option.isNone_some, Bool.false_or] at hstop
    exact hany hstop
  · intro p i l hp hl
    have hpi := hall p (List.getElem?_eq_some_iff.mp hp).1
    rw [hp] at hpi
    simp only [Bool.and_eq_true, hl] at hpi
    exact hpi.2

/-! ## 12a. The cut programs under a change of the function name -/

/-- **The goto to the label `fin` sent to the function `fn'`**: a goto to `fin` jumps
    within `fn'`, and every other instruction is unchanged. -/
def renFin (fn' : String) (fin : LLabel) (i : LinstrRM) : LinstrRM :=
  match i with
  | (.Lgoto (f, l), tag) => (.Lgoto (if l = fin then fn' else f, l), tag)
  | _ => i

/-- An instruction that jumps to no label `fin` is unchanged by `renFin`. -/
theorem renFin_of_jumpLabel {fn' : String} {fin : LLabel} {i : LinstrRM}
    (h : jumpLabel? i.fst ≠ some fin) : renFin fn' fin i = i := by
  obtain ⟨ir, tag⟩ := i
  cases ir <;> try rfl
  rename_i d
  obtain ⟨f, l⟩ := d
  have hl : l ≠ fin := fun e => h (by rw [e]; rfl)
  simp [renFin, hl]

/-- The exit jump of `fn` is sent to the exit jump of `fn'`. -/
@[simp] theorem renFin_exitI (fn fn' : String) (fin : LLabel) :
    renFin fn' fin (exitI fn fin) = exitI fn' fin := by
  simp [renFin, exitI]

/-- The declaration of `fin` is unchanged by `renFin`. -/
@[simp] theorem renFin_finI (fn' : String) (fin : LLabel) : renFin fn' fin (finI fin) = finI fin :=
  rfl

/-- `renFin` keeps the label an instruction declares. -/
theorem isLabel_renFin (fn' : String) (fin l : LLabel) (i : LinstrRM) :
    isLabel l (renFin fn' fin i).fst = isLabel l i.fst := by
  obtain ⟨ir, tag⟩ := i
  cases ir <;> rfl

/-- `renFin` keeps the shadow instructions of calls of symbols of `T`. -/
theorem procCall?_renFin (T : ProcTable) (fn' : String) (fin : LLabel) (i : LinstrRM) :
    procCall? T (renFin fn' fin i).fst = procCall? T i.fst := by
  obtain ⟨ir, tag⟩ := i
  cases ir <;> rfl

/-- `renFin` keeps the position of the first declaration of every label. -/
theorem findLabelMem_map_renFin (fn' : String) (fin l : LLabel) (C : List LinstrRM) :
    findLabelMem l (C.map (renFin fn' fin)) = findLabelMem l C := by
  simp only [findLabelMem, JasminLsemLabeled.findLabel, List.map_map, List.findIdx?_map]
  congr 1
  funext i
  exact isLabel_renFin fn' fin l i

/-- **The cut programs of the function `fn'` are those of `fn` under `renFin`**, for a body
    with no jump to the label `fin`. -/
theorem map_renFin_cutAt {fn fn' : String} {fin : LLabel} {B : List LinstrRM}
    (hB : ∀ i ∈ B, jumpLabel? i.fst ≠ some fin) (e x : Option Nat) :
    (cutAt fn fin B e x).map (renFin fn' fin) = cutAt fn' fin B e x := by
  have hBm : B.map (renFin fn' fin) = B := by
    have h := List.map_congr_left (f := renFin fn' fin) (g := id) (l := B)
      fun i hi => renFin_of_jumpLabel (hB i hi)
    simpa using h
  have hget : ∀ (L : List LinstrRM) (q : Nat) (d : LinstrRM),
      renFin fn' fin ((L[q]?).getD d) = ((L.map (renFin fn' fin))[q]?).getD (renFin fn' fin d) := by
    intro L q d
    cases h : L[q]? <;> simp [List.getElem?_map, h]
  cases x <;> cases e <;>
    simp only [cutAt, List.map_append, List.map_cons, List.map_nil, List.map_drop,
      List.map_take, List.map_set, hget, hBm, renFin_exitI, renFin_finI]

/-- The cut program ends with the declaration of `fin`. -/
theorem cutAt_last (fn : String) (fin : LLabel) (B : List LinstrRM) (e x : Option Nat) :
    (cutAt fn fin B e x)[(cutAt fn fin B e x).length - 1]? = some (finI fin) := by
  rw [← List.getLast?_eq_getElem?]
  cases x <;> cases e <;> simp [cutAt, List.getLast?_append, List.getLast?_cons]

/-- **A cut of `B` at the function `fn` is a cut at every function `fn'`**, for the cut
    programs `cutAt` and a body with no jump to the label `fin`. -/
theorem IsCut.rename {T : ProcTable} {fn fn' : String} {fin : LLabel} {B : List LinstrRM}
    {e x : Option Nat} {φ : Nat → Nat} (hB : ∀ i ∈ B, jumpLabel? i.fst ≠ some fin)
    (h : IsCut T fn B e x (cutAt fn fin B e x) φ) :
    IsCut T fn' B e x (cutAt fn' fin B e x) φ := by
  rw [← map_renFin_cutAt (fn := fn) hB]
  refine ⟨h.entry, fun p i hp hq => ?_, fun l q hl => ?_, ?_⟩
  · obtain ⟨hC, hs⟩ := h.instr p i hp hq
    refine ⟨?_, hs⟩
    rw [List.getElem?_map, hC, Option.map_some,
      renFin_of_jumpLabel (hB i (List.mem_of_getElem? hp))]
  · rw [findLabelMem_map_renFin]
    exact h.label l q hl
  · obtain ⟨tag, fin0, k, hC, hk, hk'⟩ := h.exit
    have hfin : fin0 = fin := by
      have hk1 := hk
      unfold findLabelMem at hk1
      obtain ⟨j, hj, hlab⟩ := JasminLsemLabeled.findLabel_sound fin0 _ k hk1
      have hlast := cutAt_last fn fin B e x
      rw [show (cutAt fn fin B e x).length - 1 = k by omega] at hlast
      rw [List.getElem?_map, hlast, Option.map_some] at hj
      cases hj
      simpa [finI, JasminLsemLabeled.isLabel] using hlab
    subst hfin
    refine ⟨tag, fin0, k, ?_, by rw [findLabelMem_map_renFin]; exact hk, by
      rw [List.length_map]; exact hk'⟩
    rw [List.getElem?_map, hC, Option.map_some]
    simp [renFin]

/-- **A cut that halts only at its exit stays so under `renFin`.** -/
theorem IsCutRev.map_renFin {T : ProcTable} {B : List LinstrRM} {x : Option Nat}
    {C : List LinstrRM} {φ : Nat → Nat} (fn' : String) (fin : LLabel)
    (h : IsCutRev T B x C φ) : IsCutRev T B x (C.map (renFin fn' fin)) φ := by
  refine ⟨fun p i hp hq hx => ?_, fun p hx => ?_, h.target⟩
  · obtain ⟨j, hj, hjq⟩ := h.shadow p i hp hq hx
    exact ⟨renFin fn' fin j, by rw [List.getElem?_map, hj]; rfl,
      by rw [procCall?_renFin]; exact hjq⟩
  · obtain ⟨j, hj, hjq⟩ := h.stop p hx
    exact ⟨renFin fn' fin j, by rw [List.getElem?_map, hj]; rfl,
      by rw [procCall?_renFin]; exact hjq⟩

/-- A body that `IsCutRev` accepts and that declares no label `fin` has no jump to
    `fin`. -/
theorem jumpLabel_ne_of_isCutRev {T : ProcTable} {B : List LinstrRM} {x : Option Nat}
    {C : List LinstrRM} {φ : Nat → Nat} {fin : LLabel} (h : IsCutRev T B x C φ)
    (hfin : findLabelMem fin B = none) : ∀ i ∈ B, jumpLabel? i.fst ≠ some fin := by
  intro i hi hj
  obtain ⟨p, hp⟩ := List.getElem?_of_mem hi
  have := h.target p i fin hp hj
  rw [hfin] at this
  cases this

section CutOkRename

variable [DecidableEq LinstrR]

/-- **The cut checks at one function name give the cut relations at every function
    name.** If `cutOkB T fn fin B` accepts and `B` has no jump to the label `fin`, then for
    every function name `fn'` and every entry and exit of `B` the cut program
    `cutAt fn' fin B e x` is a cut of `B` at `fn'` along `cutPos B e`. -/
theorem isCut_cutAt_of_cutOkB {T : ProcTable} {fn : String} {fin : LLabel}
    {B : List LinstrRM} (hok : cutOkB T fn fin B = true)
    (hB : ∀ i ∈ B, jumpLabel? i.fst ≠ some fin) (fn' : String) {e x : Option Nat}
    (he : IsSite T B e) (hx : IsSite T B x) :
    IsCut T fn' B e x (cutAt fn' fin B e x) (cutPos B e) := by
  simp only [cutOkB, List.all_eq_true] at hok
  exact (isCut_of_isCutB (hok e (mem_of_isSite he) x (mem_of_isSite hx))).rename hB

end CutOkRename

/-- **The reverse cut check at one function name gives the reverse cut relation at every
    function name**, for a body with no jump to the label `fin`. -/
theorem isCutRev_cutAt_rename {T : ProcTable} {fn fn' : String} {fin : LLabel}
    {B : List LinstrRM} {e x : Option Nat} {φ : Nat → Nat}
    (hB : ∀ i ∈ B, jumpLabel? i.fst ≠ some fin)
    (h : isCutRevB T B x (cutAt fn fin B e x) φ = true) :
    IsCutRev T B x (cutAt fn' fin B e x) φ := by
  rw [← map_renFin_cutAt (fn := fn) hB]
  exact (isCutRev_of_isCutRevB h).map_renFin fn' fin

/-- A run of steps from a halted state is empty. -/
theorem halted_steps_eq {I : Isa} {P : LprogM} : ∀ {m : Nat} {a t : LstateMF},
    Steps I P m a t → Halted P a → a = t
  | 0, _, _, h, _ => Option.some.inj h
  | m + 1, a, t, h, ha => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, -⟩ := h
      unfold Isa.lsemStepPMemF at hc
      rw [show findInstrMem P a.prog = none from ha] at hc
      cases hc

/-- A run of steps to a halted state from a state that fetches `j` starts with the step of
    `j`. -/
theorem first_step {I : Isa} {P : LprogM} {m : Nat} {a t : LstateMF} (h : Steps I P m a t)
    (ht : Halted P t) {j : LinstrRM} (hj : findInstrMem P a.prog = some j) :
    ∃ m' c, m = m' + 1 ∧ I.step P j a = some c ∧ Steps I P m' c t := by
  cases m with
  | zero =>
      have hat : a = t := Option.some.inj h
      subst hat
      rw [show findInstrMem P a.prog = none from ht] at hj
      cases hj
  | succ m =>
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      unfold Isa.lsemStepPMemF at hc
      rw [hj] at hc
      exact ⟨m, c, rfl, hc, h⟩

/-- **A run of steps of a cut program to a halted state is a segment of the body.** Let
    `C` be a cut of `B` along `φ` for the entry `e` and the exit `x` that halts only at the
    exit, and let the steps of `I` stay in the function. A run of steps of `C` from the
    image of a state `w` of `fn` at a position of `B` to a halted state `t` is a segment of
    `B` from `w` to the exit `x`, and `t` is the end state of the segment with the counter
    at the length of `C`. -/
theorem segTo_of_steps_cut {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {e x : Option Nat} {C : List LinstrRM} {φ : Nat → Nat} (hI : PcFree I)
    (hR : I.RefusesProcs T) (hS : FnStable I) (hc : IsCut T fn B e x C φ)
    (hv : IsCutRev T B x C φ) {t : LstateMF} (ht : Halted (singletonProgM fn C) t)
    (m : Nat) : ∀ (w : LstateMF), w.prog.lfn = fn → w.prog.base.lpc ≤ B.length →
      Steps I (singletonProgM fn C) m (emb φ w) t →
      ∃ w', SegTo I T (singletonProgM fn B) w x w' ∧ t = goto w' C.length := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro w hfn hle hst
  have hat : atPc (singletonProgM fn C) (φ w.prog.base.lpc) (emb φ w) := ⟨hfn, rfl⟩
  have hfetch : ∀ j, C[φ w.prog.base.lpc]? = some j →
      findInstrMem (singletonProgM fn C) (emb φ w).prog = some j := fun j hj => by
    rw [findInstrMem_of_atPc hat]
    exact hj
  have hrefuse : ∀ j, C[φ w.prog.base.lpc]? = some j → procCall? T j.fst ≠ none → False := by
    intro j hj hne
    obtain ⟨m', c, -, hstep, -⟩ := first_step hst ht (hfetch j hj)
    rw [hR _ j _ hne] at hstep
    cases hstep
  have hexit : w.prog.base.lpc = stopPos B x → t = goto w C.length := by
    intro hpc
    have hex := exit_step (I := I) hc hfn hpc
    obtain ⟨tag, fin, k, hi, -, -⟩ := hc.exit
    rw [← hpc] at hi
    obtain ⟨m', c, -, hstep, hrest⟩ := first_step hst ht (hfetch _ hi)
    rw [lsemStepPMemF_of_atPc I hat hi, hstep] at hex
    cases hex
    exact (halted_steps_eq hrest
      (halted_of_atPc (P := singletonProgM fn C) ⟨hfn, rfl⟩ (Nat.le_refl _))).symm
  cases hBi : B[w.prog.base.lpc]? with
  | none =>
      have hlen : w.prog.base.lpc = B.length :=
        Nat.le_antisymm hle (List.getElem?_eq_none_iff.mp hBi)
      cases x with
      | none =>
          refine ⟨w, ⟨0, Steps.refl _ _ _, ?_⟩, hexit hlen⟩
          show findInstrMem (singletonProgM fn B) w.prog = none
          unfold findInstrMem
          rw [if_pos (show w.prog.lfn = (singletonProgM fn B).lfn from hfn)]
          exact hBi
      | some p =>
          obtain ⟨j, hj, hne⟩ := hv.stop p rfl
          rw [← hlen] at hj
          exact (hrefuse j hj hne).elim
  | some i =>
      by_cases hq : procCall? T i.fst = none
      · obtain ⟨hCi, hφ⟩ := hc.instr _ i hBi hq
        obtain ⟨m', c, rfl, hstep, hrest⟩ := first_step hst ht (hfetch i hCi)
        have hsome : ∃ w₁, I.step (singletonProgM fn B) i w = some w₁ := by
          cases hctl : isCtl i.fst with
          | false =>
              have hg := hI.step (singletonProgM fn B) (singletonProgM fn C) i hctl w
                (φ w.prog.base.lpc)
              rw [show goto w (φ w.prog.base.lpc) = emb φ w from rfl, hstep] at hg
              cases hw : I.step (singletonProgM fn B) i w with
              | none => rw [hw] at hg; cases hg
              | some w₁ => exact ⟨w₁, rfl⟩
          | true =>
              rw [I.step_ctl _ i _ hctl] at hstep
              rw [I.step_ctl _ i _ hctl]
              obtain ⟨ir, tag⟩ := i
              cases ir with
              | Llabel k l => exact ⟨_, rfl⟩
              | Lcond c l =>
                  obtain ⟨q, hq'⟩ := Option.isSome_iff_exists.mp (hv.target _ _ l hBi rfl)
                  simp only [ctlStep]
                  split
                  · exact ⟨_, evalJumpMem_of_findLabelMem (P := singletonProgM fn B) hq' w⟩
                  · exact ⟨_, rfl⟩
              | Lgoto tgt =>
                  obtain ⟨g, l⟩ := tgt
                  obtain ⟨q, hq'⟩ := Option.isSome_iff_exists.mp (hv.target _ _ l hBi rfl)
                  simp only [ctlStep] at hstep ⊢
                  split at hstep
                  · rw [if_pos (by assumption)]
                    exact ⟨_, evalJumpMem_of_findLabelMem (P := singletonProgM fn B) hq' w⟩
                  · cases hstep
              | _ => simp [isCtl] at hctl
        obtain ⟨w₁, hw₁⟩ := hsome
        have hB1 : I.lsemStepPMemF (singletonProgM fn B) w = some w₁ := by
          rw [lsemStepPMemF_of_atPc I (k := w.prog.base.lpc) ⟨hfn, rfl⟩ hBi]
          exact hw₁
        obtain ⟨hC1, hle₁⟩ := step_emb hI hR hc hB1
        rw [lsemStepPMemF_of_atPc I hat hCi, hstep] at hC1
        cases hC1
        obtain ⟨w', ⟨n, hn, hx⟩, hw'⟩ := ih m' (Nat.lt_succ_self _) w₁
          ((hS _ _ _ _ hw₁).trans hfn) hle₁ hrest
        exact ⟨w', ⟨1 + n, (Steps.one hB1).trans hn, hx⟩, hw'⟩
      · by_cases hxp : x = some w.prog.base.lpc
        · subst hxp
          exact ⟨w, ⟨0, Steps.refl _ _ _, ⟨hfn, rfl⟩, i, hBi, Option.isSome_iff_ne_none.mpr hq⟩,
            hexit rfl⟩
        · obtain ⟨j, hj, hne⟩ := hv.shadow _ i hBi hq hxp
          exact (hrefuse j hj hne).elim

/-- **A halting run of a cut program is a segment of the body**, the converse of
    `cutRun_of_segTo`: a halting run of `C` from the counter `0`, from `s` to `u`, is a
    segment of `B` from `s` at the entry position to `u` at some counter. -/
theorem segTo_of_cutRun {I : Isa} {T : ProcTable} {fn : String} {B : List LinstrRM}
    {e x : Option Nat} {C : List LinstrRM} {φ : Nat → Nat} (hI : PcFree I)
    (hR : I.RefusesProcs T) (hS : FnStable I) (hc : IsCut T fn B e x C φ)
    (hv : IsCutRev T B x C φ) {s u : LstateMF} (hfn : s.prog.lfn = fn)
    (hle : entryPos e ≤ B.length) (h : CutRun I fn C s u) :
    ∃ q, SegTo I T (singletonProgM fn B) (goto s (entryPos e)) x (goto u q) := by
  obtain ⟨k, q, hk⟩ := h
  obtain ⟨m, -, hm, ht⟩ := steps_of_lsemFuelMemF I _ (k + 0) _ _ (hk 0)
  have hs0 : emb φ (goto s (entryPos e)) = goto s 0 := by
    show goto (goto s (entryPos e)) (φ (entryPos e)) = goto s 0
    rw [hc.entry]
    rfl
  rw [← hs0] at hm
  obtain ⟨w', hseg, hw'⟩ := segTo_of_steps_cut hI hR hS hc hv ht m
    (goto s (entryPos e)) hfn hle hm
  refine ⟨w'.prog.base.lpc, ?_⟩
  have hw : goto u w'.prog.base.lpc = w' := by
    calc goto u w'.prog.base.lpc = goto (goto u q) w'.prog.base.lpc := rfl
      _ = goto (goto w' C.length) w'.prog.base.lpc := by rw [hw']
      _ = w' := rfl
  rw [hw]
  exact hseg

/-! ## 13. Soundness of a validation by segments -/

/-- The step of the summary does not read the counter. -/
theorem Glue.goto {T : ProcTable} {P : LprogM} {p : Nat} {u v : LstateMF}
    (hg : Glue T P p u v) (k : Nat) : Glue T P p (goto u k) (goto v (k + 1)) := by
  obtain ⟨i, pr, dst, srcs, hi, hq, hstep⟩ := hg
  refine ⟨i, pr, dst, srcs, hi, hq, ?_⟩
  have he : evalOperandN (Ascent.IsaCfg.goto u k).prog.base.reg 64
      = evalOperandN u.prog.base.reg 64 := by
    funext o
    cases o <;> rfl
  unfold procStep at hstep ⊢
  rw [argsRead_congr (b := u.prog.base) (b' := (Ascent.IsaCfg.goto u k).prog.base) pr.arrArgs
    rfl 0 srcs fun o _ => congrFun he o]
  split at hstep
  · rw [if_pos (by assumption)]
    obtain ⟨vs, hvs, hstep⟩ := Option.bind_eq_some_iff.mp hstep
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hstep
    rw [hvs]
    simp only [Option.bind_some, hx, Option.map_some]
    cases x <;> rfl
  · cases hstep

/-- **A chain of halting runs of cut programs of `B` on the instruction set `I` is, under a
    simulation `CutSimI I`, a chain of segments of `B'`.** The branch condition of `I` does
    not read the counter, `I` refuses the procedures of `T`, the steps of `I` stay in the
    function, and the cut programs of `B'` are cuts that halt only at their exits. From a
    state of `fn` related by `R e` to the start of the chain, for an entry `e` of `B`, the
    chain of segments of `B'` starts at the entry position of `site e` and ends in a state
    that agrees with the end of the chain on the registers `outs`, the arrays and the word
    memory. -/
theorem runChain_of_cutChainI {I : Isa} {T : ProcTable} {outs : List String} {fn : String}
    {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
    {pos' : Option Nat → Option Nat → Nat → Nat} (hI : PcFree I) (hR : I.RefusesProcs T)
    (hS : FnStable I)
    (hcut' : ∀ e x, IsSite T B' e → IsSite T B' x →
      IsCut T fn B' e x (cut' e x) (pos' e x) ∧ IsCutRev T B' x (cut' e x) (pos' e x))
    (sim : CutSimI I T outs fn B B' cut cut') {e : Option Nat} {s t : LstateMF}
    (h : CutChain I T fn B cut e s t) :
    ∀ (s' : LstateMF), sim.R e s s' → s'.prog.lfn = fn → IsSite T B e →
      IsSite T B' (sim.site e) →
      ∃ t', RunChain I T (singletonProgM fn B') (goto s' (entryPos (sim.site e))) t' ∧
        Obs outs t t' := by
  have hle : ∀ e, IsSite T B' e → entryPos e ≤ B'.length := by
    intro e he
    cases e with
    | none => exact Nat.zero_le _
    | some p =>
        obtain ⟨i, hi, -⟩ := he
        exact (List.getElem?_eq_some_iff.mp hi).1
  induction h with
  | @done e s t hrun _ =>
      intro s' hRs hfn hB he
      obtain ⟨u', hrun', hQ⟩ := sim.seg e none s s' t hB trivial hfn hRs hrun
      rw [sim.site_none] at hrun'
      obtain ⟨hc, hv⟩ := hcut' (sim.site e) none he trivial
      obtain ⟨q, hseg⟩ := segTo_of_cutRun hI hR hS hc hv hfn (hle _ he) hrun'
      have ho : Obs outs t u' := sim.fin _ _ hQ
      exact ⟨_, .done hseg, ho.1, ho.2.1, ho.2.2⟩
  | @call e s u v t p hrun _ hglue _ ih =>
      intro s' hRs hfn hB he
      have hp : IsSite T B (some p) := by
        obtain ⟨i, pr, dst, srcs, hi, hpq, -⟩ := hglue
        exact ⟨i, hi, by simp only [isProcB, hpq, Option.isSome_some]⟩
      obtain ⟨u', hrun', hQ⟩ := sim.seg e (some p) s s' u hB hp hfn hRs hrun
      obtain ⟨q, v', hsite, hglue', hR'⟩ := sim.glue p u u' v hQ hglue
      have hq : IsSite T B' (some q) := by
        obtain ⟨i, pr, dst, srcs, hi, hpq, -⟩ := hglue'
        exact ⟨i, hi, by simp only [isProcB, hpq, Option.isSome_some]⟩
      rw [hsite] at hrun'
      obtain ⟨hc, hv⟩ := hcut' (sim.site e) (some q) he hq
      obtain ⟨q', hseg⟩ := segTo_of_cutRun hI hR hS hc hv hfn (hle _ he) hrun'
      have hat : atPc (singletonProgM fn B') q (goto u' q') := by
        obtain ⟨_, _, hat, _⟩ := hseg
        exact hat
      have hqq : q' = q := hat.2
      subst hqq
      have hg := hglue'.goto q'
      have hfn' : v'.prog.lfn = fn := (hg.atPc_succ hat).1
      obtain ⟨t', hch, hobs⟩ := ih v' hR' hfn' hp (by rw [hsite]; exact hq)
      rw [hsite] at hch
      exact ⟨t', .call q' hseg hg hch, hobs⟩

/-- **A chain of halting runs of cut programs of `B` is, under a simulation `CutSim`, a
    chain of segments of `B'`.** The cut programs of `B'` are cuts that halt only at their
    exits. From a state of `fn` related by `R e` to the start of the chain, for an entry `e`
    of `B`, the chain of segments of `B'` starts at the entry position of `site e` and ends
    in a state that agrees with the end of the chain on the registers `outs`, the arrays and
    the word memory. -/
theorem runChain_of_cutChain {T : ProcTable} {outs : List String} {fn : String}
    {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
    {pos' : Option Nat → Option Nat → Nat → Nat}
    (hcut' : ∀ e x, IsSite T B' e → IsSite T B' x →
      IsCut T fn B' e x (cut' e x) (pos' e x) ∧ IsCutRev T B' x (cut' e x) (pos' e x))
    (sim : CutSim T outs fn B B' cut cut') {e : Option Nat} {s t : LstateMF}
    (h : CutChain x86Isa T fn B cut e s t) :
    ∀ (s' : LstateMF), sim.R e s s' → s'.prog.lfn = fn → IsSite T B e →
      IsSite T B' (sim.site e) →
      ∃ t', RunChain x86Isa T (singletonProgM fn B') (goto s' (entryPos (sim.site e))) t' ∧
        Obs outs t t' :=
  runChain_of_cutChainI x86Isa_pcFree (x86Isa_refusesProcs T) fnStable_x86Isa hcut' sim h

/-- **Soundness of a validation by segments on the instruction set `I`.** Let the branch
    condition of `I` not read the counter, `I` refuse the procedures of `T`, the steps of
    `I` stay in the function, the cut programs of `B` be cuts and the cut programs of `B'`
    be cuts that halt only at their exits. Then `CutCheckSoundI I` holds: under a
    simulation `CutSimI I`, every halting run of `I.withProcs T` on `B` from a state of
    `fn` at the counter `0` is matched by a halting run on `B'` from the same state, the
    end states agreeing on the registers `outs`, the arrays and the word memory. -/
theorem cutCheck_soundI {I : Isa} {T : ProcTable} {outs : List String} {fn : String}
    {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
    {pos pos' : Option Nat → Option Nat → Nat → Nat} (hI : PcFree I) (hR : I.RefusesProcs T)
    (hS : FnStable I)
    (hcut : ∀ e x, IsSite T B e → IsSite T B x → IsCut T fn B e x (cut e x) (pos e x))
    (hcut' : ∀ e x, IsSite T B' e → IsSite T B' x →
      IsCut T fn B' e x (cut' e x) (pos' e x) ∧ IsCutRev T B' x (cut' e x) (pos' e x)) :
    CutCheckSoundI I T outs fn B B' cut cut' := by
  intro sim s t hfn hpc fuel hrun
  have hch := withProcs_run_cut hI hR hcut fuel s t hfn hpc hrun
  obtain ⟨t', hrc, hobs⟩ := runChain_of_cutChainI hI hR hS hcut' sim hch s (sim.init s) hfn
    trivial (by rw [sim.site_none]; trivial)
  rw [sim.site_none] at hrc
  have hs : goto s (entryPos none) = s := by
    calc goto s (entryPos none) = goto s s.prog.base.lpc := by rw [hpc]; rfl
      _ = s := rfl
  rw [hs] at hrc
  obtain ⟨n, hn⟩ := run_of_runChain hR hrc
  exact ⟨n + 0, t', hn 0, hobs⟩

/-- **Soundness of a validation by segments.** Let the cut programs of `B` be cuts and the
    cut programs of `B'` be cuts that halt only at their exits. Then `CutCheckSound` holds:
    under a simulation `CutSim`, every halting run of the x86 instruction set with
    procedures on `B` from a state of `fn` at the counter `0` is matched by a halting run
    on `B'` from the same state, the end states agreeing on the registers `outs`, the
    arrays and the word memory. -/
theorem cutCheck_sound {T : ProcTable} {outs : List String} {fn : String}
    {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
    {pos pos' : Option Nat → Option Nat → Nat → Nat}
    (hcut : ∀ e x, IsSite T B e → IsSite T B x → IsCut T fn B e x (cut e x) (pos e x))
    (hcut' : ∀ e x, IsSite T B' e → IsSite T B' x →
      IsCut T fn B' e x (cut' e x) (pos' e x) ∧ IsCutRev T B' x (cut' e x) (pos' e x)) :
    CutCheckSound T outs fn B B' cut cut' :=
  cutCheck_soundI x86Isa_pcFree (x86Isa_refusesProcs T) fnStable_x86Isa hcut hcut'

end CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
