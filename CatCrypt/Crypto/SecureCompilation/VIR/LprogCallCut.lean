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
* `CutCheckSound`: the statement of soundness of a validation of the cut programs of two
  bodies, segment by segment.

## Main results

* `runChain_of_run`, `run_of_runChain`: a halting run of `I.withProcs T` is a chain of
  segments of `I`, and conversely when `I` refuses the procedures of `T`.
* `x86Isa_pcFree`: `PcFree x86Isa`.
* `steps_emb`, `cutRun_of_segTo`: a segment of the body is a run of a cut program.
* `isCut_of_isCutB`: soundness of `isCutB`.
* `withProcs_run_cut`: a halting run of `I.withProcs T` on a body from the counter `0` is
  a chain of halting runs of cut programs on `I`.
* `x86_withProcs_run_cutAt`: the same at `x86Isa` for the cut programs `cutAt` of a body
  that `cutOkB` accepts.
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
    obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp hstep
    exact ⟨hu.1, by
      simp only [retWord, JasminLsemMemLoop.LstateM.lpc_nextPc,
        JasminLsemMemLoop.LstateM.lpc_setReg, hu.2]⟩
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

/-- **A simulation of the cut programs of `B` by the cut programs of `B'`.** `site` sends
    an entry or exit of `B` to one of `B'`. `R e` relates a state of `B` at the entry `e`
    to a state of `B'` at the entry `site e`, and `Q x` relates the end states of two
    segments with the exits `x` and `site x`. Equal states are related at the entry of the
    bodies; a halting run of a cut program of `B` from a related state is matched by a
    halting run of the cut program of `B'` to states related by `Q`; states related by `Q`
    at the end of the bodies agree on the registers `outs`, the arrays and the word memory;
    and from states related by `Q` at a shadow instruction, the step of the summary on `B`
    is matched by the step of the summary on `B'` to states related by `R`. -/
structure CutSim (T : ProcTable) (outs : List String) (fn : String) (B B' : List LinstrRM)
    (cut cut' : Option Nat → Option Nat → List LinstrRM) : Type where
  site : Option Nat → Option Nat
  R : Option Nat → LstateMF → LstateMF → Prop
  Q : Option Nat → LstateMF → LstateMF → Prop
  site_none : site none = none
  init : ∀ s, R none s s
  seg : ∀ e x s s' u, R e s s' → CutRun x86Isa fn (cut e x) s u →
    ∃ u', CutRun x86Isa fn (cut' (site e) (site x)) s' u' ∧ Q x u u'
  fin : ∀ t t', Q none t t' → Obs outs t t'
  glue : ∀ p u u' v, Q (some p) u u' → Glue T (singletonProgM fn B) p u v →
    ∃ q v', site (some p) = some q ∧ Glue T (singletonProgM fn B') q u' v' ∧ R (some p) v v'

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

end CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
