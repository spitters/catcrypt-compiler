/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

@[expose] public section

set_option autoImplicit false

/-!
# Congruence of the address machine's step in the names it reads

One step of the address machine `JasminLsemAddrMem.fstepA` reads the register file only at
the names of the instruction's source operands (`readsI`): the register sources, the base
and index of an indexed access, the base register of a cell operand `mem.B.off`, the
implicit multiplicand `RDX` of `MULX`, and the empty name that `operandName` gives a
non-register operand. Two states that agree on those names,
on the program counter, on the memory and on the carry and overflow flags therefore step
alike: both step or neither does, and every register of the two results is either equal
or, in both, the register of the state it came from (`NStep`).

The congruence is proved bottom-up through the stack the step is built from:
`lsemStepN`, `lsemStepSh`, `lsemStepMC`, `lsemStepCast` on the register file;
`lsemStepMem`, `withALUFlags`, `carryStep`, `wideStep`, `stepMemF`, `fstepF` on the flag
machine state; `regStepA` and `fstepA` on the address state.

## Main definitions

* `srcNames`, `readsI` — the names an instruction reads.
* `ORel` — two optional results, both absent or both present and related.
* `NAgree`, `NStep` — agreement before a step and the relation of the two results.

## Main results

* `lsemStepCast_congr`, `stepMemF_congr`, `fstepF_congr`, `fstepA_congr`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

/-! ## 1. The names an instruction reads -/

/-- The register names of an operand: a register, the base and index of an indexed
    element, the base of an array element. -/
def srcNames : LOperand → List String
  | .reg r => [r]
  | .imm _ => []
  | .arr b _ => [b]
  | .arrIdx b i _ => [b, i]

/-- The base register of a cell operand `mem.B.off`. -/
def cellBase : LOperand → Option String
  | .reg n => (cellParts? n).map Prod.fst
  | _ => none

/-- The names one step of `i` may read: the names of its source operands, the base
    registers of its cell operands, the implicit multiplicand `RDX` and the empty name. -/
def readsI (i : LinstrR) (r : String) : Prop :=
  r = "" ∨ r = "RDX" ∨
    match i with
    | .Lopn ds _ ss => r ∈ ss.flatMap srcNames ∨ r ∈ (ds ++ ss).filterMap cellBase
    | _ => False

theorem readsI_src {ds : List LOperand} {o : String} {ss : List LOperand} {r : String}
    (h : r ∈ ss.flatMap srcNames) : readsI (.Lopn ds o ss) r :=
  Or.inr (Or.inr (Or.inl h))

/-- The base register of a cell operand is read. -/
theorem cell_reads {ds : List LOperand} {o : String} {ss : List LOperand} {n b : String}
    {off : Nat} (hx : LOperand.reg n ∈ ds ++ ss) (hc : cellParts? n = some (b, off)) :
    readsI (.Lopn ds o ss) b :=
  Or.inr (Or.inr (Or.inr (List.mem_filterMap.2 ⟨.reg n, hx, by simp [cellBase, hc]⟩)))

theorem readsI_rdx (i : LinstrR) : readsI i "RDX" := Or.inr (Or.inl rfl)

theorem readsI_empty (i : LinstrR) : readsI i "" := Or.inl rfl

/-! ## 2. Related results -/

/-- Two optional results: both absent, or both present and related by `P`. -/
inductive ORel {α β : Type} (P : α → β → Prop) : Option α → Option β → Prop
  | none : ORel P none none
  | some {a : α} {b : β} : P a b → ORel P (some a) (some b)

theorem ORel.map {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {f : α → γ} {g : β → δ} (hf : ∀ a b, P a b → Q (f a) (g b)) :
    ∀ {x : Option α} {y : Option β}, ORel P x y → ORel Q (x.map f) (y.map g)
  | _, _, .none => .none
  | _, _, .some h => .some (hf _ _ h)

theorem ORel.mono {α β : Type} {P Q : α → β → Prop} (hPQ : ∀ a b, P a b → Q a b) :
    ∀ {x : Option α} {y : Option β}, ORel P x y → ORel Q x y
  | _, _, .none => .none
  | _, _, .some h => .some (hPQ _ _ h)

/-- Two register files agree on the names `R` and on the program counter. -/
def NAgree (R : String → Prop) (s t : LstateN) : Prop :=
  s.lpc = t.lpc ∧ ∀ r, R r → s.lvm r = t.lvm r

/-- The results `s'`, `t'` of one step from `s`, `t`: equal program counters, and every
    register equal in the two results or, in both, the register of the state it came
    from. -/
def NStep (s t s' t' : LstateN) : Prop :=
  s'.lpc = t'.lpc ∧ ∀ r, s'.lvm r = t'.lvm r ∨ (s'.lvm r = s.lvm r ∧ t'.lvm r = t.lvm r)

theorem NStep.refl {s t : LstateN} (h : s.lpc = t.lpc) : NStep s t s t :=
  ⟨h, fun _ => Or.inr ⟨rfl, rfl⟩⟩

theorem NStep.setReg {s t s' t' : LstateN} (h : NStep s t s' t') (d : String) {w : Nat}
    (v : BitVec w) : NStep s t (s'.setReg d v) (t'.setReg d v) := by
  refine ⟨h.1, fun r => ?_⟩
  simp only [LstateN.setReg]
  by_cases hr : r = d
  · exact Or.inl (by simp [hr])
  · simpa [hr] using h.2 r

theorem NStep.nextPc {s t s' t' : LstateN} (h : NStep s t s' t') :
    NStep s t s'.nextPc t'.nextPc :=
  ⟨by simp [LstateN.nextPc, h.1], fun r => h.2 r⟩

/-- The step that writes `v` to `d` and advances the program counter. -/
theorem NStep.write {R : String → Prop} {s t : LstateN} (h : NAgree R s t) (d : String)
    {w : Nat} (v : BitVec w) : NStep s t (s.setReg d v).nextPc (t.setReg d v).nextPc :=
  ((NStep.refl h.1).setReg d v).nextPc

theorem NAgree.mono {R R' : String → Prop} {s t : LstateN} (h : NAgree R s t)
    (hR : ∀ r, R' r → R r) : NAgree R' s t :=
  ⟨h.1, fun r hr => h.2 r (hR r hr)⟩

/-! ## 3. Reads -/

theorem readReg_congr {R : String → Prop} {s t : LstateN} (h : NAgree R s t)
    {o : LOperand} (ho : ∀ r ∈ srcNames o, R r) : readReg s o = readReg t o := by
  cases o with
  | reg r => simp only [readReg, h.2 r (ho r (by simp [srcNames]))]
  | _ => rfl

theorem getW_congr {R : String → Prop} {s t : LstateN} (h : NAgree R s t) {r : String}
    (hr : R r) (w : Nat) : s.getW r w = t.getW r w := by
  unfold LstateN.getW
  rw [h.2 r hr]

theorem evalOperandN_congr {R : String → Prop} {s t : LstateN} (h : NAgree R s t)
    {o : LOperand} (ho : ∀ r ∈ srcNames o, R r) (w : Nat) :
    evalOperandN s w o = evalOperandN t w o := by
  cases o with
  | reg r => exact getW_congr h (ho r (by simp [srcNames])) w
  | _ => rfl

theorem src_reads {ds : List LOperand} {o : String} {ss : List LOperand} {x : LOperand}
    (hx : x ∈ ss) : ∀ r ∈ srcNames x, readsI (.Lopn ds o ss) r :=
  fun _ hr => readsI_src (List.mem_flatMap.2 ⟨x, hx, hr⟩)

theorem reg_reads {ds : List LOperand} {o : String} {ss : List LOperand} {r : String}
    (hx : LOperand.reg r ∈ ss) : readsI (.Lopn ds o ss) r :=
  src_reads hx r (by simp [srcNames])

theorem idx_reads {ds : List LOperand} {o : String} {ss : List LOperand} {b r : String}
    {sc : Nat} (hx : LOperand.arrIdx b r sc ∈ ss) : readsI (.Lopn ds o ss) r :=
  src_reads hx r (by simp [srcNames])

theorem base_reads {ds : List LOperand} {o : String} {ss : List LOperand} {b r : String}
    {sc : Nat} (hx : LOperand.arrIdx b r sc ∈ ss) : readsI (.Lopn ds o ss) b :=
  src_reads hx b (by simp [srcNames])

theorem operandName_reads {ds : List LOperand} {o : String} {ss : List LOperand}
    {x : LOperand} (hx : x ∈ ss) : readsI (.Lopn ds o ss) (operandName x) := by
  cases x with
  | reg r => exact src_reads hx r (by simp [srcNames])
  | _ => exact readsI_empty _

/-- The implicit multiplicand of `MULX` is read. -/
theorem mulxSrc_reads (i : LinstrR) : ∀ r ∈ srcNames (.reg mulxSrc), readsI i r := by
  intro r hr
  simp only [srcNames, mulxSrc, List.mem_singleton] at hr
  subst hr
  exact readsI_rdx i

/-- Prove a list membership by choosing a position, assigning metavariables. -/
macro "mem_tac" : tactic =>
  `(tactic| (repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)))

/-- Discharge a read-name side condition of a congruence rewrite. -/
macro "reads_tac" : tactic =>
  `(tactic| first
    | exact readsI_rdx _ | exact readsI_empty _ | exact mulxSrc_reads _
    | (apply reg_reads; simp; done) | (apply idx_reads; mem_tac; done)
    | (apply base_reads; mem_tac; done) | (apply operandName_reads; simp; done)
    | (apply src_reads; simp; done))

/-- Rewrite every read of `s` in the goal to the same read of `t`. -/
macro "reads_rw" h:ident : tactic =>
  `(tactic| simp (disch := reads_tac) only [readReg_congr $h, getW_congr $h,
    evalOperandN_congr $h])

/-- Close the goals left by splitting two step results that read alike. -/
macro "orel_close" h:ident : tactic =>
  `(tactic| first
    | exact ORel.none
    | exact ORel.some (NStep.write $h _ _)
    | exact ORel.some (((NStep.refl $h.1).setReg _ _).setReg _ _ |>.nextPc)
    | exact ORel.some ((NStep.refl $h.1).nextPc))

/-- Rewrite the reads and split the two results until they are matched. -/
macro "orel_loop" h:ident : tactic =>
  `(tactic| ((repeat' (first | reads_rw $h:ident | split)) <;> orel_close $h:ident))

/-! ## 4. The register-file steps -/

theorem lsemStepN_congr (i : LinstrR) {s t : LstateN} (h : NAgree (readsI i) s t) :
    ORel (NStep s t) (lsemStepN i s) (lsemStepN i t) := by
  unfold lsemStepN
  split
  all_goals (try reads_rw h)
  all_goals (repeat' split)
  all_goals orel_close h

/-- Split a recognizer equation `X? i = some p` into the instruction's shape. -/
macro "recog" hx:ident : tactic =>
  `(tactic| (repeat' split at $hx:ident) <;> (try simp only [Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq] at $hx:ident) <;> (try casesm* _ ∧ _) <;> subst_vars)

theorem lsemStepSh_congr (i : LinstrR) {s t : LstateN} (h : NAgree (readsI i) s t) :
    ORel (NStep s t) (lsemStepSh i s) (lsemStepSh i t) := by
  unfold lsemStepSh
  cases hx : sarStruct? i with
  | none => exact lsemStepN_congr i h
  | some p =>
    obtain ⟨dst, src, n⟩ := p
    unfold sarStruct? at hx
    recog hx
    all_goals (reads_rw h; (repeat' split) <;> orel_close h)

/-- Close a step whose recognizer `X` returned a result: read off the instruction's shape,
    rewrite the reads and match the two results. -/
macro "recog_close" h:ident hx:ident X:ident : tactic =>
  `(tactic| (unfold $X:ident at $hx:ident <;> recog $hx:ident <;> orel_loop $h:ident))

theorem lsemStepMC_congr (i : LinstrR) {s t : LstateN} (h : NAgree (readsI i) s t) :
    ORel (NStep s t) (lsemStepMC i s) (lsemStepMC i t) := by
  unfold lsemStepMC
  cases h1 : mulhiStruct? i with
  | some p =>
    obtain ⟨_, _, _⟩ := p
    unfold mulhiStruct? at h1
    recog h1
    all_goals orel_loop h
  | none =>
  cases h2 : adcxStruct? i with
  | some p => obtain ⟨_, _, _, _⟩ := p; recog_close h h2 adcxStruct?
  | none =>
  cases h3 : adcxhiStruct? i with
  | some p => obtain ⟨_, _, _, _⟩ := p; recog_close h h3 adcxhiStruct?
  | none =>
  cases h4 : sbbStruct? i with
  | some p => obtain ⟨_, _, _, _⟩ := p; recog_close h h4 sbbStruct?
  | none =>
  cases h5 : sbbhiStruct? i with
  | some p => obtain ⟨_, _, _, _⟩ := p; recog_close h h5 sbbhiStruct?
  | none => exact lsemStepSh_congr i h

/-- The typed step `lsemStepCast` on `(i, c)`. -/
theorem lsemStepCast_congr (i : LinstrR) (c : Option Nat) {s t : LstateN}
    (h : NAgree (readsI i) s t) :
    ORel (NStep s t) (lsemStepCast (i, c) s) (lsemStepCast (i, c) t) := by
  unfold lsemStepCast
  cases h1 : castStruct? i with
  | some p =>
    obtain ⟨_, _⟩ := p
    cases c with
    | none =>
      simp only
      cases h2 : movImmStruct? i with
      | some q => exact lsemStepMC_congr i h
      | none => exact lsemStepMC_congr i h
    | some w' => recog_close h h1 castStruct?
  | none =>
    simp only
    cases h2 : movImmStruct? i with
    | some q =>
      cases c with
      | none => exact lsemStepMC_congr i h
      | some w' => exact ORel.some (NStep.write h _ _)
    | none => exact lsemStepMC_congr i h

/-! ## 5. The flag machine -/

/-- Two flag-machine states agree on the names `R`, the program counter, the arrays, the
    word memory and the two flags. -/
def MAgree (R : String → Prop) (s t : LstateM) : Prop :=
  NAgree R s.reg t.reg ∧ s.larr = t.larr ∧ s.lmem = t.lmem ∧ s.cf = t.cf ∧ s.of = t.of

/-- The results of one flag-machine step from `s`, `t`: `NStep` on the register files and
    equal arrays, word memories and flags. -/
def MStep (s t s' t' : LstateM) : Prop :=
  NStep s.reg t.reg s'.reg t'.reg ∧ s'.larr = t'.larr ∧ s'.lmem = t'.lmem ∧ s'.cf = t'.cf
    ∧ s'.of = t'.of

theorem MAgree.mono {R R' : String → Prop} {s t : LstateM} (h : MAgree R s t)
    (hR : ∀ r, R' r → R r) : MAgree R' s t :=
  ⟨h.1.mono hR, h.2⟩

theorem MStep.refl {R : String → Prop} {s t : LstateM} (h : MAgree R s t) :
    MStep s t s t :=
  ⟨NStep.refl h.1.1, h.2⟩

theorem MStep.setReg {s t s' t' : LstateM} (h : MStep s t s' t') (d : String) {w : Nat}
    (v : BitVec w) : MStep s t (s'.setReg d v) (t'.setReg d v) :=
  ⟨h.1.setReg d v, h.2⟩

theorem MStep.nextPc {s t s' t' : LstateM} (h : MStep s t s' t') :
    MStep s t s'.nextPc t'.nextPc :=
  ⟨h.1.nextPc, h.2⟩

theorem MStep.setArr {s t s' t' : LstateM} (h : MStep s t s' t') (d : String) {w n : Nat}
    (a : Fin n → BitVec w) : MStep s t (s'.setArr d a) (t'.setArr d a) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, by simp [LstateM.setArr, h2], h3, h4, h5⟩

theorem MStep.storeMemC {s t s' t' : LstateM} (h : MStep s t s' t') (b : String) (o : Int)
    (v : BitVec 64) : MStep s t (s'.storeMemC b o v) (t'.storeMemC b o v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, by simp [LstateM.storeMemC, h3], h4, h5⟩

theorem MStep.flags {s t s' t' : LstateM} (h : MStep s t s' t') (c o : Bool) :
    MStep s t { s' with cf := c, of := o } { t' with cf := c, of := o } :=
  ⟨h.1, h.2.1, h.2.2.1, rfl, rfl⟩

theorem MStep.cf {s t s' t' : LstateM} (h : MStep s t s' t') (c : Bool) :
    MStep s t { s' with cf := c } { t' with cf := c } :=
  ⟨h.1, h.2.1, h.2.2.1, rfl, h.2.2.2.2⟩

theorem MStep.of {s t s' t' : LstateM} (h : MStep s t s' t') (o : Bool) :
    MStep s t { s' with of := o } { t' with of := o } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩

/-- A register-file step lifted to the flag machine state. -/
theorem MStep.ofReg {R : String → Prop} {s t : LstateM} (h : MAgree R s t)
    {a b : LstateN} (hn : NStep s.reg t.reg a b) :
    MStep s t { s with reg := a } { t with reg := b } :=
  ⟨hn, h.2⟩

theorem getArr_congr {s t : LstateM} (h : s.larr = t.larr) (r : String) (w n : Nat) :
    s.getArr r w n = t.getArr r w n := by
  unfold LstateM.getArr
  rw [h]

/-- Close the goals left by splitting two flag-machine results. -/
macro "morel_close" h:ident : tactic =>
  `(tactic| first
    | exact ORel.none
    | exact ORel.some ((MStep.refl $h).setReg _ _ |>.nextPc)
    | exact ORel.some ((MStep.refl $h).setArr _ _ |>.nextPc)
    | exact ORel.some ((MStep.refl $h).storeMemC _ _ _ |>.nextPc)
    | exact ORel.some (((MStep.refl $h).setReg _ _).setReg _ _ |>.nextPc)
    | exact ORel.some ((MStep.refl $h).nextPc))

/-- Rewrite the flag-machine reads and split the two results until they are matched. -/
macro "morel_loop" h:ident hN:ident hA:ident hM:ident : tactic =>
  `(tactic| ((repeat' (first | (reads_rw $hN:ident) | (simp only [getArr_congr $hA:ident, $hM:ident]) | split)) <;> morel_close $h:ident))

theorem lsemStepMem_congr (i : LinstrRM) {s t : LstateM} (h : MAgree (readsI i.fst) s t) :
    ORel (MStep s t) (lsemStepMem i s) (lsemStepMem i t) := by
  obtain ⟨w, tag⟩ := i
  have hN : NAgree (readsI w) s.reg t.reg := h.1
  have hA := h.2.1
  have hM := h.2.2.1
  unfold lsemStepMem
  cases tag with
  | load wd n =>
    simp only
    cases hx : loadStruct? w with
    | some p =>
      obtain ⟨_, _, _⟩ := p
      unfold loadStruct? at hx
      recog hx
      all_goals morel_loop h hN hA hM
    | none =>
      exact ORel.map (fun a b hab => MStep.ofReg h hab) (lsemStepCast_congr w none hN)
  | store wd n =>
    simp only
    cases hx : storeStruct? w with
    | some p =>
      obtain ⟨_, _, _, _⟩ := p
      unfold storeStruct? at hx
      recog hx
      all_goals morel_loop h hN hA hM
    | none =>
      exact ORel.map (fun a b hab => MStep.ofReg h hab) (lsemStepCast_congr w none hN)
  | loadC =>
    simp only
    cases hx : loadCStruct? w with
    | some p =>
      obtain ⟨_, _, _⟩ := p
      unfold loadCStruct? at hx
      recog hx
      all_goals morel_loop h hN hA hM
    | none => exact ORel.none
  | storeC =>
    simp only
    cases hx : storeCStruct? w with
    | some p =>
      obtain ⟨_, _, _⟩ := p
      unfold storeCStruct? at hx
      recog hx
      all_goals morel_loop h hN hA hM
    | none => exact ORel.none
  | reg c =>
    exact ORel.map (fun a b hab => MStep.ofReg h hab) (lsemStepCast_congr w c hN)

theorem withALUFlags_congr (i : LinstrRM) {s t s' t' : LstateM}
    (h : MAgree (readsI i.fst) s t) (hs : MStep s t s' t') :
    MStep s t (withALUFlags i s s') (withALUFlags i t t') := by
  obtain ⟨w, tag⟩ := i
  have hN : NAgree (readsI w) s.reg t.reg := h.1
  unfold withALUFlags
  cases hx : aluFlagOp? (w, tag) with
  | none => exact hs
  | some p =>
    obtain ⟨_, _, _⟩ := p
    unfold aluFlagOp? at hx
    simp only at hx
    recog hx
    all_goals
      reads_rw hN
      repeat' split
      all_goals first | exact hs.flags _ _ | exact hs

/-- Close the goals of a step with flag updates. -/
macro "fl_close" h:ident : tactic =>
  `(tactic| first
    | exact ORel.none
    | exact ORel.some ((((MStep.refl $h).setReg _ _).nextPc).flags _ _)
    | exact ORel.some ((((MStep.refl $h).setReg _ _).nextPc).cf _)
    | exact ORel.some ((((MStep.refl $h).setReg _ _).nextPc).of _)
    | exact ORel.some (((MStep.refl $h).setReg _ _).nextPc)
    | exact ORel.some ((((MStep.refl $h).setReg _ _).setReg _ _).nextPc))

theorem stepMemF_congr (i : LinstrRM) {s t : LstateM} (h : MAgree (readsI i.fst) s t) :
    ORel (MStep s t) (stepMemF i s) (stepMemF i t) := by
  obtain ⟨w, tag⟩ := i
  have hN : NAgree (readsI w) s.reg t.reg := h.1
  have hC := h.2.2.2.1
  have hO := h.2.2.2.2
  unfold stepMemF
  have hr := lsemStepMem_congr (w, tag) h
  revert hr
  generalize lsemStepMem (w, tag) s = x
  generalize lsemStepMem (w, tag) t = y
  intro hr
  rcases hr with _ | hab
  · simp only
    cases hk : carryArgs? (w, tag) with
    | some p =>
      obtain ⟨op, d, a, b⟩ := p
      unfold carryArgs? at hk
      simp only at hk
      recog hk
      all_goals
        unfold carryStep
        (repeat' (first | (reads_rw hN) | (simp only [hC, hO]) | split)) <;> fl_close h
    | none =>
      simp only
      cases hw : wideArgs? (w, tag) with
      | none => exact ORel.none
      | some p =>
        unfold wideArgs? at hw
        simp only at hw
        recog hw
        all_goals
          unfold wideStep
          (repeat' (first | (reads_rw hN) | split)) <;> fl_close h
  · exact ORel.some (withALUFlags_congr (w, tag) h hab)

/-- The results of one step of `fstepF` from `s`, `t`: `MStep` and equal zero flags. -/
def FStep (s t : LstateM) (p q : LstateM × Bool) : Prop := MStep s t p.1 q.1 ∧ p.2 = q.2

theorem fstepF_congr (i : LinstrRM) {s t : LstateM} (h : MAgree (readsI i.fst) s t)
    (zf : Bool) : ORel (FStep s t) (fstepF i s zf) (fstepF i t zf) := by
  obtain ⟨w, tag⟩ := i
  have hN : NAgree (readsI w) s.reg t.reg := h.1
  unfold fstepF
  cases hc : cmpArgs? (w, tag) with
  | some p =>
    obtain ⟨a, b⟩ := p
    unfold cmpArgs? at hc
    simp only at hc
    recog hc
    all_goals
      (repeat' (first | (reads_rw hN) | split)) <;>
        first | exact ORel.none | exact ORel.some ⟨(MStep.refl h).nextPc, rfl⟩
  | none =>
    simp only
    cases hm : movRegArgs? (w, tag) with
    | some p =>
      obtain ⟨dst, src⟩ := p
      unfold movRegArgs? at hm
      simp only at hm
      recog hm
      all_goals
        (repeat' (first | (reads_rw hN) | split)) <;>
          first | exact ORel.none | exact ORel.some ⟨((MStep.refl h).setReg _ _).nextPc, rfl⟩
    | none =>
      simp only
      exact ORel.map (fun a b hab => ⟨hab, rfl⟩) (stepMemF_congr (w, tag) h)

/-! ## 6. The address machine -/

/-- Two address states agree on the names `R`, the program counter, the memory and the two
    flags. -/
def AAgree (R : String → Prop) (s t : LstateA) : Prop :=
  NAgree R s.reg t.reg ∧ s.mem = t.mem ∧ s.cf = t.cf ∧ s.of = t.of

/-- The results of one address-machine step from `s`, `t`: `NStep` on the register files,
    equal memories, flags and zero flags. -/
def AStep (s t : LstateA) (p q : LstateA × Bool) : Prop :=
  NStep s.reg t.reg p.1.reg q.1.reg ∧ p.1.mem = q.1.mem ∧ p.1.cf = q.1.cf ∧ p.1.of = q.1.of
    ∧ p.2 = q.2

theorem AAgree.mono {R R' : String → Prop} {s t : LstateA} (h : AAgree R s t)
    (hR : ∀ r, R' r → R r) : AAgree R' s t :=
  ⟨h.1.mono hR, h.2⟩

theorem regStepA_congr (i : LinstrRM) {s t : LstateA} (h : AAgree (readsI i.fst) s t)
    (zf : Bool) : ORel (AStep s t) (regStepA i s zf) (regStepA i t zf) := by
  unfold regStepA
  have hm : MAgree (readsI i.fst) { reg := s.reg, cf := s.cf, of := s.of }
      { reg := t.reg, cf := t.cf, of := t.of } := ⟨h.1, rfl, rfl, h.2.2.1, h.2.2.2⟩
  refine ORel.map (fun p q hpq => ?_) (fstepF_congr i hm zf)
  obtain ⟨⟨h1, -, -, h4, h5⟩, h6⟩ := hpq
  exact ⟨h1, h.2.1, h4, h5, h6⟩

/-- Close the goals of an address-machine step. -/
macro "a_close" h:ident hN:ident zf:ident : tactic =>
  `(tactic| first
    | exact ORel.none
    | exact ORel.some ⟨((NStep.refl $hN.1).setReg _ _).nextPc, rfl, $h.2.2.1, $h.2.2.2, rfl⟩
    | exact ORel.some ⟨(NStep.refl $hN.1).nextPc, rfl, $h.2.2.1, $h.2.2.2, rfl⟩
    | exact regStepA_congr _ $h $zf)

/-- Rewrite the reads of an address-machine step and split until the results match. -/
macro "a_loop" h:ident hN:ident hM:ident zf:ident : tactic =>
  `(tactic| ((repeat' (first | (reads_rw $hN:ident) | (simp only [$hM:ident]) | split)) <;> a_close $h $hN $zf))

theorem fstepA_congr (frame : String → Option (BitVec 64)) (i : LinstrRM) {s t : LstateA}
    (h : AAgree (readsI i.fst) s t) (zf : Bool) :
    ORel (AStep s t) (fstepA frame i s zf) (fstepA frame i t zf) := by
  obtain ⟨w, tag⟩ := i
  have hN : NAgree (readsI w) s.reg t.reg := h.1
  have hM := h.2.1
  unfold fstepA
  cases tag with
  | load wd n =>
    simp only
    cases hx : loadIdxA? w with
    | none => exact ORel.none
    | some p =>
      obtain ⟨_, _, _, _⟩ := p
      unfold loadIdxA? at hx
      recog hx
      all_goals a_loop h hN hM zf
  | store wd n =>
    simp only
    cases hx : storeIdxA? w with
    | none => exact ORel.none
    | some p =>
      obtain ⟨_, _, _, _⟩ := p
      unfold storeIdxA? at hx
      recog hx
      all_goals a_loop h hN hM zf
  | reg c =>
    simp only
    cases hs : slotMov? w with
    | some p =>
      obtain ⟨dst, src⟩ := p
      unfold slotMov? at hs
      recog hs
      all_goals a_loop h hN hM zf
    | none =>
      simp only
      cases hk : slotCmp? w with
      | none =>
        simp only
        cases hcl : cellA? w with
        | none =>
          simp only
          cases hsc : slotCarry? frame w with
          | none => exact regStepA_congr _ h zf
          | some q =>
            obtain ⟨lo, d, a, s', c'⟩ := q
            unfold slotCarry? at hsc
            split at hsc
            · split_ifs at hsc with h1
              obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hsc
              have hwa : wordA frame s a = wordA frame t a := by
                unfold wordA
                split
                · rw [hM]
                · exact getW_congr hN (reg_reads (by simp)) 64
              have hws : wordA frame s s' = wordA frame t s' := by
                unfold wordA
                split
                · rw [hM]
                · exact getW_congr hN (reg_reads (by simp)) 64
              simp only
              rw [hwa, hws, getW_congr hN (reg_reads (by simp)) 1, hM]
              repeat' split
              all_goals first
                | exact ORel.none
                | exact ORel.some ⟨((NStep.refl hN.1).setReg _ _).nextPc, rfl, h.2.2.1,
                    h.2.2.2, rfl⟩
                | exact ORel.some ⟨(NStep.refl hN.1).nextPc, rfl, h.2.2.1, h.2.2.2, rfl⟩
            · cases hsc
        | some op =>
          unfold cellA? at hcl
          split at hcl
          · rename_i d o n
            split_ifs at hcl with h1 h2
            · obtain ⟨⟨b, off⟩, hp, he⟩ := Option.map_eq_some_iff.1 hcl
              subst he
              have hb : readsI (.Lopn [.reg d] o [.reg n]) b := cell_reads (by simp) hp
              simp only
              rw [getW_congr hN hb, hM]
              split
              · exact ORel.some ⟨((NStep.refl hN.1).setReg _ _).nextPc, rfl, h.2.2.1,
                  h.2.2.2, rfl⟩
              · exact ORel.none
            · obtain ⟨⟨b, off⟩, hp, he⟩ := Option.map_eq_some_iff.1 hcl
              subst he
              have hb : readsI (.Lopn [.reg d] o [.reg n]) b := cell_reads (by simp) hp
              have hv : readsI (.Lopn [.reg d] o [.reg n]) n := reg_reads (by simp)
              simp only
              rw [getW_congr hN hb, getW_congr hN hv, hM]
              split
              · exact ORel.some ⟨(NStep.refl hN.1).nextPc, rfl, h.2.2.1, h.2.2.2, rfl⟩
              · exact ORel.none
          · cases hcl
      | some p =>
        obtain ⟨d, x, q⟩ := p
        unfold slotCmp? at hk
        recog hk
        all_goals
          simp only [hM]
          split
          · refine regStepA_congr _ (h.mono fun r hr => ?_) zf
            rcases hr with hr | hr | hr | hr
            · exact Or.inl hr
            · exact Or.inr (Or.inl hr)
            · simp [srcNames] at hr
              subst hr
              exact reg_reads (by simp)
            · refine Or.inr (Or.inr (Or.inr ?_))
              obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.1 hr
              refine List.mem_filterMap.2 ⟨a, ?_, hfa⟩
              simp only [List.cons_append, List.nil_append, List.mem_cons,
                List.not_mem_nil, or_false] at ha ⊢
              rcases ha with rfl | rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · simp [cellBase] at hfa
          · exact regStepA_congr _ h zf
  | _ => exact ORel.none

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
