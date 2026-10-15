/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

/-!
# Scheduling soundness on the flag machine `stepMemF`

The scheduler `LprogScheduler.scheduleBody` reorders adjacent instructions that its
independence test `LprogScheduler.indep` accepts. This module proves that the reordering
preserves the straight-line run `JasminLsemMemFlagGuard.lsemStraightMemF` of the flag
machine, whose state `LstateM` carries width-tagged registers, the stack arrays `larr`, the
word memory `lmem` and the carry and overflow flags `cf`, `of`.

One step of `stepMemF` on an instruction without a runtime-indexed operand is described by
its effect relative to the incoming state: the registers named by the write tokens of the
instruction (`writeToks`), the word-memory cells whose token is a write token, and the two
flags when the instruction touches the flags (`touchesFlags`), are taken from the result;
every other cell, the arrays, and the program counter plus one, are taken from the incoming
state (`mergeM`). The step from a state `t` that agrees with `s` on the read and write
tokens of the instruction, and on the flags when the instruction touches them (`AgreeM`), is
the step from `s` with its effect applied to `t` (`stepMemF_transport`). Two independent
instructions read and write disjoint tokens and do not both touch the flags, so their effects
commute (`mergeM_comm`).

## Main definitions

* `mergeN`, `mergeM` — the effect of a step applied to another state.
* `AgreeM`, `Agree` — agreement on a token list and on the flags.

## Main results

* `lsemStepCast_transport`, `lsemStepMem_transport`, `stepMemF_transport` — a step from an
  agreeing state is the effect of the step applied to that state.
* `stepMemF_swap`, `lsemStraightMemF_swap` — two adjacent independent instructions commute.
* `scheduleBody_lsemStraightMemF`, `scheduleBodyTail_lsemStraightMemF` — the scheduled body,
  tagged by any tagging function, reaches the same flag-machine state as the input.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksMemF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
  (indep hazardReads hazardWrites writeToks readToksSem implicitReads hasArrIdx opIsArrIdx
    touchesFlags flagFree flagToks flagsTok opTok srcTok disjointL disjointL_ne keyStartsWith
    stepEff applyEff lsemStepN_eq_applyEff stepEff_congr stepEff_writeToks indep_symm
    indep_arrIdx_left indep_arrIdx_right scheduleBody scheduleBodyTail scheduleBody_run
    scheduleBodyTail_run)

/-! ## 1. Extensionality -/

theorem lstateN_ext {s t : LstateN} (h1 : s.lvm = t.lvm) (h2 : s.lpc = t.lpc) : s = t := by
  cases s; cases t; simp_all

theorem lstateM_ext {s t : LstateM} (h1 : s.reg = t.reg) (h2 : s.larr = t.larr)
    (h3 : s.lmem = t.lmem) (h4 : s.cf = t.cf) (h5 : s.of = t.of) : s = t := by
  cases s; cases t; simp_all

/-! ## 2. The effect of a step on the register file -/

/-- The register file `t` with the registers named in `W` taken from `s'`, and the program
    counter of `t` advanced by one. -/
def mergeN (W : List String) (t s' : LstateN) : LstateN :=
  { lvm := fun r => if r ∈ W then s'.lvm r else t.lvm r, lpc := t.lpc + 1 }

/-- A write of `d` from `s`, applied to `t`, is the same write on `t`, when `d` is in `W` and
    `s`, `t` agree on `W`. -/
theorem mergeN_write {W : List String} {s t : LstateN} {d : String} (hd : d ∈ W)
    (hW : ∀ r ∈ W, s.lvm r = t.lvm r) {w : Nat} (v : BitVec w) :
    mergeN W t ((s.setReg d v).nextPc) = (t.setReg d v).nextPc := by
  refine lstateN_ext ?_ (by simp [mergeN])
  funext r
  simp only [mergeN, LstateN.lvm_setReg, LstateN.nextPc]
  by_cases hr : r = d
  · subst hr; simp [hd]
  · by_cases hrW : r ∈ W <;> simp [hr, hrW, hW r]

/-- Two writes from `s`, applied to `t`, are the same writes on `t`. -/
theorem mergeN_write2 {W : List String} {s t : LstateN} {d e : String} (hd : d ∈ W)
    (he : e ∈ W) (hW : ∀ r ∈ W, s.lvm r = t.lvm r) {w w' : Nat} (v : BitVec w)
    (v' : BitVec w') :
    mergeN W t (((s.setReg d v).setReg e v').nextPc) = ((t.setReg d v).setReg e v').nextPc := by
  refine lstateN_ext ?_ (by simp [mergeN])
  funext r
  simp only [mergeN, LstateN.lvm_setReg, LstateN.nextPc]
  by_cases hre : r = e
  · subst hre; simp [he]
  · by_cases hr : r = d
    · subst hr; simp [hd, hre]
    · by_cases hrW : r ∈ W <;> simp [hr, hre, hrW, hW r]

/-- A step that writes nothing, applied to `t`, advances the program counter of `t`. -/
theorem mergeN_nextPc {W : List String} {s t : LstateN} (hW : ∀ r ∈ W, s.lvm r = t.lvm r) :
    mergeN W t s.nextPc = t.nextPc := by
  refine lstateN_ext ?_ (by simp [mergeN])
  funext r
  simp only [mergeN, LstateN.nextPc]
  by_cases hrW : r ∈ W <;> simp [hrW, hW r]

/-- Agreement of two register files on the read and write tokens of an instruction. -/
structure RegAgree (i : LinstrR) (s t : LstateN) : Prop where
  /-- Agreement on the read tokens. -/
  rd : ∀ r ∈ readToksSem i, s.lvm r = t.lvm r
  /-- Agreement on the write tokens. -/
  wr : ∀ r ∈ writeToks i, s.lvm r = t.lvm r

/-- A width-tagged step that only advances the pc is not an `Lopn`, so it writes no token. -/
theorem stepEff_writeToks_none (i : LinstrR) (s : LstateN) (h : stepEff i s = some none) :
    writeToks i = [] := by
  unfold stepEff at h
  repeat' split at h
  all_goals simp_all [writeToks]

/-- Split a recognizer equation `X? i = some p` into the instruction's shape. -/
local macro "recog" hx:ident : tactic =>
  `(tactic| (repeat' split at $hx:ident) <;> (try simp only [Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq] at $hx:ident) <;> (try casesm* _ ∧ _) <;> subst_vars)

/-- Rewrite every register read of `t` in the goal to the same read of `s`. -/
local macro "rt_rw" h:ident : tactic =>
  `(tactic| simp (disch := (apply Eq.symm; apply RegAgree.rd $h; simp [readToksSem, srcTok])) only
    [LprogScheduler.readReg_congr (s1 := _) (s2 := _), LprogScheduler.getW_congr (s1 := _) (s2 := _),
     LprogScheduler.evalOperandN_congr (s1 := _) (s2 := _)])

/-- Close the goals left by splitting a register-file step from `t` and from `s`. -/
local macro "rt_close" h:ident : tactic =>
  `(tactic| first
    | rfl
    | (simp only [Option.map_some]; congr 1;
       exact (mergeN_write (by simp [writeToks, opTok]) (RegAgree.wr $h) _).symm))

theorem lsemStepN_transport (i : LinstrR) (hai : hasArrIdx i = false) {s t : LstateN}
    (h : RegAgree i s t) :
    lsemStepN i t = (lsemStepN i s).map (mergeN (writeToks i) t) := by
  rw [lsemStepN_eq_applyEff, lsemStepN_eq_applyEff, ← stepEff_congr i s t hai h.rd,
    Option.map_map]
  rcases he : stepEff i s with _ | e
  · rfl
  · simp only [Option.map_some, Function.comp_apply, Option.some.injEq]
    rcases e with _ | ⟨d, w, v⟩
    · rw [stepEff_writeToks_none i s he]
      exact (mergeN_nextPc (by simp)).symm
    · have hw := stepEff_writeToks i s d ⟨w, v⟩ he
      simp only [applyEff]
      rw [hw]
      exact (mergeN_write (by simp) (hw ▸ h.wr) v).symm

theorem lsemStepSh_transport (i : LinstrR) (hai : hasArrIdx i = false) {s t : LstateN}
    (h : RegAgree i s t) :
    lsemStepSh i t = (lsemStepSh i s).map (mergeN (writeToks i) t) := by
  unfold lsemStepSh
  cases hx : sarStruct? i with
  | none => exact lsemStepN_transport i hai h
  | some p =>
    obtain ⟨dst, src, n⟩ := p
    unfold sarStruct? at hx
    recog hx
    all_goals (simp only []; rt_rw h; (repeat' split) <;> rt_close h)

/-- Close a register-file step whose recognizer `X` returned a result. -/
local macro "rt_recog" h:ident hx:ident X:ident : tactic =>
  `(tactic| (unfold $X:ident at $hx:ident <;> recog $hx:ident <;>
    (simp only []; rt_rw $h; (repeat' split) <;> rt_close $h)))

theorem lsemStepMC_transport (i : LinstrR) (hai : hasArrIdx i = false) {s t : LstateN}
    (h : RegAgree i s t) :
    lsemStepMC i t = (lsemStepMC i s).map (mergeN (writeToks i) t) := by
  unfold lsemStepMC
  cases h1 : mulhiStruct? i with
  | some p => obtain ⟨_, _, _⟩ := p; rt_recog h h1 mulhiStruct?
  | none =>
  cases h2 : adcxStruct? i with
  | some p => obtain ⟨_, _, _, _⟩ := p; rt_recog h h2 adcxStruct?
  | none =>
  cases h3 : adcxhiStruct? i with
  | some p => obtain ⟨_, _, _, _⟩ := p; rt_recog h h3 adcxhiStruct?
  | none =>
  cases h4 : sbbStruct? i with
  | some p => obtain ⟨_, _, _, _⟩ := p; rt_recog h h4 sbbStruct?
  | none =>
  cases h5 : sbbhiStruct? i with
  | some p => obtain ⟨_, _, _, _⟩ := p; rt_recog h h5 sbbhiStruct?
  | none => exact lsemStepSh_transport i hai h

/-- The typed register step `lsemStepCast` on `(i, c)`, from an agreeing register file, is
    its effect applied to that register file. -/
theorem lsemStepCast_transport (i : LinstrR) (c : Option Nat) (hai : hasArrIdx i = false)
    {s t : LstateN} (h : RegAgree i s t) :
    lsemStepCast (i, c) t = (lsemStepCast (i, c) s).map (mergeN (writeToks i) t) := by
  unfold lsemStepCast
  cases h1 : castStruct? i with
  | some p =>
    obtain ⟨_, _⟩ := p
    cases c with
    | none =>
      simp only
      cases h2 : movImmStruct? i with
      | some q => exact lsemStepMC_transport i hai h
      | none => exact lsemStepMC_transport i hai h
    | some w' => rt_recog h h1 castStruct?
  | none =>
    simp only
    cases h2 : movImmStruct? i with
    | some q =>
      cases c with
      | none => exact lsemStepMC_transport i hai h
      | some w' =>
        obtain ⟨_, _⟩ := q
        unfold movImmStruct? at h2
        recog h2
        all_goals rt_close h
    | none => exact lsemStepMC_transport i hai h

/-! ## 3. The effect of a step on the flag-machine state -/

/-- The footprint token of the word-memory cell at base `b` and offset `o`, the token
    `LprogScheduler.opTok` gives the operand `.arr b o`. -/
def memTok (b : String) (o : Nat) : String := b ++ "#" ++ toString o

/-- The state `t` with the effect of a step of `i` whose result is `s'`: the registers named by
    the write tokens of `i`, the word-memory cells at a non-negative offset whose token is a
    write token, and the two flags when `i` touches the flags, are those of `s'`; every other
    register and cell and the arrays are those of `t`; the program counter is that of `t` plus
    one. -/
def mergeM (i : LinstrR) (t s' : LstateM) : LstateM where
  reg := mergeN (writeToks i) t.reg s'.reg
  larr := t.larr
  lmem := fun b o => if 0 ≤ o ∧ memTok b o.toNat ∈ writeToks i then s'.lmem b o else t.lmem b o
  cf := if touchesFlags i then s'.cf else t.cf
  of := if touchesFlags i then s'.of else t.of

/-- Two flag-machine states agree on the registers and word-memory cells whose token is in
    `T`, and, when `fl`, on the two flags. -/
structure AgreeM (T : List String) (fl : Bool) (s t : LstateM) : Prop where
  /-- Agreement on the registers named in `T`. -/
  reg : ∀ r ∈ T, s.reg.lvm r = t.reg.lvm r
  /-- Agreement on the word-memory cells whose token is in `T`. -/
  mem : ∀ (b : String) (o : Nat), memTok b o ∈ T → s.lmem b (Int.ofNat o) = t.lmem b (Int.ofNat o)
  /-- Agreement on the flags. -/
  flags : fl = true → s.cf = t.cf ∧ s.of = t.of

/-- Agreement on the hazard read and write tokens of `i`, and on the flags when `i` touches
    them. -/
abbrev Agree (i : LinstrR) : LstateM → LstateM → Prop :=
  AgreeM (hazardReads i ++ hazardWrites i) (touchesFlags i)

theorem agree_refl (i : LinstrR) (s : LstateM) : Agree i s s :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem mem_T_write {i : LinstrR} {r : String} (h : r ∈ writeToks i) :
    r ∈ hazardReads i ++ hazardWrites i := by
  simp [hazardWrites, h]

theorem mem_T_read {i : LinstrR} {r : String} (h : r ∈ readToksSem i) :
    r ∈ hazardReads i ++ hazardWrites i := by
  simp [hazardReads, h]

theorem Agree.regAgree {i : LinstrR} {s t : LstateM} (h : Agree i s t) :
    RegAgree i s.reg t.reg :=
  ⟨fun r hr => h.reg r (mem_T_read hr), fun r hr => h.reg r (mem_T_write hr)⟩

/-- Agreement on a word-memory cell whose token is a write token. -/
theorem Agree.lmem_write {i : LinstrR} {s t : LstateM} (h : Agree i s t) {b : String} {o : Int}
    (h0 : 0 ≤ o) (hm : memTok b o.toNat ∈ writeToks i) : s.lmem b o = t.lmem b o := by
  have := h.mem b o.toNat (mem_T_write hm)
  simpa [Int.toNat_of_nonneg h0] using this

theorem mergeM_lmem {i : LinstrR} {s t s' : LstateM} (h : Agree i s t) (hs : s'.lmem = s.lmem) :
    (mergeM i t s').lmem = t.lmem := by
  funext b o
  simp only [mergeM, hs]
  split_ifs with hc
  · exact h.lmem_write hc.1 hc.2
  · rfl

theorem mergeM_cf {i : LinstrR} {s t s' : LstateM} (h : Agree i s t) (hs : s'.cf = s.cf) :
    (mergeM i t s').cf = t.cf := by
  simp only [mergeM, hs]
  split
  · exact (h.flags ‹_›).1
  · rfl

theorem mergeM_of {i : LinstrR} {s t s' : LstateM} (h : Agree i s t) (hs : s'.of = s.of) :
    (mergeM i t s').of = t.of := by
  simp only [mergeM, hs]
  split
  · exact (h.flags ‹_›).2
  · rfl

theorem mergeM_ofReg {i : LinstrR} {s t : LstateM} (h : Agree i s t) (r : LstateN) :
    mergeM i t { s with reg := r } = { t with reg := mergeN (writeToks i) t.reg r } :=
  lstateM_ext rfl rfl (mergeM_lmem h rfl) (mergeM_cf h rfl) (mergeM_of h rfl)

theorem mergeM_setReg {i : LinstrR} {s t : LstateM} (h : Agree i s t) {d : String}
    (hd : d ∈ writeToks i) {w : Nat} (v : BitVec w) :
    mergeM i t ((s.setReg d v).nextPc) = (t.setReg d v).nextPc :=
  lstateM_ext (mergeN_write hd h.regAgree.wr v) rfl (mergeM_lmem h rfl) (mergeM_cf h rfl)
    (mergeM_of h rfl)

theorem mergeM_setReg2 {i : LinstrR} {s t : LstateM} (h : Agree i s t) {d e : String}
    (hd : d ∈ writeToks i) (he : e ∈ writeToks i) {w w' : Nat} (v : BitVec w)
    (v' : BitVec w') :
    mergeM i t (((s.setReg d v).setReg e v').nextPc) = ((t.setReg d v).setReg e v').nextPc :=
  lstateM_ext (mergeN_write2 hd he h.regAgree.wr v v') rfl (mergeM_lmem h rfl) (mergeM_cf h rfl)
    (mergeM_of h rfl)

theorem mergeM_regFlags {i : LinstrR} {s t : LstateM} (h : Agree i s t)
    (ht : touchesFlags i = true) {d : String} (hd : d ∈ writeToks i) {w : Nat} (v : BitVec w)
    (c o : Bool) :
    mergeM i t { (s.setReg d v).nextPc with cf := c, of := o }
      = { (t.setReg d v).nextPc with cf := c, of := o } :=
  lstateM_ext (mergeN_write hd h.regAgree.wr v) rfl (mergeM_lmem h rfl) (by simp [mergeM, ht])
    (by simp [mergeM, ht])

theorem mergeM_regCf {i : LinstrR} {s t : LstateM} (h : Agree i s t)
    (ht : touchesFlags i = true) {d : String} (hd : d ∈ writeToks i) {w : Nat} (v : BitVec w)
    (c : Bool) :
    mergeM i t { (s.setReg d v).nextPc with cf := c } = { (t.setReg d v).nextPc with cf := c } :=
  lstateM_ext (mergeN_write hd h.regAgree.wr v) rfl (mergeM_lmem h rfl) (by simp [mergeM, ht])
    (mergeM_of h rfl)

theorem mergeM_regOf {i : LinstrR} {s t : LstateM} (h : Agree i s t)
    (ht : touchesFlags i = true) {d : String} (hd : d ∈ writeToks i) {w : Nat} (v : BitVec w)
    (o : Bool) :
    mergeM i t { (s.setReg d v).nextPc with of := o } = { (t.setReg d v).nextPc with of := o } :=
  lstateM_ext (mergeN_write hd h.regAgree.wr v) rfl (mergeM_lmem h rfl) (mergeM_cf h rfl)
    (by simp [mergeM, ht])

theorem mergeM_store {i : LinstrR} {s t : LstateM} (h : Agree i s t) {b : String} {off : Nat}
    (hd : memTok b off ∈ writeToks i) (v : BitVec 64) :
    mergeM i t ((s.storeMemC b (Int.ofNat off) v).nextPc)
      = (t.storeMemC b (Int.ofNat off) v).nextPc := by
  refine lstateM_ext (mergeN_nextPc h.regAgree.wr) rfl ?_ (mergeM_cf h rfl) (mergeM_of h rfl)
  funext b' o'
  simp only [mergeM, LstateM.nextPc, LstateM.storeMemC]
  by_cases he : b' = b ∧ o' = Int.ofNat off
  · obtain ⟨rfl, rfl⟩ := he
    simp [hd]
  · simp only [if_neg he]
    split_ifs with hc
    · exact h.lmem_write hc.1 hc.2
    · rfl

theorem loadStruct?_none {w : LinstrR} (hai : hasArrIdx w = false) : loadStruct? w = none := by
  unfold loadStruct?
  split
  · simp [hasArrIdx, opIsArrIdx] at hai
  · rfl

theorem storeStruct?_none {w : LinstrR} (hai : hasArrIdx w = false) :
    storeStruct? w = none := by
  unfold storeStruct?
  split
  · simp [hasArrIdx, opIsArrIdx] at hai
  · rfl

theorem keyStartsWith_MULX : keyStartsWith "MULX" (withWidthTag 64 "MULX") = true := by decide

theorem keyStartsWith_MULXMEM : keyStartsWith "MULX" (withWidthTag 64 "MULXMEM") = true := by
  decide

/-- A recognised arithmetic or logical operation touches the flags. -/
theorem touchesFlags_of_alu {i : LinstrRM} {p : AluOp × LOperand × LOperand}
    (h : aluFlagOp? i = some p) : touchesFlags i.1 = true := by
  obtain ⟨w, tag⟩ := i
  unfold aluFlagOp? at h
  simp only at h
  split at h
  · split_ifs at h <;> subst_vars <;> simp only [touchesFlags] <;> decide
  · simp at h

/-- A carry-family operation touches the flags. -/
theorem touchesFlags_of_carry {i : LinstrRM} {p : CarryOp × String × LOperand × LOperand}
    (h : carryArgs? i = some p) : touchesFlags i.1 = true := by
  obtain ⟨w, tag⟩ := i
  unfold carryArgs? at h
  simp only at h
  split at h
  · split_ifs at h <;> subst_vars <;> simp only [touchesFlags] <;> decide
  · simp at h

/-- Discharge `t.reg.lvm r = s.reg.lvm r` for a hazard token `r`. -/
local macro "m_disch" h:ident : tactic =>
  `(tactic| (apply Eq.symm
             apply AgreeM.reg $h
             simp [hazardReads, hazardWrites, readToksSem, srcTok, implicitReads, mulxSrc,
               keyStartsWith_MULX, keyStartsWith_MULXMEM]))

/-- Rewrite every register read of `t` in the goal to the same read of `s`. -/
local macro "m_rw" h:ident : tactic =>
  `(tactic| simp (disch := m_disch $h) only
    [LprogScheduler.readReg_congr (s1 := _) (s2 := _), LprogScheduler.getW_congr (s1 := _) (s2 := _),
     LprogScheduler.evalOperandN_congr (s1 := _) (s2 := _)])

/-- Close the goals left by splitting a flag-machine step from `t` and from `s`. -/
local macro "m_close" h:ident : tactic =>
  `(tactic| first
    | rfl
    | (simp only [Option.map_some]; congr 1; first
        | exact (mergeM_setReg $h (by simp [writeToks, opTok]) _).symm
        | exact (mergeM_setReg2 $h (by simp [writeToks, opTok]) (by simp [writeToks, opTok])
            _ _).symm
        | exact (mergeM_regFlags $h ‹_› (by simp [writeToks, opTok]) _ _ _).symm
        | exact (mergeM_regCf $h ‹_› (by simp [writeToks, opTok]) _ _).symm
        | exact (mergeM_regOf $h ‹_› (by simp [writeToks, opTok]) _ _).symm
        | exact (mergeM_store $h (by simp [writeToks, opTok, memTok]) _).symm))

/-- The straight-line step `lsemStepMem`, from an agreeing state, is its effect applied to that
    state. -/
theorem lsemStepMem_transport (i : LinstrRM) (hai : hasArrIdx i.1 = false) {s t : LstateM}
    (h : Agree i.1 s t) : lsemStepMem i t = (lsemStepMem i s).map (mergeM i.1 t) := by
  obtain ⟨w, tag⟩ := i
  simp only at hai h ⊢
  have hreg : ∀ c, (lsemStepCast (w, c) t.reg).map (fun r => { t with reg := r })
      = ((lsemStepCast (w, c) s.reg).map (fun r => { s with reg := r })).map (mergeM w t) := by
    intro c
    rw [lsemStepCast_transport w c hai h.regAgree]
    cases lsemStepCast (w, c) s.reg <;> simp [mergeM_ofReg h]
  unfold lsemStepMem
  cases tag with
  | load wd n => simp only [loadStruct?_none hai]; exact hreg none
  | store wd n => simp only [storeStruct?_none hai]; exact hreg none
  | reg c => exact hreg c
  | zero wd n =>
    have hz : zeroStruct? w = none := by
      cases w with
      | Lopn ds opn srcs =>
          have hne : (opn == "ZEROARR") = false := by
            simp only [hasArrIdx, Bool.or_eq_false_iff] at hai
            exact hai.1.1
          unfold zeroStruct?
          split <;> simp_all
      | _ => rfl
    simp only [hz, Option.map_none]
  | loadC =>
    simp only
    cases hx : loadCStruct? w with
    | none => rfl
    | some p =>
      obtain ⟨dst, base, off⟩ := p
      have hmb := h.mem base off
      unfold loadCStruct? at hx
      recog hx
      all_goals
        simp only [Option.map_some]
        rw [← hmb (by simp [hazardReads, readToksSem, srcTok, memTok])]
        exact congrArg some (mergeM_setReg h (by simp [writeToks, opTok]) _).symm
  | storeC =>
    simp only
    cases hx : storeCStruct? w with
    | none => rfl
    | some p =>
      obtain ⟨base, off, src⟩ := p
      unfold storeCStruct? at hx
      recog hx
      all_goals (m_rw h; (repeat' split) <;> m_close h)

/-- The flags `withALUFlags` writes commute with the effect of the step. -/
theorem withALUFlags_transport (i : LinstrRM) {s t : LstateM} (h : Agree i.1 s t)
    (b : LstateM) : withALUFlags i t (mergeM i.1 t b) = mergeM i.1 t (withALUFlags i s b) := by
  obtain ⟨w, tag⟩ := i
  unfold withALUFlags
  cases hx : aluFlagOp? (w, tag) with
  | none => rfl
  | some p =>
    have ht := touchesFlags_of_alu hx
    obtain ⟨op, a, b'⟩ := p
    unfold aluFlagOp? at hx
    simp only at hx ht h ⊢
    recog hx
    all_goals
      m_rw h
      split
      · exact lstateM_ext rfl rfl rfl (by simp [mergeM, ht]) (by simp [mergeM, ht])
      · rfl

/-- **Transport of a flag-machine step.** The step of an instruction without a
    runtime-indexed operand, from a state that agrees with `s` on its hazard tokens and on the
    flags when it touches them, is the step from `s` with its effect applied to that state. -/
theorem stepMemF_transport (i : LinstrRM) (hai : hasArrIdx i.1 = false) {s t : LstateM}
    (h : Agree i.1 s t) : stepMemF i t = (stepMemF i s).map (mergeM i.1 t) := by
  obtain ⟨w, tag⟩ := i
  unfold stepMemF
  rw [lsemStepMem_transport (w, tag) hai h]
  cases hm : lsemStepMem (w, tag) s with
  | some b =>
    simp only [Option.map_some]
    exact congrArg some (withALUFlags_transport (w, tag) h b)
  | none =>
    simp only [Option.map_none]
    cases hk : carryArgs? (w, tag) with
    | some p =>
      have ht := touchesFlags_of_carry hk
      have hfl := h.flags ht
      obtain ⟨op, d, a, b⟩ := p
      unfold carryArgs? at hk
      obtain ⟨hcf, hof⟩ := hfl
      simp only at hk
      recog hk
      all_goals
        simp only [carryStep, ← hcf, ← hof]
        m_rw h
        (repeat' split) <;> m_close h
    | none =>
      simp only
      cases hw : wideArgs? (w, tag) with
      | none => rfl
      | some p =>
        unfold wideArgs? at hw
        simp only at hw h ⊢
        recog hw
        all_goals (try (casesm* _ ∨ _) <;> subst_vars)
        all_goals
          simp only [wideStep]
          m_rw h
          (repeat' split) <;> m_close h

/-- A successful step is its own effect applied to its incoming state. -/
theorem stepMemF_mergeM {i : LinstrRM} (hai : hasArrIdx i.1 = false) {s s' : LstateM}
    (h : stepMemF i s = some s') : mergeM i.1 s s' = s' := by
  have := stepMemF_transport i hai (agree_refl i.1 s)
  rw [h, Option.map_some, Option.some.injEq] at this
  exact this.symm

/-! ## 4. Independent instructions commute -/

/-- The token disjointness `indep` asserts. -/
theorem indep_disjoint {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    disjointL (hazardWrites i1) (hazardWrites i2) = true ∧
      disjointL (hazardWrites i1) (hazardReads i2) = true := by
  simp only [indep, Bool.and_eq_true] at h
  exact ⟨h.1.1.2, h.1.2⟩

/-- A write token of `i1` is no hazard token of `i2`. -/
theorem indep_write_not_mem {i1 i2 : LinstrR} (h : indep i1 i2 = true) {r : String}
    (hr : r ∈ writeToks i1) : r ∉ hazardReads i2 ++ hazardWrites i2 := by
  obtain ⟨hww, hwr⟩ := indep_disjoint h
  have hr' : r ∈ hazardWrites i1 := by simp [hazardWrites, hr]
  intro hm
  rcases List.mem_append.1 hm with hm | hm
  · exact disjointL_ne hwr hr' hm rfl
  · exact disjointL_ne hww hr' hm rfl

/-- Two independent instructions do not both touch the flags. -/
theorem indep_flags {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    ¬ (touchesFlags i1 = true ∧ touchesFlags i2 = true) := by
  rintro ⟨h1, h2⟩
  obtain ⟨-, hwr⟩ := indep_disjoint h
  exact disjointL_ne hwr (x := flagsTok) (y := flagsTok)
    (by simp [hazardWrites, LprogScheduler.flagToks, h1])
    (by simp [hazardReads, LprogScheduler.flagToks, h2]) rfl

/-- After a step of `i1`, the state agrees with the incoming one on the hazard tokens of an
    independent `i2`. -/
theorem agree_after {i1 i2 : LinstrR} (hind : indep i1 i2 = true) {s s1 : LstateM}
    (hs1 : mergeM i1 s s1 = s1) : Agree i2 s s1 := by
  refine ⟨fun r hr => ?_, fun b o hm => ?_, fun ht => ?_⟩
  · rw [← hs1]
    have : r ∉ writeToks i1 := fun hw => indep_write_not_mem hind hw hr
    simp [mergeM, mergeN, this]
  · rw [← hs1]
    have : memTok b o ∉ writeToks i1 := fun hw => indep_write_not_mem hind hw hm
    simp [mergeM, this]
  · rw [← hs1]
    have : touchesFlags i1 = false := by
      cases h1 : touchesFlags i1
      · rfl
      · exact absurd ⟨h1, ht⟩ (indep_flags hind)
    simp [mergeM, this]

/-- The effects of two independent instructions commute. -/
theorem mergeM_comm {i1 i2 : LinstrR} (hind : indep i1 i2 = true) (s a b : LstateM) :
    mergeM i2 (mergeM i1 s a) b = mergeM i1 (mergeM i2 s b) a := by
  have hw : ∀ r, r ∈ writeToks i1 → r ∉ writeToks i2 := fun r h1 h2 =>
    indep_write_not_mem hind h1 (List.mem_append_right _ (by simp [hazardWrites, h2]))
  have hfl := indep_flags hind
  refine lstateM_ext (lstateN_ext ?_ ?_) rfl ?_ ?_ ?_
  · funext r
    simp only [mergeM, mergeN]
    by_cases h1 : r ∈ writeToks i1
    · simp [h1, hw r h1]
    · by_cases h2 : r ∈ writeToks i2 <;> simp [h1, h2]
  · simp [mergeM, mergeN]
  · funext b' o
    simp only [mergeM]
    by_cases h1 : 0 ≤ o ∧ memTok b' o.toNat ∈ writeToks i1
    · have h2 : ¬ (0 ≤ o ∧ memTok b' o.toNat ∈ writeToks i2) := fun h2 => hw _ h1.2 h2.2
      simp only [if_pos h1, if_neg h2]
    · simp only [if_neg h1]
  · simp only [mergeM]
    cases h1 : touchesFlags i1 <;> cases h2 : touchesFlags i2 <;> simp_all
  · simp only [mergeM]
    cases h1 : touchesFlags i1 <;> cases h2 : touchesFlags i2 <;> simp_all

/-- **Adjacent independent instructions commute under `stepMemF`.** -/
theorem stepMemF_swap (i1 i2 : LinstrRM) (s : LstateM) (h : indep i1.1 i2.1 = true) :
    (stepMemF i1 s).bind (stepMemF i2) = (stepMemF i2 s).bind (stepMemF i1) := by
  have h' : indep i2.1 i1.1 = true := by rw [indep_symm]; exact h
  have ha1 := indep_arrIdx_left h
  have ha2 := indep_arrIdx_right h
  rcases h1 : stepMemF i1 s with _ | s1 <;> rcases h2 : stepMemF i2 s with _ | s2
  · rfl
  · simp only [Option.bind_none, Option.bind_some]
    rw [stepMemF_transport i1 ha1 (agree_after h' (stepMemF_mergeM ha2 h2)), h1]
    rfl
  · simp only [Option.bind_none, Option.bind_some]
    rw [stepMemF_transport i2 ha2 (agree_after h (stepMemF_mergeM ha1 h1)), h2]
    rfl
  · simp only [Option.bind_some]
    rw [stepMemF_transport i2 ha2 (agree_after h (stepMemF_mergeM ha1 h1)), h2,
      stepMemF_transport i1 ha1 (agree_after h' (stepMemF_mergeM ha2 h2)), h1]
    simp only [Option.map_some, Option.some.injEq]
    calc mergeM i2.1 s1 s2 = mergeM i2.1 (mergeM i1.1 s s1) s2 := by
          rw [stepMemF_mergeM ha1 h1]
      _ = mergeM i1.1 (mergeM i2.1 s s2) s1 := mergeM_comm h s s1 s2
      _ = mergeM i1.1 s2 s1 := by rw [stepMemF_mergeM ha2 h2]

/-- `lsemStraightMemF` composes over list concatenation. -/
theorem lsemStraightMemF_append (l1 l2 : List LinstrRM) (s : LstateM) :
    lsemStraightMemF (l1 ++ l2) s = (lsemStraightMemF l1 s).bind (lsemStraightMemF l2) := by
  induction l1 generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, lsemStraightMemF_cons, ih, Option.bind_assoc]

/-- **Adjacent-transposition commutation for `lsemStraightMemF`.** -/
theorem lsemStraightMemF_swap (i1 i2 : LinstrRM) (rest : List LinstrRM) (s : LstateM)
    (h : indep i1.1 i2.1 = true) :
    lsemStraightMemF (i1 :: i2 :: rest) s = lsemStraightMemF (i2 :: i1 :: rest) s := by
  have e : ∀ (j k : LinstrRM), lsemStraightMemF (j :: k :: rest) s
      = ((stepMemF j s).bind (stepMemF k)).bind (lsemStraightMemF rest) := by
    intro j k
    rw [lsemStraightMemF_cons, Option.bind_assoc]
    rfl
  rw [e, e, stepMemF_swap i1 i2 s h]

/-! ## 5. Schedule soundness -/

/-- **Schedule soundness on the flag machine.** For any tagging of the wire instructions by
    memory tags, the scheduled body run by `lsemStraightMemF` reaches the same state as the
    input body. -/
theorem scheduleBody_lsemStraightMemF (tag : LinstrR → MemTag) (b : List Linstr)
    (s : LstateM) :
    lsemStraightMemF ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)) s
      = lsemStraightMemF (b.map fun i => (i.li_i, tag i.li_i)) s := by
  have := scheduleBody_run (run := fun l s => lsemStraightMemF (l.map fun i => (i, tag i)) s)
    (fun l1 l2 s => by simp only [List.map_append, lsemStraightMemF_append])
    (fun i1 i2 rest s hi => lsemStraightMemF_swap (i1, tag i1) (i2, tag i2) _ s hi) b s
  simpa [List.map_map, Function.comp_def] using this

/-- **Tail-preserving schedule soundness on the flag machine.** -/
theorem scheduleBodyTail_lsemStraightMemF (tag : LinstrR → MemTag) (keepTail : Nat)
    (b : List Linstr) (s : LstateM) :
    lsemStraightMemF ((scheduleBodyTail keepTail b).map fun i => (i.li_i, tag i.li_i)) s
      = lsemStraightMemF (b.map fun i => (i.li_i, tag i.li_i)) s := by
  have := scheduleBodyTail_run
    (run := fun l s => lsemStraightMemF (l.map fun i => (i, tag i)) s)
    (fun l1 l2 s => by simp only [List.map_append, lsemStraightMemF_append])
    (fun i1 i2 rest s hi => lsemStraightMemF_swap (i1, tag i1) (i2, tag i2) _ s hi)
    keepTail b s
  simpa [List.map_map, Function.comp_def] using this

end CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksMemF
