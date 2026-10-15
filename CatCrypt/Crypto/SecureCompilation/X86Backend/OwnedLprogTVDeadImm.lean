/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLICM

/-!
# Completeness of the value checker for dead immediate moves

`ConstIndexFold.dropDeadImmBody` removes an immediate move `mov r, $k` when the gathered
machine block overwrites `r` before reading it. This module proves that
`OwnedLprogTV.ownedCheckM` accepts a straight-line body against the body without such moves,
when the removed moves are dead at the level of the symbolic step: no kept instruction reads a
removed register before a kept instruction writes it, and every removed register is written
again before the end of the body (`dropOk`).

## Method

The symbolic step reads the register file only at the registers its source operands read
(`symStep_congr`), and the names it writes do not depend on the state (`symStep_sh`,
`symStep_wr`). An immediate move sets its register to an atom, so its run interns nothing
(`tRun_immMov`). The run of the body and the run of the kept instructions therefore proceed
from states that agree off the pending registers (`SSt.EqvOn`); interning registers on which
the two states agree gives one table (`Tbl.internSt_on`), and the runs agree at the end, where
no register is pending (`tRun_drop`). One `ownedCheckM_of_res` closes the body.

## Main definitions

* `symReads`, `wrOf`: the registers a symbolic step reads and the names it writes.
* `immMov?`: the register an immediate move sets.
* `srcOf`, `keptOf`, `dropOk`: a marked body, its unmarked instructions, and the condition
  that the marks are dead immediate moves.
* `deadMarks`, `dropDeadImmMarks`, `spellMarks`: the marks of the elimination.
* `flagQuiet`, `dropOkW`, `ResW`: steps that write no flag and no array, the condition that
  the marks are dead flag-quiet writes, and agreement of runs up to guards.
* `deadWriteMarks`, `dropDeadWriteBody`: the elimination of a `MUL`, `IMUL` or move into a
  register whose next access is a write of a widening multiply `MULX`.

## Dead flag-quiet writes

A marked instruction may be any flag-quiet step (`flagQuiet`): in the flag machine a `MUL`,
an `IMUL` and a move write no flag (`aluFlagOp?` records the flags of `ADD`, `SUB`, `AND`,
`OR` and `XOR` only), so dropping one leaves the flags, and every later flag reader, as they
are (`symStep_same`). Its step may carry width guards and intern a compound word; the run of
the kept instructions then carries a sublist of the guards of the source run (`ResW`), which
the guard check of `ownedCheckM` accepts (`blockOkR_fallW`).

## Main results

* `symStep_congr`: a step reads the register file only at `symReads`.
* `symStep_wr`: the names a step writes do not depend on the state.
* `tRun_drop`: runs without dead immediate moves agree.
* `dropOk_ownedCheckM_complete`, `marks_ownedCheckM_complete`: completeness for a marked body.
* `dropDeadImm_ownedCheckM_complete`: completeness for `ConstIndexFold.dropDeadImmBody`.
* `foldIndexed_ownedCheckM_complete`: completeness for the elimination followed by the
  array-ABI spelling, the pair `ConstIndexFold.foldIndexedBody` produces.
* `symStep_same`: a flag-quiet step keeps the flags and the arrays.
* `tRun_dropW`, `ownedCheckM_of_resW`, `dropOkW_ownedCheckM_complete`: runs without dead
  flag-quiet writes agree up to guards, and `ownedCheckM` accepts them.
* `dropOk_dropOkW`: dead immediate moves are dead flag-quiet writes.
* `dropDeadWrite_ownedCheckM_complete`: completeness for `dropDeadWriteBody`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLICM (operandReads instrReadRegs)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (widthFromTag)

/-! ## 1. The registers a symbolic step reads -/

/-- The base register a load-effective-address `LEA d, [b + x · sc]` reads, which
    `instrReadRegs` (the index registers of an indexed operand) does not list. -/
def leaReads : LinstrR → List String
  | .Lopn _ opn [.arrIdx b _ _] => if stripWidthTag opn = "LEA" then [b] else []
  | _ => []

/-- The registers the symbolic step of `x` reads: the registers its source operands read,
    the base register of a load-effective-address and, for a widening multiply, its
    implicit first source `mulxSrc`. -/
def symReads (x : LinstrR) : List String :=
  instrReadRegs x ++ (leaReads x ++
    match x with
    | .Lopn _ opn _ =>
        if opn = withWidthTag 64 "MULX" ∨ opn = withWidthTag 64 "MULXMEM" then [mulxSrc] else []
    | _ => [])

theorem symOp64_congr {R R' : String → STerm} {o : LOperand}
    (h : ∀ q ∈ operandReads o, R q = R' q) : symOp64 R o = symOp64 R' o := by
  cases o <;> simp_all [symOp64, operandReads]

theorem symN_congr {R R' : String → STerm} {x : LinstrR}
    (h : ∀ q ∈ instrReadRegs x, R q = R' q) (hl : ∀ q ∈ leaReads x, R q = R' q) :
    symN x R = symN x R' := by
  unfold symN
  repeat' split
  all_goals simp_all [instrReadRegs, operandReads, leaReads]

theorem instrReadRegs_sub (x : LinstrR) : ∀ q ∈ instrReadRegs x, q ∈ symReads x :=
  fun _ h => List.mem_append_left _ h

theorem leaReads_sub (x : LinstrR) : ∀ q ∈ leaReads x, q ∈ symReads x :=
  fun _ h => List.mem_append_right _ (List.mem_append_left _ h)

theorem symSh_congr {R R' : String → STerm} {x : LinstrR}
    (h : ∀ q ∈ instrReadRegs x, R q = R' q) (hl : ∀ q ∈ leaReads x, R q = R' q) :
    symSh x R = symSh x R' := by
  unfold symSh
  split
  · rename_i d s n hm
    unfold JasminLsemShift.sarStruct? at hm
    repeat' split at hm
    all_goals simp_all [instrReadRegs, operandReads]
  · exact symN_congr h hl

theorem symMC_congr {R R' : String → STerm} {x : LinstrR}
    (h : ∀ q ∈ instrReadRegs x, R q = R' q) (hl : ∀ q ∈ leaReads x, R q = R' q) :
    symMC x R = symMC x R' := by
  unfold symMC
  split
  · rename_i d a b hm
    unfold JasminLsemMulCarry.mulhiStruct? at hm
    repeat' split at hm
    all_goals simp_all [instrReadRegs, operandReads]
  · split
    · rename_i d a b c hm
      unfold JasminLsemMulCarry.adcxStruct? at hm
      repeat' split at hm
      all_goals simp_all [instrReadRegs, operandReads]
    · split
      · rename_i d a b c hm
        unfold JasminLsemMulCarry.adcxhiStruct? at hm
        repeat' split at hm
        all_goals simp_all [instrReadRegs, operandReads]
      · split
        · rename_i d a b c hm
          unfold JasminLsemMulCarry.sbbStruct? at hm
          repeat' split at hm
          all_goals simp_all [instrReadRegs, operandReads]
        · split
          · rename_i d a b c hm
            unfold JasminLsemMulCarry.sbbhiStruct? at hm
            repeat' split at hm
            all_goals simp_all [instrReadRegs, operandReads]
          · exact symSh_congr h hl

theorem symCast_congr {R R' : String → STerm} {i : JasminLsemCast.LinstrRT}
    (h : ∀ q ∈ instrReadRegs i.1, R q = R' q) (hl : ∀ q ∈ leaReads i.1, R q = R' q) :
    symCast i R = symCast i R' := by
  unfold symCast
  split
  · split
    · rfl
    · exact symMC_congr h hl
  · rename_i d a hm
    split
    · exact symMC_congr h hl
    · unfold JasminLsemCast.castStruct? at hm
      repeat' split at hm
      all_goals simp_all [instrReadRegs, operandReads]

/-- The words of a state other than its registers and its write lists. -/
def SSt.Same (ss ss' : SSt) : Prop :=
  ss.arrs = ss'.arrs ∧ ss.zf = ss'.zf ∧ ss.cf = ss'.cf ∧ ss.of = ss'.of

theorem SSt.Same.refl (ss : SSt) : ss.Same ss := ⟨rfl, rfl, rfl, rfl⟩

/-- The step descriptions `o` from `ss` and `o'` from `ss'` agree on what they write: both
    fail, both are outside the fragment, or both succeed with equal guards, the same words
    other than registers, each written list extended by one list `ds` of names, and one
    word for every name of `ds`. -/
def SOut.RelOn (ss ss' : SSt) : SOut → SOut → Prop
  | .ok s g, .ok s' g' => g = g' ∧ s.Same s' ∧
      ∃ ds, s.wr = ds ++ ss.wr ∧ s'.wr = ds ++ ss'.wr ∧ ∀ q ∈ ds, s.regs q = s'.regs q
  | .fail, .fail => True
  | .unk, .unk => True
  | _, _ => False

theorem liftR_congr {ss ss' : SSt} (hS : ss.Same ss') (o : ROut) :
    SOut.RelOn ss ss' (liftR ss o) (liftR ss' o) := by
  cases o with
  | set d t gs =>
      refine ⟨rfl, hS, [d], rfl, rfl, fun q hq => ?_⟩
      simp only [List.mem_singleton] at hq
      simp [SSt.setR, hq]
  | nop => exact ⟨rfl, hS, [], rfl, rfl, fun _ h => by cases h⟩
  | fail => trivial
  | unk => trivial

theorem symMem_congr {ss ss' : SSt} (hS : ss.Same ss') (i : LinstrRM)
    (hR : ∀ q ∈ instrReadRegs i.1, ss.regs q = ss'.regs q)
    (hL : ∀ q ∈ leaReads i.1, ss.regs q = ss'.regs q) :
    SOut.RelOn ss ss' (symMem i ss) (symMem i ss') := by
  obtain ⟨x, tag⟩ := i
  unfold symMem
  cases tag with
  | load w n =>
      dsimp only
      split
      · rename_i dst base idx hl
        have hi : ss.regs idx = ss'.regs idx := by
          unfold loadStruct? at hl
          repeat' split at hl
          all_goals simp_all [instrReadRegs, operandReads]
        refine ⟨by rw [hS.1, hi], ⟨?_, hS.2⟩, [dst], rfl, rfl, fun q hq => ?_⟩
        · simp [SSt.setR, hS.1]
        · simp only [List.mem_singleton] at hq
          simp [SSt.setR, hq, hS.1, hi]
      · rw [symCast_congr (R' := ss'.regs) hR hL]; exact liftR_congr hS _
  | store w n =>
      dsimp only
      split
      · rename_i dst base idx val hl
        have hi : ss.regs idx = ss'.regs idx ∧ ss.regs val = ss'.regs val := by
          unfold storeStruct? at hl
          repeat' split at hl
          all_goals simp_all [instrReadRegs, operandReads]
        refine ⟨by rw [hS.1, hi.1, hi.2], ⟨?_, hS.2⟩, [], rfl, rfl, fun _ h => by cases h⟩
        simp [SSt.setA, hS.1, hi.1, hi.2]
      · rw [symCast_congr (R' := ss'.regs) hR hL]; exact liftR_congr hS _
  | loadC => trivial
  | storeC => trivial
  | zero _ _ => trivial
  | storeImm _ _ => trivial
  | reg cd => dsimp only; rw [symCast_congr (R' := ss'.regs) hR hL]; exact liftR_congr hS _

theorem aluFlagOp?_reads {i : LinstrRM} {op : AluOp} {a c : LOperand}
    (h : aluFlagOp? i = some (op, a, c)) :
    (∀ q ∈ operandReads a, q ∈ instrReadRegs i.1) ∧
      ∀ q ∈ operandReads c, q ∈ instrReadRegs i.1 := by
  obtain ⟨x, t⟩ := i
  simp only [aluFlagOp?] at h
  split at h
  · repeat' split at h
    all_goals simp_all [instrReadRegs]
  · cases h

theorem cmpArgs?_reads {i : LinstrRM} {a c : LOperand} (h : cmpArgs? i = some (a, c)) :
    (∀ q ∈ operandReads a, q ∈ instrReadRegs i.1) ∧
      ∀ q ∈ operandReads c, q ∈ instrReadRegs i.1 := by
  obtain ⟨x, t⟩ := i
  simp only [cmpArgs?] at h
  split at h
  · split at h <;> simp_all [instrReadRegs]
  · cases h

theorem movRegArgs?_reads {i : LinstrRM} {d s : String} (h : movRegArgs? i = some (d, s)) :
    s ∈ instrReadRegs i.1 := by
  obtain ⟨x, t⟩ := i
  simp only [movRegArgs?] at h
  split at h
  · repeat' split at h
    all_goals simp_all [instrReadRegs, operandReads]
  · cases h

theorem carryArgs?_reads {i : LinstrRM} {op : CarryOp} {d : String} {a c : LOperand}
    (h : carryArgs? i = some (op, d, a, c)) :
    (∀ q ∈ operandReads a, q ∈ instrReadRegs i.1) ∧
      ∀ q ∈ operandReads c, q ∈ instrReadRegs i.1 := by
  obtain ⟨x, t⟩ := i
  simp only [carryArgs?] at h
  split at h
  · repeat' split at h
    all_goals simp_all [instrReadRegs]
  · cases h

theorem wideArgs?_reads_mov {i : LinstrRM} {d : String} {b : LOperand}
    (h : wideArgs? i = some (.mov d b)) : ∀ q ∈ operandReads b, q ∈ instrReadRegs i.1 := by
  obtain ⟨x, t⟩ := i
  simp only [wideArgs?] at h
  split at h
  · split at h <;> simp_all [instrReadRegs]
  · split at h <;> simp_all
  · cases h

theorem wideArgs?_reads_mulx {i : LinstrRM} {lo hi : String} {b : LOperand}
    (h : wideArgs? i = some (.mulx lo hi b)) :
    (∀ q ∈ operandReads b, q ∈ symReads i.1) ∧ mulxSrc ∈ symReads i.1 := by
  obtain ⟨x, t⟩ := i
  simp only [wideArgs?] at h
  split at h
  · split at h <;> simp_all
  · split at h
    · rename_i opn _ ho
      simp only [Option.some.injEq, WideOp.mulx.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨fun q hq => List.mem_append_left _ (by simp [instrReadRegs, hq]), ?_⟩
      simp [symReads, ho]
    · cases h
  · cases h

theorem aluFlT_congr {ss ss' : SSt} (hS : ss.Same ss') (i : LinstrRM)
    (hR : ∀ q ∈ instrReadRegs i.1, ss.regs q = ss'.regs q) (b : Bool) :
    aluFlT i ss b = aluFlT i ss' b := by
  unfold aluFlT
  split
  · rename_i op a c ha
    have hr := aluFlagOp?_reads ha
    rw [symOp64_congr (R' := ss'.regs) fun q hq => hR q (hr.1 q hq),
      symOp64_congr (R' := ss'.regs) fun q hq => hR q (hr.2 q hq), hS.2.2.1, hS.2.2.2]
  · rw [hS.2.2.1, hS.2.2.2]

theorem aluFl_congr {ss ss' : SSt} (hS : ss.Same ss') (i : LinstrRM)
    (hR : ∀ q ∈ instrReadRegs i.1, ss.regs q = ss'.regs q) {o o' : SOut}
    (ho : SOut.RelOn ss ss' o o') : SOut.RelOn ss ss' (aluFl i ss o) (aluFl i ss' o') := by
  cases o <;> cases o' <;> simp only [SOut.RelOn, aluFl] at ho ⊢
  obtain ⟨hg, ⟨hA, hZ, -, -⟩, hw⟩ := ho
  exact ⟨hg, ⟨hA, hZ, aluFlT_congr hS i hR false, aluFlT_congr hS i hR true⟩, hw⟩

theorem symCarry_congr {ss ss' : SSt} (hS : ss.Same ss') (op : CarryOp) (d : String)
    (a b : LOperand) (ha : ∀ q ∈ operandReads a, ss.regs q = ss'.regs q)
    (hb : ∀ q ∈ operandReads b, ss.regs q = ss'.regs q) :
    SOut.RelOn ss ss' (symCarry op d a b ss) (symCarry op d a b ss') := by
  obtain ⟨hA, hZ, hC, hO⟩ := hS
  unfold symCarry
  rw [symOp64_congr (R' := ss'.regs) ha, symOp64_congr (R' := ss'.regs) hb]
  split
  · cases op <;>
      refine ⟨rfl, ⟨by simp only [SSt.setR, hA], by simp only [SSt.setR, hZ],
        by simp only [SSt.setR, hC, hO], by simp only [SSt.setR, hC, hO]⟩, [d], rfl, rfl,
        fun q hq => ?_⟩ <;>
      simp only [List.mem_singleton] at hq <;> simp [SSt.setR, hq, hC, hO]
  · trivial

theorem symWide_congr {ss ss' : SSt} (hS : ss.Same ss') (i : LinstrRM) {w : WideOp}
    (hw : wideArgs? i = some w) (hR : ∀ q ∈ symReads i.1, ss.regs q = ss'.regs q) :
    SOut.RelOn ss ss' (symWide w ss) (symWide w ss') := by
  obtain ⟨hA, hZ, hC, hO⟩ := hS
  cases w with
  | mov d b =>
      have hr := wideArgs?_reads_mov hw
      simp only [symWide]
      rw [symOp64_congr (R' := ss'.regs) fun q hq => hR q (instrReadRegs_sub _ q (hr q hq))]
      split
      · refine ⟨rfl, ⟨hA, hZ, hC, hO⟩, [d], rfl, rfl, fun q hq => ?_⟩
        simp only [List.mem_singleton] at hq
        simp [SSt.setR, hq]
      · trivial
  | mulx lo hi b =>
      have hr := wideArgs?_reads_mulx hw
      simp only [symWide]
      rw [symOp64_congr (R' := ss'.regs) (o := .reg mulxSrc) (by
          simp only [operandReads, List.mem_singleton]
          rintro q rfl
          exact hR _ hr.2),
        symOp64_congr (R' := ss'.regs) fun q hq => hR q (hr.1 q hq)]
      split
      · refine ⟨rfl, ⟨hA, hZ, hC, hO⟩, [hi, lo], rfl, rfl, fun q hq => ?_⟩
        simp only [SSt.setR_regs]
        split <;> simp_all
      · trivial

/-- **A step reads the register file only at `symReads`.** From states with the same
    words other than registers and one word for every register the instruction reads, the
    two steps agree on what they write. -/
theorem symStep_congr {ss ss' : SSt} (hS : ss.Same ss') (i : LinstrRM)
    (hR : ∀ q ∈ symReads i.1, ss.regs q = ss'.regs q) :
    SOut.RelOn ss ss' (symStep i ss) (symStep i ss') := by
  have hR0 : ∀ q ∈ instrReadRegs i.1, ss.regs q = ss'.regs q :=
    fun q hq => hR q (instrReadRegs_sub _ q hq)
  have hL : ∀ q ∈ leaReads i.1, ss.regs q = ss'.regs q :=
    fun q hq => hR q (leaReads_sub _ q hq)
  obtain ⟨hA, hZ, hC, hO⟩ := hS
  unfold symStep
  split
  · rename_i a b hc
    have hr := cmpArgs?_reads hc
    rw [symOp64_congr (R' := ss'.regs) fun q hq => hR0 q (hr.1 q hq),
      symOp64_congr (R' := ss'.regs) fun q hq => hR0 q (hr.2 q hq)]
    split
    · exact ⟨rfl, ⟨hA, rfl, hC, hO⟩, [], rfl, rfl, fun _ h => by cases h⟩
    · trivial
  · split
    · rename_i dst src hm
      have hs := hR0 src (movRegArgs?_reads hm)
      refine ⟨rfl, ⟨hA, hZ, hC, hO⟩, [dst], rfl, rfl, fun q hq => ?_⟩
      simp only [List.mem_singleton] at hq
      simp [SSt.setR, hq, hs]
    · split
      · trivial
      · split
        · exact ⟨rfl, ⟨hA, hZ, hC, hO⟩, [], rfl, rfl, fun _ h => by cases h⟩
        · trivial
        · trivial
        · split
          · rename_i op d a b hc
            have hr := carryArgs?_reads hc
            exact symCarry_congr ⟨hA, hZ, hC, hO⟩ op d a b (fun q hq => hR0 q (hr.1 q hq))
              (fun q hq => hR0 q (hr.2 q hq))
          · split
            · rename_i w hw
              exact symWide_congr ⟨hA, hZ, hC, hO⟩ i hw hR
            · exact aluFl_congr ⟨hA, hZ, hC, hO⟩ i hR0 (symMem_congr ⟨hA, hZ, hC, hO⟩ i hR0 hL)

/-! ## 2. The names a step writes -/

/-- Two register-file descriptions write the same register, or both write nothing, both
    fail, or both are outside the fragment. -/
def ROut.Sh : ROut → ROut → Prop
  | .set d _ _, .set d' _ _ => d = d'
  | .nop, .nop => True
  | .fail, .fail => True
  | .unk, .unk => True
  | _, _ => False

/-- Two step descriptions from `ss` and from `ss'` extend the written lists by one list of
    names, or both fail, or both are outside the fragment. -/
def SOut.Sh (ss ss' : SSt) : SOut → SOut → Prop
  | .ok s _, .ok s' _ => ∃ ds, s.wr = ds ++ ss.wr ∧ s'.wr = ds ++ ss'.wr
  | .fail, .fail => True
  | .unk, .unk => True
  | _, _ => False

theorem symN_sh (x : LinstrR) (R R' : String → STerm) : ROut.Sh (symN x R) (symN x R') := by
  unfold symN
  repeat' split
  all_goals simp_all [ROut.Sh]

theorem symCast_sh (i : JasminLsemCast.LinstrRT) (R R' : String → STerm) :
    ROut.Sh (symCast i R) (symCast i R') := by
  unfold symCast symMC symSh
  repeat' split
  all_goals first | exact symN_sh _ _ _ | simp_all [ROut.Sh]

theorem liftR_sh (ss ss' : SSt) {o o' : ROut} (h : ROut.Sh o o') :
    SOut.Sh ss ss' (liftR ss o) (liftR ss' o') := by
  cases o <;> cases o' <;> simp only [ROut.Sh] at h <;> simp only [liftR, SOut.Sh]
  · exact ⟨[_], rfl, by simp [SSt.setR, h]⟩
  · exact ⟨[], rfl, rfl⟩

/-- **The names a step writes do not depend on the state.** -/
theorem symStep_sh (i : LinstrRM) (ss ss' : SSt) :
    SOut.Sh ss ss' (symStep i ss) (symStep i ss') := by
  unfold symStep
  split
  · rename_i a b _
    cases a <;> cases b <;> simp only [symOp64] <;> first | exact ⟨[], rfl, rfl⟩ | trivial
  · split
    · exact ⟨[_], rfl, rfl⟩
    · split
      · trivial
      · split
        · exact ⟨[], rfl, rfl⟩
        · trivial
        · trivial
        · split
          · rename_i op d a b _
            unfold symCarry
            cases a <;> cases b <;> simp only [symOp64] <;>
              first | (cases op <;> exact ⟨[d], rfl, rfl⟩) | trivial
          · split
            · rename_i w _
              cases w with
              | mov d b =>
                  simp only [symWide]
                  cases b <;> simp only [symOp64] <;>
                    first | exact ⟨[d], rfl, rfl⟩ | trivial
              | mulx lo hi b =>
                  simp only [symWide]
                  cases b <;> simp only [symOp64] <;>
                    first | exact ⟨[hi, lo], rfl, rfl⟩ | trivial
            · have hm : SOut.Sh ss ss' (symMem i ss) (symMem i ss') := by
                obtain ⟨x, tag⟩ := i
                unfold symMem
                cases tag with
                | load w n =>
                    dsimp only
                    split
                    · exact ⟨[_], rfl, rfl⟩
                    · exact liftR_sh ss ss' (symCast_sh _ _ _)
                | store w n =>
                    dsimp only
                    split
                    · exact ⟨[], rfl, rfl⟩
                    · exact liftR_sh ss ss' (symCast_sh _ _ _)
                | loadC => trivial
                | storeC => trivial
                | zero _ _ => trivial
                | storeImm _ _ => trivial
                | reg cd => exact liftR_sh ss ss' (symCast_sh _ _ _)
              generalize symMem i ss = o at hm
              generalize symMem i ss' = o' at hm
              cases o <;> cases o' <;> simp_all [aluFl, SOut.Sh]

/-- The names the step of `i` writes, read off its step from the start state. -/
def wrOf (i : LinstrRM) : List String :=
  match symStep i SSt.start with
  | .ok s _ => s.wr
  | _ => []

theorem symStep_wr {i : LinstrRM} {ss s : SSt} {g : List SG} (h : symStep i ss = .ok s g) :
    s.wr = wrOf i ++ ss.wr := by
  have hs := symStep_sh i SSt.start ss
  rw [h] at hs
  unfold wrOf
  cases h0 : symStep i SSt.start with
  | ok s0 g0 =>
      rw [h0] at hs
      obtain ⟨ds, h1, h2⟩ := hs
      simp only [SSt.start, List.append_nil] at h1
      simp only [h1, h2]
  | fail => rw [h0] at hs; cases hs
  | unk => rw [h0] at hs; cases hs

/-! ## 3. Immediate moves -/

/-- A memory tag under which the step of a register instruction is the register-file
    step: every tag but the compile-time-offset ones and the array-zeroing one. -/
def tagPlain : MemTag → Bool
  | .loadC => false
  | .storeC => false
  | .zero _ _ => false
  | .storeImm _ _ => false
  | _ => true

/-- The register an immediate move `MOV d, $n` sets, for a plain tag. -/
def immMov? (i : LinstrRM) : Option String :=
  match i with
  | (.Lopn [.reg d] opn [.imm _], tag) =>
      if stripWidthTag opn = "MOV" ∧ tagPlain tag = true then some d else none
  | _ => none

theorem immMov?_spec {i : LinstrRM} {r : String} (h : immMov? i = some r) :
    ∃ opn n tag, i = (.Lopn [.reg r] opn [.imm n], tag) ∧ stripWidthTag opn = "MOV" ∧
      tagPlain tag = true := by
  unfold immMov? at h
  split at h
  · split at h
    · rename_i d opn n tag hc
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨opn, n, tag, rfl, hc.1, hc.2⟩
    · cases h
  · cases h

/-- **The step of an immediate move.** It sets the register to an immediate, with no
    guard, from every state. -/
theorem symStep_immMov {i : LinstrRM} {r : String} (h : immMov? i = some r) :
    ∃ w n, ∀ ss, symStep i ss = .ok (ss.setR r (.immW w n)) [] := by
  obtain ⟨opn, n, tag, rfl, hm, ht⟩ := immMov?_spec h
  have hn : ∀ R, symN (.Lopn [.reg r] opn [.imm n]) R =
      .set r (.immW (widthFromTag opn) n) [] := fun R => by
    unfold symN
    simp only [hm, if_true]
  have hd : ∀ R, symMC (.Lopn [.reg r] opn [.imm n]) R =
      .set r (.immW (widthFromTag opn) n) [] := fun R => by
    simp only [symMC, symSh, JasminLsemMulCarry.mulhiStruct?, JasminLsemMulCarry.adcxStruct?,
      JasminLsemMulCarry.adcxhiStruct?, JasminLsemMulCarry.sbbStruct?,
      JasminLsemMulCarry.sbbhiStruct?, JasminLsemShift.sarStruct?, hn]
  have hc : ∀ cd, ∃ w, ∀ R, symCast (.Lopn [.reg r] opn [.imm n], cd) R =
      .set r (.immW w n) [] := by
    intro cd
    by_cases ho : opn = "MOV"
    · subst ho
      cases cd with
      | none =>
          exact ⟨widthFromTag "MOV", fun R => by
            simp only [symCast, JasminLsemCast.castStruct?, JasminLsemCast.movImmStruct?, hd]⟩
      | some w' =>
          exact ⟨w', fun R => by
            simp only [symCast, JasminLsemCast.castStruct?, JasminLsemCast.movImmStruct?]⟩
    · have hmi : JasminLsemCast.movImmStruct? (.Lopn [.reg r] opn [.imm n]) = none := by
        unfold JasminLsemCast.movImmStruct?
        split
        · rename_i heq
          injection heq with _ h2 _
          exact absurd h2 ho
        · rfl
      exact ⟨widthFromTag opn, fun R => by simp only [symCast, JasminLsemCast.castStruct?, hmi, hd]⟩
  obtain ⟨w, hm'⟩ : ∃ w, ∀ ss : SSt, symMem (.Lopn [.reg r] opn [.imm n], tag) ss =
      .ok (ss.setR r (.immW w n)) [] := by
    cases tag with
    | load a k =>
        obtain ⟨w, hw⟩ := hc none
        exact ⟨w, fun ss => by simp [symMem, loadStruct?, hw, liftR]⟩
    | store a k =>
        obtain ⟨w, hw⟩ := hc none
        exact ⟨w, fun ss => by simp [symMem, storeStruct?, hw, liftR]⟩
    | loadC => cases ht
    | storeC => cases ht
    | zero _ _ => cases ht
    | storeImm _ _ => cases ht
    | reg cd =>
        obtain ⟨w, hw⟩ := hc cd
        exact ⟨w, fun ss => by simp [symMem, hw, liftR]⟩
  refine ⟨w, n, fun ss => ?_⟩
  simp [symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, hm' ss, aluFl,
    aluFlT, aluFlagOp?, SSt.setR]

/-! ## 4. Interning states that agree on the interned registers -/

theorem Tbl.internRegs_keep : ∀ (T : Tbl) (ss : SSt) (ds : List String) (q : String),
    q ∉ ds → (T.internRegs ss ds).2.regs q = ss.regs q
  | _, _, [], _, _ => rfl
  | T, ss, d :: ds, q, hq => by
      simp only [List.mem_cons, not_or] at hq
      simp only [Tbl.internRegs]
      rw [Tbl.internRegs_keep _ _ ds q hq.2, SSt.putR_regs, if_neg hq.1]

theorem Tbl.internRegs_on : ∀ (T : Tbl) (ss ss' : SSt) (ds : List String),
    (∀ q ∈ ds, ss.regs q = ss'.regs q) →
      (T.internRegs ss' ds).1 = (T.internRegs ss ds).1 ∧
        ∀ q ∈ ds, (T.internRegs ss' ds).2.regs q = (T.internRegs ss ds).2.regs q
  | _, _, _, [], _ => ⟨rfl, fun _ h => by cases h⟩
  | T, ss, ss', d :: ds, h => by
      simp only [Tbl.internRegs]
      have hd : ss'.regs d = ss.regs d := (h d (List.mem_cons_self ..)).symm
      rw [hd]
      have ih := Tbl.internRegs_on (T.intern (ss.regs d)).1
        (ss.putR d (T.intern (ss.regs d)).2) (ss'.putR d (T.intern (ss.regs d)).2) ds
        (fun q hq => by
          rw [SSt.putR_regs, SSt.putR_regs]
          split
          · rfl
          · exact h q (List.mem_cons_of_mem _ hq))
      refine ⟨ih.1, fun q hq => ?_⟩
      by_cases hqs : q ∈ ds
      · exact ih.2 q hqs
      · rw [Tbl.internRegs_keep _ _ ds q hqs, Tbl.internRegs_keep _ _ ds q hqs]
        have hqd : q = d := by simpa [hqs] using hq
        simp [hqd, SSt.putR_regs]

theorem Tbl.internSt_keep (T : Tbl) (ss : SSt) (ds : List String) (q : String) (hq : q ∉ ds) :
    (T.internSt ss ds).2.regs q = ss.regs q :=
  Tbl.internRegs_keep T ss ds q hq

/-- **Interning states that agree on the interned registers.** Two states with the same
    words other than registers and one word for every register of `ds` intern to the same
    table, with the same words other than registers and one word for every register of
    `ds`. -/
theorem Tbl.internSt_on (T : Tbl) {ss ss' : SSt} (ds : List String) (hS : ss.Same ss')
    (hd : ∀ q ∈ ds, ss.regs q = ss'.regs q) :
    (T.internSt ss' ds).1 = (T.internSt ss ds).1 ∧
      (T.internSt ss ds).2.Same (T.internSt ss' ds).2 ∧
      (∀ q ∈ ds, (T.internSt ss ds).2.regs q = (T.internSt ss' ds).2.regs q) ∧
      (T.internSt ss' ds).2.wr = ss'.wr := by
  obtain ⟨h1, h2⟩ := Tbl.internRegs_on T ss ss' ds hd
  have e1 := Tbl.internRegs_snd T ss ds
  have e2 := Tbl.internRegs_snd T ss' ds
  have hc : (T.internRegs ss' ds).2.cf = (T.internRegs ss ds).2.cf := by
    rw [e1, e2]; exact hS.2.2.1.symm
  have ho : (T.internRegs ss' ds).2.of = (T.internRegs ss ds).2.of := by
    rw [e1, e2]; exact hS.2.2.2.symm
  simp only [Tbl.internSt, h1, hc, ho]
  refine ⟨by simp, ⟨?_, ?_, rfl, rfl⟩, fun q hq => (h2 q hq).symm, ?_⟩
  · rw [e1, e2]; exact hS.1
  · rw [e1, e2]; exact hS.2.1
  · rw [e2]

/-! ## 5. Runs without dead immediate moves -/

/-- The instructions of a marked body. -/
def srcOf (B : List (LinstrRM × Bool)) : List LinstrRM := B.map Prod.fst

/-- The unmarked instructions of a marked body. -/
def keptOf (B : List (LinstrRM × Bool)) : List LinstrRM :=
  (B.filter (fun p => !p.2)).map Prod.fst

/-- The marks of a body are dead immediate moves, with the registers `D` set by marked
    moves still pending: every marked instruction is an immediate move; no unmarked
    instruction reads a pending register; a register leaves the pending list when an
    unmarked instruction writes it; and no register is pending at the end. -/
def dropOk (D : List String) : List (LinstrRM × Bool) → Bool
  | [] => D.isEmpty
  | (i, true) :: rest =>
      match immMov? i with
      | some r => dropOk (r :: D) rest
      | none => false
  | (i, false) :: rest =>
      D.all (fun q => !(symReads i.1).contains q) &&
        dropOk (D.filter (fun q => !(wrOf i).contains q)) rest

/-- Two states with the same words other than registers and one word for every register
    outside `D`. -/
def SSt.EqvOn (D : List String) (s t : SSt) : Prop :=
  s.Same t ∧ ∀ q, q ∉ D → s.regs q = t.regs q

theorem tRun_immMov {ss : SSt} {T : Tbl} (hI : ss.Inv T.ents.size) (r : String) (w n : Nat) :
    T.internSt (ss.setR r (.immW w n)) [r] = (T, ss.setR r (.immW w n)) := by
  have hc := Tbl.intern_atom T hI.2.2.1
  have ho := Tbl.intern_atom T hI.2.2.2
  have hi : T.intern (.immW w n) = (T, .immW w n) := Tbl.intern_atom T rfl
  have hp : (ss.setR r (.immW w n)).putR r (.immW w n) = ss.setR r (.immW w n) :=
    SSt.ext (fun q => by
      rw [SSt.putR_regs, SSt.setR_regs]
      by_cases h : q = r <;> simp [h]) rfl rfl rfl rfl rfl rfl
  simp only [Tbl.internSt, Tbl.internRegs, SSt.setR_regs, ↓reduceIte, hi, hp]
  rw [show (ss.setR r (.immW w n)).cf = ss.cf from rfl,
    show (ss.setR r (.immW w n)).of = ss.of from rfl, hc, ho]
  rfl

/-- **Runs without dead immediate moves.** From states that agree off the pending
    registers `D`, the run of a marked body and the run of its unmarked instructions, in
    a table holding what the first run interns, agree, when the marks are dead immediate
    moves (`dropOk`). -/
theorem tRun_drop : ∀ (B : List (LinstrRM × Bool)) (D : List String) (ss ss' : SSt)
    (T T' : Tbl), dropOk D B = true → ss.EqvOn D ss' → ss.Inv T.ents.size →
    (tRun (srcOf B) ss T).1.Sub T' → Res T' (tRun (srcOf B) ss T).2 (tRun (keptOf B) ss' T')
  | [], D, ss, ss', T, T', hok, e, _, _ => by
      simp only [dropOk, List.isEmpty_iff] at hok
      subst hok
      simp only [srcOf, keptOf, List.map_nil, List.filter_nil, tRun]
      exact ⟨rfl, ⟨funext fun q => e.2 q (by simp), e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2⟩, rfl⟩
  | (i, true) :: rest, D, ss, ss', T, T', hok, e, hI, hS => by
      simp only [dropOk] at hok
      cases hm : immMov? i with
      | none => rw [hm] at hok; cases hok
      | some r =>
          rw [hm] at hok
          obtain ⟨w, n, hst⟩ := symStep_immMov hm
          have hsrc : srcOf ((i, true) :: rest) = i :: srcOf rest := rfl
          have hkept : keptOf ((i, true) :: rest) = keptOf rest := by simp [keptOf]
          rw [hsrc, tRun_cons, hst ss] at hS
          rw [hsrc, hkept, tRun_cons, hst ss]
          have hds : (ss.setR r (.immW w n)).wr.take
              ((ss.setR r (.immW w n)).wr.length - ss.wr.length) = [r] :=
            SSt.Frm.ds_eq (by simp [SSt.setR])
          dsimp only at hS ⊢
          rw [hds, tRun_immMov hI] at hS ⊢
          simp only [runAfter, SOut.after_nil] at hS ⊢
          have e' : (ss.setR r (.immW w n)).EqvOn (r :: D) ss' := by
            refine ⟨e.1, fun q hq => ?_⟩
            simp only [List.mem_cons, not_or] at hq
            rw [SSt.setR_regs, if_neg hq.1]
            exact e.2 q hq.2
          have hI' : (ss.setR r (.immW w n)).Inv T.ents.size := by
            obtain ⟨⟨hr, ha, hz, hc, ho⟩, hat, hca, hoa⟩ := hI
            refine ⟨⟨fun q => ?_, ha, hz, hc, ho⟩, fun q => ?_, hca, hoa⟩ <;>
              rw [SSt.setR_regs] <;> split
            · rfl
            · exact hr q
            · rfl
            · exact hat q
          exact tRun_drop rest (r :: D) _ ss' T T' hok e' hI' hS
  | (i, false) :: rest, D, ss, ss', T, T', hok, e, hI, hS => by
      simp only [dropOk, Bool.and_eq_true, List.all_eq_true] at hok
      obtain ⟨hrd, hok⟩ := hok
      have hR : ∀ q ∈ symReads i.1, ss.regs q = ss'.regs q := by
        intro q hq
        refine e.2 q fun hqD => ?_
        have := hrd q hqD
        simp_all
      have hc := symStep_congr e.1 i hR
      have hsrc : srcOf ((i, false) :: rest) = i :: srcOf rest := rfl
      have hkept : keptOf ((i, false) :: rest) = i :: keptOf rest := by simp [keptOf]
      rw [hsrc, tRun_cons] at hS
      rw [hsrc, hkept, tRun_cons, tRun_cons]
      cases hs : symStep i ss with
      | ok s1 g1 =>
          cases hs' : symStep i ss' with
          | ok s1' g1' =>
              rw [hs, hs'] at hc
              obtain ⟨rfl, hSame, ds, hw, hw', hds⟩ := hc
              rw [hs] at hS
              dsimp only at hS ⊢
              rw [SSt.Frm.ds_eq hw] at hS ⊢
              rw [SSt.Frm.ds_eq hw']
              have hR1 := symStep_refsLt i hI.1 hs
              obtain ⟨ds0, hw0, hr0⟩ := symStep_frm i hs
              have hd0 : ds = ds0 := List.append_cancel_right (hw.symm.trans hw0)
              obtain ⟨ds1, hw1, hr1⟩ := symStep_frm i hs'
              have hd1 : ds = ds1 := List.append_cancel_right (hw'.symm.trans hw1)
              have hdw : ds = wrOf i := List.append_cancel_right (hw.symm.trans (symStep_wr hs))
              have hI2 : (T.internSt s1 ds).2.Inv (T.internSt s1 ds).1.ents.size :=
                Tbl.internSt_inv (T := T) ds hR1.1 (fun r hr => by
                  rw [hr0 r (hd0 ▸ hr)]; exact hI.2.1 r)
              have hSub : (T.internSt s1 ds).1.Sub T' :=
                (tRun_sub _ _ _).trans (by simpa [runAfter] using hS)
              obtain ⟨s0, h0, e0, -, -⟩ :=
                Tbl.internSt_rerun (ss := s1)
                  (ss' := { s1 with wr := s1'.wr, awr := s1'.awr, nwr := s1'.nwr,
                                    nwr_eq := s1'.nwr_eq })
                  ⟨rfl, rfl, rfl, rfl, rfl⟩ ds hR1.1 hSub
              obtain ⟨ht1, hSm, hag, -⟩ :=
                Tbl.internSt_on T'
                  (ss := { s1 with wr := s1'.wr, awr := s1'.awr, nwr := s1'.nwr,
                                   nwr_eq := s1'.nwr_eq })
                  (ss' := s1') ds hSame hds
              rw [h0] at ht1 hSm hag
              dsimp only at ht1 hSm hag
              have eD : (T.internSt s1 ds).2.EqvOn (D.filter (fun q => !(wrOf i).contains q))
                  (T'.internSt s1' ds).2 := by
                refine ⟨⟨e0.2.1.trans hSm.1, e0.2.2.1.trans hSm.2.1, e0.2.2.2.1.trans hSm.2.2.1,
                  e0.2.2.2.2.trans hSm.2.2.2⟩, fun q hq => ?_⟩
                by_cases hqd : q ∈ ds
                · rw [e0.1]; exact hag q hqd
                · rw [Tbl.internSt_keep _ _ _ q hqd, Tbl.internSt_keep _ _ _ q hqd,
                    hr0 q (hd0 ▸ hqd), hr1 q (hd1 ▸ hqd)]
                  refine e.2 q fun hqD => hq ?_
                  simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
                    decide_eq_false_iff_not]
                  exact ⟨hqD, hdw ▸ hqd⟩
              have ih := tRun_drop rest _ _ _ _ T' hok eD hI2 (by simpa [runAfter] using hS)
              have hT : (T'.internSt s1' ds).1 = T' := ht1
              rw [hT]
              generalize tRun (srcOf rest) (T.internSt s1 ds).2 (T.internSt s1 ds).1 = r1 at ih ⊢
              generalize tRun (keptOf rest) (T'.internSt s1' ds).2 T' = r2 at ih ⊢
              obtain ⟨R1, o1⟩ := r1
              obtain ⟨R2, o2⟩ := r2
              cases o1 <;> cases o2 <;> simp_all [Res, runAfter, SOut.after]
          | fail => rw [hs, hs'] at hc; cases hc
          | unk => rw [hs, hs'] at hc; cases hc
      | fail =>
          cases hs' : symStep i ss' <;> rw [hs, hs'] at hc <;> simp only [SOut.RelOn] at hc
          trivial
      | unk =>
          cases hs' : symStep i ss' <;> rw [hs, hs'] at hc <;> simp only [SOut.RelOn] at hc
          trivial

/-- **Completeness for dropping dead immediate moves.** A straight-line marked body whose
    marks are dead immediate moves, whose symbolic run lies inside the fragment and which
    keeps an instruction, passes `ownedCheckM` against its unmarked instructions. -/
theorem dropOk_ownedCheckM_complete (outs : List String) (B : List (LinstrRM × Bool))
    (hne : keptOf B ≠ []) (hs : ∀ p ∈ B, straightR p.1.1 = true) (hok : dropOk [] B = true)
    (hfrag : symRun (srcOf B) SSt.start ≠ .unk) :
    ownedCheckM outs (srcOf B) (keptOf B) = true := by
  have hsrc : srcOf B ≠ [] := by
    intro h
    apply hne
    simp only [srcOf, List.map_eq_nil_iff] at h
    simp [keptOf, h]
  refine ownedCheckM_of_res outs hsrc hne ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact hs p hp
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact hs p (List.mem_filter.mp hp).1
  · exact tRun_drop B [] SSt.start SSt.start Tbl.empty _ hok
      ⟨SSt.Same.refl _, fun _ _ => rfl⟩ SSt.inv_start (Tbl.Sub.refl _)
  · rwa [ne_eq, tRun_unk_iff]

/-! ## 6. The dead-move elimination of `ConstIndexFold` -/

section DeadImm

open ConstIndexFold

/-- The body with each instruction marked when `ConstIndexFold.dropDeadCore` removes it. -/
def deadMarks (p : Nat × Nat × Nat) : Lcmd → List (Linstr × Bool)
  | [] => []
  | i :: is =>
      (i, match deadImmReg? p i with
          | some r => deadAfter p r is
          | none => false) :: deadMarks p is

theorem deadMarks_fst (p : Nat × Nat × Nat) : ∀ body : Lcmd,
    (deadMarks p body).map Prod.fst = body
  | [] => rfl
  | i :: is => by simp [deadMarks, deadMarks_fst p is]

theorem deadMarks_kept (p : Nat × Nat × Nat) : ∀ body : Lcmd,
    ((deadMarks p body).filter (fun q => !q.2)).map Prod.fst = dropDeadCore p body
  | [] => rfl
  | i :: is => by
      simp only [deadMarks, dropDeadCore]
      cases deadImmReg? p i with
      | none => simp [deadMarks_kept p is]
      | some r =>
          cases hd : deadAfter p r is <;> simp [hd, deadMarks_kept p is]

/-- The marks of `dropDeadImmBody`: those of `dropDeadCore` at the body's frame
    parameters when the elimination keeps them, and none otherwise. -/
def dropDeadImmMarks (body : Lcmd) : List (Linstr × Bool) :=
  if bodyParams (dropDeadCore (bodyParams body) body) = bodyParams body then
    deadMarks (bodyParams body) body
  else body.map (·, false)

/-- The typed marked body at the typing `tg`. -/
def typeMarks (tg : LinstrR → MemTag) (M : List (Linstr × Bool)) : List (LinstrRM × Bool) :=
  M.map fun q => ((q.1.li_i, tg q.1.li_i), q.2)

/-- The unmarked instructions of a marked body. -/
def keptL (M : List (Linstr × Bool)) : Lcmd := (M.filter (fun q => !q.2)).map Prod.fst

theorem srcOf_typeMarks (tg : LinstrR → MemTag) (M : List (Linstr × Bool)) :
    srcOf (typeMarks tg M) = typeBody tg (M.map Prod.fst) := by
  simp [srcOf, typeMarks, typeBody]

theorem keptOf_typeMarks (tg : LinstrR → MemTag) (M : List (Linstr × Bool)) :
    keptOf (typeMarks tg M) = typeBody tg (keptL M) := by
  simp [keptOf, keptL, typeMarks, typeBody, List.filter_map, Function.comp_def]

/-- **Completeness for a marked body.** -/
theorem marks_ownedCheckM_complete (outs : List String) (tg : LinstrR → MemTag)
    (M : List (Linstr × Bool)) (hne : keptL M ≠ [])
    (hs : ∀ i ∈ M.map Prod.fst, straightR i.li_i = true)
    (hok : dropOk [] (typeMarks tg M) = true)
    (hfrag : symRun (typeBody tg (M.map Prod.fst)) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody tg (M.map Prod.fst)) (typeBody tg (keptL M)) = true := by
  rw [← srcOf_typeMarks, ← keptOf_typeMarks]
  refine dropOk_ownedCheckM_complete outs _ ?_ ?_ hok (by rwa [srcOf_typeMarks])
  · rw [keptOf_typeMarks]
    simpa [typeBody] using hne
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hq
    exact hs m.1 (List.mem_map_of_mem hm)

theorem dropDeadImmMarks_fst (body : Lcmd) : (dropDeadImmMarks body).map Prod.fst = body := by
  unfold dropDeadImmMarks
  split
  · exact deadMarks_fst _ body
  · simp [Function.comp_def]

theorem keptL_dropDeadImmMarks (body : Lcmd) :
    keptL (dropDeadImmMarks body) = dropDeadImmBody body := by
  unfold keptL dropDeadImmMarks dropDeadImmBody
  dsimp only
  split
  · exact deadMarks_kept _ body
  · rw [List.filter_map]
    simp [Function.comp_def]

/-- **Completeness of the value checker for the dead-move elimination.** For a
    straight-line body whose eliminated instructions are dead immediate moves at the level
    of the symbolic step (`dropOk`), whose symbolic run lies inside the fragment and whose
    elimination keeps an instruction, `ownedCheckM` accepts the body against
    `ConstIndexFold.dropDeadImmBody`, for every observed list `outs` and every typing. -/
theorem dropDeadImm_ownedCheckM_complete (outs : List String) (tg : LinstrR → MemTag)
    (body : Lcmd) (hne : dropDeadImmBody body ≠ [])
    (hs : ∀ i ∈ body, straightR i.li_i = true)
    (hok : dropOk [] (typeMarks tg (dropDeadImmMarks body)) = true)
    (hfrag : symRun (typeBody tg body) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody tg body) (typeBody tg (dropDeadImmBody body)) = true := by
  have h := marks_ownedCheckM_complete outs tg (dropDeadImmMarks body)
    (by rwa [keptL_dropDeadImmMarks]) (by rwa [dropDeadImmMarks_fst]) hok
    (by rwa [dropDeadImmMarks_fst])
  rwa [dropDeadImmMarks_fst, keptL_dropDeadImmMarks] at h

/-- A marked body with the array-ABI spelling `ConstIndexFold.spellMemInstr` applied to every
    instruction. -/
def spellMarks (M : List (Linstr × Bool)) : List (Linstr × Bool) :=
  M.map fun q => ({ q.1 with li_i := spellMemInstr q.1.li_i }, q.2)

theorem spellMarks_fst (M : List (Linstr × Bool)) :
    (spellMarks M).map Prod.fst = spellMemBody (M.map Prod.fst) := by
  simp [spellMarks, spellMemBody]

theorem keptL_spellMarks (M : List (Linstr × Bool)) :
    keptL (spellMarks M) = spellMemBody (keptL M) := by
  simp [keptL, spellMarks, spellMemBody, List.filter_map, Function.comp_def]

/-- **Completeness for the dead-move elimination followed by the array-ABI spelling.** The
    pair is the one `ConstIndexFold.foldIndexedBody` produces from the folded body `f`:
    `ownedCheckM` accepts the spelled body against the spelled body without its dead
    immediate moves, when the hypotheses of `marks_ownedCheckM_complete` hold on the spelled
    marks. -/
theorem spellDropDeadImm_ownedCheckM_complete (outs : List String) (tg : LinstrR → MemTag)
    (f : Lcmd) (hne : dropDeadImmBody f ≠ [])
    (hs : ∀ i ∈ spellMemBody f, straightR i.li_i = true)
    (hok : dropOk [] (typeMarks tg (spellMarks (dropDeadImmMarks f))) = true)
    (hfrag : symRun (typeBody tg (spellMemBody f)) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody tg (spellMemBody f))
      (typeBody tg (spellMemBody (dropDeadImmBody f))) = true := by
  have hf : (spellMarks (dropDeadImmMarks f)).map Prod.fst = spellMemBody f := by
    rw [spellMarks_fst, dropDeadImmMarks_fst]
  have hk : keptL (spellMarks (dropDeadImmMarks f)) = spellMemBody (dropDeadImmBody f) := by
    rw [keptL_spellMarks, keptL_dropDeadImmMarks]
  have h := marks_ownedCheckM_complete outs tg (spellMarks (dropDeadImmMarks f))
    (by rw [hk]; simpa [spellMemBody] using hne) (by rwa [hf]) hok (by rwa [hf])
  rwa [hf, hk] at h

/-- **Completeness at the owned stage.** `ownedCheckM` accepts the spelled fold of a body
    against `ConstIndexFold.foldIndexedBody`, under the hypotheses of
    `spellDropDeadImm_ownedCheckM_complete` at the folded body. -/
theorem foldIndexed_ownedCheckM_complete (outs : List String) (tg : LinstrR → MemTag)
    (body : Lcmd) (hne : dropDeadImmBody (constIndexFoldBody body) ≠ [])
    (hs : ∀ i ∈ spellMemBody (constIndexFoldBody body), straightR i.li_i = true)
    (hok : dropOk [] (typeMarks tg (spellMarks (dropDeadImmMarks (constIndexFoldBody body))))
      = true)
    (hfrag : symRun (typeBody tg (spellMemBody (constIndexFoldBody body))) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody tg (spellMemBody (constIndexFoldBody body)))
      (typeBody tg (foldIndexedBody body)) = true :=
  spellDropDeadImm_ownedCheckM_complete outs tg _ hne hs hok hfrag

end DeadImm

/-! ## 7. Flag-quiet steps -/

/-- The step of `i` writes no array: its tag is not an array store, or its instruction is
    not a recognised indexed store. -/
def arrQuiet (i : LinstrRM) : Bool :=
  match i.2 with
  | .store _ _ => (storeStruct? i.1).isNone
  | _ => true

/-- The step of `i` writes no flag and no array: `i` is not a compare, not a carry-family
    operation, not an arithmetic or logical operation whose flags the machine records
    (`aluFlagOp?`), and not an array store. A `MUL`, an `IMUL` and every `MOV` are
    flag-quiet in this sense. -/
def flagQuiet (i : LinstrRM) : Bool :=
  (cmpArgs? i).isNone && (carryArgs? i).isNone && (aluFlagOp? i).isNone && arrQuiet i

theorem SSt.Same.symm {s t : SSt} (h : s.Same t) : t.Same s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem SSt.Same.trans {s t u : SSt} (h1 : s.Same t) (h2 : t.Same u) : s.Same u :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem SSt.Same.setR (ss : SSt) (d : String) (t : STerm) : (ss.setR d t).Same ss :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem liftR_same {ss s : SSt} {o : ROut} {gs : List SG} (h : liftR ss o = .ok s gs) :
    s.Same ss := by
  cases o <;> simp only [liftR, SOut.ok.injEq, reduceCtorEq] at h
  · rw [← h.1]; exact SSt.Same.setR _ _ _
  · rw [← h.1]; exact SSt.Same.refl ss

theorem symMem_same (i : LinstrRM) (ha : arrQuiet i = true) {ss s : SSt} {gs : List SG}
    (h : symMem i ss = .ok s gs) : s.Same ss := by
  obtain ⟨x, tag⟩ := i
  unfold symMem at h
  cases tag with
  | load w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact SSt.Same.setR _ _ _
      · exact liftR_same h
  | store w n =>
      dsimp only at h
      split at h
      · rename_i hs
        simp [arrQuiet, hs] at ha
      · exact liftR_same h
  | loadC => cases h
  | storeC => cases h
  | zero _ _ => cases h
  | storeImm _ _ => cases h
  | reg cd => exact liftR_same h

/-- **A flag-quiet step keeps the flags and the arrays.** -/
theorem symStep_same (i : LinstrRM) (hq : flagQuiet i = true) {ss s : SSt} {g : List SG}
    (h : symStep i ss = .ok s g) : s.Same ss := by
  simp only [flagQuiet, Bool.and_eq_true, Option.isNone_iff_eq_none] at hq
  obtain ⟨⟨⟨hc, hk⟩, hm⟩, ha⟩ := hq
  unfold symStep at h
  simp only [hc, hk] at h
  split at h
  · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact SSt.Same.setR _ _ _
  · split at h
    · cases h
    · split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact SSt.Same.refl ss
      · cases h
      · cases h
      · split at h
        · rename_i w _
          cases w with
          | mov d b =>
              simp only [symWide] at h
              split at h
              · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact SSt.Same.setR _ _ _
              · cases h
          | mulx lo hi b =>
              simp only [symWide] at h
              split at h
              · simp only [SOut.ok.injEq] at h; rw [← h.1]
                exact (SSt.Same.setR _ _ _).trans (SSt.Same.setR _ _ _)
              · cases h
        · cases hs : symMem i ss with
          | ok s1 g1 =>
              rw [hs] at h
              simp only [aluFl, SOut.ok.injEq] at h
              rw [← h.1]
              have e := symMem_same i ha hs
              exact ⟨e.1, e.2.1, by simp [aluFlT, hm], by simp [aluFlT, hm]⟩
          | fail => rw [hs] at h; cases h
          | unk => rw [hs] at h; cases h

/-- Interning a state whose flags are atoms keeps its flags and arrays. -/
theorem Tbl.internSt_same (T : Tbl) {s : SSt} (ds : List String) (hc : s.cf.atom = true)
    (ho : s.of.atom = true) : (T.internSt s ds).2.Same s := by
  have e1 := Tbl.internRegs_snd T s ds
  simp only [Tbl.internSt]
  generalize hp : T.internRegs s ds = p at e1
  obtain ⟨P, ps⟩ := p
  dsimp only at e1 ⊢
  rw [e1]
  dsimp only
  rw [Tbl.intern_atom P hc]
  dsimp only
  rw [Tbl.intern_atom P ho]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 8. Runs without dead flag-quiet writes -/

/-- The marks of a body are dead flag-quiet writes, with the registers `D` written by marked
    instructions still pending: every marked instruction is flag-quiet and adds the names it
    writes (`wrOf`) to the pending list; no unmarked instruction reads a pending register; a
    register leaves the pending list when an unmarked instruction writes it; and no register
    is pending at the end. -/
def dropOkW (D : List String) : List (LinstrRM × Bool) → Bool
  | [] => D.isEmpty
  | (i, true) :: rest => flagQuiet i && dropOkW (wrOf i ++ D) rest
  | (i, false) :: rest =>
      D.all (fun q => !(symReads i.1).contains q) &&
        dropOkW (D.filter (fun q => !(wrOf i).contains q)) rest

/-- The source description `o` and the target run `r` agree up to guards: when the source
    succeeds, the target succeeds in the table `T'`, in a state with one word for every
    name, with guards among the source guards. -/
def ResW (T' : Tbl) : SOut → Tbl × SOut → Prop
  | .ok s g, r =>
      match r.2 with
      | .ok s' g' => r.1 = T' ∧ s.Eqv s' ∧ ∀ x ∈ g', x ∈ g
      | _ => False
  | .fail, _ => True
  | .unk, _ => True

theorem ResW_after {T' : Tbl} {o : SOut} {r : Tbl × SOut} (g : List SG) (h : ResW T' o r) :
    ResW T' (o.after g) r := by
  obtain ⟨R, o'⟩ := r
  cases o with
  | ok s g2 =>
      cases o' with
      | ok s' g' =>
          obtain ⟨h1, h2, h3⟩ := h
          exact ⟨h1, h2, fun x hx => List.mem_append_right _ (h3 x hx)⟩
      | fail => exact h.elim
      | unk => exact h.elim
  | fail => trivial
  | unk => trivial

theorem ResW_after₂ {T' : Tbl} {o : SOut} {r : Tbl × SOut} (g : List SG) (h : ResW T' o r) :
    ResW T' (o.after g) (runAfter g r) := by
  obtain ⟨R, o'⟩ := r
  cases o with
  | ok s g2 =>
      cases o' with
      | ok s' g' =>
          obtain ⟨h1, h2, h3⟩ := h
          refine ⟨h1, h2, fun x hx => ?_⟩
          simp only [List.mem_append] at hx ⊢
          exact hx.imp id (h3 x)
      | fail => exact h.elim
      | unk => exact h.elim
  | fail => trivial
  | unk => trivial

/-- **Runs without dead flag-quiet writes.** From states that agree off the pending
    registers `D`, the run of a marked body and the run of its unmarked instructions, in a
    table holding what the first run interns, agree up to guards (`ResW`), when the marks are
    dead flag-quiet writes (`dropOkW`). -/
theorem tRun_dropW : ∀ (B : List (LinstrRM × Bool)) (D : List String) (ss ss' : SSt)
    (T T' : Tbl), dropOkW D B = true → ss.EqvOn D ss' → ss.Inv T.ents.size →
    (tRun (srcOf B) ss T).1.Sub T' → ResW T' (tRun (srcOf B) ss T).2 (tRun (keptOf B) ss' T')
  | [], D, ss, ss', T, T', hok, e, _, _ => by
      simp only [dropOkW, List.isEmpty_iff] at hok
      subst hok
      simp only [srcOf, keptOf, List.map_nil, List.filter_nil, tRun]
      exact ⟨rfl, ⟨funext fun q => e.2 q (by simp), e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2⟩,
        fun _ h => h⟩
  | (i, true) :: rest, D, ss, ss', T, T', hok, e, hI, hS => by
      simp only [dropOkW, Bool.and_eq_true] at hok
      obtain ⟨hq, hok⟩ := hok
      have hsrc : srcOf ((i, true) :: rest) = i :: srcOf rest := rfl
      have hkept : keptOf ((i, true) :: rest) = keptOf rest := by simp [keptOf]
      rw [hsrc, tRun_cons] at hS
      rw [hsrc, hkept, tRun_cons]
      cases hs : symStep i ss with
      | ok s1 g1 =>
          rw [hs] at hS
          dsimp only at hS ⊢
          have hw := symStep_wr hs
          rw [SSt.Frm.ds_eq hw] at hS ⊢
          obtain ⟨ds0, hw0, hr0⟩ := symStep_frm i hs
          have hd0 : wrOf i = ds0 := List.append_cancel_right (hw.symm.trans hw0)
          have hR1 := symStep_refsLt i hI.1 hs
          have hsm := symStep_same i hq hs
          have hI2 : (T.internSt s1 (wrOf i)).2.Inv (T.internSt s1 (wrOf i)).1.ents.size :=
            Tbl.internSt_inv _ hR1.1 (fun r hr => by
              rw [hr0 r (hd0 ▸ hr)]; exact hI.2.1 r)
          have hsm2 := Tbl.internSt_same T (wrOf i) (s := s1)
            (by rw [hsm.2.2.1]; exact hI.2.2.1) (by rw [hsm.2.2.2]; exact hI.2.2.2)
          have e' : (T.internSt s1 (wrOf i)).2.EqvOn (wrOf i ++ D) ss' := by
            refine ⟨(hsm2.trans hsm).trans e.1, fun q hq => ?_⟩
            simp only [List.mem_append, not_or] at hq
            rw [Tbl.internSt_keep _ _ _ q hq.1, hr0 q (hd0 ▸ hq.1)]
            exact e.2 q hq.2
          have ih := tRun_dropW rest _ _ ss' _ T' hok e' hI2 (by simpa [runAfter] using hS)
          exact ResW_after g1 ih
      | fail => trivial
      | unk => trivial
  | (i, false) :: rest, D, ss, ss', T, T', hok, e, hI, hS => by
      simp only [dropOkW, Bool.and_eq_true, List.all_eq_true] at hok
      obtain ⟨hrd, hok⟩ := hok
      have hR : ∀ q ∈ symReads i.1, ss.regs q = ss'.regs q := by
        intro q hq
        refine e.2 q fun hqD => ?_
        have := hrd q hqD
        simp_all
      have hc := symStep_congr e.1 i hR
      have hsrc : srcOf ((i, false) :: rest) = i :: srcOf rest := rfl
      have hkept : keptOf ((i, false) :: rest) = i :: keptOf rest := by simp [keptOf]
      rw [hsrc, tRun_cons] at hS
      rw [hsrc, hkept, tRun_cons, tRun_cons]
      cases hs : symStep i ss with
      | ok s1 g1 =>
          cases hs' : symStep i ss' with
          | ok s1' g1' =>
              rw [hs, hs'] at hc
              obtain ⟨rfl, hSame, ds, hw, hw', hds⟩ := hc
              rw [hs] at hS
              dsimp only at hS ⊢
              rw [SSt.Frm.ds_eq hw] at hS ⊢
              rw [SSt.Frm.ds_eq hw']
              have hR1 := symStep_refsLt i hI.1 hs
              obtain ⟨ds0, hw0, hr0⟩ := symStep_frm i hs
              have hd0 : ds = ds0 := List.append_cancel_right (hw.symm.trans hw0)
              obtain ⟨ds1, hw1, hr1⟩ := symStep_frm i hs'
              have hd1 : ds = ds1 := List.append_cancel_right (hw'.symm.trans hw1)
              have hdw : ds = wrOf i := List.append_cancel_right (hw.symm.trans (symStep_wr hs))
              have hI2 : (T.internSt s1 ds).2.Inv (T.internSt s1 ds).1.ents.size :=
                Tbl.internSt_inv (T := T) ds hR1.1 (fun r hr => by
                  rw [hr0 r (hd0 ▸ hr)]; exact hI.2.1 r)
              have hSub : (T.internSt s1 ds).1.Sub T' :=
                (tRun_sub _ _ _).trans (by simpa [runAfter] using hS)
              obtain ⟨s0, h0, e0, -, -⟩ :=
                Tbl.internSt_rerun (ss := s1)
                  (ss' := { s1 with wr := s1'.wr, awr := s1'.awr, nwr := s1'.nwr,
                                    nwr_eq := s1'.nwr_eq })
                  ⟨rfl, rfl, rfl, rfl, rfl⟩ ds hR1.1 hSub
              obtain ⟨ht1, hSm, hag, -⟩ :=
                Tbl.internSt_on T'
                  (ss := { s1 with wr := s1'.wr, awr := s1'.awr, nwr := s1'.nwr,
                                   nwr_eq := s1'.nwr_eq })
                  (ss' := s1') ds hSame hds
              rw [h0] at ht1 hSm hag
              dsimp only at ht1 hSm hag
              have eD : (T.internSt s1 ds).2.EqvOn (D.filter (fun q => !(wrOf i).contains q))
                  (T'.internSt s1' ds).2 := by
                refine ⟨⟨e0.2.1.trans hSm.1, e0.2.2.1.trans hSm.2.1, e0.2.2.2.1.trans hSm.2.2.1,
                  e0.2.2.2.2.trans hSm.2.2.2⟩, fun q hq => ?_⟩
                by_cases hqd : q ∈ ds
                · rw [e0.1]; exact hag q hqd
                · rw [Tbl.internSt_keep _ _ _ q hqd, Tbl.internSt_keep _ _ _ q hqd,
                    hr0 q (hd0 ▸ hqd), hr1 q (hd1 ▸ hqd)]
                  refine e.2 q fun hqD => hq ?_
                  simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
                    decide_eq_false_iff_not]
                  exact ⟨hqD, hdw ▸ hqd⟩
              have ih := tRun_dropW rest _ _ _ _ T' hok eD hI2 (by simpa [runAfter] using hS)
              have hT : (T'.internSt s1' ds).1 = T' := ht1
              rw [hT]
              exact ResW_after₂ g1 ih
          | fail => rw [hs, hs'] at hc; cases hc
          | unk => rw [hs, hs'] at hc; cases hc
      | fail => trivial
      | unk => trivial

/-- **The check of one falling block, up to guards.** `blockOkR_fall` with target guards
    `g'` among the source guards `g`. -/
theorem blockOkR_fallW {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} {b b' : AllocCheck.LcmdCFG.Block} {T1 : Tbl} {s s' : SSt}
    {g g' : List SG} (e : s.Eqv s') (hI : s.Inv T1.ents.size)
    (hg : ∀ x ∈ g, x.refsLt T1.ents.size = true) (hsub : ∀ x ∈ g', x ∈ g)
    (hE : TBnd T1.ents)
    (hL : LiveCov (L 0) (blockNeed outs L (.fall none) (T1, .ok s g, .ok s' g') B b))
    (hlast : ∀ p, B[b.stop - 1]? = some p → AllocCheck.LcmdCFG.isTermR p.1 = false) :
    blockOkR outs L 0 (.fall none) (T1, .ok s g, .ok s' g') B B' b b' = true := by
  simp only [blockNeed, AllocCheck.LcmdCFG.Term.succs, AllocCheck.LcmdCFG.Term.halts,
    Option.toList, List.flatMap_nil, List.any_nil, ↓reduceIte, Bool.false_or,
    Bool.or_false, Bool.true_and, Option.map_none, Option.getD_none, List.append_nil] at hL
  simp only [blockOkR, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [guardsT, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    refine ⟨fun x hx => hx.elim (hg x) (fun h => hg x (hsub x h)), fun x hx => ⟨?_, ?_⟩⟩
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
      simpa [normGT] using ⟨y, hsub y hy, hxy⟩
    · simp only [okInGT, Bool.and_eq_true]
      obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
      refine ⟨SG.normT_refsLt hE (hg y (hsub y hy)) x hxy,
        okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
      · simp only [List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inl ⟨x, hx, hv⟩)
      · simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inl (Or.inl ⟨x, hx, h⟩)
  · cases hb : B[b.stop - 1]? with
    | none => simp [termAgreeT]
    | some p =>
        have hp := hlast p hb
        obtain ⟨x, τ⟩ := p
        cases x <;> simp_all [termAgreeT, AllocCheck.LcmdCFG.isTermR]
  · simp only [exitAgreeT, AllocCheck.LcmdCFG.Term.succs, Option.toList, List.all_nil,
      AllocCheck.LcmdCFG.Term.halts, Bool.not_true, Bool.false_or, Bool.true_and,
      Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    refine ⟨fun r hr => ⟨congrFun e.1 r, ?_⟩, fun q hq =>
      arrAgreeT_of_eq (congrFun e.2.1 q) ?_⟩
    · simp only [okInT, Bool.and_eq_true]
      refine ⟨hI.1.1 r, okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
      · simp only [List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨r, hr, hv⟩)
      · simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inl (Or.inr ⟨r, hr, h⟩)
    · simp only [okInAT, Bool.and_eq_true]
      refine ⟨hI.1.2.1 q, okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
      · simp only [List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨q, by simpa using hq, hv⟩
      · simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨q, by simpa using hq, h⟩

/-- **Completeness for straight-line bodies, up to guards.** Two non-empty straight-line
    typed bodies whose shared runs agree up to guards (`ResW`), the source run being inside
    the fragment, pass `ownedCheckM`. -/
theorem ownedCheckM_of_resW (outs : List String) {B B' : List LinstrRM} (hne : B ≠ [])
    (hne' : B' ≠ []) (hs : ∀ p ∈ B, straightR p.1 = true) (hs' : ∀ p ∈ B', straightR p.1 = true)
    (hres : ResW (tRun B SSt.start Tbl.empty).1 (tRun B SSt.start Tbl.empty).2
      (tRun B' SSt.start (tRun B SSt.start Tbl.empty).1))
    (hunk : (tRun B SSt.start Tbl.empty).2 ≠ .unk) : ownedCheckM outs B B' = true := by
  have hG := cfgOf_straight (wl := B.map Prod.fst) (by simpa using hne)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs p hp)
  have hG' := cfgOf_straight (wl := B'.map Prod.fst) (by simpa using hne')
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs' p hp)
  unfold ownedCheckM
  rw [hG, hG']
  dsimp only
  have hsz : ∀ n, (straightCFG n).blocks.size = 1 := fun _ => rfl
  have hterm : ∀ n, ((straightCFG n).blk 0).term = .fall none := fun _ => rfl
  generalize hp : tRun B SSt.start Tbl.empty = p at hres hunk
  obtain ⟨T1, o⟩ := p
  have hR : (runsOf B B' (straightCFG (B.map Prod.fst).length)
      (straightCFG (B'.map Prod.fst).length))[0]? =
      some (blockRuns B B' ((straightCFG (B.map Prod.fst).length).blk 0)
        ((straightCFG (B'.map Prod.fst).length).blk 0) (.fall none)) := by
    simp [runsOf, hsz, hterm]
  have hBR : blockRuns B B' ((straightCFG (B.map Prod.fst).length).blk 0)
      ((straightCFG (B'.map Prod.fst).length).blk 0) (.fall none) =
      ((tRun B' SSt.start T1).1, o, (tRun B' SSt.start T1).2) := by
    simp only [blockRuns, bodyAt_straight, hp]
  rw [hBR] at hR
  simp only [ownedCheckWithR, hsz, hterm, hR, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Nat.lt_one_iff, forall_eq, beq_self_eq_true, true_and]
  refine ⟨by simp [hne, hne'], ?_⟩
  cases o with
  | unk => exact absurd rfl hunk
  | fail => simp [blockOkR]
  | ok s g =>
      generalize hq : tRun B' SSt.start T1 = q at hres hR
      obtain ⟨Q, o'⟩ := q
      cases o' with
      | ok s' g' =>
          obtain ⟨hQ, e, hsub⟩ := hres
          simp only at hQ
          simp only [hQ] at hR ⊢
          have hinv := tRun_inv B SSt.start Tbl.empty SSt.inv_start hp
          have hE : TBnd T1.ents := by
            have := tRun_valid B SSt.start Tbl.empty tValid_empty
            rw [hp] at this
            exact this.2
          refine blockOkR_fallW e hinv.1 hinv.2 hsub hE ?_ ?_
          · refine liveIter_single (hsz _) _ hR (fun L => ?_)
            simp only [blockNeed, hterm, AllocCheck.LcmdCFG.Term.succs,
              AllocCheck.LcmdCFG.Term.halts, Option.toList, List.flatMap_nil, List.any_nil]
          · intro p hp'
            have hmem : p ∈ B := List.mem_of_getElem? hp'
            have := hs p hmem
            simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
            exact this.1.1
      | fail => exact hres.elim
      | unk => exact hres.elim

/-- **Completeness for dropping dead flag-quiet writes.** A straight-line marked body whose
    marks are dead flag-quiet writes (`dropOkW`), whose symbolic run lies inside the fragment
    and which keeps an instruction, passes `ownedCheckM` against its unmarked instructions. -/
theorem dropOkW_ownedCheckM_complete (outs : List String) (B : List (LinstrRM × Bool))
    (hne : keptOf B ≠ []) (hs : ∀ p ∈ B, straightR p.1.1 = true) (hok : dropOkW [] B = true)
    (hfrag : symRun (srcOf B) SSt.start ≠ .unk) :
    ownedCheckM outs (srcOf B) (keptOf B) = true := by
  have hsrc : srcOf B ≠ [] := by
    intro h
    apply hne
    simp only [srcOf, List.map_eq_nil_iff] at h
    simp [keptOf, h]
  refine ownedCheckM_of_resW outs hsrc hne ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact hs p hp
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact hs p (List.mem_filter.mp hp).1
  · exact tRun_dropW B [] SSt.start SSt.start Tbl.empty _ hok
      ⟨SSt.Same.refl _, fun _ _ => rfl⟩ SSt.inv_start (Tbl.Sub.refl _)
  · rwa [ne_eq, tRun_unk_iff]

/-! ### Immediate moves as dead flag-quiet writes -/

theorem immMov?_flagQuiet {i : LinstrRM} {r : String} (h : immMov? i = some r) :
    flagQuiet i = true := by
  obtain ⟨opn, n, tag, rfl, -, -⟩ := immMov?_spec h
  cases tag <;> simp [flagQuiet, cmpArgs?, carryArgs?, aluFlagOp?, arrQuiet, storeStruct?]

theorem wrOf_immMov {i : LinstrRM} {r : String} (h : immMov? i = some r) : wrOf i = [r] := by
  obtain ⟨w, n, hs⟩ := symStep_immMov h
  simp [wrOf, hs, SSt.setR, SSt.start]

/-- Dead immediate moves (`dropOk`) are dead flag-quiet writes (`dropOkW`). -/
theorem dropOk_dropOkW : ∀ (B : List (LinstrRM × Bool)) (D : List String),
    dropOk D B = true → dropOkW D B = true
  | [], _, h => h
  | (i, true) :: rest, D, h => by
      simp only [dropOk] at h
      cases hm : immMov? i with
      | none => rw [hm] at h; cases h
      | some r =>
          rw [hm] at h
          simp only [dropOkW, immMov?_flagQuiet hm, wrOf_immMov hm, List.singleton_append,
            Bool.true_and]
          exact dropOk_dropOkW rest _ h
  | (i, false) :: rest, D, h => by
      simp only [dropOk, Bool.and_eq_true] at h
      simp only [dropOkW, Bool.and_eq_true]
      exact ⟨h.1, dropOk_dropOkW rest _ h.2⟩

/-! ## 9. The dead-write elimination before a widening multiply -/

/-- The register a candidate pure register write sets: a `MUL`, `IMUL` or `MOV` (at any
    width tag), a `MOVQ` or a `LOAD:64`, with one register destination. -/
def pureWrDst? (x : LinstrR) : Option String :=
  match x with
  | .Lopn [.reg d] opn _ =>
      if stripWidthTag opn = "MUL" ∨ stripWidthTag opn = "IMUL" ∨ stripWidthTag opn = "MOV" ∨
          opn = "MOVQ" ∨ opn = "LOAD:64" then some d
      else none
  | _ => none

/-- `x` is a widening multiply `MULX [lo, hi] [b]` (or `MULXMEM`, at any width tag) with `d`
    among its destinations. -/
def mulxWrites (d : String) (x : LinstrR) : Bool :=
  match x with
  | .Lopn [.reg lo, .reg hi] opn [_] =>
      (stripWidthTag opn == "MULX" || stripWidthTag opn == "MULXMEM") && (d == lo || d == hi)
  | _ => false

/-- `x` names `d` among its register destinations. -/
def namesDstB (d : String) (x : LinstrR) : Bool :=
  match x with
  | .Lopn ds _ _ => ds.any (· == .reg d)
  | _ => false

/-- The next access of `d` among the unmarked instructions of `M` is a write by a widening
    multiply: no unmarked instruction before it is a control instruction or a label, reads
    `d` (`symReads`) or names `d` as a destination. -/
def killedByMulx (d : String) : List (Linstr × Bool) → Bool
  | [] => false
  | (_, true) :: rest => killedByMulx d rest
  | (j, false) :: rest =>
      straightR j.li_i && !(symReads j.li_i).contains d &&
        (mulxWrites d j.li_i || (!namesDstB d j.li_i && killedByMulx d rest))

/-- The marks of the dead-write elimination, computed from the end of the body: an
    instruction is marked when it is a straight-line candidate pure register write
    (`pureWrDst?`) whose register is next accessed, among the unmarked instructions after
    it, by a write of a widening multiply (`killedByMulx`). -/
def deadWriteMarks : Lcmd → List (Linstr × Bool)
  | [] => []
  | i :: is =>
      let M := deadWriteMarks is
      (i, match pureWrDst? i.li_i with
          | some d => straightR i.li_i && killedByMulx d M
          | none => false) :: M

/-- **The dead-write elimination.** The body without the marked instructions of
    `deadWriteMarks`. -/
def dropDeadWriteBody (body : Lcmd) : Lcmd := keptL (deadWriteMarks body)

theorem deadWriteMarks_fst : ∀ body : Lcmd, (deadWriteMarks body).map Prod.fst = body
  | [] => rfl
  | i :: is => by simp [deadWriteMarks, deadWriteMarks_fst is]

theorem keptL_sublist : ∀ M : List (Linstr × Bool), (keptL M).Sublist (M.map Prod.fst)
  | [] => List.Sublist.slnil
  | (i, b) :: M => by
      cases b
      · simpa [keptL] using (keptL_sublist M).cons_cons i
      · simpa [keptL] using (keptL_sublist M).cons i

/-- The elimination removes instructions only. -/
theorem dropDeadWriteBody_sublist (body : Lcmd) : (dropDeadWriteBody body).Sublist body := by
  have h := keptL_sublist (deadWriteMarks body)
  rwa [deadWriteMarks_fst] at h

/-- **Completeness for a marked body, dead flag-quiet writes.** -/
theorem marksW_ownedCheckM_complete (outs : List String) (tg : LinstrR → MemTag)
    (M : List (Linstr × Bool)) (hne : keptL M ≠ [])
    (hs : ∀ i ∈ M.map Prod.fst, straightR i.li_i = true)
    (hok : dropOkW [] (typeMarks tg M) = true)
    (hfrag : symRun (typeBody tg (M.map Prod.fst)) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody tg (M.map Prod.fst)) (typeBody tg (keptL M)) = true := by
  rw [← srcOf_typeMarks, ← keptOf_typeMarks]
  refine dropOkW_ownedCheckM_complete outs _ ?_ ?_ hok (by rwa [srcOf_typeMarks])
  · rw [keptOf_typeMarks]
    simpa [typeBody] using hne
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hq
    exact hs m.1 (List.mem_map_of_mem hm)

/-- **Completeness of the value checker for the dead-write elimination.** For a
    straight-line body whose eliminated instructions are dead flag-quiet writes at the level
    of the symbolic step (`dropOkW`), whose symbolic run lies inside the fragment and whose
    elimination keeps an instruction, `ownedCheckM` accepts the body against
    `dropDeadWriteBody`, for every observed list `outs` and every typing. -/
theorem dropDeadWrite_ownedCheckM_complete (outs : List String) (tg : LinstrR → MemTag)
    (body : Lcmd) (hne : dropDeadWriteBody body ≠ [])
    (hs : ∀ i ∈ body, straightR i.li_i = true)
    (hok : dropOkW [] (typeMarks tg (deadWriteMarks body)) = true)
    (hfrag : symRun (typeBody tg body) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody tg body) (typeBody tg (dropDeadWriteBody body)) = true := by
  have h := marksW_ownedCheckM_complete outs tg (deadWriteMarks body) hne
    (by rwa [deadWriteMarks_fst]) hok (by rwa [deadWriteMarks_fst])
  rwa [deadWriteMarks_fst] at h

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
