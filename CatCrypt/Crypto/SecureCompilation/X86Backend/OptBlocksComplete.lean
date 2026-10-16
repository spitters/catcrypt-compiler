/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg

@[expose] public section

set_option autoImplicit false

/-!
# The check of the basic-block optimiser, with register copies, and its completeness

`BlocksCfg.optBlocksOKB A tag body` is a decision under which the basic-block optimiser
`LprogOptPipeline.optimizeBasicBlocks` preserves halting runs of the checked flag machine
(`BlocksCfg.optBlocksOKB_sound`). It asks that every instruction pass `CfgLift.keepOKB` and
that every straight segment of the partition `splitStraightRuns` pass the segment check
`BlocksCfg.optSegOKB`, which has three disjuncts:

1. a segment of flag compares outside the modelled bodies;
2. a segment of the fragment with flags `LsemBridge.fragFB` whose scheduled and
   copy-propagated form is in the fragment and has no indexed access;
3. `optSegRegOKB`: a segment whose instructions are flag compares, register copies
   (`JasminLsemMemFlagGuard.movRegArgs?`: `MOV`, `MOVQ`, `LOAD:64`, `STORE:64` between
   register-shaped names) or instructions of the fragment with flags (`relStepB`), with
   register destinations, on which copy propagation passes the checks `CopyPropCfg.cpRegOKB`
   and `CopyPropCfg.deadOKB` of its register-fact proof.

The first two disjuncts were the whole check before; they refuse every segment with a
one-source register copy, such as the body `MOV:64 a, b; ret`, since a register copy is
neither a flag compare nor in the fragment with flags. The third disjunct accepts it. Its
soundness is the proof of copy propagation over the extended straight fold
(`CopyPropCfg.copyPropSim_of_deadOKB`) together with the invariant of the bridge
`BlocksCfg.RelInv A`, which every step of a flag compare, a register copy, or an in-bounds
instruction of the fragment with flags preserves (`relInv_fstepF_of_relStepB`). It holds for
a tagging that depends on the destinations and the mnemonic only (`CopyPropCfg.TagShape`).

The completeness theorem `optBlocksOKB_optimizeBasicBlocks` states that the check holds on
every body whose instructions pass `keepOKB` and whose straight instructions pass `relStepB`,
have register destinations and pass the operand-form check `deadFormB`, a per-instruction
check that, unlike `deadOKB`, is kept by the source rewriting of copy propagation
(`deadFormB_rewrite`).

## Main definitions

* `relStepB A`: a flag compare, a register copy, or an instruction of the fragment with flags.
* `optSegRegOKB A tag`: the third disjunct of the segment check.
* `BlocksCfg.optSegOKB`, `BlocksCfg.optBlocksOKB`: the segment check and the check on a body.
* `deadFormB`: the operand form of an instruction under which `deadOKB` holds before and
  after the rewriting of its register sources to physical registers.

## Main results

* `relInv_fstepF_movReg`, `relInv_fstepF_of_relStepB`, `relInv_runStraightF`: the invariant
  of the bridge along a run of a segment of `relStepB` instructions in bounds.
* `optRunBody_segOK_of_reg`: the five stages on a segment that passes `optSegRegOKB`.
* `BlocksCfg.optSegOKB_sound`, `BlocksCfg.optBlocksOKB_sound`: soundness of the check.
* `optSegRegOKB_regCopy`, `optBlocksOKB_regCopyRetBody`: the check accepts the register
  copy `MOV:64 a, b` and the body `MOV:64 a, b; ret`.
* `mem_propagateAux`, `deadFormB_rewrite`, `deadOKB_of_deadFormB`: the instructions of the
  propagated body are instructions of the body with register sources rewritten to physical
  registers, and they keep the operand form.
* `optBlocksOKB_optimizeBasicBlocks`: completeness of the check on bodies of that form;
  `optBlocksOKB_optimizeLprogBasicBlocks`: on every function body of a program, the input of
  `optimizeBasicBlocks` in `LprogOptPipeline.ownedLprog`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (elimReloads isMovMnem)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg

/-! ## 1. Steps that preserve the invariant of the bridge -/

/-- The instructions whose step preserves the invariant of the bridge `RelInv A` when it is
    in bounds: a flag compare, a register copy, or an instruction of the fragment with
    flags. -/
def relStepB (A : String → Option Nat) (i : LinstrRM) : Bool :=
  (cmpArgs? i).isSome || (movRegArgs? i).isSome || fragFB A i

/-- An instruction the register-copy recognizer accepts is an `Lopn`. -/
theorem isLopn_of_movRegArgs {i : LinstrRM} (h : (movRegArgs? i).isSome = true) :
    IsLopn i := by
  unfold movRegArgs? at h
  split at h
  · next dst opn src heq => exact ⟨_, _, _, heq⟩
  · simp at h

theorem isLopn_of_relStepB {A : String → Option Nat} {i : LinstrRM}
    (h : relStepB A i = true) : IsLopn i := by
  simp only [relStepB, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact isLopn_of_cmpArgs h
  · exact isLopn_of_movRegArgs h
  · exact (fragFB_plain h).1

/-- **A register copy preserves the invariant of the bridge**: under `LsemRelF` the source
    is a `64`-bit register, so the copy writes a `64`-bit value. -/
theorem relInv_fstepF_movReg {A : String → Option Nat} {i : LinstrRM}
    (hc : cmpArgs? i = none) {dst src : String} (hm : movRegArgs? i = some (dst, src))
    {s t : LstateM} {zf zt : Bool} (hI : RelInv A s) (h : fstepF i s zf = some (t, zt)) :
    RelInv A t := by
  obtain ⟨l, hr⟩ := hI
  unfold fstepF at h
  rw [hc, hm] at h
  simp only [readReg, hr.regs src, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  refine ⟨{ l with lvm := fun r => if r = dst then l.lvm src else l.lvm r, lpc := l.lpc + 1 },
    ⟨⟨fun r => ?_, ?_, fun B n hB => ?_⟩, hr.cf, hr.of⟩⟩
  · simp only [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc]
    split <;> simp [hr.regs]
  · simp only [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hr.pc]
  · exact hr.arrs B n hB

/-- **An in-bounds step of a `relStepB` instruction preserves the invariant of the
    bridge.** -/
theorem relInv_fstepF_of_relStepB {A : String → Option Nat} {i : LinstrRM}
    (h : relStepB A i = true) {s t : LstateM} {zf zt : Bool} (hI : RelInv A s)
    (hb : baseIdxOk i s = true) (hst : fstepF i s zf = some (t, zt)) : RelInv A t := by
  cases hc : cmpArgs? i with
  | some ab => exact relInv_fstepF_cmp (by simp [hc]) hI hst
  | none =>
      cases hm : movRegArgs? i with
      | some p => exact relInv_fstepF_movReg hc hm hI hst
      | none =>
          have hf : fragFB A i = true := by simpa [relStepB, hc, hm] using h
          obtain ⟨l, hr⟩ := hI
          have hib := inBoundsB_of_baseIdxOk hf hr.toLsemRel hb
          obtain ⟨s1, l1, hs1, -, hr1, -, -⟩ := lsemStepFlag_stepMemF_rel hf hr hib
          have he : fstepF i s zf = some (s1, zf) := by
            unfold fstepF
            rw [hc, hm, hs1]
            rfl
          rw [he, Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, -⟩ := hst
          exact ⟨l1, hr1⟩

/-- **The invariant of the bridge along an in-bounds run** of a segment of `relStepB`
    instructions. -/
theorem relInv_runStraightF {A : String → Option Nat} :
    ∀ (seg : List LinstrRM), (∀ i ∈ seg, relStepB A i = true) →
      ∀ (s : LstateM) (zf : Bool) (t : LstateM) (zt : Bool), RelInv A s → SegIdxOk seg s zf →
        runStraightF seg s zf = some (t, zt) → RelInv A t
  | [], _, s, zf, t, zt, hI, _, h => by
      simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact hI
  | i :: is, hs, s, zf, t, zt, hI, hok, h => by
      rw [runStraightF_cons] at h
      cases h1 : fstepF i s zf with
      | none => rw [h1] at h; cases h
      | some bz =>
          obtain ⟨b, z⟩ := bz
          rw [h1, Option.bind_some] at h
          exact relInv_runStraightF is (fun j hj => hs j (List.mem_cons_of_mem _ hj)) b z t zt
            (relInv_fstepF_of_relStepB (hs i List.mem_cons_self) hI hok.1 h1) (hok.2 b z h1) h

/-! ## 2. The segment check with register copies -/

/-- The first three stages of `optRunBody`: reload elimination, spill-pair elimination and
    scheduling. -/
def threeStages (seg : List Linstr) : List Linstr :=
  scheduleBody (reloadElimBody (elimReloads seg))

/-- **The third disjunct of the segment check**: every instruction passes `relStepB` and has
    register destinations, the segment after the first three stages passes `cpRegOKB`, and
    its forward-propagated form passes `deadOKB`. -/
def optSegRegOKB (A : String → Option Nat) (tag : LinstrR → MemTag) (seg : List Linstr) :
    Bool :=
  seg.all (fun i => relStepB A (i.li_i, tag i.li_i) && dstsRegB i.li_i)
    && (threeStages seg).all cpRegOKB
    && (propagateAux [] (threeStages seg)).all deadOKB

/-- **The five stages on a segment that passes `optSegRegOKB`**, under the invariant of the
    bridge and the in-bounds premise of the checked machine, for a tagging that depends on
    the destinations and the mnemonic only. -/
theorem optRunBody_segOK_of_reg {A : String → Option Nat} {tag : LinstrR → MemTag}
    (hT : TagShape tag) {seg : List Linstr} (h : optSegRegOKB A tag seg = true) :
    SegOK true (RelInv A) tag optRunBody seg := by
  simp only [optSegRegOKB, threeStages, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hl : ∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i) := fun i hi => isLopn_of_relStepB (h1 i hi).1
  have hcp := copyPropSim_of_deadOKB tag hT _ h2 h3
  refine ⟨optRunBody_length_le seg, hl, optRunBody_isLopn tag seg hl,
    BlockSim.of_same (fun s t zf zt hI hok hr => ?_)⟩
  obtain ⟨t₂, ht₂, hE⟩ := optRunBody_runStraightF tag seg (fun i hi => (h1 i hi).2) hcp s zf t
    zt hr
  refine ⟨t₂, ht₂, hE, relInv_runStraightF _ (fun i hi => ?_) s zf t zt hI (hok rfl) hr⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  exact (h1 j hj).1

/-- The check of the optimiser on one straight segment: a segment of flag-`CMP`
    instructions outside the modelled bodies; a segment of the fragment with flags whose
    scheduled and copy-propagated form is in the fragment and has no indexed access; or a
    segment that passes `optSegRegOKB`. -/
def optSegOKB (A : String → Option Nat) (tag : LinstrR → MemTag) (seg : List Linstr) : Bool :=
  (!bodyAllModeled seg && seg.all fun i => (cmpArgs? (i.li_i, tag i.li_i)).isSome)
    || (seg.all (fun i => fragFB A (i.li_i, tag i.li_i))
        && (copyPropagateBody (scheduleBody seg)).all
            (fun i => fragFB A (i.li_i, tag i.li_i) && !LprogScheduler.hasArrIdx i.li_i))
    || optSegRegOKB A tag seg

/-- **The check of the optimiser on a body**: every instruction passes `keepOKB` and every
    straight segment of the partition passes `optSegOKB`. -/
def optBlocksOKB (A : String → Option Nat) (tag : LinstrR → MemTag) (body : List Linstr) :
    Bool :=
  body.all (fun i => keepOKB (i.li_i, tag i.li_i))
    && (splitStraightRuns body).all
        (fun seg => !bodyIsStraightLine seg || optSegOKB A tag seg)

theorem optSegOKB_sound {A : String → Option Nat} {tag : LinstrR → MemTag}
    (hT : TagShape tag) {seg : List Linstr} (h : optSegOKB A tag seg = true) :
    SegOK true (RelInv A) tag optRunBody seg := by
  unfold optSegOKB at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h1 | h2) | h3
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h1
    exact optRunBody_segOK_of_cmp tag seg h1.1 h1.2
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h2
    exact optRunBody_segOK_of_idxFree tag seg h2.1 (fun i hi => (h2.2 i hi).1)
      (fun i hi => (h2.2 i hi).2)
  · exact optRunBody_segOK_of_reg hT h3

/-- **Soundness of the check: the basic-block optimiser on a checked body.** For a tagging
    that depends on the destinations and the mnemonic only and a body that passes
    `optBlocksOKB`, every halting run of the checked machine on the tagged body from program
    counter `0` and a state of `RelInv A` is matched by a halting run of the tagged optimised
    body from the same state with at most the same fuel, to a state with the same function
    name and zero flag and a base equal up to the program counter. -/
theorem optBlocksOKB_sound {A : String → Option Nat} {tag : LinstrR → MemTag}
    (hT : TagShape tag) {body : List Linstr} (h : optBlocksOKB A tag body = true)
    (fn : String) :
    WholeBodySim true (RelInv A) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((optimizeBasicBlocks body).map fun i => (i.li_i, tag i.li_i)) := by
  simp only [optBlocksOKB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine optimizeBasicBlocks_lsemFuelMemF tag body relInv_setLpc h.1
    (fun seg hs hsl => optSegOKB_sound hT ?_) fn
  rcases h.2 seg hs with h' | h'
  · rw [hsl] at h'
    cases h'
  · exact h'

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames cellBase)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (isMovMnem)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-! ## 3. The register copy is accepted -/

/-- The register copy `MOV:64 a, b`. -/
def regCopy : Linstr := ⟨0, .Lopn [.reg "a"] (withWidthTag 64 "MOV") [.reg "b"]⟩

/-- The body `MOV:64 a, b; ret`. -/
def regCopyRetBody : List Linstr := [regCopy, ⟨0, .Lret⟩]

/-- The untyped tagging: every instruction is a register instruction. -/
def regTag : LinstrR → MemTag := fun _ => .reg none

theorem tagShape_regTag : TagShape regTag := fun _ _ _ _ => rfl

/-! ## 4. The operand form kept by copy propagation -/

/-- Every physical register among the names an operand in source position reads, as
    `CopyPropCfg.readNames` lists them, is one of its `operandReads`. -/
def srcReadOKB (o : LOperand) : Bool :=
  (srcNames o ++ (cellBase o).toList).all fun r => !isPhysGP r || (operandReads o).contains r

/-- The registers `instrUses` lists for an operand in destination position. -/
def dstReads (o : LOperand) : List String :=
  match o with
  | .reg n => if isPhysGP n then [] else nameReads n
  | o => operandReads o

/-- Every physical cell base of an operand in destination position is one of its
    `dstReads`. -/
def dstReadOKB (o : LOperand) : Bool :=
  (cellBase o).toList.all fun r => !isPhysGP r || (dstReads o).contains r

/-- **The operand form of an instruction for dead-move elimination**: the instruction passes
    `cpRegOKB`; if it is an `Lopn` with a recognised mnemonic, its sources pass `srcReadOKB`,
    its destinations pass `dstReadOKB`, and if it has a killing definition it has one
    destination and is neither an indexed store nor the flag compare. -/
def deadFormB (i : Linstr) : Bool :=
  cpRegOKB i &&
    (match i.li_i with
     | .Lopn dsts opn srcs =>
         !isRecognizedOpn opn ||
           (srcs.all srcReadOKB && dsts.all dstReadOKB
             && ((fullDefsOf dsts opn).isEmpty
                  || (dsts.length == 1 && opn != "STOREIDX" && opn != withWidthTag 64 "CMP")))
     | _ => true)

theorem cpRegOKB_of_deadFormB {i : Linstr} (h : deadFormB i = true) : cpRegOKB i = true := by
  simp only [deadFormB, Bool.and_eq_true] at h
  exact h.1

/-- **The operand form gives the check of dead-move elimination.** -/
theorem deadOKB_of_deadFormB {i : Linstr} (h : deadFormB i = true) : deadOKB i = true := by
  unfold deadFormB at h
  unfold deadOKB
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨-, h2⟩ := h
  split
  · next dsts opn srcs hi =>
      rw [hi] at h2
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h2 ⊢
      rcases h2 with h2 | ⟨⟨hs, hd⟩, hk⟩
      · exact Or.inl h2
      · refine Or.inr ⟨?_, hk⟩
        simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          List.contains_iff_mem, srcReadOKB, dstReadOKB] at hs hd ⊢
        intro r hr
        rw [hi] at hr
        by_cases hp : isPhysGP r = true
        · right
          simp only [readNames, List.mem_append, List.mem_flatMap, List.mem_filterMap] at hr
          simp only [instrUses, List.mem_append, List.mem_flatMap]
          rcases hr with ⟨o, ho, hro⟩ | ⟨o, ho | ho, hco⟩
          · have := hs o ho r (List.mem_append_left _ hro)
            rcases this with hn | hm
            · exact absurd hp (by simp [hn])
            · exact Or.inl (Or.inl (Or.inl ⟨o, ho, hm⟩))
          · have := hd o ho r (by simp [hco])
            rcases this with hn | hm
            · exact absurd hp (by simp [hn])
            · refine Or.inl (Or.inl (Or.inr ⟨o, ho, ?_⟩))
              cases o <;> simpa [dstReads] using hm
          · have := hs o ho r (List.mem_append_right _ (by simp [hco]))
            rcases this with hn | hm
            · exact absurd hp (by simp [hn])
            · exact Or.inl (Or.inl (Or.inl ⟨o, ho, hm⟩))
        · left
          simpa using hp
  · rfl

/-- A physical register is no cell name. -/
theorem cellParts?_of_isPhysGP {r : String} (h : isPhysGP r = true) :
    JasminLsemAddrMem.cellParts? r = none := by
  simp only [isPhysGP, physGPs, List.contains_iff_mem, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide +kernel

/-- A physical register in source position has the operand form. -/
theorem srcReadOKB_phys {r : String} (h : isPhysGP r = true) : srcReadOKB (.reg r) = true := by
  simp [srcReadOKB, srcNames, cellBase, cellParts?_of_isPhysGP h, operandReads, nameReads, h]

/-- Register facts: every fact records a physical source register. -/
def FactsReg (facts : List MoveFact) : Prop :=
  ∀ f ∈ facts, ∃ r, f.2.1 = LOperand.reg r ∧ isPhysGP r = true

/-- Under register facts a rewritten operand is the operand or a physical register. -/
theorem rewriteOperand_cases {facts : List MoveFact} (hF : FactsReg facts) (w : Nat)
    (a : Bool) (ds : Option String) (o : LOperand) :
    rewriteOperand facts w a ds o = o
      ∨ ∃ r, rewriteOperand facts w a ds o = .reg r ∧ isPhysGP r = true := by
  cases o with
  | reg u =>
      simp only [rewriteOperand]
      split
      · cases hl : lookupFact facts u with
        | none => exact Or.inl rfl
        | some p =>
            obtain ⟨v, fw⟩ := p
            obtain ⟨r, hv, hr⟩ := hF _ (lookupFact_mem hl)
            have hv' : v = LOperand.reg r := hv
            subst hv'
            simp only
            split
            · exact Or.inr ⟨r, rfl, hr⟩
            · exact Or.inl rfl
      · exact Or.inl rfl
  | _ => exact Or.inl rfl

/-- **The operand form is kept by the source rewriting of copy propagation**, under register
    facts. -/
theorem deadFormB_rewrite {facts : List MoveFact} (hF : FactsReg facts) {i : Linstr}
    {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn dsts opn srcs) (h : deadFormB i = true) (w : Nat) (a : Bool)
    (ds : Option String) :
    deadFormB { i with li_i := .Lopn dsts opn (srcs.map (rewriteOperand facts w a ds)) }
      = true := by
  have hcases := rewriteOperand_cases hF w a ds
  unfold deadFormB cpRegOKB at h ⊢
  rw [hi] at h
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hd, hm⟩, hr⟩ := h
  refine ⟨⟨by simpa [dstsRegB] using hd, ?_⟩, ?_⟩
  · rcases srcs with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · exact hm
    · simp only [List.map_cons, List.map_nil]
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hm ⊢
      rcases hm with hm | ⟨hm, hx⟩
      · exact Or.inl hm
      · refine Or.inr ⟨hm, ?_⟩
        rcases hcases x with e | ⟨r, e, -⟩ <;> rw [e]
        · exact hx
        · rfl
    · exact hm
  · simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, List.all_eq_true] at hr ⊢
    rcases hr with hr | ⟨⟨hs, hd'⟩, hk⟩
    · exact Or.inl hr
    · refine Or.inr ⟨⟨fun o ho => ?_, hd'⟩, hk⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
      rcases hcases x with e | ⟨r, e, hp⟩ <;> rw [e]
      · exact hs x hx
      · exact srcReadOKB_phys hp

theorem factsReg_foldl_killFacts :
    ∀ (rs : List String) (facts : List MoveFact), FactsReg facts →
      FactsReg (rs.foldl killFacts facts)
  | [], _, h => h
  | _ :: rest, _, h => factsReg_foldl_killFacts rest _ (fun f hf =>
      h f (List.mem_filter.1 hf).1)

/-- A candidate move among the rewritten instructions of a body that passes `cpRegOKB`
    records a physical source register, under register facts. -/
theorem moveShape_rewrite_reg {facts : List MoveFact} (hF : FactsReg facts) {i : Linstr}
    {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn dsts opn srcs) (hc : cpRegOKB i = true) (w : Nat) (a : Bool)
    (ds : Option String) {d : String} {src : LOperand} {ww : Nat}
    (h : moveShape { i with li_i := .Lopn dsts opn (srcs.map (rewriteOperand facts w a ds)) }
      = some (d, src, ww)) :
    ∃ r, src = LOperand.reg r ∧ isPhysGP r = true := by
  obtain ⟨opn', hsh, -, hfs, hstrip⟩ := moveShape_inv h
  simp only [LinstrR.Lopn.injEq] at hsh
  obtain ⟨-, rfl, hmap⟩ := hsh
  rcases srcs with _ | ⟨x, _ | ⟨y, r⟩⟩
  · simp at hmap
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
    rcases rewriteOperand_cases hF w a ds x with e | ⟨r, e, hp⟩
    · rw [e] at hmap
      subst hmap
      simp only [cpRegOKB, hi, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne, ne_eq, Bool.or_eq_false_iff] at hc
      have hx : notImmB x = true := by
        rcases hc.2 with hno | hyes
        · rcases hstrip with e | e
          · exact absurd e hno.1
          · exact absurd e hno.2
        · exact hyes.2
      cases x with
      | reg u => exact ⟨u, rfl, by simpa [isFactSrc] using hfs⟩
      | imm k => simp [notImmB] at hx
      | arr b k => simp [isFactSrc] at hfs
      | arrIdx b x k => simp [isFactSrc] at hfs
    · exact ⟨r, by rw [← hmap, e], hp⟩
  · simp at hmap

/-- **The instructions of the forward-propagated body.** For a body that passes `cpRegOKB`
    and register facts, every instruction of `propagateAux facts body` is an instruction of
    the body, or an instruction of the body with its sources rewritten under register
    facts. -/
theorem mem_propagateAux : ∀ (body : Lcmd) (facts : List MoveFact), FactsReg facts →
    (∀ i ∈ body, cpRegOKB i = true) → ∀ j ∈ propagateAux facts body, ∃ i ∈ body,
      j = i ∨ ∃ (dsts : List LOperand) (opn : String) (srcs : List LOperand)
        (fs : List MoveFact) (w : Nat) (a : Bool) (ds : Option String), FactsReg fs ∧
        i.li_i = .Lopn dsts opn srcs ∧
        j = { i with li_i := .Lopn dsts opn (srcs.map (rewriteOperand fs w a ds)) }
  | [], _, _, _, j, hj => by simp [propagateAux] at hj
  | i :: rest, facts, hF, hb, j, hj => by
      have hrest : ∀ k ∈ rest, cpRegOKB k = true := fun k hk => hb k (List.mem_cons_of_mem _ hk)
      have hnil : FactsReg ([] : List MoveFact) := fun f hf => absurd hf (by simp)
      have lift : ∀ (fs : List MoveFact), FactsReg fs → j ∈ propagateAux fs rest →
          ∃ i' ∈ i :: rest, j = i' ∨ ∃ (dsts : List LOperand) (opn : String)
            (srcs : List LOperand) (fs : List MoveFact) (w : Nat) (a : Bool)
            (ds : Option String), FactsReg fs ∧ i'.li_i = .Lopn dsts opn srcs ∧
            j = { i' with li_i := .Lopn dsts opn (srcs.map (rewriteOperand fs w a ds)) } := by
        intro fs hfs hm
        obtain ⟨i', hi', h'⟩ := mem_propagateAux rest fs hfs hrest j hm
        exact ⟨i', List.mem_cons_of_mem _ hi', h'⟩
      rw [propagateAux] at hj
      split at hj
      · rename_i dsts opn srcs hi
        split at hj
        · rcases List.mem_cons.1 hj with rfl | hj
          · exact ⟨i, List.mem_cons_self, Or.inr ⟨dsts, opn, srcs, facts, _, _, _, hF, hi, rfl⟩⟩
          · refine lift _ ?_ hj
            have h1 := factsReg_foldl_killFacts (regDefsOf dsts) facts hF
            split
            · rename_i d src ww hms
              split
              · exact h1
              · intro f hf
                rcases List.mem_cons.1 hf with rfl | hf
                · exact moveShape_rewrite_reg hF hi (hb i List.mem_cons_self) _ _ _ hms
                · exact h1 f hf
            · exact h1
        · rcases List.mem_cons.1 hj with rfl | hj
          · exact ⟨_, List.mem_cons_self, Or.inl rfl⟩
          · exact lift [] hnil hj
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact ⟨_, List.mem_cons_self, Or.inl rfl⟩
        · exact lift [] hnil hj

/-! ## 5. Completeness -/

/-- An instruction of a straight segment is no control instruction. -/
theorem isCtlInstr_of_straight {seg : List Linstr} (h : bodyIsStraightLine seg = true)
    {i : Linstr} (hi : i ∈ seg) : isCtlInstr i = false := by
  simp only [bodyIsStraightLine, List.all_eq_true] at h
  have h1 := h i hi
  unfold isCtlInstr
  split <;> simp_all

/-- **The third disjunct of the segment check holds on a segment of the operand form**:
    every instruction passes `relStepB`, has register destinations and passes `deadFormB`. -/
theorem optSegRegOKB_of_forms {A : String → Option Nat} {tag : LinstrR → MemTag}
    {seg : List Linstr}
    (h : ∀ i ∈ seg, relStepB A (i.li_i, tag i.li_i) = true ∧ dstsRegB i.li_i = true
      ∧ deadFormB i = true) :
    optSegRegOKB A tag seg = true := by
  have h3 : ∀ j ∈ threeStages seg, deadFormB j = true := fun j hj =>
    (h j (mem_of_mem_three_stages hj)).2.2
  have hc : ∀ j ∈ threeStages seg, cpRegOKB j = true := fun j hj => cpRegOKB_of_deadFormB (h3 j hj)
  simp only [optSegRegOKB, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun i hi => ⟨(h i hi).1, (h i hi).2.1⟩, hc⟩, fun j hj => ?_⟩
  obtain ⟨i, hi, e⟩ := mem_propagateAux _ [] (fun f hf => absurd hf (by simp)) hc j hj
  refine deadOKB_of_deadFormB ?_
  rcases e with rfl | ⟨dsts, opn, srcs, fs, w, a, ds, hF, hii, rfl⟩
  · exact h3 j hi
  · exact deadFormB_rewrite hF hii (h3 i hi) w a ds

/-- **Completeness of the check of the basic-block optimiser.** The check `optBlocksOKB A tag`
    holds on every body whose instructions pass `keepOKB` (operations, labels, conditional and
    unconditional jumps, returns) and whose instructions other than control instructions are
    flag compares, register copies or instructions of the fragment with flags (`relStepB`),
    with register destinations and the operand form `deadFormB`. -/
theorem optBlocksOKB_optimizeBasicBlocks (A : String → Option Nat) (tag : LinstrR → MemTag)
    (body : List Linstr) (hk : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hs : ∀ i ∈ body, isCtlInstr i = false →
      relStepB A (i.li_i, tag i.li_i) = true ∧ dstsRegB i.li_i = true ∧ deadFormB i = true) :
    optBlocksOKB A tag body = true := by
  simp only [optBlocksOKB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨hk, fun seg hseg => ?_⟩
  cases hsl : bodyIsStraightLine seg with
  | false => exact Or.inl rfl
  | true =>
      refine Or.inr ?_
      simp only [optSegOKB, Bool.or_eq_true]
      exact Or.inr (optSegRegOKB_of_forms fun i hi =>
        hs i (mem_body_of_mem_splitStraightRuns hseg hi) (isCtlInstr_of_straight hsl hi))

/-- **Completeness and soundness on the input of the optimiser in `ownedLprog`.** For every
    function body of `p` of the form of `optBlocksOKB_optimizeBasicBlocks`, the check holds,
    and every halting run of the checked machine on the tagged body is matched by a halting
    run of its image under `optimizeLprogBasicBlocks p`, the first stage of
    `LprogOptPipeline.ownedLprog p`. -/
theorem optBlocksOKB_optimizeLprogBasicBlocks (A : String → Option Nat)
    {tag : LinstrR → MemTag} (hT : TagShape tag) (p : Lprog)
    (hk : ∀ f ∈ p.lp_funcs, ∀ i ∈ f.2.lfd_body, keepOKB (i.li_i, tag i.li_i) = true)
    (hs : ∀ f ∈ p.lp_funcs, ∀ i ∈ f.2.lfd_body, isCtlInstr i = false →
      relStepB A (i.li_i, tag i.li_i) = true ∧ dstsRegB i.li_i = true ∧ deadFormB i = true) :
    ∀ f ∈ p.lp_funcs, optBlocksOKB A tag f.2.lfd_body = true ∧
      ∀ fn, WholeBodySim true (RelInv A) fn (f.2.lfd_body.map fun i => (i.li_i, tag i.li_i))
        ((optimizeBasicBlocks f.2.lfd_body).map fun i => (i.li_i, tag i.li_i)) := by
  intro f hf
  have h := optBlocksOKB_optimizeBasicBlocks A tag _ (hk f hf) (hs f hf)
  exact ⟨h, optBlocksOKB_sound hT h⟩

/-! ## 6. The register copy is accepted -/

/-- The register copy `MOV:64 a, b` has the operand form of the completeness theorem. -/
theorem regCopy_forms : relStepB (fun _ => none) (regCopy.li_i, regTag regCopy.li_i) = true
    ∧ dstsRegB regCopy.li_i = true ∧ deadFormB regCopy = true := by
  refine ⟨rfl, rfl, ?_⟩
  simp [deadFormB, cpRegOKB, regCopy, dstsRegB, notImmB, srcReadOKB, dstReadOKB, srcNames,
    cellBase, operandReads, nameReads, isPhysGP, physGPs, fullDefsOf, regDefsOf, isMovMnem,
    withWidthTag, stripWidthTag, JasminLsemAddrMem.cellParts?, hasPrefix]
  exact Or.inr rfl

/-- **The segment check accepts the register copy** `MOV:64 a, b` through its third
    disjunct, at the empty array table and the untyped tagging. -/
theorem optSegRegOKB_regCopy : optSegRegOKB (fun _ => none) regTag [regCopy] = true :=
  optSegRegOKB_of_forms fun i hi => by
    rw [List.mem_singleton.1 hi]
    exact regCopy_forms

/-- **The check accepts the body `MOV:64 a, b; ret`**, at the empty array table and the
    untyped tagging, while the first two disjuncts of the segment check refuse its segment
    `[MOV:64 a, b]`. -/
theorem optBlocksOKB_regCopyRetBody : optBlocksOKB (fun _ => none) regTag regCopyRetBody = true
    ∧ (!bodyAllModeled [regCopy] && [regCopy].all fun i =>
          (cmpArgs? (i.li_i, regTag i.li_i)).isSome) = false
    ∧ ([regCopy].all fun i => fragFB (fun _ => none) (i.li_i, regTag i.li_i)) = false := by
  refine ⟨optBlocksOKB_optimizeBasicBlocks _ _ _ (fun i hi => ?_) (fun i hi hc => ?_), ?_, rfl⟩
  · simp only [regCopyRetBody, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl
  · simp only [regCopyRetBody, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact regCopy_forms
    · exact absurd hc (by decide)
  · decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksComplete
