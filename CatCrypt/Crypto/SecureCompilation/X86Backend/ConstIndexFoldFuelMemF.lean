/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVDeadImm
public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg

@[expose] public section

set_option autoImplicit false

/-!
# The constant-index fold on the flag machine

`ConstIndexFold.foldIndexedBody` is the stage of `LprogOptPipeline.ownedLprog` that rewrites a
register-indexed access at a known index into a move of a cell name `mem.B.off`
(`constIndexFoldBody`, spelled by `spellMemBody`) and removes the immediate moves that are
overwritten before they are read (`dropDeadImmBody`). `ConstIndexFold.foldInstr_lower` and
`ConstIndexFold.gatherPrinted_dropDeadImm_constIndexFold` state the pass on the gathered
machine block `runBlock`. This module states it on whole bodies of the flag machine
`lsemFuelMemF`.

## The two machines

The flag machine keys an array by its name (`LstateM.larr`) and reads a cell name `mem.B.off`
as a register. A register-indexed load `LOADIDX d, (B, x, 8)` reads the array `B`; its folded
form `LOAD:64 d, mem.B.(8k)` copies the register `mem.B.(8k)`. The two agree only from states
in which the cell names hold the words of the arrays, which is the cell relation
`ImageCellFold.CellRel` of the cell fold `CellFoldLReg.cellFoldLR`, proved sound on the flag
machine (`CellFoldLReg.lsemFuelMemF_cellFoldLR`). The analysis of `constIndexFoldBody` runs on
the gathered block, whose semantics is not the flag machine's; the theorem therefore takes as
a side condition that the fold and its spelling are the cell fold `cellFoldLR` of the body at
the slot arrays `R`, an equation of two typed bodies.

## The dead moves

`dropDeadImmBody` removes immediate moves marked by `OwnedLprogTVDeadImm.dropDeadImmMarks`.
On the flag machine a marked move is dead when its register is pending until an unmarked
instruction writes it as its one destination without reading it, no unmarked instruction
reads a pending register, and no register is pending at a control instruction or at the end
of the body (`dropScan`, `dropOkF`). Under this decidable check the removal is a rewrite of
straight segments (`blockRel_drop`), lifted to whole bodies by
`CfgLift.lsemFuelMemF_blockRel_entry`.

## Main definitions

* `AgreeOff`: two bases equal off a list of pending registers.
* `readsB`, `ovB`: the decidable read and overwrite tests of an instruction.
* `dropStep`, `dropScan`, `dropOkF`: the flag-level check of a marked body.
* `CellObs`: the relation of final states.
* `foldMarks`, `FoldIndexedOK`: the marked body of the stage and the side conditions of the
  theorem.

## Main results

* `runStraightF_drop`: the removal on a straight segment.
* `blockRel_drop`, `lsemFuelMemF_drop`: the removal on whole bodies.
* `foldIndexedBody_lsemFuelMemF`, `foldIndexedLprog_lsemFuelMemF`: the stage on whole bodies of
  the flag machine.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFoldFuelMemF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (EqPc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (readsI readsRdx srcNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames fstepF_frame_dst)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg
  (readNames readsI_cases fstepF_liveStep fstepF_setReg_dst)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
  (typeBody immMov? immMov?_spec tagPlain srcOf keptOf typeMarks keptL spellMarks
   dropDeadImmMarks srcOf_typeMarks keptOf_typeMarks spellMarks_fst keptL_spellMarks
   dropDeadImmMarks_fst keptL_dropDeadImmMarks)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
  (Slots slotsOkB cellsDistinctB CellRel isCellB isArrB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL (CellRelF envAt envAt_zero)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg
  (cellFoldLR lsemFuelMemF_cellFoldLR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
  (foldIndexedBody foldIndexedLprog constIndexFoldBody spellMemBody dropDeadImmBody)

/-! ## 1. Dropped moves -/

/-- An immediate move under a plain tag steps to its base with only the register file
    replaced, and keeps the zero flag. -/
theorem fstepF_immMov {i : LinstrRM} {r : String} (h : immMov? i = some r) {s t : LstateM}
    {zf z : Bool} (hs : fstepF i s zf = some (t, z)) :
    z = zf ∧ t.larr = s.larr ∧ t.lmem = s.lmem ∧ t.cf = s.cf ∧ t.of = s.of := by
  obtain ⟨opn, n, tag, rfl, hm, ht⟩ := immMov?_spec h
  have hcmp : cmpArgs? (.Lopn [.reg r] opn [.imm n], tag) = none := by
    simp only [cmpArgs?]
  have hmv : movRegArgs? (.Lopn [.reg r] opn [.imm n], tag) = none := rfl
  have hca : carryArgs? (.Lopn [.reg r] opn [.imm n], tag) = none := rfl
  have hwa : wideArgs? (.Lopn [.reg r] opn [.imm n], tag) = none := rfl
  have hal : aluFlagOp? (.Lopn [.reg r] opn [.imm n], tag) = none := rfl
  simp only [fstepF, hcmp, hmv, stepMemF, hca, hwa, Option.map_eq_some_iff] at hs
  obtain ⟨b, hb, hbt⟩ := hs
  simp only [Prod.mk.injEq] at hbt
  obtain ⟨rfl, rfl⟩ := hbt
  refine ⟨rfl, ?_⟩
  cases hl : lsemStepMem (.Lopn [.reg r] opn [.imm n], tag) s with
  | none => rw [hl] at hb; cases hb
  | some b' =>
      rw [hl] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      rw [withALUFlags_of_none hal]
      cases tag <;> simp [tagPlain] at ht <;>
        simp only [lsemStepMem, loadStruct?, storeStruct?, Option.map_eq_some_iff] at hl <;>
        (obtain ⟨_, -, rfl⟩ := hl) <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Two bases agree off the pending registers `D`: every other register, the arrays, the word
    memory and the carry and overflow flags are equal. -/
def AgreeOff (D : List String) (s t : LstateM) : Prop :=
  (∀ q, q ∉ D → t.reg.lvm q = s.reg.lvm q) ∧ t.larr = s.larr ∧ t.lmem = s.lmem ∧ t.cf = s.cf
    ∧ t.of = s.of

theorem agreeOff_of_eqPc {s t : LstateM} (h : EqPc s t) : AgreeOff [] s t := by
  unfold EqPc at h
  rw [h]
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem eqPc_of_agreeOff {s t : LstateM} (h : AgreeOff [] s t) : EqPc s t := by
  obtain ⟨hr, ha, hm, hc, ho⟩ := h
  have hl : t.reg.lvm = s.reg.lvm := funext fun q => hr q (by simp)
  obtain ⟨⟨lvm, lpc⟩, larr, lmem, cf, of⟩ := s
  obtain ⟨⟨lvm', lpc'⟩, larr', lmem', cf', of'⟩ := t
  simp only at hl ha hm hc ho
  subst hl ha hm hc ho
  rfl

/-- `q` may be read by the step of `i`: the empty name, `RDX` for a widening multiply, or a
    name of `CopyPropCfg.readNames`. -/
def readsB (i : LinstrRM) (q : String) : Bool :=
  q == "" || (q == "RDX" && readsRdx i.1) || (readNames i.1).contains q

theorem not_readsI {i : LinstrRM} {q : String} (h : readsB i q = false) : ¬ readsI i.1 q := by
  intro hr
  simp only [readsB, Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rcases readsI_cases hr with rfl | ⟨rfl, hx⟩ | hm
  · exact h1 rfl
  · rcases h2 with h2 | h2
    · exact h2 rfl
    · rw [hx] at h2; cases h2
  · have := List.contains_iff_mem.mpr hm
    rw [h3] at this
    cases this

/-- The step of `i` writes `q` as its one register destination without reading it, under the
    conditions of `CopyPropCfg.fstepF_setReg_dst`. -/
def ovB (i : LinstrRM) (q : String) : Bool :=
  match i.1 with
  | .Lopn [.reg d] _ srcs =>
      d == q && q != "" && srcs.all (fun x => !(srcNames x).contains q)
        && (storeStruct? i.1).isNone && (zeroStruct? i.1).isNone
        && (storeImmStruct? i.1).isNone && (cmpArgs? i).isNone
  | _ => false

/-- **A step that overwrites `q`** is the same from a base and from that base with any cell
    at `q`. -/
theorem fstepF_ovB {i : LinstrRM} {q : String} (h : ovB i q = true) (s : LstateM)
    (x : Σ w, BitVec w) (zf : Bool) :
    fstepF i (s.setReg q x.2) zf = fstepF i s zf := by
  obtain ⟨w, tg⟩ := i
  unfold ovB at h
  split at h
  · rename_i d o srcs hw
    simp only at hw
    subst hw
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
      Bool.not_eq_true', Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, hq0⟩, hs⟩, hst⟩, hz⟩, hsi⟩, hc⟩ := h
    exact fstepF_setReg_dst (c := x.2) hq0 o srcs tg zf
      (fun y hy hm => by
        have := hs y hy
        rw [List.contains_iff_mem.mpr hm] at this
        cases this) hst hz hsi hc
  · cases h

/-- **A kept step.** An instruction that reads no pending register steps from two bases that
    agree off `D` to two bases that agree off the pending registers it does not overwrite. -/
theorem keep_step {D : List String} {i : LinstrRM} (hr : ∀ q ∈ D, readsB i q = false)
    {s t s₁ : LstateM} {zf z₁ : Bool} (hA : AgreeOff D s t) (h : fstepF i s zf = some (s₁, z₁)) :
    ∃ t₁, fstepF i t zf = some (t₁, z₁) ∧ AgreeOff (D.filter fun q => !ovB i q) s₁ t₁ := by
  obtain ⟨hR, ha, hm, hc, ho⟩ := hA
  have hreads : ∀ r, readsI i.1 r → s.reg.lvm r = t.reg.lvm r := by
    intro r hr'
    refine (hR r fun hrD => ?_).symm
    exact not_readsI (hr r hrD) hr'
  obtain ⟨t₁, ht₁, hN, ha₁, hm₁, hc₁, ho₁⟩ :=
    fstepF_liveStep hreads ha.symm hm.symm hc.symm ho.symm h
  refine ⟨t₁, ht₁, fun q hq => ?_, ha₁.symm, hm₁.symm, hc₁.symm, ho₁.symm⟩
  by_cases hqD : q ∈ D
  · -- `q` is pending and overwritten by the step
    have hov : ovB i q = true := by
      by_contra hn
      exact hq (List.mem_filter.mpr ⟨hqD, by simpa using hn⟩)
    let t' : LstateM := t.setReg q (s.reg.lvm q).2
    have ht' : fstepF i t' zf = some (t₁, z₁) := by rw [fstepF_ovB hov t (s.reg.lvm q)]; exact ht₁
    have hreads' : ∀ r, readsI i.1 r → s.reg.lvm r = t'.reg.lvm r := by
      intro r hr'
      by_cases hrq : r = q
      · subst hrq; simp [t', LstateM.setReg]
      · simp only [t', LstateM.reg_setReg, LstateN.lvm_setReg, hrq, if_false]
        exact hreads r hr'
    obtain ⟨t₂, ht₂, hN', -⟩ := fstepF_liveStep hreads' ha.symm hm.symm hc.symm ho.symm h
    rw [ht'] at ht₂
    simp only [Option.some.injEq, Prod.mk.injEq] at ht₂
    obtain ⟨rfl, -⟩ := ht₂
    rcases hN' q with he | ⟨he1, he2⟩
    · exact he.symm
    · rw [he2, he1]
      simp [t', LstateM.setReg]
  · rcases hN q with he | ⟨he1, he2⟩
    · exact he.symm
    · rw [he2, he1]
      exact hR q hqD

/-- **A dropped step.** An immediate move to `r` steps from a base that agrees with another
    off `D` to a base that agrees with the other off `r :: D`. -/
theorem drop_step {D : List String} {i : LinstrRM} {r : String} (hi : immMov? i = some r)
    {s t s₁ : LstateM} {zf z₁ : Bool} (hA : AgreeOff D s t) (h : fstepF i s zf = some (s₁, z₁)) :
    z₁ = zf ∧ AgreeOff (r :: D) s₁ t := by
  obtain ⟨hz, ha, hm, hc, ho⟩ := fstepF_immMov hi h
  obtain ⟨opn, n, tag, rfl, -, -⟩ := immMov?_spec hi
  refine ⟨hz, fun q hq => ?_, by rw [ha]; exact hA.2.1, by rw [hm]; exact hA.2.2.1,
    by rw [hc]; exact hA.2.2.2.1, by rw [ho]; exact hA.2.2.2.2⟩
  have hqr : q ≠ r := fun e => hq (e ▸ List.mem_cons_self)
  have hqD : q ∉ D := fun e => hq (List.mem_cons_of_mem _ e)
  rw [(fstepF_frame_dst h (by simp [dstNames, JasminLsemExportRewrites.opNames, hqr])).1]
  exact hA.1 q hqD

/-! ## 2. The check of a marked body -/

/-- One instruction of a marked body under the pending registers `D`: a marked instruction is
    an immediate move and its register becomes pending; an unmarked instruction is an `Lopn` or
    a kept control instruction (`CfgLift.keepOKB`), reads no pending register, finds no
    register pending when it is not an `Lopn`, and releases the pending registers it
    overwrites. -/
def dropStep (D : List String) (p : LinstrRM × Bool) : Option (List String) :=
  if p.2 then (immMov? p.1).map (· :: D)
  else if keepOKB p.1 && (isLopnB p.1 || D.isEmpty) && D.all (fun q => !readsB p.1 q) then
    some (D.filter fun q => !ovB p.1 q)
  else none

/-- The pending registers after a marked body, or `none` when a step of the check fails. -/
def dropScan (D : List String) : List (LinstrRM × Bool) → Option (List String)
  | [] => some D
  | p :: ps =>
      match dropStep D p with
      | some D' => dropScan D' ps
      | none => none

/-- **The check of a marked body**: the scan from no pending register ends with none. -/
def dropOkF (M : List (LinstrRM × Bool)) : Bool := dropScan [] M == some []

theorem dropScan_append (D : List String) :
    ∀ (P Q : List (LinstrRM × Bool)),
      dropScan D (P ++ Q) = (dropScan D P).bind fun D' => dropScan D' Q := by
  intro P
  induction P generalizing D with
  | nil => intro Q; rfl
  | cons p ps ih =>
      intro Q
      simp only [List.cons_append, dropScan]
      cases dropStep D p with
      | none => rfl
      | some D' => exact ih D' Q

/-- **The removal on a straight run.** A run of a marked list from a base that agrees with
    another off `D` is matched by a run of its unmarked instructions from the other base, to
    bases that agree off the pending registers after the list. -/
theorem runStraightF_drop :
    ∀ (P : List (LinstrRM × Bool)) (D D' : List String), dropScan D P = some D' →
      ∀ (s t s₂ : LstateM) (zf z₂ : Bool), AgreeOff D s t →
        runStraightF (srcOf P) s zf = some (s₂, z₂) →
        ∃ t₂, runStraightF (keptOf P) t zf = some (t₂, z₂) ∧ AgreeOff D' s₂ t₂ := by
  intro P
  induction P with
  | nil =>
      intro D D' hD s t s₂ zf z₂ hA h
      simp only [dropScan, Option.some.injEq] at hD
      subst hD
      simp only [srcOf, List.map_nil, runStraightF_nil, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨t, rfl, hA⟩
  | cons p ps ih =>
      intro D D' hD s t s₂ zf z₂ hA h
      obtain ⟨i, b⟩ := p
      cases hst : dropStep D (i, b) with
      | none => simp [dropScan, hst] at hD
      | some D₁ =>
      simp only [dropScan, hst] at hD
      have hsrc : srcOf ((i, b) :: ps) = i :: srcOf ps := rfl
      rw [hsrc, runStraightF_cons] at h
      cases hs : fstepF i s zf with
      | none => rw [hs] at h; cases h
      | some p1 =>
          obtain ⟨s₁, z₁⟩ := p1
          rw [hs, Option.bind_some] at h
          cases b with
          | true =>
              simp only [dropStep, if_true] at hst
              cases hm : immMov? i with
              | none => rw [hm] at hst; cases hst
              | some r =>
                  rw [hm, Option.map_some, Option.some.injEq] at hst
                  subst hst
                  obtain ⟨hz, hA₁⟩ := drop_step hm hA hs
                  subst hz
                  have hk : keptOf ((i, true) :: ps) = keptOf ps := by
                    simp [keptOf]
                  rw [hk]
                  exact ih _ D' hD s₁ t s₂ _ z₂ hA₁ h
          | false =>
              simp only [dropStep, Bool.false_eq_true, if_false] at hst
              split_ifs at hst with hc
              · simp only [Option.some.injEq] at hst
                subst hst
                simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hc
                obtain ⟨t₁, ht₁, hA₁⟩ := keep_step hc.2 hA hs
                have hk : keptOf ((i, false) :: ps) = i :: keptOf ps := by
                  simp [keptOf]
                obtain ⟨t₂, ht₂, hA₂⟩ := ih _ D' hD s₁ t₁ s₂ z₁ z₂ hA₁ h
                refine ⟨t₂, ?_, hA₂⟩
                rw [hk, runStraightF_cons, ht₁, Option.bind_some]
                exact ht₂

/-! ## 3. The removal on whole bodies -/

theorem isLopnB_of_immMov {i : LinstrRM} {r : String} (h : immMov? i = some r) :
    isLopnB i = true := by
  obtain ⟨opn, n, tag, rfl, -, -⟩ := immMov?_spec h
  rfl

theorem false_of_dropWhile_eq_cons {α : Type} (p : α → Bool) :
    ∀ (l : List α) (c : α) (cs : List α), l.dropWhile p = c :: cs → p c = false := by
  intro l
  induction l with
  | nil => intro c cs h; cases h
  | cons a l ih =>
      intro c cs h
      rw [List.dropWhile_cons] at h
      split at h
      · exact ih c cs h
      · rename_i hp
        simp only [List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simpa using hp

theorem srcOf_append (P Q : List (LinstrRM × Bool)) : srcOf (P ++ Q) = srcOf P ++ srcOf Q := by
  simp [srcOf]

theorem keptOf_append (P Q : List (LinstrRM × Bool)) :
    keptOf (P ++ Q) = keptOf P ++ keptOf Q := by
  simp [keptOf, List.filter_append]

/-- **The block relation of the removal.** A marked body that passes the scan from and to no
    pending register is related to its unmarked instructions by `CfgLift.BlockRel`. -/
theorem blockRel_drop :
    ∀ (n : Nat) (M : List (LinstrRM × Bool)), M.length ≤ n → dropScan [] M = some [] →
      BlockRel false (fun _ => True) (srcOf M) (keptOf M) := by
  intro n
  induction n with
  | zero =>
      intro M hl _
      obtain rfl : M = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      exact BlockRel.nil
  | succ n ih =>
      intro M hl hM
      cases M with
      | nil => exact BlockRel.nil
      | cons p ps =>
          obtain ⟨i, b⟩ := p
          by_cases hli : isLopnB i = true
          · -- a straight segment followed by the rest
            let P := ((i, b) :: ps).takeWhile fun q => isLopnB q.1
            let Q := ((i, b) :: ps).dropWhile fun q => isLopnB q.1
            have hPQ : P ++ Q = (i, b) :: ps := List.takeWhile_append_dropWhile
            have hP : P = (i, b) :: (ps.takeWhile fun q => isLopnB q.1) := by
              simp [P, hli]
            have hQ : Q = ps.dropWhile fun q => isLopnB q.1 := by
              simp [Q, hli]
            rw [← hPQ, dropScan_append] at hM
            cases hDP : dropScan [] P with
            | none => rw [hDP] at hM; cases hM
            | some D₁ =>
                rw [hDP, Option.bind_some] at hM
                -- no register is pending at the end of the segment
                have hD₁ : D₁ = [] := by
                  cases hq : Q with
                  | nil =>
                      rw [hq] at hM
                      simpa [dropScan] using hM
                  | cons c cs =>
                      have hc : isLopnB c.1 = false :=
                        false_of_dropWhile_eq_cons (fun q : LinstrRM × Bool => isLopnB q.1)
                          ((i, b) :: ps) c cs hq
                      rw [hq] at hM
                      obtain ⟨ci, cb⟩ := c
                      simp only at hc
                      simp only [dropScan] at hM
                      cases hcs : dropStep D₁ (ci, cb) with
                      | none => rw [hcs] at hM; cases hM
                      | some D₂ =>
                          cases cb with
                          | true =>
                              simp only [dropStep, if_true] at hcs
                              cases hm : immMov? ci with
                              | none => rw [hm] at hcs; cases hcs
                              | some r => rw [isLopnB_of_immMov hm] at hc; cases hc
                          | false =>
                              simp only [dropStep, Bool.false_eq_true, if_false, hc,
                                Bool.false_or] at hcs
                              split_ifs at hcs with hcc
                              simp only [Bool.and_eq_true] at hcc
                              simpa using hcc.1.2
                subst hD₁
                have hlen : Q.length ≤ n := by
                  have h1 : P.length + Q.length = ps.length + 1 := by
                    rw [← List.length_append, hPQ, List.length_cons]
                  have h2 : 1 ≤ P.length := by rw [hP]; simp
                  simp only [List.length_cons] at hl
                  omega
                have hQR := ih Q hlen hM
                rw [← hPQ, srcOf_append, keptOf_append]
                have hlopn : ∀ q ∈ P, isLopnB q.1 = true := fun q hq =>
                  List.all_eq_true.mp List.all_takeWhile q hq
                refine BlockRel.blk ?_ ?_ ?_ ?_ ?_ hQR
                · rw [hP]; simp [srcOf]
                · simp only [srcOf, keptOf, List.length_map]
                  exact List.length_filter_le _ _
                · intro j hj
                  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hj
                  exact isLopnB_isLopn (hlopn q hq)
                · intro j hj
                  simp only [keptOf, List.mem_map, List.mem_filter] at hj
                  obtain ⟨q, ⟨hq, -⟩, rfl⟩ := hj
                  exact isLopnB_isLopn (hlopn q hq)
                · intro s s' t zf zt _ hE _ hrun
                  obtain ⟨t', ht', hA⟩ := runStraightF_drop P [] [] hDP s s' t zf zt
                    (agreeOff_of_eqPc hE) hrun
                  exact ⟨t', ht', eqPc_of_agreeOff hA, trivial⟩
          · -- a kept control instruction
            have hli' : isLopnB i = false := by simpa using hli
            simp only [dropScan] at hM
            cases hst : dropStep [] (i, b) with
            | none => rw [hst] at hM; cases hM
            | some D₁ =>
                rw [hst] at hM
                cases b with
                | true =>
                    simp only [dropStep, if_true] at hst
                    cases hm : immMov? i with
                    | none => rw [hm] at hst; cases hst
                    | some r => rw [isLopnB_of_immMov hm] at hli'; cases hli'
                | false =>
                    simp only [dropStep, Bool.false_eq_true, if_false] at hst
                    split_ifs at hst with hcc
                    simp only [Option.some.injEq, List.filter_nil] at hst
                    subst hst
                    simp only [Bool.and_eq_true] at hcc
                    have hk : KeepOK i := keepOKB_sound hcc.1.1
                    have hctl : CtlKeep i := by
                      rcases hk with hl' | hc'
                      · obtain ⟨d, o, ss, he⟩ := hl'
                        simp [isLopnB, he] at hli'
                      · exact hc'
                    have hsrc : srcOf ((i, false) :: ps) = i :: srcOf ps := rfl
                    have hkept : keptOf ((i, false) :: ps) = i :: keptOf ps := by
                      simp [keptOf]
                    rw [hsrc, hkept]
                    exact BlockRel.ctl hctl (ih ps (by simp at hl; omega) hM)

/-- **The removal of dead immediate moves on whole bodies of the flag machine.** For a marked
    body that passes `dropOkF`, every halting run of its instructions from program counter `0`
    is matched by a halting run of its unmarked instructions from the same state with at most
    the same fuel; the final states have the same function name and zero flag and bases equal
    up to the program counter. -/
theorem lsemFuelMemF_drop {M : List (LinstrRM × Bool)} (h : dropOkF M = true) (fn : String)
    {fuel : Nat} {s t : LstateMF} (h0 : s.prog.base.lpc = 0)
    (hrun : lsemFuelMemF (singletonProgM fn (srcOf M)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF (singletonProgM fn (keptOf M)) fuel' s = some t'
      ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf ∧ EqPc t.prog.base t'.prog.base := by
  have hM : dropScan [] M = some [] := by simpa [dropOkF] using h
  obtain ⟨f', t', hle, hr, hl, hz, hE, -⟩ := lsemFuelMemF_blockRel_entry
    (P := singletonProgM fn (srcOf M)) (P' := singletonProgM fn (keptOf M)) (ck := false)
    (Inv := fun _ => True) rfl (fun _ _ _ => trivial) (blockRel_drop M.length M le_rfl hM) h0
    trivial (by rw [JasminLsemMemChecked.lsemFuelMemFk_false]; exact hrun)
  exact ⟨f', t', hle, hr, hl, hz, hE⟩

/-! ## 4. The fold on whole bodies -/

/-- **The relation of final states**: the registers other than the cell names, the arrays
    other than the slot arrays, the word memory and the carry and overflow flags are equal,
    and every slot array `(A, n)` of `R` of the source state is held, word by word, in the
    cell names `mem.A.(8 j)` of the target state. -/
structure CellObs (R : Slots) (s s' : LstateM) : Prop where
  /-- The registers other than the cell names agree. -/
  reg : ∀ r, isCellB R r = false → s'.reg.lvm r = s.reg.lvm r
  /-- The arrays other than the slot arrays agree. -/
  arr : ∀ r, isArrB R r = false → s'.larr r = s.larr r
  /-- The word memories agree. -/
  mem : s'.lmem = s.lmem
  /-- The carry flags agree. -/
  cf : s'.cf = s.cf
  /-- The overflow flags agree. -/
  of : s'.of = s.of
  /-- The cells of the target hold the slot arrays of the source. -/
  cells : ∀ p ∈ R, ∃ arr : Fin p.2 → BitVec 64, s.getArr p.1 64 p.2 = some arr
    ∧ ∀ j (hj : j < p.2), s'.reg.lvm (memName p.1 (8 * j)) = ⟨64, arr ⟨j, hj⟩⟩

theorem CellObs.of_cellRel {R : Slots} {env : List (String × Nat)} {s s' s'' : LstateM}
    (h : CellRel R env s s') (he : EqPc s' s'') : CellObs R s s'' := by
  unfold EqPc at he
  rw [he]
  exact ⟨h.reg, h.arr, h.mem, h.cf, h.of, h.cells⟩

/-- The marked body of the stage: the fold of the body, marked by the dead-move elimination,
    spelled, and typed with `tag`. -/
def foldMarks (tag : LinstrR → MemTag) (body : Lcmd) : List (LinstrRM × Bool) :=
  typeMarks tag (spellMarks (dropDeadImmMarks (constIndexFoldBody body)))

theorem srcOf_foldMarks (tag : LinstrR → MemTag) (body : Lcmd) :
    srcOf (foldMarks tag body) = typeBody tag (spellMemBody (constIndexFoldBody body)) := by
  rw [foldMarks, srcOf_typeMarks, spellMarks_fst, dropDeadImmMarks_fst]

theorem keptOf_foldMarks (tag : LinstrR → MemTag) (body : Lcmd) :
    keptOf (foldMarks tag body) = typeBody tag (foldIndexedBody body) := by
  rw [foldMarks, keptOf_typeMarks, keptL_spellMarks, keptL_dropDeadImmMarks]
  rfl

/-- **The side conditions of the stage** on a body typed with `tag`, at the slot arrays `R`:
    the fold and its spelling are the cell fold `CellFoldLReg.cellFoldLR` of the body from no
    known constant, and the removed moves pass the flag-level check `dropOkF`. -/
def FoldIndexedOK (tag : LinstrR → MemTag) (R : Slots) (body : Lcmd) : Prop :=
  cellFoldLR R [] (typeBody tag body) = some (typeBody tag (spellMemBody (constIndexFoldBody body)))
    ∧ dropOkF (foldMarks tag body) = true

/-- **`foldIndexedBody_lsemFuelMemF`: the constant-index stage on whole bodies of the flag
    machine.** Let the slot arrays `R` pass `slotsOkB` and `cellsDistinctB` and the body pass
    `FoldIndexedOK tag R`. Every halting run of the typed body from program counter `0` and a
    state `s` is matched by a halting run of the typed body of `foldIndexedBody body` from every
    state `s'` cell-related to `s` (`CellFoldL.CellRelF R []`: the same registers off the cell
    names, program counter, arrays off the slot arrays, word memory and flags, and each slot
    array of `s` held in the cell names of `s'`), with at most the same fuel; the final states
    are related by `CellObs R` and have the same zero flag and function name. -/
theorem foldIndexedBody_lsemFuelMemF {tag : LinstrR → MemTag} {R : Slots}
    (hR : slotsOkB R = true) (hD : cellsDistinctB R = true) {body : Lcmd}
    (h : FoldIndexedOK tag R body) (fn : String) (fuel : Nat) {s s' t : LstateMF}
    (hpc : s.prog.base.lpc = 0) (hC : CellRelF R [] s s')
    (hrun : lsemFuelMemF (singletonProgM fn (typeBody tag body)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel
      ∧ lsemFuelMemF (singletonProgM fn (typeBody tag (foldIndexedBody body))) fuel' s' = some t'
      ∧ CellObs R t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  obtain ⟨hA, hB⟩ := h
  have hC0 : CellRelF R (envAt [] (typeBody tag body) s.prog.base.lpc) s s' := by
    rw [hpc, envAt_zero]
    exact hC
  obtain ⟨t₁, hrun₁, hC₁⟩ := lsemFuelMemF_cellFoldLR hR hD hA fn fuel hC0 hrun
  have hpc' : s'.prog.base.lpc = 0 := by
    have := hC.base.pc
    simp only [LstateM.lpc] at hpc ⊢
    rw [this, hpc]
  rw [← srcOf_foldMarks] at hrun₁
  obtain ⟨fuel', t₂, hle, hrun₂, hlfn, hzf, hE⟩ := lsemFuelMemF_drop hB fn hpc' hrun₁
  rw [keptOf_foldMarks] at hrun₂
  exact ⟨fuel', t₂, hle, hrun₂, CellObs.of_cellRel hC₁.base hE, hzf.trans hC₁.zf,
    hlfn.trans hC₁.lfn⟩

/-- **`foldIndexedLprog_lsemFuelMemF`: the constant-index stage on the functions of a
    program.** Every function `(name, fd)` of `lp` has the function
    `(name, fd` with body `foldIndexedBody fd.lfd_body)` in `foldIndexedLprog lp`, and when
    the body of `fd` passes `FoldIndexedOK tag R` the conclusion of
    `foldIndexedBody_lsemFuelMemF` holds between the two bodies. -/
theorem foldIndexedLprog_lsemFuelMemF {lp : Lprog} {f : String × Lfundef} (hf : f ∈ lp.lp_funcs)
    {tag : LinstrR → MemTag} {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    (h : FoldIndexedOK tag R f.2.lfd_body) :
    (f.1, { f.2 with lfd_body := foldIndexedBody f.2.lfd_body }) ∈ (foldIndexedLprog lp).lp_funcs
      ∧ ∀ (fn : String) (fuel : Nat) {s s' t : LstateMF}, s.prog.base.lpc = 0 →
        CellRelF R [] s s' →
        lsemFuelMemF (singletonProgM fn (typeBody tag f.2.lfd_body)) fuel s = some t →
        ∃ fuel' t', fuel' ≤ fuel
          ∧ lsemFuelMemF (singletonProgM fn (typeBody tag (foldIndexedBody f.2.lfd_body)))
              fuel' s' = some t'
          ∧ CellObs R t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn :=
  ⟨List.mem_map.mpr ⟨f, hf, rfl⟩,
    fun fn fuel _ _ _ hpc hC hrun => foldIndexedBody_lsemFuelMemF hR hD h fn fuel hpc hC hrun⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFoldFuelMemF
