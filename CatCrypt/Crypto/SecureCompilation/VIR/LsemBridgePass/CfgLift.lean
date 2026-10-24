/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

/-!
# Block-local rewrites on the flag machine

A block-local rewrite of a body keeps every label, conditional branch and goto in place
and replaces straight segments of `Lopn` instructions by straight segments. This module
proves that such a rewrite preserves halting runs of the flag machine on the whole body,
given a simulation of each rewritten segment under the extended straight fold
`runStraightF`.

The source run is a run of the checked machine `lsemFuelMemFk ck`. With `ck = true` every
indexed access of the source run is in bounds, and the simulation of a segment may assume
that the accesses of the segment are in bounds from its start state (`SegIdxOk`); with
`ck = false` the source run is a run of `lsemFuelMemF` and the simulation of a segment has
no such premise.

`JasminLsemExportLower.lsemFuelMemF_expand` is the statement for a rewrite that expands
one instruction at a time; here the unit of rewriting is a segment, so a pass that permutes
or deletes instructions inside a segment is covered.

## Main definitions

* `CtlKeep` — a label, a conditional, a goto, or an instruction that takes no step.
* `KeepOK`, `keepOKB` — an `Lopn` or a `CtlKeep` instruction, and its Boolean check.
* `SegIdxOk seg s zf` — every indexed access of the run of `seg` from `s` is in bounds.
* `BlockSim ck Inv seg seg'` — from two states equal up to the program counter, the first
  satisfying `Inv` (and `SegIdxOk` when `ck`), a run of `seg` under `runStraightF` is
  matched by a run of `seg'` with the same zero flag, final states equal up to the program
  counter, and `Inv` at the end.
* `BlockRel ck Inv B B'` — `B'` is `B` with every `CtlKeep` instruction in place and
  non-empty `Lopn` segments replaced by `Lopn` segments of at most the same length that
  satisfy `BlockSim`.
* `RelB ck Inv P P' s s'` — the state relation: equal function name and zero flag, bases
  equal up to the program counter, `Inv` on the source base, and the two program counters
  at related suffixes of the bodies.

## Main results

* `BlockRel.findLabelMem` — a label position of the source body has a position in the
  target body, and the suffixes after the two labels are related.
* `evalInstrPMemF_blockRel` — one step at a kept control instruction.
* `runIdxOk_seg` — an in-bounds run that starts at a straight segment is in bounds on the
  segment and after it.
* `lsemFuelMemFk_blockRel` — every halting run of the checked source program is matched,
  from a related state, by a halting run of the target program with at most the same fuel.
* `lsemFuelMemF_blockRel`, `lsemFuelMemF_blockRel_entry` — the unchecked instance, and
  the statement from the entry of the body.
* `BlockRel.of_keepOK`, `BlockRel.append`, `BlockRel.of_segs`, `BlockSim.of_same`,
  `BlockSim.of_plain` — the constructions a pass uses to build `BlockRel` from its segment
  lemma.
* `keepOKB_sound` — the Boolean check implies `KeepOK`.

`LsemBridgePass.BlocksCfg` instantiates the lift at the basic-block optimiser.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked

/-! ## 1. The block relation -/

/-- A control instruction a block-local rewrite keeps in place: a label, a conditional, a
    goto, or an instruction on which the flag machine takes no step. -/
def CtlKeep (i : LinstrRM) : Prop :=
  (∃ kd l, i.1 = LinstrR.Llabel kd l)
    ∨ (∃ c l, i.1 = LinstrR.Lcond c l)
    ∨ (∃ tgt, i.1 = LinstrR.Lgoto tgt)
    ∨ (∀ (P : LprogM) (s : LstateMF), evalInstrPMemF P i s = none)

/-- An instruction a block-local rewrite accepts: an `Lopn` or a kept control
    instruction. -/
def KeepOK (i : LinstrRM) : Prop := IsLopn i ∨ CtlKeep i

/-- The in-bounds condition `idxOkB` of an instruction at a base state. -/
def baseIdxOk (i : LinstrRM) (b : LstateM) : Bool :=
  idxOkB i { prog := { base := b, lfn := "" }, zf := false }

theorem idxOkB_eq_baseIdxOk (i : LinstrRM) (s : LstateMF) :
    idxOkB i s = baseIdxOk i s.prog.base := rfl

/-- Every indexed access of the run of `seg` from `s` under `runStraightF` is in bounds. -/
def SegIdxOk : List LinstrRM → LstateM → Bool → Prop
  | [], _, _ => True
  | i :: is, b, zf =>
      baseIdxOk i b = true ∧ ∀ b' z, fstepF i b zf = some (b', z) → SegIdxOk is b' z

section Rel

variable (ck : Bool) (Inv : LstateM → Prop)

/-- The simulation of one rewritten segment: from two states equal up to the program
    counter, the first satisfying `Inv` and, with `ck`, in bounds on `seg`, a run of `seg`
    is matched by a run of `seg'` with the same zero flag, final states equal up to the
    program counter, and `Inv` at the final state of `seg`. -/
def BlockSim (seg seg' : List LinstrRM) : Prop :=
  ∀ (s s' t : LstateM) (zf zt : Bool), Inv s → EqPc s s' →
    (ck = true → SegIdxOk seg s zf) →
    runStraightF seg s zf = some (t, zt) →
    ∃ t', runStraightF seg' s' zf = some (t', zt) ∧ EqPc t t' ∧ Inv t

/-- The relation between a body and its block-local rewrite: kept control instructions
    alternate with non-empty `Lopn` segments, each replaced by an `Lopn` segment of at most
    the same length that simulates it. -/
inductive BlockRel : List LinstrRM → List LinstrRM → Prop
  | nil : BlockRel [] []
  | ctl {i : LinstrRM} {R R' : List LinstrRM} :
      CtlKeep i → BlockRel R R' → BlockRel (i :: R) (i :: R')
  | blk {seg seg' R R' : List LinstrRM} :
      seg ≠ [] → seg'.length ≤ seg.length →
      (∀ i ∈ seg, IsLopn i) → (∀ i ∈ seg', IsLopn i) →
      BlockSim ck Inv seg seg' → BlockRel R R' → BlockRel (seg ++ R) (seg' ++ R')

/-- The state relation of the simulation. -/
structure RelB (P P' : LprogM) (s s' : LstateMF) : Prop where
  /-- The function names agree. -/
  lfn : s'.prog.lfn = s.prog.lfn
  /-- The zero flags agree. -/
  zf : s'.zf = s.zf
  /-- The bases are equal up to the program counter. -/
  base : EqPc s.prog.base s'.prog.base
  /-- The invariant holds on the source base. -/
  inv : Inv s.prog.base
  /-- The program counters are at related suffixes of the two bodies. -/
  pc : BlockRel ck Inv (P.body.drop s.prog.base.lpc) (P'.body.drop s'.prog.base.lpc)

end Rel

variable {ck : Bool} {Inv : LstateM → Prop}

/-! ## 2. Lists and labels -/

theorem drop_succ_of_cons {α : Type} {l : List α} {n : Nat} {a : α} {R : List α}
    (h : l.drop n = a :: R) : l.drop (n + 1) = R := by
  have := congrArg (List.drop 1) h
  simpa [List.drop_drop] using this

theorem drop_add_of_append {α : Type} {l : List α} {n : Nat} {seg R : List α}
    (h : l.drop n = seg ++ R) : l.drop (n + seg.length) = R := by
  have := congrArg (List.drop seg.length) h
  simpa [List.drop_drop] using this

theorem getElem?_of_drop_append {α : Type} {l : List α} {n : Nat} {seg R : List α}
    (h : l.drop n = seg ++ R) (k : Nat) (hk : k < seg.length) : l[n + k]? = seg[k]? := by
  have := congrArg (·[k]?) h
  simp only [List.getElem?_drop] at this
  rw [this, List.getElem?_append_left hk]

/-- A related body of the empty body is empty. -/
theorem BlockRel.eq_nil {Y : List LinstrRM} (h : BlockRel ck Inv [] Y) : Y = [] := by
  generalize hX : ([] : List LinstrRM) = X at h
  cases h with
  | nil => rfl
  | ctl _ _ => cases hX
  | blk hne _ _ _ _ _ => exact absurd (List.append_eq_nil_iff.mp hX.symm).1 hne

/-- The label search at a body with a head instruction. -/
theorem findLabelMem_cons (l : LLabel) (i : LinstrRM) (R : List LinstrRM) :
    findLabelMem l (i :: R)
      = if JasminLsemLabeled.isLabel l i.1 then some 0
        else (findLabelMem l R).map (· + 1) := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_cons, List.findIdx?_cons]

/-- **Labels under a block-local rewrite.** A label position of the source body has a
    position in the target body, and the suffixes after the two labels are related. -/
theorem BlockRel.findLabelMem {B B' : List LinstrRM} (h : BlockRel ck Inv B B')
    (l : LLabel) :
    ∀ pc, findLabelMem l B = some pc →
      ∃ pc', findLabelMem l B' = some pc'
        ∧ BlockRel ck Inv (B.drop (pc + 1)) (B'.drop (pc' + 1)) := by
  induction h with
  | nil =>
      intro pc hpc
      simp [JasminLsemMemLoop.findLabelMem, JasminLsemLabeled.findLabel] at hpc
  | @ctl i R R' _ hR ih =>
      intro pc hpc
      rw [findLabelMem_cons] at hpc ⊢
      split at hpc
      · rename_i hl
        cases hpc
        exact ⟨0, ite_eq_left hl, by simpa using hR⟩
      · rename_i hl
        obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hpc
        obtain ⟨k', hk', hd⟩ := ih k hk
        exact ⟨k' + 1, by rw [ite_eq_right hl, hk']; rfl, by simpa using hd⟩
  | @blk seg seg' R R' _ _ hseg hseg' _ _ ih =>
      intro pc hpc
      rw [findLabelMem_prefix l seg R hseg] at hpc
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hpc
      obtain ⟨k', hk', hd⟩ := ih k hk
      refine ⟨k' + seg'.length, by rw [findLabelMem_prefix l seg' R' hseg', hk']; rfl, ?_⟩
      have e1 : (seg ++ R).drop (k + seg.length + 1) = R.drop (k + 1) := by
        rw [show k + seg.length + 1 = seg.length + (k + 1) from by omega]
        simp
      have e2 : (seg' ++ R').drop (k' + seg'.length + 1) = R'.drop (k' + 1) := by
        rw [show k' + seg'.length + 1 = seg'.length + (k' + 1) from by omega]
        simp
      rw [e1, e2]
      exact hd

/-! ## 3. One control step -/

/-- A jump of the source program is matched by the same jump of the target. -/
theorem evalJumpMem_blockRel {P P' : LprogM} (hB : BlockRel ck Inv P.body P'.body)
    (l : LLabel) {p p' q : LstatePM} (hE : EqPc p.base p'.base) (hfn : p'.lfn = p.lfn)
    (h : evalJumpMem P l p = some q) :
    ∃ q', evalJumpMem P' l p' = some q' ∧ EqPc q.base q'.base ∧ q'.lfn = q.lfn
      ∧ q.base = p.base.setLpc q.base.lpc
      ∧ BlockRel ck Inv (P.body.drop q.base.lpc) (P'.body.drop q'.base.lpc) := by
  unfold evalJumpMem at h ⊢
  cases hl : JasminLsemMemLoop.findLabelMem l P.body with
  | none => simp [hl] at h
  | some pc =>
      obtain ⟨pc', hpc', hR⟩ := hB.findLabelMem l pc hl
      simp only [hl, Option.some.injEq] at h
      subst h
      rw [hpc']
      exact ⟨_, rfl, hE.setLpc _ _, hfn, rfl, hR⟩

/-- **One step at a kept control instruction.** A successful step of the source program at
    a label, a conditional or a goto is matched by the step of the target program at the
    same instruction from a related state, into a related state. -/
theorem evalInstrPMemF_blockRel {P P' : LprogM} (hfn : P'.lfn = P.lfn)
    (hpc : ∀ a p, Inv a → Inv (a.setLpc p))
    (hB : BlockRel ck Inv P.body P'.body) {i : LinstrRM} (hi : CtlKeep i)
    {s s' u : LstateMF} {R R' : List LinstrRM} (hS : RelB ck Inv P P' s s')
    (hd : P.body.drop s.prog.base.lpc = i :: R)
    (hd' : P'.body.drop s'.prog.base.lpc = i :: R') (hRR : BlockRel ck Inv R R')
    (he : evalInstrPMemF P i s = some u) :
    ∃ u', evalInstrPMemF P' i s' = some u' ∧ RelB ck Inv P P' u u' := by
  have hnext : RelB ck Inv P P'
      { s with prog := { s.prog with base := s.prog.base.nextPc } }
      { s' with prog := { s'.prog with base := s'.prog.base.nextPc } } :=
    ⟨hS.lfn, hS.zf, hS.base.setLpc _ _, hpc _ _ hS.inv, by
      show BlockRel ck Inv (P.body.drop (s.prog.base.lpc + 1))
        (P'.body.drop (s'.prog.base.lpc + 1))
      rw [drop_succ_of_cons hd, drop_succ_of_cons hd']
      exact hRR⟩
  have hjump : ∀ (lbl : LLabel) {q : LstatePM}, evalJumpMem P lbl s.prog = some q →
      ∃ q', evalJumpMem P' lbl s'.prog = some q'
        ∧ RelB ck Inv P P' { s with prog := q } { s' with prog := q' } := by
    intro lbl q hq
    obtain ⟨q', hq', hEq, hfq, hqb, hpq⟩ := evalJumpMem_blockRel hB lbl hS.base hS.lfn hq
    exact ⟨q', hq', ⟨hfq, hS.zf, hEq, by
      show Inv q.base
      rw [hqb]
      exact hpc _ _ hS.inv, hpq⟩⟩
  obtain ⟨wire, tag⟩ := i
  rcases hi with ⟨kd, l, hw⟩ | ⟨c, l, hw⟩ | ⟨tgt, hw⟩ | hst
  · obtain rfl : wire = LinstrR.Llabel kd l := hw
    rw [evalInstrPMemF_label] at he
    cases he
    exact ⟨_, evalInstrPMemF_label P' kd l tag s', hnext⟩
  · obtain rfl : wire = LinstrR.Lcond c l := hw
    have h1 : cmpArgs? (LinstrR.Lcond c l, tag) = none := rfl
    have h2 : movRegArgs? (LinstrR.Lcond c l, tag) = none := rfl
    cases h3 : flagCondCC? (LinstrR.Lcond c l, tag) with
    | none =>
        have hb : s'.prog.base = s.prog.base.setLpc s'.prog.base.lpc := hS.base
        have hc : condNZ s'.prog.base c = condNZ s.prog.base c := by
          rw [hb]
          rfl
        have hev : ∀ (Q : LprogM) (x : LstateMF),
            evalInstrPMemF Q (LinstrR.Lcond c l, tag) x
              = (if condNZ x.prog.base c then evalJumpMem Q l x.prog
                  else some { x.prog with base := x.prog.base.nextPc }).map
                  (fun p => { x with prog := p }) := fun Q x => by
          rw [evalInstrPMemF_delegate Q _ x rfl rfl h3 rfl rfl rfl]
          rfl
        rw [hev] at he ⊢
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
        split at hq
        · rename_i hz
          obtain ⟨q', hq', hRq⟩ := hjump l hq
          refine ⟨{ s' with prog := q' }, ?_, hRq⟩
          rw [hc, ite_eq_left hz, hq']
          rfl
        · rename_i hz
          cases hq
          refine ⟨_, ?_, hnext⟩
          rw [hc, ite_eq_right hz]
          rfl
    | some pl =>
        obtain ⟨pol, lbl⟩ := pl
        unfold evalInstrPMemF at he ⊢
        simp only [h1, h2, h3] at he ⊢
        split at he
        · rename_i hz
          obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
          obtain ⟨q', hq', hRq⟩ := hjump lbl hq
          refine ⟨{ s' with prog := q' }, ?_, hRq⟩
          rw [ite_eq_left (hS.zf.trans hz), hq']
          rfl
        · rename_i hz
          cases he
          refine ⟨_, ?_, hnext⟩
          rw [ite_eq_right (fun h => hz (hS.zf.symm.trans h))]
  · obtain rfl : wire = LinstrR.Lgoto tgt := hw
    obtain ⟨fn, l⟩ := tgt
    have hev : ∀ (Q : LprogM) (x : LstateMF),
        evalInstrPMemF Q (LinstrR.Lgoto (fn, l), tag) x
          = (if fn = Q.lfn then evalJumpMem Q l x.prog else none).map
              (fun p => { x with prog := p }) := fun Q x => by
      rw [evalInstrPMemF_delegate Q _ x rfl rfl rfl rfl rfl rfl]
      rfl
    rw [hev] at he ⊢
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
    split at hq
    · rename_i hf
      obtain ⟨q', hq', hRq⟩ := hjump l hq
      refine ⟨{ s' with prog := q' }, ?_, hRq⟩
      rw [hfn, ite_eq_left hf, hq']
      rfl
    · exact absurd hq (by simp)
  · rw [hst P s] at he
    cases he

/-! ## 4. The simulation -/

/-- **An in-bounds run through a straight segment.** A run of `P` whose accesses are in
    bounds and that starts at a straight segment of `Lopn` instructions is in bounds on the
    segment, and the run after the segment is in bounds. -/
theorem runIdxOk_seg (P : LprogM) (fn : String) (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b0 : LstateM) (zf : Bool) (f : Nat),
      (∀ i ∈ seg, IsLopn i) →
      (∀ k, k < seg.length → P.body[b0.lpc + k]? = seg[k]?) →
      RunIdxOk P (seg.length + f) { prog := { base := b0, lfn := fn }, zf := zf } →
      SegIdxOk seg b0 zf ∧ ∀ u zu, runStraightF seg b0 zf = some (u, zu) →
        RunIdxOk P f { prog := { base := u, lfn := fn }, zf := zu } := by
  intro seg
  induction seg with
  | nil =>
      intro b0 zf f _ _ hok
      refine ⟨trivial, fun u zu h => ?_⟩
      simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa using hok
  | cons i is ih =>
      intro b0 zf f hl hpos hok
      have hi : IsLopn i := hl i List.mem_cons_self
      have his : ∀ j ∈ is, IsLopn j := fun j hj => hl j (List.mem_cons_of_mem _ hj)
      have hfetch : findInstrMem P
          ({ prog := { base := b0, lfn := fn }, zf := zf } : LstateMF).prog = some i := by
        show findInstrMem P { base := b0, lfn := fn } = some i
        unfold findInstrMem
        rw [ite_eq_left (show ({ base := b0, lfn := fn } : LstatePM).lfn = P.lfn from hfn)]
        have := hpos 0 (by simp)
        simpa using this
      rw [List.length_cons, show is.length + 1 + f = (is.length + f) + 1 from by omega] at hok
      obtain ⟨hib, hnext⟩ := hok i hfetch
      have hstep : ∀ b' z, fstepF i b0 zf = some (b', z) →
          SegIdxOk is b' z ∧ ∀ u zu, runStraightF is b' z = some (u, zu) →
            RunIdxOk P f { prog := { base := u, lfn := fn }, zf := zu } := by
        intro b' z hst
        have hpos' : ∀ k, k < is.length → P.body[b'.lpc + k]? = is[k]? := by
          intro k hk
          have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
          rw [fstepF_lpc_succ i b0 b' zf z hst,
            show b0.lpc + 1 + k = b0.lpc + (k + 1) from by omega, hp]
          simp
        refine ih b' z f his hpos' (hnext _ ?_)
        rw [evalInstrPMemF_isLopn P i _ hi, hst]
        rfl
      refine ⟨⟨hib, fun b' z hst => (hstep b' z hst).1⟩, fun u zu hrun => ?_⟩
      rw [runStraightF_cons] at hrun
      cases hst : fstepF i b0 zf with
      | none => rw [hst] at hrun; simp at hrun
      | some bz =>
          obtain ⟨b', z⟩ := bz
          rw [hst, Option.bind_some] at hrun
          exact (hstep b' z hst).2 u zu hrun

/-- The simulation over a run of `lsemFuelMemF` whose accesses are in bounds when `ck`. -/
theorem lsemFuelMemF_blockRel_of_runIdxOk {P P' : LprogM} (hfn : P'.lfn = P.lfn)
    (hpc : ∀ a p, Inv a → Inv (a.setLpc p)) (hB : BlockRel ck Inv P.body P'.body) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelB ck Inv P P' s s' →
      (ck = true → RunIdxOk P fuel s) →
      lsemFuelMemF P fuel s = some t →
      ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF P' fuel' s' = some t'
        ∧ RelB ck Inv P P' t t' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro s s' t hS hok h
  cases hf : findInstrMem P s.prog with
  | none =>
      rw [lsemFuelMemF_halt P fuel s hf] at h
      cases h
      refine ⟨0, s', Nat.zero_le _, lsemFuelMemF_halt P' 0 s' ?_, hS⟩
      unfold findInstrMem at hf ⊢
      rw [hS.lfn, hfn]
      split
      · rename_i hl
        rw [ite_eq_left hl] at hf
        have hd : P.body.drop s.prog.base.lpc = [] :=
          List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp hf)
        have hp := hS.pc
        rw [hd] at hp
        exact List.getElem?_eq_none_iff.mpr (List.drop_eq_nil_iff.mp hp.eq_nil)
      · rfl
  | some i =>
      have hfg : s.prog.lfn = P.lfn ∧ P.body[s.prog.base.lpc]? = some i := by
        unfold findInstrMem at hf
        split at hf
        · exact ⟨by assumption, hf⟩
        · simp at hf
      have hfl' : s'.prog.lfn = P'.lfn := hS.lfn.trans (hfg.1.trans hfn.symm)
      have hp := hS.pc
      generalize hX : P.body.drop s.prog.base.lpc = X at hp
      generalize hY : P'.body.drop s'.prog.base.lpc = Y at hp
      have hhead : X[0]? = some i := by
        rw [← hX, List.getElem?_drop]
        exact hfg.2
      cases hp with
      | nil => simp at hhead
      | @ctl i0 R R' hi hRR =>
          obtain rfl : i0 = i := by simpa using hhead
          have hfetch' : findInstrMem P' s'.prog = some i0 := by
            unfold findInstrMem
            rw [ite_eq_left hfl']
            have := congrArg (·[0]?) hY
            simpa [List.getElem?_drop] using this
          cases fuel with
          | zero =>
              unfold lsemFuelMemF at h
              simp [hf] at h
          | succ n =>
              unfold lsemFuelMemF at h
              simp only [hf] at h
              cases he : evalInstrPMemF P i0 s with
              | none => simp [he] at h
              | some u =>
                  simp only [he] at h
                  obtain ⟨u', hu', hSu⟩ :=
                    evalInstrPMemF_blockRel hfn hpc hB hi hS hX hY hRR he
                  obtain ⟨f', t', hle, hrun, hSt⟩ := ih n (Nat.lt_succ_self n) hSu
                    (fun hc => ((hok hc) i0 hf).2 u he) h
                  refine ⟨f' + 1, t', Nat.succ_le_succ hle, ?_, hSt⟩
                  rw [lsemFuelMemF_step P' f' i0 s' u' hfetch' hu']
                  exact hrun
      | @blk seg seg' R R' hne hlen hseg hseg' hsim hRR =>
          have hpos := getElem?_of_drop_append hX
          have hpos' := getElem?_of_drop_append hY
          have hge : seg.length ≤ fuel :=
            lsemFuelMemF_seg_fuel P s.prog.lfn hfg.1 seg s.prog.base s.zf fuel t hseg hpos h
          obtain ⟨f, rfl⟩ : ∃ f, fuel = seg.length + f := ⟨fuel - seg.length, by omega⟩
          have h2 := (lsemFuelMemF_segF P s.prog.lfn hfg.1 seg s.prog.base s.zf f hseg
            hpos).symm.trans h
          cases hr : runStraightF seg s.prog.base s.zf with
          | none => rw [hr] at h2; simp at h2
          | some bz =>
              obtain ⟨u, zu⟩ := bz
              rw [hr, Option.bind_some] at h2
              have hseg_ok : ck = true → SegIdxOk seg s.prog.base s.zf ∧
                  RunIdxOk P f { prog := { base := u, lfn := s.prog.lfn }, zf := zu } :=
                fun hc => by
                  have hk := runIdxOk_seg P s.prog.lfn hfg.1 seg s.prog.base s.zf f hseg hpos
                    (hok hc)
                  exact ⟨hk.1, hk.2 u zu hr⟩
              obtain ⟨u', hu', hEu, hIu⟩ :=
                hsim _ _ _ _ _ hS.inv hS.base (fun hc => (hseg_ok hc).1) hr
              have h1 := runStraightF_lpc _ _ _ _ _ hr
              have h1' := runStraightF_lpc _ _ _ _ _ hu'
              have hSu : RelB ck Inv P P'
                  { prog := { base := u, lfn := s.prog.lfn }, zf := zu }
                  { prog := { base := u', lfn := s'.prog.lfn }, zf := zu } :=
                ⟨hS.lfn, rfl, hEu, hIu, by
                  show BlockRel ck Inv (P.body.drop u.lpc) (P'.body.drop u'.lpc)
                  rw [h1, h1', drop_add_of_append hX, drop_add_of_append hY]
                  exact hRR⟩
              have hlt : f < seg.length + f := by
                have := List.length_pos_iff.mpr hne
                omega
              obtain ⟨f', t', hle, hrun, hSt⟩ :=
                ih f hlt hSu (fun hc => (hseg_ok hc).2) h2
              have hsegF' := lsemFuelMemF_segF P' s'.prog.lfn hfl' seg' s'.prog.base s'.zf f'
                hseg' hpos'
              rw [← hS.zf] at hu'
              rw [hu', Option.bind_some] at hsegF'
              exact ⟨seg'.length + f', t', by omega, hsegF'.trans hrun, hSt⟩

/-- **The flag machine under a block-local rewrite.** Let `P'` have the function name of
    `P` and a body related to the body of `P` by `BlockRel ck Inv`, with `Inv` independent
    of the program counter. Every halting run of the checked machine `lsemFuelMemFk ck` on
    `P` is matched, from a related state, by a halting run of `lsemFuelMemF` on `P'` into a
    related state, with at most the same fuel. -/
theorem lsemFuelMemFk_blockRel {P P' : LprogM} (hfn : P'.lfn = P.lfn)
    (hpc : ∀ a p, Inv a → Inv (a.setLpc p)) (hB : BlockRel ck Inv P.body P'.body)
    (fuel : Nat) {s s' t : LstateMF} (hS : RelB ck Inv P P' s s')
    (h : lsemFuelMemFk ck P fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF P' fuel' s' = some t'
      ∧ RelB ck Inv P P' t t' :=
  lsemFuelMemF_blockRel_of_runIdxOk hfn hpc hB fuel hS
    (fun hc => runIdxOk_of_checked P fuel s t (hc ▸ h)) (lsemFuelMemF_of_checked P fuel s t h)

/-- **The unchecked instance.** Under `BlockRel false Inv`, every halting run of
    `lsemFuelMemF` on `P` is matched by a halting run on `P'` with at most the same fuel. -/
theorem lsemFuelMemF_blockRel {P P' : LprogM} (hfn : P'.lfn = P.lfn)
    (hpc : ∀ a p, Inv a → Inv (a.setLpc p)) (hB : BlockRel false Inv P.body P'.body) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelB false Inv P P' s s' →
      lsemFuelMemF P fuel s = some t →
      ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF P' fuel' s' = some t'
        ∧ RelB false Inv P P' t t' :=
  fun fuel _ _ _ hS h =>
    lsemFuelMemF_blockRel_of_runIdxOk hfn hpc hB fuel hS (fun hc => absurd hc (by simp)) h

/-- **A block-local rewrite from the entry of the body.** From a state at program counter
    `0` that satisfies `Inv`, every halting run of the checked machine on `P` is matched by
    a halting run of `P'` from the same state with at most the same fuel; the final states
    have the same function name and zero flag and bases equal up to the program counter,
    and `Inv` holds at the final state of `P`. -/
theorem lsemFuelMemF_blockRel_entry {P P' : LprogM} (hfn : P'.lfn = P.lfn)
    (hpc : ∀ a p, Inv a → Inv (a.setLpc p)) (hB : BlockRel ck Inv P.body P'.body)
    {fuel : Nat} {s t : LstateMF} (h0 : s.prog.base.lpc = 0) (hI : Inv s.prog.base)
    (h : lsemFuelMemFk ck P fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF P' fuel' s = some t'
      ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf ∧ EqPc t.prog.base t'.prog.base
      ∧ Inv t.prog.base := by
  have hS : RelB ck Inv P P' s s :=
    ⟨rfl, rfl, rfl, hI, by rw [h0]; exact hB⟩
  obtain ⟨f', t', hle, hrun, hSt⟩ := lsemFuelMemFk_blockRel hfn hpc hB fuel hS h
  exact ⟨f', t', hle, hrun, hSt.lfn, hSt.zf, hSt.base, hSt.inv⟩

/-! ## 5. Building the block relation -/

/-- A segment simulation from a statement at one start state. -/
theorem BlockSim.of_same {seg seg' : List LinstrRM}
    (h : ∀ (s t : LstateM) (zf zt : Bool), Inv s → (ck = true → SegIdxOk seg s zf) →
      runStraightF seg s zf = some (t, zt) →
      ∃ t', runStraightF seg' s zf = some (t', zt) ∧ EqPc t t' ∧ Inv t) :
    BlockSim ck Inv seg seg' := by
  intro s s' t zf zt hI hE hok hr
  obtain ⟨t₁, ht₁, hE₁, hI₁⟩ := h s t zf zt hI hok hr
  obtain ⟨t', ht', hE'⟩ := runStraightF_eqPc seg' hE ht₁
  exact ⟨t', ht', hE₁.trans hE', hI₁⟩

/-- A segment simulation of two plain segments from a statement about the flag body-fold
    `lsemStraightMemF` at one start state. -/
theorem BlockSim.of_plain {seg seg' : List LinstrRM} (hp : PlainLopnBody seg)
    (hp' : PlainLopnBody seg')
    (h : ∀ (s t : LstateM) (zf : Bool), Inv s → (ck = true → SegIdxOk seg s zf) →
      lsemStraightMemF seg s = some t →
      ∃ t', lsemStraightMemF seg' s = some t' ∧ EqPc t t' ∧ Inv t) :
    BlockSim ck Inv seg seg' := by
  refine BlockSim.of_same (fun s t zf zt hI hok hr => ?_)
  rw [runStraightF_plain seg hp] at hr
  obtain ⟨b, hb, hbt⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbt
  obtain ⟨t', ht', hE, hI'⟩ := h s b zf hI hok hb
  exact ⟨t', by rw [runStraightF_plain seg' hp', ht']; rfl, hE, hI'⟩

/-- One `Lopn` kept in place is a related segment, when its step preserves `Inv`. -/
theorem BlockSim.single {i : LinstrRM}
    (hI : ∀ (s t : LstateM) (zf zt : Bool), Inv s → fstepF i s zf = some (t, zt) → Inv t) :
    BlockSim ck Inv [i] [i] := by
  refine BlockSim.of_same (fun s t zf zt hs _ hr => ⟨t, hr, rfl, ?_⟩)
  rw [runStraightF_cons] at hr
  cases hst : fstepF i s zf with
  | none => rw [hst] at hr; simp at hr
  | some bz =>
      obtain ⟨b, z⟩ := bz
      rw [hst, Option.bind_some, runStraightF_nil] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
      exact hI s b zf z hs hst

/-- A run of a segment whose steps preserve `Inv` preserves `Inv`. -/
theorem inv_runStraightF :
    ∀ (seg : List LinstrRM),
      (∀ i ∈ seg, ∀ (s t : LstateM) (zf zt : Bool), Inv s →
        fstepF i s zf = some (t, zt) → Inv t) →
      ∀ (s t : LstateM) (zf zt : Bool), Inv s → runStraightF seg s zf = some (t, zt) →
        Inv t := by
  intro seg
  induction seg with
  | nil =>
      intro _ s t zf zt hs hr
      simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact hs
  | cons i is ih =>
      intro hI s t zf zt hs hr
      rw [runStraightF_cons] at hr
      cases hst : fstepF i s zf with
      | none => rw [hst] at hr; simp at hr
      | some bz =>
          obtain ⟨b, z⟩ := bz
          rw [hst, Option.bind_some] at hr
          exact ih (fun j hj => hI j (List.mem_cons_of_mem _ hj)) b t z zt
            (hI i List.mem_cons_self s b zf z hs hst) hr

/-- A segment kept in place is a related segment, when its steps preserve `Inv`. -/
theorem BlockSim.of_steps {seg : List LinstrRM}
    (hI : ∀ i ∈ seg, ∀ (s t : LstateM) (zf zt : Bool), Inv s →
      fstepF i s zf = some (t, zt) → Inv t) :
    BlockSim ck Inv seg seg :=
  BlockSim.of_same (fun s t zf zt hs _ hr =>
    ⟨t, hr, rfl, inv_runStraightF seg hI s t zf zt hs hr⟩)

/-- Related bodies concatenate. -/
theorem BlockRel.append {A A' B B' : List LinstrRM} (hA : BlockRel ck Inv A A')
    (hB : BlockRel ck Inv B B') : BlockRel ck Inv (A ++ B) (A' ++ B') := by
  induction hA with
  | nil => exact hB
  | ctl hi _ ih => exact BlockRel.ctl hi ih
  | blk hne hlen hseg hseg' hsim _ ih =>
      rw [List.append_assoc, List.append_assoc]
      exact BlockRel.blk hne hlen hseg hseg' hsim ih

/-- A body of `KeepOK` instructions is related to itself, when the step of every `Lopn` of
    the body preserves `Inv`. -/
theorem BlockRel.of_keepOK :
    ∀ (B : List LinstrRM), (∀ i ∈ B, KeepOK i) →
      (∀ i ∈ B, IsLopn i → ∀ (s t : LstateM) (zf zt : Bool), Inv s →
        fstepF i s zf = some (t, zt) → Inv t) →
      BlockRel ck Inv B B := by
  intro B
  induction B with
  | nil => intro _ _; exact BlockRel.nil
  | cons i R ih =>
      intro h hI
      have hR := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
        (fun j hj => hI j (List.mem_cons_of_mem _ hj))
      rcases h i List.mem_cons_self with hl | hc
      · have hl1 : ∀ j ∈ [i], IsLopn j := fun j hj => by
          obtain rfl : j = i := by simpa using hj
          exact hl
        exact BlockRel.blk (seg := [i]) (seg' := [i]) (by simp) (Nat.le_refl _) hl1 hl1
          (BlockSim.single (hI i List.mem_cons_self hl)) hR
      · exact BlockRel.ctl hc hR

/-- A body of kept control instructions is related to itself. -/
theorem BlockRel.of_ctlKeep :
    ∀ (B : List LinstrRM), (∀ i ∈ B, CtlKeep i) → BlockRel ck Inv B B := by
  intro B
  induction B with
  | nil => intro _; exact BlockRel.nil
  | cons i R ih =>
      intro h
      exact BlockRel.ctl (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

/-- **The block relation of a segment-wise rewrite.** Let `g` and `g'` send each element
    of a partition to its source segment and its target segment. If every element is
    either kept, with instructions of `CtlKeep`, or a non-empty `Lopn` segment rewritten to
    an `Lopn` segment of at most the same length that simulates it, the concatenated
    bodies are related. -/
theorem BlockRel.of_segs {α : Type} (g g' : α → List LinstrRM) :
    ∀ (segs : List α),
      (∀ x ∈ segs, (g' x = g x ∧ ∀ i ∈ g x, CtlKeep i)
        ∨ (g x ≠ [] ∧ (g' x).length ≤ (g x).length ∧ (∀ i ∈ g x, IsLopn i)
            ∧ (∀ i ∈ g' x, IsLopn i) ∧ BlockSim ck Inv (g x) (g' x))) →
      BlockRel ck Inv (segs.map g).flatten (segs.map g').flatten := by
  intro segs
  induction segs with
  | nil => intro _; exact BlockRel.nil
  | cons x rest ih =>
      intro h
      have hrest := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.flatten_cons]
      rcases h x List.mem_cons_self with ⟨he, hc⟩ | ⟨hne, hlen, hl, hl', hsim⟩
      · rw [he]
        exact (BlockRel.of_ctlKeep _ hc).append hrest
      · exact BlockRel.blk hne hlen hl hl' hsim hrest

/-! ## 6. The check on a body -/

/-- The Boolean check of `KeepOK`: an `Lopn`, a label, a conditional, a goto or `Lret`. -/
def keepOKB (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn _ _ _ => true
  | .Llabel _ _ => true
  | .Lcond _ _ => true
  | .Lgoto _ => true
  | .Lret => true
  | _ => false

/-- The flag machine takes no step at `Lret`. -/
theorem evalInstrPMemF_ret_none (P : LprogM) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (LinstrR.Lret, tag) s = none := by
  rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl rfl]
  simp [evalInstrPMemL, X86Backend.AllocCheck.LcmdCFG.lsemStepMem_ret]

/-- **Soundness of the check.** -/
theorem keepOKB_sound {i : LinstrRM} (h : keepOKB i = true) : KeepOK i := by
  obtain ⟨wire, tag⟩ := i
  cases wire with
  | Lopn d o srcs => exact Or.inl ⟨d, o, srcs, rfl⟩
  | Llabel kd l => exact Or.inr (Or.inl ⟨kd, l, rfl⟩)
  | Lcond c l => exact Or.inr (Or.inr (Or.inl ⟨c, l, rfl⟩))
  | Lgoto tgt => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨tgt, rfl⟩)))
  | Lret => exact Or.inr (Or.inr (Or.inr (Or.inr (evalInstrPMemF_ret_none · tag ·))))
  | _ => simp [keepOKB] at h

/-- A control instruction that passes the check is a kept control instruction. -/
theorem ctlKeep_of_keepOKB {i : LinstrRM} (h : keepOKB i = true)
    (hn : ∀ d o srcs, i.1 ≠ LinstrR.Lopn d o srcs) : CtlKeep i := by
  rcases keepOKB_sound h with ⟨d, o, srcs, hd⟩ | hc
  · exact absurd hd (hn d o srcs)
  · exact hc

/-- An instruction of `CtlOK` is of `KeepOK`. -/
theorem keepOK_of_ctlOK {i : LinstrRM} (h : CtlOK i) : KeepOK i := by
  rcases h with hl | ⟨kd, l, hw⟩ | ⟨c, l, hw, _⟩ | ⟨tgt, hw⟩
  · exact Or.inl hl
  · exact Or.inr (Or.inl ⟨kd, l, hw⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, l, hw⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨tgt, hw⟩)))

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift

