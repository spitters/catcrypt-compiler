/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowerFuelMemF

/-!
# The frame expansion on the flag machine

The ABI export `JasminLprogExport.lfundefPhysAbiOfVirtCert` wraps the allocated, lowered body
in a frame: the prologue `buildPrologue` (the saves of `RDI`, `RSI` and the six callee-saved
registers to their `qsave.<R>` slots and the copy of `RSI` to `R14`), the saves of the further
argument registers, the argument materialisation `buildArgPtrMaterialize`, and before the
final return the restore `calleeSaveRestoreEpilogue`. Every instruction of these parts is a
register copy `MOVQ d, s`, which the flag machine `lsemFuelMemF` steps as a copy of the cell of
`s` to `d`.

This module states the frame expansion of a straight body on the flag machine: from bases
agreeing off the reload scratches and the save slots, a run of a body is matched by a run of
the framed body, whose final base agrees with the final base of the body off the scratches,
the save slots and the callee-saved registers, and holds the saved values in the callee-saved
registers.

## Main definitions

* `AgreeK`: agreement of two bases on the names of a predicate.
* `FrameSlot`, `KeptF`: the save-slot names `qsave.<R>`, and the names that are neither a
  scratch nor a save slot.
* `IsCopyQ`, `copyRunL`: a `MOVQ` register copy, and the base after a list of copies.

## Main results

* `fstepF_agreeK`, `runStraightF_agreeK`: an `Lopn` (a straight segment of them) that names
  only kept names and is no `MULX` steps from agreeing bases to agreeing bases.
* `runStraightF_copies`: a list of register copies runs to `copyRunL`.
* `buildPrologue_copies`, `calleeSaveRestoreEpilogue_copies`: the prologue and the restore are
  register copies.
* `copyRunL_buildPrologue_qsave`, `copyRunL_calleeSaveRestore`: the prologue saves each
  callee-saved register to its slot, and the restore loads it back.
* `frame_runStraightF`: the frame expansion of a straight body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FrameFuelMemF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (renRM_id emptyP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

/-! ## 1. Agreement on a set of names -/

/-- Two bases agree on the register and array names of `K`, on the word memory and on the
    carry and overflow flags. -/
structure AgreeK (K : String → Prop) (s s' : LstateM) : Prop where
  /-- The registers agree on `K`. -/
  reg : ∀ r, K r → s'.reg.lvm r = s.reg.lvm r
  /-- The arrays agree on `K`. -/
  arr : ∀ r, K r → s'.larr r = s.larr r
  /-- The word memories agree. -/
  mem : s'.lmem = s.lmem
  /-- The carry flags agree. -/
  cf : s'.cf = s.cf
  /-- The overflow flags agree. -/
  of : s'.of = s.of

/-- Agreement on `K` is reflexive. -/
theorem AgreeK.refl (K : String → Prop) (s : LstateM) : AgreeK K s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Agreement on `K` is transitive. -/
theorem AgreeK.trans {K : String → Prop} {a b c : LstateM} (h1 : AgreeK K a b)
    (h2 : AgreeK K b c) : AgreeK K a c :=
  ⟨fun r hr => (h2.reg r hr).trans (h1.reg r hr), fun r hr => (h2.arr r hr).trans (h1.arr r hr),
    h2.mem.trans h1.mem, h2.cf.trans h1.cf, h2.of.trans h1.of⟩

/-- Agreement on `K` gives agreement on every smaller predicate. -/
theorem AgreeK.mono {K K' : String → Prop} {a b : LstateM} (h : AgreeK K a b)
    (hK : ∀ r, K' r → K r) : AgreeK K' a b :=
  ⟨fun r hr => h.reg r (hK r hr), fun r hr => h.arr r (hK r hr), h.mem, h.cf, h.of⟩

/-- **A step from bases agreeing on `K`.** An `Lopn` that names only names of `K` and is no
    `MULX` steps from bases agreeing on `K` to bases agreeing on `K`, with the same zero flag,
    when the empty name lies in `K`. -/
theorem fstepF_agreeK {K : String → Prop} (hK : K "") {i : LinstrRM} (hl : IsLopn i)
    (hn : ∀ n ∈ instrNames i.1, K n) (hm : mulxFree i = true) {s s' t : LstateM}
    {zf zt : Bool} (hA : AgreeK K s s') (h : fstepF i s zf = some (t, zt)) :
    ∃ t', fstepF i s' zf = some (t', zt) ∧ AgreeK K t t' := by
  let S : LstateMF := { prog := { base := s, lfn := "" }, zf := zf }
  let S' : LstateMF := { prog := { base := s'.setLpc s.lpc, lfn := "" }, zf := zf }
  have hR : RelF id K S S' :=
    ⟨⟨⟨rfl, fun r hr => hA.reg r hr⟩, fun r hr => hA.arr r hr, hA.mem⟩, rfl, rfl, hA.cf,
      hA.of⟩
  have hc : CondOK i := ⟨fun c l he => (by
    obtain ⟨d, o, s0, hd⟩ := hl; rw [hd] at he; cases he), hm⟩
  have he : evalInstrPMemF emptyP i S
      = some { prog := { base := t, lfn := "" }, zf := zt } := by
    rw [evalInstrPMemF_isLopn _ i S hl]
    change (fstepF i s zf).map _ = _
    rw [h]; rfl
  have hσ : RenOn id K := ⟨fun _ _ _ _ h => h, hK, rfl⟩
  have hP : RenProg id K 0 emptyP emptyP :=
    ⟨rfl, fun _ => rfl, fun k _ => by simp [emptyP], fun k i _ h => by simp [emptyP] at h,
      fun k i _ h => by simp [emptyP] at h, fun l pc h => by simp⟩
  obtain ⟨T', hT', hRT, -⟩ := evalInstrPMemF_ren hσ hP i hn hc hR (Nat.zero_le _) he
  rw [renRM_id, evalInstrPMemF_isLopn _ i S' hl] at hT'
  obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp hT'
  have hb' : fstepF i (s'.setLpc s.lpc) zf = some bz := hb
  rw [fstepF_setLpc] at hb'
  obtain ⟨⟨t'', z''⟩, h'', hbz⟩ := Option.map_eq_some_iff.mp hb'
  subst hbz
  obtain ⟨⟨⟨-, hreg⟩, harr, hmem⟩, -, hzf, hcf, hof⟩ := hRT
  refine ⟨t'', ?_, ⟨fun r hr => hreg r hr, fun r hr => harr r hr, hmem, hcf, hof⟩⟩
  rw [h'']
  simp only at hzf
  rw [hzf]

/-- **A straight segment from bases agreeing on `K`.** -/
theorem runStraightF_agreeK {K : String → Prop} (hK : K "") :
    ∀ (B : List LinstrRM), (∀ i ∈ B, IsLopn i) → (∀ i ∈ B, ∀ n ∈ instrNames i.1, K n) →
      (∀ i ∈ B, mulxFree i = true) → ∀ {s s' t : LstateM} {zf zt : Bool}, AgreeK K s s' →
      runStraightF B s zf = some (t, zt) →
      ∃ t', runStraightF B s' zf = some (t', zt) ∧ AgreeK K t t' := by
  intro B
  induction B with
  | nil =>
      intro _ _ _ s s' t zf zt hA h
      simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s', rfl, hA⟩
  | cons i B ih =>
      intro hl hn hm s s' t zf zt hA h
      rw [runStraightF_cons] at h
      obtain ⟨⟨u, zu⟩, hu, hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨u', hu', hAu⟩ := fstepF_agreeK hK (hl i (List.mem_cons_self ..))
        (hn i (List.mem_cons_self ..)) (hm i (List.mem_cons_self ..)) hA hu
      obtain ⟨t', ht', hAt⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
        (fun j hj => hn j (List.mem_cons_of_mem _ hj))
        (fun j hj => hm j (List.mem_cons_of_mem _ hj)) hAu hr
      exact ⟨t', by rw [runStraightF_cons, hu', Option.bind_some]; exact ht', hAt⟩

/-- A straight segment leaves every register and array name that none of its instructions
    names. -/
theorem runStraightF_frame : ∀ (B : List LinstrRM) {s t : LstateM} {zf zt : Bool} {r : String},
    (∀ i ∈ B, r ∉ instrNames i.1) → runStraightF B s zf = some (t, zt) →
      t.reg.lvm r = s.reg.lvm r ∧ t.larr r = s.larr r := by
  intro B
  induction B with
  | nil =>
      intro s t zf zt r _ h
      simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | cons i B ih =>
      intro s t zf zt r hr h
      rw [runStraightF_cons] at h
      obtain ⟨⟨u, zu⟩, hu, hrun⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨h1, h2⟩ := JasminLsemStepFrame.fstepF_frame hu (hr i (List.mem_cons_self ..))
      obtain ⟨h3, h4⟩ := ih (fun j hj => hr j (List.mem_cons_of_mem _ hj)) hrun
      exact ⟨h3.trans h1, h4.trans h2⟩

/-! ## 2. Register copies -/

/-- A `MOVQ` register copy. -/
def IsCopyQ (i : LinstrR) : Prop := ∃ d s, i = .Lopn [.reg d] "MOVQ" [.reg s]

/-- The base after the register copy of the cell of `s` to `d`. -/
def copyStep (a : LstateM) (d s : String) : LstateM := (a.setReg d (a.reg.lvm s).2).nextPc

/-- The base after a list of register copies; an instruction that is no register copy ends
    the list. -/
def copyRunL : Lcmd → LstateM → LstateM
  | [], a => a
  | i :: l, a =>
      match i.li_i with
      | .Lopn [.reg d] _ [.reg s] => copyRunL l (copyStep a d s)
      | _ => a

/-- **A list of register copies runs to `copyRunL`**, under every tag function, with the
    zero flag unchanged. -/
theorem runStraightF_copies (tg : LinstrR → MemTag) :
    ∀ (l : Lcmd), (∀ i ∈ l, IsCopyQ i.li_i) → ∀ (a : LstateM) (zf : Bool),
      runStraightF (l.map fun i => (i.li_i, tg i.li_i)) a zf = some (copyRunL l a, zf) := by
  intro l
  induction l with
  | nil => intro _ a zf; rfl
  | cons i l ih =>
      intro hc a zf
      obtain ⟨d, s, hds⟩ := hc i (List.mem_cons_self ..)
      obtain ⟨ii, w⟩ := i
      simp only at hds
      subst hds
      rw [List.map_cons, runStraightF_cons, fstepF_copyWire d s "MOVQ" _ (Or.inr rfl),
        Option.bind_some]
      exact ih (fun j hj => hc j (List.mem_cons_of_mem _ hj)) _ _

/-- The destinations of a list of register copies. -/
def copyDsts (l : Lcmd) : List String :=
  l.flatMap fun i => match i.li_i with
    | .Lopn [.reg d] _ [.reg _] => [d]
    | _ => []

/-- A list of register copies leaves every register that is none of its destinations. -/
theorem copyRunL_lvm_of_not_mem : ∀ (l : Lcmd) (a : LstateM) {r : String},
    r ∉ copyDsts l → (copyRunL l a).reg.lvm r = a.reg.lvm r := by
  intro l
  induction l with
  | nil => intro a r _; rfl
  | cons i l ih =>
      intro a r hr
      unfold copyRunL
      split
      · rename_i d _ s hw
        have h1 : r ∉ copyDsts l := fun h => hr (by
          simp only [copyDsts, List.flatMap_cons, List.mem_append]
          exact Or.inr h)
        have h2 : r ≠ d := fun e => hr (by simp [copyDsts, hw, e])
        rw [ih _ h1]
        exact lvm_copy_other a s h2
      · rfl

/-- A list of register copies leaves the arrays, the word memory and the flags. -/
theorem copyRunL_frame : ∀ (l : Lcmd) (a : LstateM),
    (copyRunL l a).larr = a.larr ∧ (copyRunL l a).lmem = a.lmem ∧ (copyRunL l a).cf = a.cf
      ∧ (copyRunL l a).of = a.of := by
  intro l
  induction l with
  | nil => intro a; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons i l ih =>
      intro a
      unfold copyRunL
      split
      · rename_i d _ s _
        obtain ⟨h1, h2, h3, h4⟩ := ih (copyStep a d s)
        exact ⟨h1, h2, h3, h4⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 3. Save slots, the prologue and the restore -/

/-- A save-slot name `qsave.<R>`. -/
def FrameSlot (r : String) : Prop := ∃ x, r = "qsave." ++ x

/-- A name that is neither a reload scratch nor a save slot. -/
def KeptF (r : String) : Prop := KeptS r ∧ ¬ FrameSlot r

/-- The empty name is kept. -/
theorem keptF_empty : KeptF "" := by
  refine ⟨LowerFuelMemF.keptS_empty, ?_⟩
  rintro ⟨x, hx⟩
  have := congrArg String.length hx
  rw [String.length_append, show "qsave.".length = 6 from rfl] at this
  simp_all

/-- The six callee-saved registers the prologue saves and the restore loads back. -/
def calleeSaved6 : List String := ["RBX", "RBP", "R12", "R13", "R14", "R15"]

/-- The prologue is a list of register copies. -/
theorem buildPrologue_copies (v : Lfundef) (tbl : Array Nat) (m : InLoadMap) :
    ∀ i ∈ buildPrologue v tbl m, IsCopyQ i.li_i := by
  simp [buildPrologue, IsCopyQ]

/-- The restore of the callee-saved registers is a list of register copies. -/
theorem calleeSaveRestoreEpilogue_copies : ∀ i ∈ calleeSaveRestoreEpilogue, IsCopyQ i.li_i := by
  simp [calleeSaveRestoreEpilogue, IsCopyQ]

/-- **The prologue saves each callee-saved register to its slot.** -/
theorem copyRunL_buildPrologue_qsave (v : Lfundef) (tbl : Array Nat) (m : InLoadMap)
    (a : LstateM) {X : String} (hX : X ∈ calleeSaved6) :
    (copyRunL (buildPrologue v tbl m) a).reg.lvm ("qsave." ++ X) = a.reg.lvm X := by
  simp only [calleeSaved6, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [buildPrologue, copyRunL, copyStep, abiSaveRdiName, abiSaveRsiName, reloadScratch2,
      LstateM.setReg, LstateM.nextPc]

/-- **The restore loads each callee-saved register from its slot.** -/
theorem copyRunL_calleeSaveRestore (a : LstateM) {X : String} (hX : X ∈ calleeSaved6) :
    (copyRunL calleeSaveRestoreEpilogue a).reg.lvm X = a.reg.lvm ("qsave." ++ X) := by
  simp only [calleeSaved6, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [calleeSaveRestoreEpilogue, copyRunL, copyStep, LstateM.setReg, LstateM.nextPc]

/-- The restore writes only the callee-saved registers. -/
theorem copyDsts_calleeSaveRestore : copyDsts calleeSaveRestoreEpilogue = calleeSaved6 := by
  decide

/-- **The argument materialisation is a list of register copies.** -/
theorem buildArgPtrMaterialize_copies (v : Lfundef) (tbl : Array Nat) (abiArgs : List String)
    (m : InLoadMap) (abi : LprogIsa.IsaAbi) :
    ∀ i ∈ buildArgPtrMaterialize v tbl abiArgs m abi, IsCopyQ i.li_i := by
  intro i hi
  simp only [buildArgPtrMaterialize, List.mem_flatMap] at hi
  obtain ⟨p, -, hi⟩ := hi
  unfold IsCopyQ
  grind

/-- Agreement off the scratches gives agreement on the kept names. -/
theorem AgreeS.agreeK {s s' : LstateM} (h : AgreeS s s') : AgreeK KeptF s s' :=
  ⟨fun r hr => h.reg r hr.1, fun r hr => h.arr r hr.1, h.mem, h.cf, h.of⟩

/-- Agreement on the names other than the scratches is agreement off the scratches. -/
theorem AgreeK.agreeS {s s' : LstateM} (h : AgreeK KeptS s s') : AgreeS s s' :=
  ⟨h.reg, h.arr, h.mem, h.cf, h.of⟩

/-! ## 4. The frame of a straight body -/

/-- **The frame expansion of a straight body.** Let the straight body `B` name no scratch and
    no save slot and contain no `MULX`, and let `pre` (the prologue, the further saves and the
    argument materialisation) be a list of register copies. When `B` runs from a base `s`
    agreeing off the scratches and the save slots with the base after `pre` from the entry base
    `e`, the framed body `pre ++ B ++ calleeSaveRestoreEpilogue` runs from `e` with the same
    zero flag to a base that agrees with the final base of `B` on the kept names other than the
    callee-saved registers, and holds in each callee-saved register `X` the slot `qsave.X` of
    the base after `pre`. -/
theorem frame_runStraightF (tg : LinstrR → MemTag) {pre : Lcmd} {B : List LinstrRM}
    (hpre : ∀ i ∈ pre, IsCopyQ i.li_i) (hl : ∀ i ∈ B, IsLopn i)
    (hn : ∀ i ∈ B, ∀ n ∈ instrNames i.1, KeptF n) (hm : ∀ i ∈ B, mulxFree i = true)
    {e s t : LstateM} {zf zt : Bool} (hA : AgreeK KeptF s (copyRunL pre e))
    (h : runStraightF B s zf = some (t, zt)) :
    ∃ t', runStraightF ((pre.map fun i => (i.li_i, tg i.li_i)) ++ B
        ++ (calleeSaveRestoreEpilogue.map fun i => (i.li_i, tg i.li_i))) e zf = some (t', zt)
      ∧ AgreeK (fun r => KeptF r ∧ r ∉ calleeSaved6) t t'
      ∧ ∀ X ∈ calleeSaved6, t'.reg.lvm X = (copyRunL pre e).reg.lvm ("qsave." ++ X) := by
  obtain ⟨t1, ht1, hA1⟩ := runStraightF_agreeK keptF_empty B hl hn hm hA h
  obtain ⟨hla, hlm, hlc, hlo⟩ := copyRunL_frame calleeSaveRestoreEpilogue t1
  refine ⟨copyRunL calleeSaveRestoreEpilogue t1, ?_, ?_, fun X hX => ?_⟩
  · simp only [JasminLsemAddrMem.runStraightF_append, runStraightF_copies tg pre hpre,
      Option.bind_some, ht1, runStraightF_copies tg _ calleeSaveRestoreEpilogue_copies]
  · refine ⟨fun r hr => ?_, fun r hr => ?_, hlm.trans hA1.mem, hlc.trans hA1.cf,
      hlo.trans hA1.of⟩
    · rw [copyRunL_lvm_of_not_mem _ _ (by rw [copyDsts_calleeSaveRestore]; exact hr.2)]
      exact hA1.reg r hr.1
    · rw [hla]
      exact hA1.arr r hr.1
  · rw [copyRunL_calleeSaveRestore t1 hX]
    refine (runStraightF_frame B (fun i hi hm' => ?_) ht1).1
    exact (hn i hi _ hm').2 ⟨X, rfl⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.FrameFuelMemF
