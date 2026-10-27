/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW

@[expose] public section

set_option autoImplicit false

/-!
# The cell fold with array names as registers

`CellFoldL.cellFoldL` keeps an `Lopn` that is no array access only when it names no slot
array (`ImageCellFold.keepB`). A flag-machine state has a register carrier and an array
carrier, and `ImageCellFold.CellRel` relates the register carriers at every name that is no
cell name, the names of the slot arrays included. An instruction whose tag is no array load,
store or zeroing reads and writes the register carrier, the word memory and the flags
only, so it steps alike from cell-related states when it reads and writes no cell name,
whether or not a name of a slot array occurs in it as a register. An array zeroing
`ZEROARR D, [#m, #w]` or a constant-index store `STOREIMM D, [B, V, #k]` whose array names `D`
and `B` are no slot arrays writes an array the cell relation relates and reads the
register `V`, so it steps alike under the same condition.

This module proves these steps, gives the cell fold `cellFoldLR` that keeps such an
instruction where `ImageCellFold.foldOne` refuses it, proves the fold sound on the flag
machine, and gives the image route `routeBW` over it.

## Main definitions

* `noArrB`: the tag of the instruction is no array load, store or zeroing.
* `setL`: a state with its array carrier replaced.
* `readNames`: the names a step of an instruction may read, apart from `RDX` and the empty
  name.
* `arrImmB`: an array zeroing or a constant-index store whose array names are no slot
  arrays.
* `keepRegB`: an `Lopn` without an array tag, or of `arrImmB`, that reads and writes no cell
  name.
* `foldOneR`, `foldOneLR`, `cellFoldLR`: the fold of one `Lopn`, of one instruction of a
  body, and of a body.
* `routeBW`: the check of the image route with carry chains and cells, over the fold
  `cellFoldLR` and the gate `ImageAddrSimW.imgGateBW`.

## Main results

* `fstepF_setL`: a step of an instruction without an array tag commutes with the
  replacement of the array carrier.
* `arrImm_step`: an instruction of `arrImmB` that reads no cell name steps alike from
  cell-related states.
* `keepReg_step`: an instruction of `keepRegB` steps alike from cell-related states.
* `foldR_step`: one step of `foldOneR`.
* `cellFoldLR_of_cellFoldL`: a fold by `cellFoldL` is the fold by `cellFoldLR`.
* `lsemFuelMemF_cellFoldLR`: a halting run of the body is matched, with the same fuel, by a
  run of the folded body.
* `CellFoldL.evalInstrPMemF_cellFoldL`, `CellFoldL.lsemFuelMemF_cellFoldL`: the step and the
  run for the fold `CellFoldL.cellFoldL`.
* `loop_image_bytesW`: under `routeBW`, a halting run of the node from the entry state is
  matched by a halting run of the decoded bytes of the printed body, with the output array
  in memory at its entry base.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM MemTag ArrCell
  lsemStepMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM LstatePM singletonProgM
  findInstrMem findLabelMem evalJumpMem evalInstrPMemL IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF evalInstrPMemF
  lsemFuelMemF findInstrMem_singleton flagCondCC? withALUFlags stepMemF carryStep wideStep
  CarryOp WideOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn
  fstepF fstepF_lpc_succ evalInstrPMemF_isLopn runStraightF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK shiftS
  lsemFuelMemF_of_prefix lsemFuelMemF_prepend)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (isLabel findLabel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames fstepF_frame_dst)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames cellBase readsI MAgree
  ORel FStep fstepF_congr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf
  movesOf_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseOKL fuseLoPre)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64 Disjoint8)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes cmovRedZone)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen regK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (rsOK abiBase abiReg
  frameSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (abiEntryM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI frameOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW imgGateBW_congr
  retOutsB retOutsB_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop (virt_bytesC')
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots KEnv isArrB isCellB keepB
  foldOne kstep slotsOkB cellsDistinctB CellRel keep_step fold_step stepEnv isCellB_cell
  isArrB_mem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW

/-! ## 1. Steps that do not read the array carrier -/

/-- The tag of the instruction is no array load, no array store and no array zeroing. -/
def noArrB (i : LinstrRM) : Bool :=
  match i.2 with
  | .load _ _ => false
  | .store _ _ => false
  | .zero _ _ => false
  | .storeImm _ _ => false
  | _ => true

theorem noStoreB_of_noArrB {i : LinstrRM} (h : noArrB i = true) : noStoreB i = true := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> first | rfl | cases h

/-- The state `s` with the array carrier `L`. -/
abbrev setL (L : String → ArrCell) (s : LstateM) : LstateM := { s with larr := L }

theorem withALUFlags_setL (i : LinstrRM) (L : String → ArrCell) (s0 s1 : LstateM) :
    withALUFlags i (setL L s0) (setL L s1) = setL L (withALUFlags i s0 s1) := by
  unfold withALUFlags
  dsimp only [setL]
  split
  · split <;> rfl
  · rfl

theorem carryStep_setL (op : CarryOp) (d : String) (a b : LOperand) (L : String → ArrCell)
    (s : LstateM) : carryStep op d a b (setL L s) = (carryStep op d a b s).map (setL L) := by
  unfold carryStep
  dsimp only [setL]
  split
  · cases op <;> rfl
  · rfl

theorem wideStep_setL (w : WideOp) (L : String → ArrCell) (s : LstateM) :
    wideStep w (setL L s) = (wideStep w s).map (setL L) := by
  unfold wideStep
  dsimp only [setL]
  cases w with
  | mov d b => dsimp only; split <;> rfl
  | mulx lo hi b => dsimp only; split <;> rfl

theorem lsemStepMem_setL {i : LinstrRM} (hi : noArrB i = true) (L : String → ArrCell)
    (s : LstateM) : lsemStepMem i (setL L s) = (lsemStepMem i s).map (setL L) := by
  obtain ⟨w, tag⟩ := i
  unfold lsemStepMem
  cases tag with
  | load _ _ => cases hi
  | store _ _ => cases hi
  | zero _ _ => cases hi
  | storeImm _ _ => cases hi
  | loadC => dsimp only [setL]; split <;> rfl
  | storeC =>
      dsimp only [setL]
      split
      · split <;> rfl
      · rfl
  | reg c =>
      dsimp only [setL]
      cases JasminLsemCast.lsemStepCast (w, c) s.reg <;> rfl

theorem stepMemF_setL {i : LinstrRM} (hi : noArrB i = true) (L : String → ArrCell)
    (s : LstateM) : stepMemF i (setL L s) = (stepMemF i s).map (setL L) := by
  unfold stepMemF
  rw [lsemStepMem_setL hi]
  cases lsemStepMem i s with
  | some b => exact congrArg some (withALUFlags_setL i L s b)
  | none =>
      dsimp only [Option.map_none]
      split
      · exact carryStep_setL _ _ _ _ L s
      · split
        · exact wideStep_setL _ L s
        · rfl

/-- **A step of an instruction without an array tag commutes with the replacement of the
    array carrier.** -/
theorem fstepF_setL {i : LinstrRM} (hi : noArrB i = true) (L : String → ArrCell)
    (s : LstateM) (zf : Bool) :
    fstepF i (setL L s) zf = (fstepF i s zf).map (fun p => (setL L p.1, p.2)) := by
  unfold fstepF
  split
  · dsimp only [setL]
    split <;> rfl
  · split
    · dsimp only [setL]
      split <;> rfl
    · rw [stepMemF_setL hi]
      cases stepMemF i s <;> rfl

/-! ## 2. The kept instructions that name slot arrays as registers -/

/-- The names a step of the instruction may read, apart from `RDX` and the empty name: the
    names of its source operands and the base registers of its cell operands. -/
def readNames : LinstrR → List String
  | .Lopn ds _ ss => ss.flatMap srcNames ++ (ds ++ ss).filterMap cellBase
  | _ => []

/-- The array zeroing `ZEROARR D, [#m, #w]` at a zeroing tag and the constant-index store
    `STOREIMM D, [B, V, #k]` at a constant-index store tag, whose array names `D` and `B` are
    no slot arrays. -/
def arrImmB (R : Slots) : LinstrRM → Bool
  | (.Lopn [.reg d] o [.imm _, .imm _], .zero _ _) => o == "ZEROARR" && !isArrB R d
  | (.Lopn [.reg d] o [.reg b, .reg _, .imm _], .storeImm _ _) =>
      o == "STOREIMM" && !isArrB R d && !isArrB R b
  | _ => false

/-- The step of the array zeroing `ZEROARR D, [#m, #w']` at the tag `.zero w n`. -/
theorem fstepF_zeroArr (d : String) (m w' w n : Nat) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] "ZEROARR" [.imm m, .imm w'], .zero w n) s zf
      = some ((s.setArr d (fun _ : Fin n => (0 : BitVec w))).nextPc, zf) := by
  simp (config := { decide := true }) [fstepF, JasminLsemMemFlagGuard.cmpArgs?,
    JasminLsemMemFlagGuard.movRegArgs?, stepMemF, JasminLsemMem.lsemStepMem,
    JasminLsemMem.zeroStruct?, withALUFlags, JasminLsemMemFlagGuard.aluFlagOp?]

/-- The step of the constant-index store `STOREIMM D, [B, V, #k]` at the tag
    `.storeImm w n`. -/
theorem fstepF_storeImmArr (d b v : String) (k w n : Nat) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k], .storeImm w n) s zf
      = (s.getArr b w n).bind fun arr => (s.reg.getW v w).map fun vv =>
          ((s.setArr d (JasminDialect.stackSet arr k vv)).nextPc, zf) := by
  simp (config := { decide := true }) [fstepF, JasminLsemMemFlagGuard.cmpArgs?,
    JasminLsemMemFlagGuard.movRegArgs?, stepMemF, JasminLsemMem.lsemStepMem,
    JasminLsemMem.storeImmStruct?, withALUFlags, JasminLsemMemFlagGuard.aluFlagOp?,
    JasminLsemMemFlagGuard.carryArgs?, JasminLsemMemFlagGuard.wideArgs?]
  cases s.getArr b w n <;> cases s.reg.getW v w <;> simp

/-- Writing the same array to a name that is no slot array, and advancing the program
    counter, keeps the cell relation, under constants `env'` the written state holds. -/
theorem cellRel_setArr_nextPc {R : Slots} {env env' : KEnv} {s s' : LstateM}
    (hC : CellRel R env s s') {d : String} (hd : isArrB R d = false) {w n : Nat}
    (a : Fin n → BitVec w)
    (hE : ∀ x k, ImageCellFold.kval env' x = some k →
      ((s.setArr d a).nextPc).reg.getW x 64 = some (BitVec.ofNat 64 k)) :
    CellRel R env' ((s.setArr d a).nextPc) ((s'.setArr d a).nextPc) := by
  refine ⟨fun r hr => hC.reg r hr, ?_, fun r hr => ?_, hC.mem, hC.cf, hC.of, fun p hp => ?_, hE⟩
  · simp [LstateM.nextPc, JasminLsemWidthN.LstateN.nextPc, hC.pc]
  · by_cases hrd : r = d
    · simp [LstateM.setArr, LstateM.nextPc, hrd]
    · simp [LstateM.setArr, LstateM.nextPc, hrd, hC.arr r hr]
  · obtain ⟨arr, ha, hcl⟩ := hC.cells p hp
    have hne : p.1 ≠ d := fun he => by
      have := isArrB_mem hp
      rw [he, hd] at this
      cases this
    refine ⟨arr, ?_, fun j hj => hcl j hj⟩
    rw [ImageCellFold.getArr_congr (show ((s.setArr d a).nextPc).larr p.1 = s.larr p.1 by
      simp [LstateM.setArr, LstateM.nextPc, hne])]
    exact ha

/-- **An instruction of `arrImmB` that reads no cell name** steps alike from cell-related
    states. -/
theorem arrImm_step {R : Slots} {env : KEnv} {i : LinstrRM} (ha : arrImmB R i = true)
    (hr : ∀ r ∈ readNames i.1, isCellB R r = false) {s s' t : LstateM} {zf z : Bool}
    (hC : CellRel R env s s') (h : fstepF i s zf = some (t, z)) :
    ∃ t', fstepF i s' zf = some (t', z) ∧ CellRel R (kstep env i) t t' := by
  unfold arrImmB at ha
  split at ha
  · rename_i d o m w' w n
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ha
    obtain ⟨rfl, hd⟩ := ha
    have h0 := fstepF_zeroArr d m w' w n s zf
    rw [h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨_, fstepF_zeroArr d m w' w n s' zf,
      cellRel_setArr_nextPc hC hd _ (stepEnv h0 hC.env)⟩
  · rename_i d o b v k w n
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ha
    obtain ⟨⟨rfl, hd⟩, hb⟩ := ha
    have hv : isCellB R v = false := hr v (by simp [readNames, srcNames])
    have hgA : s'.getArr b w n = s.getArr b w n := ImageCellFold.getArr_congr (hC.arr b hb) w n
    have hgV : s'.reg.getW v w = s.reg.getW v w := by
      unfold JasminLsemWidthN.LstateN.getW
      rw [hC.reg v hv]
    have h0 := fstepF_storeImmArr d b v k w n s zf
    rw [h0] at h
    obtain ⟨arr, harr, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vv, hvv, h2⟩ := Option.map_eq_some_iff.mp h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    have hs : fstepF (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k], .storeImm w n) s zf
        = some ((s.setArr d (JasminDialect.stackSet arr k vv)).nextPc, zf) := by
      rw [h0, harr, hvv]
      rfl
    refine ⟨_, ?_, cellRel_setArr_nextPc hC hd _ (stepEnv hs hC.env)⟩
    rw [fstepF_storeImmArr, hgA, hgV, harr, hvv]
    rfl
  · cases ha

/-- An instruction kept by the fold with slot-array names as registers: an `Lopn` whose tag
    is no array load and no array store, or an instruction of `arrImmB`, that writes no cell
    name and reads no cell name, where `RDX` is no cell name. -/
def keepRegB (R : Slots) (i : LinstrRM) : Bool :=
  isLopnB i && (noArrB i || arrImmB R i) && ((dstNames i.1).all fun r => !isCellB R r)
    && ((readNames i.1).all fun r => !isCellB R r) && !isCellB R "RDX"

/-- **An instruction of `keepRegB`** steps alike from cell-related states. -/
theorem keepReg_step {R : Slots} (hR : slotsOkB R = true) {env : KEnv} {i : LinstrRM}
    (hk : keepRegB R i = true) {s s' t : LstateM} {zf z : Bool} (hC : CellRel R env s s')
    (h : fstepF i s zf = some (t, z)) :
    ∃ t', fstepF i s' zf = some (t', z) ∧ CellRel R (kstep env i) t t' := by
  simp only [keepRegB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hk
  obtain ⟨⟨⟨⟨hl, hor⟩, hd⟩, hr⟩, hrdx⟩ := hk
  by_cases ha : noArrB i = true
  swap
  · rw [Bool.eq_false_iff.2 ha, Bool.false_or] at hor
    exact arrImm_step hor hr hC h
  simp only [slotsOkB, Bool.and_eq_true, Bool.not_eq_true'] at hR
  have hreads : ∀ r, readsI i.1 r → isCellB R r = false := by
    intro r hr'
    rcases hr' with rfl | ⟨rfl, -⟩ | hm
    · exact hR.1.1.2
    · exact hrdx
    · obtain ⟨d, o, sr, hdd⟩ := isLopnB_isLopn hl
      rw [hdd] at hm
      refine hr r ?_
      rw [hdd]
      simp only [readNames, List.mem_append]
      exact hm
  have hag : MAgree (readsI i.1) s (setL s.larr s') :=
    ⟨⟨hC.pc.symm, fun r hr' => (hC.reg r (hreads r hr')).symm⟩, rfl, hC.mem.symm, hC.cf.symm,
      hC.of.symm⟩
  have hrel := fstepF_congr i hag zf
  rw [h] at hrel
  generalize hq : fstepF i (setL s.larr s') zf = q at hrel
  cases hrel with
  | @some _ q' hst =>
  obtain ⟨t'', z''⟩ := q'
  obtain ⟨⟨hN, -, hmem, hcf, hof⟩, hz⟩ := hst
  dsimp only at hN hmem hcf hof hz
  subst hz
  have hs' : fstepF i s' zf = some (setL s'.larr t'', z) := by
    have h1 := fstepF_setL ha s'.larr (setL s.larr s') zf
    rw [hq] at h1
    exact h1
  have hlt : t.larr = s.larr := fstepF_larr (noStoreB_of_noArrB ha) h
  refine ⟨_, hs', ⟨fun r hr' => ?_, hN.1.symm, fun r hr' => ?_, hmem.symm, hcf.symm, hof.symm,
    fun p hp => ?_, stepEnv h hC.env⟩⟩
  · rcases hN.2 r with h1 | ⟨h1, h2⟩
    · exact h1.symm
    · exact h2.trans ((hC.reg r hr').trans h1.symm)
  · show s'.larr r = t.larr r
    rw [hlt]
    exact hC.arr r hr'
  · obtain ⟨arr, ha', hcl⟩ := hC.cells p hp
    refine ⟨arr, ?_, fun j hj => ?_⟩
    · rw [ImageCellFold.getArr_congr (congrFun hlt p.1)]
      exact ha'
    · have hcn : memName p.1 (8 * j) ∉ dstNames i.1 := fun hm => by
        have := hd _ hm
        rw [isCellB_cell hp hj] at this
        cases this
      rw [(fstepF_frame_dst hs' hcn).1]
      exact hcl j hj

/-! ## 3. The fold -/

/-- **The fold of one `Lopn`** under the known constants `env`: the fold `foldOne`, and where
    it refuses, the instruction itself when `keepRegB` holds. -/
def foldOneR (R : Slots) (env : KEnv) (i : LinstrRM) : Option LinstrRM :=
  match foldOne R env i with
  | some i' => some i'
  | none => if keepRegB R i then some i else none

theorem foldOneR_of_foldOne {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (h : foldOne R env i = some i') : foldOneR R env i = some i' := by
  unfold foldOneR
  rw [h]

/-- A folded instruction is an `Lopn`. -/
theorem foldOneR_isLopn {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOneR R env i = some i') : isLopnB i' = true := by
  unfold foldOneR at hf
  split at hf
  · rename_i j hj
    cases hf
    exact foldOne_isLopn hj
  · split at hf
    · rename_i hk
      cases hf
      simp only [keepRegB, Bool.and_eq_true] at hk
      exact hk.1.1.1.1
    · cases hf

/-- **One step of the fold `foldOneR`.** -/
theorem foldR_step {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    {env : KEnv} {i i' : LinstrRM} (hf : foldOneR R env i = some i') {s s' t : LstateM}
    {zf z : Bool} (hC : CellRel R env s s') (h : fstepF i s zf = some (t, z)) :
    ∃ t', fstepF i' s' zf = some (t', z) ∧ CellRel R (kstep env i) t t' := by
  unfold foldOneR at hf
  split at hf
  · rename_i j hj
    cases hf
    exact fold_step hR hD hj hC h
  · split at hf
    · rename_i hk
      cases hf
      exact keepReg_step hR hk hC h
    · cases hf

/-- **The fold of one instruction of a body** under the known constants `env`: an `Lopn`
    is folded by `foldOneR`, a control instruction of `ctlB` is kept, and every other
    instruction is refused. -/
def foldOneLR (R : Slots) (env : KEnv) (i : LinstrRM) : Option LinstrRM :=
  if isLopnB i then foldOneR R env i else if ctlB i then some i else none

/-- **The cell fold of a body** from the known constants `env`, with slot-array names as
    registers. -/
def cellFoldLR (R : Slots) : KEnv → List LinstrRM → Option (List LinstrRM)
  | _, [] => some []
  | env, i :: is =>
      match foldOneLR R env i, cellFoldLR R (kstepL env i) is with
      | some i', some is' => some (i' :: is')
      | _, _ => none

theorem foldOneLR_of_foldOneL {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (h : foldOneL R env i = some i') : foldOneLR R env i = some i' := by
  unfold foldOneL at h
  unfold foldOneLR
  split
  · rename_i hl
    rw [ite_eq_left hl] at h
    exact foldOneR_of_foldOne h
  · rename_i hl
    rw [ite_eq_right hl] at h
    exact h

/-- **A fold by `cellFoldL` is the fold by `cellFoldLR`.** -/
theorem cellFoldLR_of_cellFoldL {R : Slots} :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldL R env is = some is' →
      cellFoldLR R env is = some is'
  | [], _, _, hf => by
      cases hf
      rfl
  | i :: is, env, is', hf => by
      unfold cellFoldL at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        unfold cellFoldLR
        rw [foldOneLR_of_foldOneL h1, cellFoldLR_of_cellFoldL is _ _ h2]
      · cases hf

/-- The fold of an `Lopn` is `foldOneR`; an instruction that is no `Lopn` is kept. -/
theorem foldOneLR_cases {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOneLR R env i = some i') :
    (isLopnB i = true ∧ isLopnB i' = true ∧ foldOneR R env i = some i')
      ∨ (isLopnB i = false ∧ ctlB i = true ∧ i' = i) := by
  unfold foldOneLR at hf
  split at hf
  · rename_i hl
    exact Or.inl ⟨hl, foldOneR_isLopn hf, hf⟩
  · rename_i hl
    split at hf
    · rename_i hc
      cases hf
      exact Or.inr ⟨by simpa using hl, hc, rfl⟩
    · cases hf

/-- **The fold keeps the labels.** -/
theorem isLabel_foldOneLR {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOneLR R env i = some i') (l : LLabel) : isLabel l i'.1 = isLabel l i.1 := by
  rcases foldOneLR_cases hf with ⟨h1, h2, -⟩ | ⟨-, -, rfl⟩
  · rw [isLabel_of_isLopnB h1, isLabel_of_isLopnB h2]
  · rfl

/-- **The fold keeps the length of the body.** -/
theorem cellFoldLR_length {R : Slots} :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldLR R env is = some is' →
      is'.length = is.length
  | [], _, _, hf => by
      cases hf
      rfl
  | i :: is, env, is', hf => by
      unfold cellFoldLR at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        simp only [List.length_cons, cellFoldLR_length is _ _ h2]
      · cases hf

/-- **The fold is position by position:** the instruction of the folded body at a
    position is the fold of the instruction of the body there, under the constants known
    at that position. -/
theorem cellFoldLR_getElem? {R : Slots} :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldLR R env is = some is' →
      ∀ (k : Nat) (i : LinstrRM), is[k]? = some i →
        ∃ i', is'[k]? = some i' ∧ foldOneLR R (envAt env is k) i = some i'
  | [], _, _, _, k, i, hi => by simp at hi
  | j :: is, env, is', hf, k, i, hi => by
      unfold cellFoldLR at hf
      split at hf
      · rename_i j' is'' h1 h2
        cases hf
        cases k with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨j', rfl, h1⟩
        | succ k =>
            rw [List.getElem?_cons_succ] at hi
            obtain ⟨i', hi', hfo⟩ := cellFoldLR_getElem? is _ _ h2 k i hi
            exact ⟨i', by rw [List.getElem?_cons_succ]; exact hi', by
              rw [envAt_cons_succ]; exact hfo⟩
      · cases hf

/-- **The fold keeps the label positions.** -/
theorem findLabelMem_cellFoldLR {R : Slots} (l : LLabel) :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldLR R env is = some is' →
      findLabelMem l is' = findLabelMem l is
  | [], _, _, hf => by
      cases hf
      rfl
  | i :: is, env, is', hf => by
      unfold cellFoldLR at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        have ih := findLabelMem_cellFoldLR l is _ _ h2
        unfold findLabelMem findLabel at ih ⊢
        simp only [List.map_cons, List.findIdx?_cons, isLabel_foldOneLR h1 l, ih]
      · cases hf

/-- An instruction with a fold, and its fold, are in the class `CtlOK`. -/
theorem ctlOK_of_foldOneLR {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (h : foldOneLR R env i = some i') : CtlOK i ∧ CtlOK i' := by
  rcases foldOneLR_cases h with ⟨h1, h2, -⟩ | ⟨-, hc, rfl⟩
  · exact ⟨Or.inl (isLopnB_isLopn h1), Or.inl (isLopnB_isLopn h2)⟩
  · have hi : CtlOK i' := by
      obtain ⟨w, tg⟩ := i'
      unfold ctlB at hc
      dsimp only at hc
      split at hc
      · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, Option.isSome_iff_ne_none.mp hc⟩))
      · cases hc
    exact ⟨hi, hi⟩

/-- **A body with a cell fold, and the fold, are in the class `CtlOK`.** -/
theorem ctlOK_of_cellFoldLR {R : Slots} :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldLR R env is = some is' →
      (∀ i ∈ is, CtlOK i) ∧ (∀ i ∈ is', CtlOK i)
  | [], _, _, hf => by
      cases hf
      exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  | i :: is, env, is', hf => by
      unfold cellFoldLR at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        obtain ⟨a, b⟩ := ctlOK_of_foldOneLR h1
        obtain ⟨c, d⟩ := ctlOK_of_cellFoldLR is _ _ h2
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact a
          · exact c j hj
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact b
          · exact d j hj
      · cases hf

/-! ## 4. One step and the run -/

/-- **One step of the fold of a body.** For slot arrays `R` that pass `slotsOkB` and
    `cellsDistinctB` and a body `is` whose cell fold `cellFoldLR` from the constants `e0` is
    `is'`: a step of the instruction of `is` at the program counter of `s` is matched, from
    every state `s'` cell-related to `s` under the constants known at that position, by a
    step of the instruction of `is'` at the same position, into a state cell-related under
    the constants known at the new program counter. -/
theorem evalInstrPMemF_cellFoldLR {R : Slots} (hR : slotsOkB R = true)
    (hD : cellsDistinctB R = true) {e0 : KEnv} {is is' : List LinstrRM}
    (hf : cellFoldLR R e0 is = some is') (fn : String) {i : LinstrRM} {s s' t : LstateMF}
    (hi : is[s.prog.base.lpc]? = some i)
    (hC : CellRelF R (envAt e0 is s.prog.base.lpc) s s')
    (h : evalInstrPMemF (singletonProgM fn is) i s = some t) :
    ∃ i' t', is'[s.prog.base.lpc]? = some i'
      ∧ evalInstrPMemF (singletonProgM fn is') i' s' = some t'
      ∧ CellRelF R (envAt e0 is t.prog.base.lpc) t t' := by
  obtain ⟨i', hi', hfo⟩ := cellFoldLR_getElem? is e0 is' hf _ i hi
  refine ⟨i', ?_⟩
  have hlbl := fun l => findLabelMem_cellFoldLR (R := R) l is e0 is' hf
  have hnext : envAt e0 is (s.prog.base.lpc + 1) = kstepL (envAt e0 is s.prog.base.lpc) i :=
    envAt_succ hi
  rcases foldOneLR_cases hfo with ⟨hl, hl', hfo'⟩ | ⟨hl, hc, hii⟩
  · rw [evalInstrPMemF_isLopn _ i s (isLopnB_isLopn hl)] at h
    obtain ⟨bz, hbz, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨b, z⟩ := bz
    obtain ⟨b', hb', hCb⟩ := foldR_step hR hD hfo' hC.base hbz
    refine ⟨{ prog := { s'.prog with base := b' }, zf := z }, hi', ?_, ?_, hC.lfn, rfl⟩
    · rw [evalInstrPMemF_isLopn _ i' s' (isLopnB_isLopn hl'), hC.zf, hb']
      rfl
    · have hpc : b.lpc = s.prog.base.lpc + 1 := fstepF_lpc_succ i _ b _ z hbz
      show CellRel R (envAt e0 is b.lpc) b b'
      rw [hpc, hnext, kstepL_lopn hl]
      exact hCb
  · subst hii
    obtain ⟨w, tg⟩ := i'
    unfold ctlB at hc
    dsimp only at hc
    split at hc
    · rename_i k l
      rw [evalInstrPMemF_label] at h
      cases h
      refine ⟨_, hi', evalInstrPMemF_label _ _ _ _ _, ?_, hC.lfn, hC.zf⟩
      show CellRel R (envAt e0 is (s.prog.base.nextPc).lpc) _ _
      rw [JasminLsemMemLoop.LstateM.lpc_nextPc, hnext]
      exact cellRel_nextPc (cellRel_nil hC.base)
    · rename_i tgt
      obtain ⟨f, l⟩ := tgt
      rw [evalInstrPMemF_goto] at h ⊢
      by_cases hfn : f = (singletonProgM fn is).lfn
      · rw [ite_eq_left hfn] at h
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨q', hq', hqfn, hCq⟩ := evalJumpMem_cellFoldL (e0 := e0) (fn := fn) (hlbl l)
          hC.base hC.lfn hq
        refine ⟨{ s' with prog := q' }, hi', ?_, hCq, hqfn, hC.zf⟩
        rw [ite_eq_left (show f = (singletonProgM fn is').lfn from hfn), hq']
        rfl
      · rw [ite_eq_right hfn] at h
        cases h
    · rename_i c l
      obtain ⟨⟨pol, l'⟩, hcc⟩ := Option.isSome_iff_exists.mp hc
      rw [evalInstrPMemF_flagCond _ rfl hcc] at h ⊢
      rw [hC.zf]
      split at h
      · rename_i hz
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨q', hq', hqfn, hCq⟩ := evalJumpMem_cellFoldL (e0 := e0) (fn := fn) (hlbl l')
          hC.base hC.lfn hq
        refine ⟨{ prog := q', zf := s.zf }, hi', ?_, hCq, hqfn, rfl⟩
        rw [ite_eq_left hz, hq']
        rfl
      · rename_i hz
        cases h
        refine ⟨_, hi', ite_eq_right hz, ?_, hC.lfn, rfl⟩
        show CellRel R (envAt e0 is (s.prog.base.nextPc).lpc) _ _
        rw [JasminLsemMemLoop.LstateM.lpc_nextPc, hnext]
        exact cellRel_nextPc hC.base
    · cases hc

/-- **The cell fold `cellFoldLR` of a body realises the body.** For slot arrays `R` that
    pass `slotsOkB` and `cellsDistinctB` and a body `is` whose cell fold from the constants
    `e0` is `is'`: a halting run of `is` on the flag machine from `s` is matched, with the
    same fuel, by a run of `is'` from every state `s'` cell-related to `s` under the
    constants known at the program counter of `s`, into a state cell-related to the final
    state, with the same zero flag. -/
theorem lsemFuelMemF_cellFoldLR {R : Slots} (hR : slotsOkB R = true)
    (hD : cellsDistinctB R = true) {e0 : KEnv} {is is' : List LinstrRM}
    (hf : cellFoldLR R e0 is = some is') (fn : String) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      lsemFuelMemF (singletonProgM fn is) fuel s = some t →
      ∃ t', lsemFuelMemF (singletonProgM fn is') fuel s' = some t'
        ∧ CellRelF R (envAt e0 is t.prog.base.lpc) t t' := by
  have hfetch : ∀ {s s' : LstateMF}, CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      findInstrMem (singletonProgM fn is) s.prog = none →
      findInstrMem (singletonProgM fn is') s'.prog = none := fun {s s'} hC h => by
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hC.base.pc
    by_cases hfn : s.prog.lfn = fn
    · rw [findInstrMem_singleton _ _ _ hfn] at h
      rw [findInstrMem_singleton _ _ _ (hC.lfn.trans hfn), hpc]
      rw [List.getElem?_eq_none_iff] at h ⊢
      rw [cellFoldLR_length is e0 is' hf]
      exact h
    · exact ite_eq_right fun h' => hfn (hC.lfn.symm.trans h')
  have hfetch' : ∀ {s s' : LstateMF} {i : LinstrRM},
      CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      findInstrMem (singletonProgM fn is) s.prog = some i →
      is[s.prog.base.lpc]? = some i
        ∧ ∀ i', is'[s.prog.base.lpc]? = some i' →
          findInstrMem (singletonProgM fn is') s'.prog = some i' := fun {s s' i} hC h => by
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hC.base.pc
    by_cases hfn : s.prog.lfn = fn
    · rw [findInstrMem_singleton _ _ _ hfn] at h
      refine ⟨h, fun i' hi' => ?_⟩
      rw [findInstrMem_singleton _ _ _ (hC.lfn.trans hfn), hpc]
      exact hi'
    · have hn : findInstrMem (singletonProgM fn is) s.prog = none := ite_eq_right hfn
      rw [hn] at h
      cases h
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hC h
      unfold lsemFuelMemF at h ⊢
      cases hfi : findInstrMem (singletonProgM fn is) s.prog with
      | none =>
          rw [hfi] at h
          cases h
          rw [hfetch hC hfi]
          exact ⟨s', rfl, hC⟩
      | some i =>
          rw [hfi] at h
          cases h
  | succ n ih =>
      intro s s' t hC h
      unfold lsemFuelMemF at h ⊢
      cases hfi : findInstrMem (singletonProgM fn is) s.prog with
      | none =>
          rw [hfi] at h
          cases h
          rw [hfetch hC hfi]
          exact ⟨s', rfl, hC⟩
      | some i =>
          rw [hfi] at h
          dsimp only at h
          cases hev : evalInstrPMemF (singletonProgM fn is) i s with
          | none => rw [hev] at h; cases h
          | some u =>
              rw [hev] at h
              dsimp only at h
              obtain ⟨hi, hfi'⟩ := hfetch' hC hfi
              obtain ⟨i', u', hi', hev', hCu⟩ :=
                evalInstrPMemF_cellFoldLR hR hD hf fn hi hC hev
              rw [hfi' i' hi']
              dsimp only
              rw [hev']
              exact ih hCu h

/-! ## 5. The image route over the fold -/

/-- **The check of the image route with carry chains and cells** of the node `seeds ++ loop`
    with the renaming `ps`, the fusion flag `fuse` and the output array `out` of `m` words,
    against the printed body `body`. With the renamed cell arrays `cellArrsR σ ps`, the slot
    map `slotR`, the cell body of `body` and the cells of the renamed output array as
    observed names: the renamed loop has a cell fold `L2` by `cellFoldLR`; the register
    allocation check of the virtual body `virtBW` against the image of the cell body; the
    bounds invariant of the virtual body; the W class of printed bodies; the image class; the
    gate with carry chains `ImageAddrSimW.imgGateBW` with no observed name in its width
    analysis at the return; the frame, entry and renaming checks; the cell frames; no slot
    name in a cell move; the cell names; the cell arrays regions at their lengths; the seeds
    kept instructions; no source or target of the renaming a cell name; when `fuse` holds,
    the fusion check of the prefix and the folded loop and no observed name `R15`; and the
    output array a name of the loop. -/
def routeBW (σ : AbiLayout) (nm : String → String) (body : Lcmd) (seeds loop : List LinstrRM)
    (ps : List (String × String)) (fuse : Bool) (out : String) (m : Nat) : Bool :=
  match cellFoldLR (cellArrsR σ ps) [] (loop.map (renRM (renOf ps))) with
  | some L2 =>
      ownedCheckMC (outCells (renOf ps out) m) (virtBW σ nm seeds ps L2 fuse)
          (virtImg (slotR σ nm ps) (cellBody (slotR σ nm ps) body))
        && idxInvCheckB (boundFacts σ nm)
          (idxAnnot (boundFacts σ nm) (virtBW σ nm seeds ps L2 fuse)) (virtBW σ nm seeds ps L2 fuse)
        && printedAddrWB body && physImgB (slotR σ nm ps) (cellBody (slotR σ nm ps) body)
        && (imgGateBW (frameMarkC (cellArrsR σ ps) body) (slotR σ nm ps)
            (cellBody (slotR σ nm ps) body)
          && retOutsB (frameMarkC (cellArrsR σ ps) body) (cellBody (slotR σ nm ps) body)
            (outCells (renOf ps out) m))
        && frameOkB σ body && entryB σ nm body && renB σ nm seeds loop ps
        && cellAccB (slotR σ nm ps) (cellArrsR σ ps) body && cellNoSlotB (slotR σ nm ps) body
        && cellNamesRB (cellArrsR σ ps) σ body
        && (cellArrsR σ ps).all (fun p => regLen (rsOf σ) (unren ps p.1) == p.2)
        && seeds.all (keepB (cellArrsR σ ps))
        && ps.all (fun p => !isCellB (cellArrsR σ ps) p.1 && !isCellB (cellArrsR σ ps) p.2)
        && (!fuse || (fuseOKL (fuseRegs σ nm ++ cellNames (cellArrsR σ ps))
            (fuseLoPre (argBind σ nm ++ seeds ++ movesOf ps) L2)
            (argBind σ nm ++ seeds ++ movesOf ps ++ L2)
          && (outCells (renOf ps out) m).all (· != "R15")))
        && (loopNames loop).contains out
        && (outCells (renOf ps out) m).all (fun r => !faB r)
  | none => false

/-- The facts of the entry and renaming checks behind `routeBW`. -/
theorem routeBW_checks {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    {m : Nat} (hg : routeBW σ nm body seeds loop ps fuse out m = true) :
    entryB σ nm body = true ∧ renB σ nm seeds loop ps = true := by
  unfold routeBW at hg
  split at hg
  · simp only [Bool.and_eq_true] at hg
    exact ⟨hg.1.1.1.1.1.1.1.1.1.1.2, hg.1.1.1.1.1.1.1.1.1.2⟩
  · cases hg

/-- Under the route check `routeBW`, `entryV` at the frame of the printed body is an ABI
    entry. -/
theorem routeBW_abiEntry {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    {m : Nat} (hg : routeBW σ nm body seeds loop ps fuse out m = true) (sa : AState) :
    ExportCertEntry.AbiEntryM σ sa (entryV σ (frameE body sa) sa (unren ps)) := by
  obtain ⟨hent, hren⟩ := routeBW_checks hg
  have E := entryB_spec hent sa
  exact entryV_abiEntry E.argF E.argG fun j hj => ((renB_spec hren).unr j hj).1

/-- **The node on the decoded bytes through the image route over the fold `cellFoldLR`.**
    Let the printed body `body`, the node `seeds ++ loop`, the renaming `ps`, the fusion flag
    `fuse` and the output array `out` of the slot `q` of length `m` pass `routeBW`. From
    every machine state `sa` satisfying `σ.Regions`, every halting run of the node from the
    entry state `entryV` is matched by a halting run of the decoded bytes of the printed body
    from `sa`, at the end of which the words at the entry base of `out` are the array `out`
    at the end of the run of the node. -/
theorem loop_image_bytesW {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    {m : Nat} (hg : routeBW σ nm body seeds loop ps fuse out m = true) {q : String}
    (hq : slotArrOf σ nm q = some (out, m)) (sa : AState) (hreg : σ.Regions sa) (fn : String)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
        = some t) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr, t.prog.base.getArr out 64 m = some arr
        ∧ ∀ j (hj : j < m), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa out) j) = arr ⟨j, hj⟩ := by
  unfold routeBW at hg
  split at hg
  case h_2 => cases hg
  rename_i L2 hfold
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hidx⟩, hpr⟩, hphys⟩, ⟨hgW, hro⟩⟩, hfr⟩, hent⟩, hren⟩, hacc⟩, hns⟩,
    hN⟩, hlen⟩, hkeep⟩, hpsC⟩, hfuse⟩, hout⟩, hof⟩ := hg
  have hofa : ∀ r ∈ outCells (renOf ps out) m, faB r = false := by simpa using hof
  have E := entryB_spec hent sa
  have R := renB_spec hren
  have N := cellNamesRB_spec hN
  have hunr : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j :=
    fun j hj => (R.unr j hj).2
  have hun : ∀ q A n, slotArrOf σ nm q = some (A, n) → unren ps (renOf ps A) = A := by
    intro q A n h
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
    exact hunr j (List.getElem?_eq_some_iff.mp hj).1
  have hgpN : ∀ r, gpOk r = true → cellIdx (cellArrsR σ ps) r = none := by
    intro r hr
    cases hc : cellIdx (cellArrsR σ ps) r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hfrA : ∀ j, j < σ.args.length → frameR σ sa ps body (argName j) = none := by
    intro j hj
    simp only [frameC, N.arg j hj]
    exact E.argF j hj
  have hS := E.argSrc hreg.stackIn
  have hfrR : ArgSrc σ nm (frameR σ sa ps body) sa :=
    hS.congr (fun x hx => by simp only [frameC, hgpN _ hx])
      (fun x => by simp only [frameC, cellIdx_slotOfReg])
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (un := unren ps) E.argF E.argG hS false
  have hA : ∀ b2 z2, runStraightF (argBind σ nm ++ seeds)
      (entryV σ (frameE body sa) sa (unren ps)) false = some (b2, z2) →
      ∀ r, r ∈ loopNames loop → b2.larr (renOf ps r) = b2.larr r := by
    intro b2 z2 hb2 r _
    have hl := runStraightF_larr R.store hb2
    rw [hl]
    rcases renOf_cases ps r with he | ⟨p, hp, rfl, he⟩
    · rw [he]
    · rw [he]
      show (abiEntryM σ sa).larr (unren ps p.2) = (abiEntryM σ sa).larr (unren ps p.1)
      rw [unren_target R.nd hp, unren_of_not_target fun q hq => R.ts p hp q hq]
  obtain ⟨fuel', t', hrun', harr⟩ := ImageAddrSrc.src_chain fn (argBind σ nm) seeds loop ps
    (· ∈ loopNames loop) (movesOf_isLopn _) R.lopn R.ctl R.cond R.ren R.names R.nd R.ts R.tgt
    R.fresh (entryV σ (frameE body sa) sa (unren ps)) _ false rfl hpr0 rfl hA fuel t hrun out
    hout 64 m
  have hXL := ctlOK_of_cellFoldLR _ _ _ hfold
  have hpreL : ∀ i ∈ argBind σ nm ++ seeds ++ movesOf ps, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact movesOf_isLopn _ i hi
      · exact R.lopn i hi
    · exact movesOf_isLopn _ i hi
  obtain ⟨b1, z1, tX, hb1run, hXrun, rfl⟩ :=
    strip_prefix fn _ _ hpreL hXL.1 _ false rfl fuel' t' hrun'
  obtain ⟨b1C, hb1C, hC1⟩ := cellRel_pre E hS N hunr hkeep (fun p hp => by
    have := List.all_eq_true.mp hpsC p hp
    simpa using this) hb1run
  have hCF : CellRelF (cellArrsR σ ps) []
      { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 }
      { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 } :=
    ⟨cellRel_setLpc hC1 0, rfl, rfl⟩
  obtain ⟨t2, ht2, hC2⟩ := lsemFuelMemF_cellFoldLR N.slots N.dist hfold fn fuel'
    (s := { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 })
    (s' := { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 }) hCF hXrun
  obtain ⟨t2', ht2', hSh⟩ := lsemFuelMemF_prepend fn _ L2 hpreL hXL.2 (entryC σ sa ps body) b1C
    false z1 rfl hb1C fuel' t2 ht2
  have hmem : (renOf ps out, m) ∈ cellArrsR σ ps := by
    obtain ⟨j, a, hj, hk, rfl, -⟩ := slotArrOf_some hq
    exact List.mem_map.mpr ⟨_, mem_cellArrs hj hk, rfl⟩
  obtain ⟨arr, ha, hcl⟩ := hC2.base.cells _ hmem
  have hlv2 : ∀ r, t2'.prog.base.reg.lvm r = t2.prog.base.reg.lvm r := by
    intro r
    rw [hSh.base]
    rfl
  obtain ⟨fuelB, tB, hrunB, hagB⟩ : ∃ fuelB tB, lsemFuelMemF
      (singletonProgM fn (virtBW σ nm seeds ps L2 fuse)) fuelB
        { prog := { base := entryC σ sa ps body, lfn := fn }, zf := false } = some tB
      ∧ ∀ r ∈ outCells (renOf ps out) m,
        tB.prog.base.reg.lvm r = t2'.prog.base.reg.lvm r := by
    cases fuse with
    | false => exact ⟨_, _, ht2', fun _ _ => rfl⟩
    | true =>
        simp only [Bool.true_eq_false, false_or, List.all_eq_true, bne_iff_ne, ne_eq] at hfuse
        have habiC := entryV_abiEntry (un := unren ps) (sa := sa) hfrA E.argG
          fun j hj => (R.unr j hj).1
        have hE : JasminLsemFuseMulHi.E64 (fuseRegs σ nm ++ cellNames (cellArrsR σ ps))
            (entryC σ sa ps body) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_append.mp hx with hx | hx
            · exact e64_of_abiEntryM habiC x hx
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              exact congrArg (·.1) (entryV_srcOf (un := unren ps) hfrR ha)
          · obtain ⟨⟨A, j⟩, hc⟩ := Option.isSome_iff_exists.mp (cellIdx_isSome.mpr hx)
            simp only [emptyArrs, entryV, frameC, hc]
        obtain ⟨f2, t3, -, ht3, hag, -, -⟩ :=
          JasminLsemFuseMulHi.fuseMulHi_lsemFuelMemF_pre hfuse.1 fn _ _ rfl hE _ ht2'
        exact ⟨f2, t3, ht3, fun r hr => hag.reg r (hfuse.2 r hr)⟩
  have hents := boundFacts_entryV (nm := nm) (fr := frameR σ sa ps body) (un := unren ps) hreg
    fun b hb => by
      obtain ⟨h1, h2, h3⟩ := E.bnds b hb
      refine ⟨h1, h2, ?_⟩
      simp only [frameC, hgpN _ h1]
      exact h3
  have hok := runIdxOk_of_idxInvCheckB hidx fn
    { prog := { base := entryC σ sa ps body, lfn := fn }, zf := false } tB rfl rfl (hents _) fuelB
    hrunB
  have hS0 := imgSep_slotRen (ren := renOf ps)
    (ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot
      ImageAddrRoute.slotArrOf_not_fa) hun
  have hword : ∀ q a, frameE body sa q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o := by
    intro q a ha
    obtain ⟨hq, o, ho, rfl⟩ := ImageAddrFrame.frameIn_some ha
    have := ImageAddrFrame.frameOkB_range hfr hq ho
    exact ⟨_, this.1, this.2, rfl⟩
  have hsl : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      regLen (rsOf σ) (unren ps A) = n := by
    intro q A n hq'
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hq'
    rw [hun q A0 n hq0]
    exact E.len q A0 n hq0
  have hrenS : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      renOf ps (unren ps A) = A := by
    intro q A n hq'
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hq'
    rw [hun q A0 n hq0]
  have hrenR : ∀ p ∈ cellArrsR σ ps, renOf ps (unren ps p.1) = p.1 := by
    intro p hp
    obtain ⟨j, a, hj, -, he⟩ := cellArrsR_mem hp
    rw [he, hunr j (List.getElem?_eq_some_iff.mp hj).1]
  have hRlen : ∀ p ∈ cellArrsR σ ps, regLen (rsOf σ) (unren ps p.1) = p.2 := fun p hp => by
    simpa using List.all_eq_true.mp hlen p hp
  have hslC : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      cellIdx (cellArrsR σ ps) q = none := by
    intro q A n hq'
    obtain ⟨A0, hq0, -⟩ := slotRen_some hq'
    obtain ⟨a, ha⟩ := E.slot q A0 n hq0
    exact N.body q (ImageAddrFrame.frameIn_some ha).1
  have hsep := imgSep_cellsU (ren := renOf ps) E.rs hreg hS0 hword hsl hRlen hrenR hrenS N.gp
    hslC
  have hred : ∀ A j, cellIdx (cellArrsR σ ps) (memName A (8 * j)) = some (A, j) →
      Disjoint8 (redW (frameRsp body sa)) (cellAt (baseR σ sa ps A) j) := by
    intro A j hc
    obtain ⟨n, hn, hj, -⟩ := cellIdx_spec hc
    have hk : regK (rsOf σ) (unren ps A) j := by
      unfold regK
      rw [hRlen _ hn]
      exact hj
    have hr : redW (frameRsp body sa)
        = sa.regs "%rsp" + BitVec.ofInt 64 (cmovRedZone - (Params.ofBody body).frame) := by
      simp only [redW, frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
      congr 2
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hr]
    have h2 := ImageAddrFrame.frameOkB_red hfr
    exact frameSep_of_regions E.rs hreg (unren ps A) j hk _ h2.1 h2.2
  have hF := cellFrames_of (base := baseR σ sa ps) (rsp := frameRsp body sa) hacc N.gp
    (fun r hr => hS0.gp r hr) hred
  have hgate' : imgGateBW (frameR σ sa ps body) (slotR σ nm ps)
      (cellBody (slotR σ nm ps) body) = true := by
    rw [imgGateBW_congr (frame' := frameMarkC (cellArrsR σ ps) body) (frameC_isSome _ _ body sa)]
    exact hgW
  have hro' : retOutsB (frameR σ sa ps body) (cellBody (slotR σ nm ps) body)
      (outCells (renOf ps out) m) = true := by
    rw [retOutsB_congr (frame' := frameMarkC (cellArrsR σ ps) body) (frameC_isSome _ _ body sa)]
    exact hro
  have hfr' : ∀ q ∈ bodyNamesI body,
      frameR σ sa ps body q = frameP (Params.ofBody body) (frameRsp body sa) q := by
    intro q hq'
    simp only [frameC, N.body q hq']
    show ImageAddrFrame.frameIn body _ q = _
    unfold ImageAddrFrame.frameIn
    rw [ite_eq_left hq']
  have hrel0 := imgRel_entryV (nm := nm) (fr := frameR σ sa ps body) (sa := sa)
    (body := cellBody (slotR σ nm ps) body) (fn := fn) (ren := renOf ps) (un := unren ps)
    hfrR (fun _ _ hs => cellBody_save hent hs) hunr
  have hrel := imgRel_cellArrs (R := cellArrsR σ ps) hrel0
  obtain ⟨prog, sa', hdec, hh, hobs⟩ := virt_bytesC' (base := baseR σ sa ps) hck hpr hphys
    (by rw [hgate', hro']; simp) hsep (cellNoSlotB_spec hns) hF hfr' fn
    (imgStepWCond_of_gate _ hphys hgate' fn) _ _ rfl rfl (entryA σ sa) false hrel rfl
    (fun R' hR => by
      have hl : (entryA σ sa).reg.lvm R' = ⟨64, sa.regs (phys R')⟩ := by
        simp only [entryA, hR, ite_true]
      unfold LstateN.getW
      rw [hl]
      simp) rfl _ hrunB hok hofa
  refine ⟨prog, sa', hdec, hh, arr, ?_, fun j hj => ?_⟩
  · rw [← harr]
    exact ha
  · have hc := cellIdx_memName N.dist hmem hj
    have hjm : memName (renOf ps out) (8 * j) ∈ outCells (renOf ps out) m :=
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have h4 := hobs (memName (renOf ps out) (8 * j)) _ hjm (by simp only [frameC, hc])
      (hred _ j hc)
    rw [hagB _ hjm, hlv2, hcl j hj] at h4
    have hb : baseR σ sa ps (renOf ps out) = abiBase (abiReg σ) sa out := by
      show abiBase (abiReg σ) sa (unren ps (renOf ps out)) = _
      rw [hun q out m hq]
    rw [hb] at h4
    exact (eq_of_heq (Sigma.mk.inj h4).2).symm

end CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF evalInstrPMemF
  lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots KEnv slotsOkB
  cellsDistinctB)

/-! ## 6. The fold `cellFoldL` -/

/-- **One step of the fold of a body.** For slot arrays `R` that pass `slotsOkB` and
    `cellsDistinctB` and a body `is` whose cell fold from the constants `e0` is `is'`: a
    step of the instruction of `is` at the program counter of `s` is matched, from every
    state `s'` cell-related to `s` under the constants known at that position, by a step
    of the instruction of `is'` at the same position, into a state cell-related under the
    constants known at the new program counter. -/
theorem evalInstrPMemF_cellFoldL {R : Slots} (hR : slotsOkB R = true)
    (hD : cellsDistinctB R = true) {e0 : KEnv} {is is' : List LinstrRM}
    (hf : cellFoldL R e0 is = some is') (fn : String) {i : LinstrRM} {s s' t : LstateMF}
    (hi : is[s.prog.base.lpc]? = some i)
    (hC : CellRelF R (envAt e0 is s.prog.base.lpc) s s')
    (h : evalInstrPMemF (singletonProgM fn is) i s = some t) :
    ∃ i' t', is'[s.prog.base.lpc]? = some i'
      ∧ evalInstrPMemF (singletonProgM fn is') i' s' = some t'
      ∧ CellRelF R (envAt e0 is t.prog.base.lpc) t t' :=
  CellFoldLReg.evalInstrPMemF_cellFoldLR hR hD
    (CellFoldLReg.cellFoldLR_of_cellFoldL _ _ _ hf) fn hi hC h

/-- **The cell fold of a body realises the body.** For slot arrays `R` that pass
    `slotsOkB` and `cellsDistinctB` and a body `is` whose cell fold from the constants `e0`
    is `is'`: a halting run of `is` on the flag machine from `s` is matched, with the same
    fuel, by a run of `is'` from every state `s'` cell-related to `s` under the constants
    known at the program counter of `s`, into a state cell-related to the final state, with
    the same zero flag. -/
theorem lsemFuelMemF_cellFoldL {R : Slots} (hR : slotsOkB R = true)
    (hD : cellsDistinctB R = true) {e0 : KEnv} {is is' : List LinstrRM}
    (hf : cellFoldL R e0 is = some is') (fn : String) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      lsemFuelMemF (singletonProgM fn is) fuel s = some t →
      ∃ t', lsemFuelMemF (singletonProgM fn is') fuel s' = some t'
        ∧ CellRelF R (envAt e0 is t.prog.base.lpc) t t' :=
  CellFoldLReg.lsemFuelMemF_cellFoldLR hR hD (CellFoldLReg.cellFoldLR_of_cellFoldL _ _ _ hf) fn

end CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL
