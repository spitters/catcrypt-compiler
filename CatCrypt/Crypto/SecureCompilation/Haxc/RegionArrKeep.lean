/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract

/-!
# The read-only regions of a region export keep their bytes

`renImage_bytes` keeps the memory outside the stack words and outside every pointer region of
the layout. This module adds the bytes of the read-only regions, the regions other than the
region of an out result (`LinkedFnContract.isResRegion`): when no instruction of the virtual
body writes the array of a read-only region and the array is no cell array, the array holds
its entry words at the end of the virtual run, and `renImage_bytes` reads these words back
from the final memory, so each byte of the region keeps its value. A read-only region held as
cells is kept when no instruction of the image of the printed body writes a cell name of its
array: the cell names hold the entry words of the cells throughout the run of the image, and
at its halt each observed cell name holds the word of its cell.

## Main results

* `noArrWriteB`, `getArr_of_run`: the decided check that an instruction writes no array of a
  name, and the array of such a name through a halting run of the flag machine.
* `emptiedEntry_getArr`: the entry state `emptiedEntry` holds each slot array that is no cell
  array as the words of its region at entry.
* `mem_eq_of_read64_eq`, `regionWords_keep`: equal words at the cells of a region give equal
  bytes at every byte of the region.
* `regKeepB`, `lsemFuelMemF_lvm_keep`: the decided check that an instruction writes no
  register of a name, and the register of such a name through a halting run.
* `cellKeepB`, `renImage_cellKeep`: the check that no instruction of the image writes a cell
  name of a cell array, and the words of such a cell array at the halt of the decoded bytes.
* `roKeepB`, `roKeepB_spec`: the check that every read-only region is a slot array that is
  either no cell array and written by no instruction of the virtual body, or a cell array
  that passes `cellKeepB`.
* `keepRO_of_cells`, `renImage_bytes_ro`: `renImage_bytes` with the bytes of the read-only
  regions kept.
* `regionROB`, `compileRegion_spec_ro`: the check `roKeepB` on the virtual body that
  `compileRegion` computes, and the facts of `compileRegion_spec` with it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionArrKeep

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (NoArrWriteAt
  lsemFuelMemF_larr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots isArrB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC cellIdx frameC)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW (baseR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (isResRegion
  write64_read64_self)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState AMem read64 write64 InRange8)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (Loc wordsLocs frameWords regionWords)

/-! ## 1. A run that writes no array of a name keeps it -/

/-- **The array-write check of an instruction**: the instruction is no `STOREIDX`, `ZEROARR`
    or `STOREIMM` whose destination is `r`. -/
def noArrWriteB (r : String) (i : LinstrRM) : Bool :=
  (match storeStruct? i.1 with
    | some (d, _, _, _) => d != r
    | none => true)
    && (match zeroStruct? i.1 with
      | some d => d != r
      | none => true)
    && (match storeImmStruct? i.1 with
      | some (d, _, _, _) => d != r
      | none => true)

/-- An instruction that passes `noArrWriteB` at `r` writes no array named `r`. -/
theorem noArrWriteAt_of_noArrWriteB {r : String} {i : LinstrRM}
    (h : noArrWriteB r i = true) : NoArrWriteAt r i := by
  refine ⟨fun d b x v hs => ?_, fun d hs => ?_, fun d b v k hs => ?_⟩
  · simp_all [noArrWriteB]
  · simp_all [noArrWriteB]
  · simp_all [noArrWriteB]

/-- **A run that writes no array of a name keeps it.** A halting run of the flag machine on
    a body none of whose instructions writes the array `r` ends with the array `r` of its
    start state, at every shape. -/
theorem getArr_of_run {fn : String} {B : List LinstrRM} {r : String}
    (hB : B.all (noArrWriteB r) = true) {fuel : Nat} {s t : LstateMF}
    (h : lsemFuelMemF (singletonProgM fn B) fuel s = some t) (w n : Nat) :
    t.prog.base.getArr r w n = s.prog.base.getArr r w n := by
  have hl := lsemFuelMemF_larr r (singletonProgM fn B)
    (fun i hi => noArrWriteAt_of_noArrWriteB (List.all_eq_true.1 hB i hi)) fuel s t h
  unfold LstateM.getArr
  rw [hl]

/-- **The register-write check of an instruction**: the instruction is an `Lopn` none of
    whose destinations names `r`, a label, a jump or a conditional jump. -/
def regKeepB (r : String) (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn _ _ _ => !(JasminLsemStepFrame.dstNames i.1).contains r
  | .Llabel _ _ => true
  | .Lgoto _ => true
  | .Lcond _ _ => true
  | _ => false

/-- A step of the flag machine at an instruction that passes `regKeepB` at `r` keeps the
    register `r`. -/
theorem evalInstrPMemF_lvm_keep {P : JasminLsemMemLoop.LprogM} {r : String} {i : LinstrRM}
    (hk : regKeepB r i = true) {s t : LstateMF}
    (h : JasminLsemMemFlagGuard.evalInstrPMemF P i s = some t) :
    t.prog.base.reg.lvm r = s.prog.base.reg.lvm r := by
  obtain ⟨c, tag⟩ := i
  cases c with
  | Lopn ds o ss =>
      refine X86Backend.ImageAddrSim.evalInstrPMemF_lvm_of_not_dst P ⟨ds, o, ss, rfl⟩ h ?_
      simpa [regKeepB] using hk
  | Llabel k l =>
      rw [JasminLsemMemFlagNestJoin.evalInstrPMemF_label] at h
      cases h
      rfl
  | Lgoto fl =>
      obtain ⟨f, l⟩ := fl
      rw [X86Backend.CellFoldL.evalInstrPMemF_goto] at h
      split at h
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
        unfold JasminLsemMemLoop.evalJumpMem at hp
        split at hp <;> cases hp
        rfl
      · cases h
  | Lcond c l =>
      unfold JasminLsemMemFlagGuard.evalInstrPMemF at h
      simp only [JasminLsemMemFlagGuard.cmpArgs?, JasminLsemMemFlagGuard.movRegArgs?] at h
      split at h
      · split at h
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
          unfold JasminLsemMemLoop.evalJumpMem at hp
          split at hp <;> cases hp
          rfl
        · cases h
          rfl
      · split at h
        · rename_i p hp
          cases h
          simp only [JasminLsemMemFlagGuard.withALUFlags_reg]
          simp only [JasminLsemMemLoop.evalInstrPMemL] at hp
          split at hp
          · unfold JasminLsemMemLoop.evalJumpMem at hp
            split at hp <;> cases hp
            rfl
          · cases hp
            rfl
        · simp [JasminLsemMemFlagGuard.carryArgs?, JasminLsemMemFlagGuard.wideArgs?] at h
  | _ => simp [regKeepB] at hk

/-- **A run that writes no register of a name keeps it.** A halting run of the flag machine
    on a program each of whose instructions passes `regKeepB` at `r` ends with the register
    `r` of its start state. -/
theorem lsemFuelMemF_lvm_keep {r : String} (P : JasminLsemMemLoop.LprogM)
    (hP : ∀ i ∈ P.body, regKeepB r i = true) :
    ∀ (fuel : Nat) (s t : LstateMF), lsemFuelMemF P fuel s = some t →
      t.prog.base.reg.lvm r = s.prog.base.reg.lvm r := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      unfold lsemFuelMemF at h
      split at h
      · cases h; rfl
      · exact absurd h (by simp)
  | succ n ih =>
      intro s t h
      unfold lsemFuelMemF at h
      split at h
      · cases h; rfl
      · next i hf =>
          split at h
          · next s' he =>
              rw [ih s' t h]
              exact evalInstrPMemF_lvm_keep
                (hP i (JasminLsemMemFlagGuard.findInstrMem_mem P s.prog i hf)) he
          · exact absurd h (by simp)

/-! ## 2. The arrays of the entry state -/

/-- **The entry state holds each slot array as its entry words.** Under the image check
    `renImageB`, at every machine state `sa` satisfying `σ.Regions`, the entry state
    `emptiedEntry` holds, at the renamed name of each slot array `A` of length `n` that is
    no cell array, an array whose word `j` is the word of `sa` at the cell `j` of the entry
    base of `A`. -/
theorem emptiedEntry_getArr {σ : AbiLayout} {nm : String → String}
    {ps : List (String × String)} {R : Slots} {outs : List String} {body : Lcmd}
    {B : List LinstrRM} {callee : Option CalleeData}
    (hg : renImageB σ nm ps R outs body B callee = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (sa : AState)
    (hreg : σ.Regions sa) {q A : String} {n : Nat} (hq : slotArrOf σ nm q = some (A, n))
    (hA : isArrB R (renOf ps A) = false) :
    ∃ arr, (emptiedEntry σ ps R body sa).getArr (renOf ps A) 64 n = some arr
      ∧ ∀ j (hj : j < n), read64 sa.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩ := by
  obtain ⟨-, hrel, -⟩ := renImage_entry hg hU sa hreg ""
  have hq' : slotArrC R (slotRen (slotArrOf σ nm) (renOf ps)) q = some (renOf ps A, n) := by
    simp [slotArrC, slotRen, hq, hA]
  obtain ⟨arr, h1, h2⟩ := hrel.cells q (renOf ps A) n hq'
  have hun : unren ps (renOf ps A) = A := by
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some hq
    exact hU j (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨arr, h1, fun j hj => ?_⟩
  have h3 := h2 j hj
  simp only [baseR, hun] at h3
  exact h3

/-! ## 2b. The cells of a cell array without a cell store -/

/-- The cell names `memName A (8 j)`, `j < n`, of a cell array `(A, n)`. -/
def cellNamesOf (A : String) (n : Nat) : List String :=
  (List.range n).map fun j => memName A (8 * j)

/-- **The cell check of a cell array**: the printed body `body` passes the gate of its image
    simulation `regionImgB` with the cell names of `(A, n)` observed beside `outs`, and no
    instruction of the image of its cell body writes a cell name of `(A, n)` (`regKeepB`),
    at the slot map `slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))` of `renImageB`. -/
def cellKeepB (σ : AbiLayout) (nm : String → String) (ps : List (String × String))
    (R : Slots) (outs : List String) (body : Lcmd) (A : String) (n : Nat) : Bool :=
  let sl := slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))
  regionImgB sl R (outs ++ cellNamesOf A n) body
    && (virtImg sl (cellBody sl body)).all fun i => (cellNamesOf A n).all fun q => regKeepB q i

/-- **A cell array without a cell store keeps its words.** Under the image check `renImageB`
    and a halting run of the virtual body `B` from `emptiedEntry`, for a cell array `(A, n)`
    of `R` that passes `cellKeepB`, the decoded bytes of `body` halt from `sa` in a state
    whose words at the cells of the entry base of `unren ps A` are those of `sa`. The cell
    names of `(A, n)` hold the words of their cells at entry (`ImgRel.slots`), no step of the
    image writes them (`lsemFuelMemF_lvm_keep`), and at the halt of the image an observed
    cell name holds the word of its cell (`regionImg_sim`). -/
theorem renImage_cellKeep {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    (hg : renImageB σ nm ps R outs body B = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel
      { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some t)
    {A : String} {n : Nat} (hA : (A, n) ∈ R) (hk : cellKeepB σ nm ps R outs body A n = true) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∀ j, j < n → read64 sa'.mem (cellAt (abiBase (abiReg σ) sa (unren ps A)) j)
        = read64 sa.mem (cellAt (abiBase (abiReg σ) sa (unren ps A)) j) := by
  obtain ⟨hsep, hrel, hents⟩ := renImage_entry hg hU sa hreg fn
  simp only [renImageB, calleeImg_none, calleeImgB_none, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨hck, hidx⟩, hphys⟩, -⟩, hfr⟩, hent⟩, hN⟩, hlen⟩ := hg
  simp only [cellKeepB, Bool.and_eq_true, List.all_eq_true] at hk
  obtain ⟨himg, hkeep⟩ := hk
  have E := entryB_spec hent sa
  have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hN
  have hred : ∀ A j, cellIdx R (memName A (8 * j)) = some (A, j) →
      Ascent.AddrMem.Disjoint8 (X86Backend.DecodePrintedAddr.redW
        (X86Backend.DecodePrintedCFG.frameRsp body sa)) (cellAt (baseR σ sa ps A) j) := by
    intro A j hc
    obtain ⟨n, hn, hj, -⟩ := X86Backend.ImageStraightCells.cellIdx_spec hc
    have hk : X86Backend.DecodeGenMem.regK (rsOf σ) (unren ps A) j := by
      unfold X86Backend.DecodeGenMem.regK
      rw [(hlen _ hn).1]
      exact hj
    rw [redW_frameRsp]
    have h2 := X86Backend.ImageAddrFrame.frameOkB_red hfr
    exact X86Backend.DecodeGenNode.frameSep_of_regions E.rs hreg (unren ps A) j hk _ h2.1 h2.2
  have hok := X86Backend.IdxInvCheck.runIdxOk_of_idxInvCheckB hidx fn
    { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } t rfl rfl
    (hents _) fuel hrun
  have hck' := JasminLsemMemChecked.lsemFuelMemFk_of_runIdxOk true _ fuel _ t hrun hok
  obtain ⟨f', t', hr', -⟩ :=
    X86Backend.OwnedLprogTVChecked.ownedCheckMC_sound hck fn _ t rfl rfl fuel hck'
  obtain ⟨prog, sa', s', hdec, hh, -, -, hslots, -, hm', -⟩ :=
    regionImg_sim (σ := σ) (base := baseR σ sa ps) hphys himg hsep N.gp N.body hred fn f' _ t'
      rfl hrel hr'
  refine ⟨prog, sa', hdec, hh, fun j hj => ?_⟩
  have hc := X86Backend.ImageStraightCells.cellIdx_memName N.dist hA hj
  have hfc : frameC (baseR σ sa ps) R (frameE body sa) (memName A (8 * j))
      = some (cellAt (baseR σ sa ps A) j) := by
    simp only [frameC, hc]
  have hmemC : memName A (8 * j) ∈ cellNamesOf A n :=
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have hmem : memName A (8 * j) ∈ outs ++ cellNamesOf A n := List.mem_append_right _ hmemC
  have h1 := hslots _ _ hmem hfc
  have h2 := lsemFuelMemF_lvm_keep (r := memName A (8 * j)) _
    (fun i hi => hkeep i hi _ hmemC) f' _ t'
    (JasminLsemMemChecked.lsemFuelMemF_of_checked _ f' _ t' hr')
  have h3 := hrel.slots _ _ hfc
  rw [X86Backend.ImageAddrSim.frameVal_of_not_fa (not_fa_of_regionImgB himg _ hmem)] at h3
  have h4 : read64 s'.mem (cellAt (baseR σ sa ps A) j)
      = read64 sa.mem (cellAt (baseR σ sa ps A) j) := by
    have h5 := h1.symm.trans (h2.trans h3)
    simpa [entryA] using h5
  have hr := X86Backend.DecodePrintedAddr.read64_eq_of_agree hm' (hred A j hc)
  simp only [baseR] at h4 hr
  rw [← hr, h4]

/-! ## 3. Equal words give equal bytes -/

/-- Memories with equal words at `a` agree at each of the eight bytes from `a`. -/
theorem mem_eq_of_read64_eq {m m' : AMem} {a x : BitVec 64} (h : read64 m' a = read64 m a)
    (hx : InRange8 a x) : m' x = m x := by
  rw [← write64_read64_self m' a, ← write64_read64_self m a, h]
  simp only [write64, hx, ↓reduceIte]

/-- **Equal words at the cells of a region give equal bytes.** Memories with equal words at
    the cells `base + 8 j`, `j < n`, agree at every byte of `regionWords base n`. -/
theorem regionWords_keep {m m' : AMem} {base : BitVec 64} {n : Nat}
    (h : ∀ j, j < n → read64 m' (cellAt base j) = read64 m (cellAt base j)) {x : BitVec 64}
    (hx : Loc.mem x ∈ wordsLocs (regionWords base n)) : m' x = m x := by
  obtain ⟨_, ⟨k, hk, rfl⟩, y, hy, he⟩ := Set.mem_iUnion₂.1 hx
  cases he
  exact mem_eq_of_read64_eq (h k hk) hy

/-! ## 4. The check of the read-only regions -/

/-- **The read-only check** of a virtual body `B` against the printed body `body` at the
    pairs `ps`, the cell arrays `R` and the observed names `outs`: each array parameter `j`
    of `σ` whose region is not the region of an out result is the slot array `argName j` of
    its length at the slot of its register, the parameter its name denotes has its register,
    and either its renamed name is no cell array and no instruction of `B` writes the array
    of its renamed name, or its renamed name is a cell array of `R` of its length that passes
    the cell check `cellKeepB`. -/
def roKeepB (σ : AbiLayout) (nm : String → String) (ps : List (String × String)) (R : Slots)
    (outs : List String) (body : Lcmd) (B : List LinstrRM) : Bool :=
  (List.range σ.args.length).all fun j =>
    match σ.args[j]? with
    | some a =>
        match a.kind with
        | .words n =>
            isResRegion σ (a.reg, n)
              || (slotArrOf σ nm (slotOfReg (nm a.reg)) == some (argName j, n)
                && abiReg σ (argName j) == some a.reg
                && ((!isArrB R (renOf ps (argName j))
                    && B.all (noArrWriteB (renOf ps (argName j))))
                  || (R.contains (renOf ps (argName j), n)
                    && cellKeepB σ nm ps R outs body (renOf ps (argName j)) n)))
        | .scalar => true
    | none => true

/-- A read-only region of a layout that passes `roKeepB` is a slot array `A` of the region's
    length at the region's register, either no cell array and written by no instruction of
    `B`, or a cell array of `R` of the region's length that passes `cellKeepB`. -/
theorem roKeepB_spec {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    (h : roKeepB σ nm ps R outs body B = true) {p : String × Nat}
    (hp : p ∈ σ.regions) (hres : isResRegion σ p = false) :
    ∃ q A, slotArrOf σ nm q = some (A, p.2) ∧ abiReg σ A = some p.1
      ∧ ((isArrB R (renOf ps A) = false ∧ B.all (noArrWriteB (renOf ps A)) = true)
        ∨ ((renOf ps A, p.2) ∈ R ∧ cellKeepB σ nm ps R outs body (renOf ps A) p.2 = true)) := by
  obtain ⟨a, ha, hr⟩ := List.mem_filterMap.mp hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hj' : σ.args[j]? = some σ.args[j] := List.getElem?_eq_getElem hj
  have hc := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [hj'] at hc
  unfold AbiArg.region at hr
  split at hr
  · cases hr
  · rename_i n hk
    cases hr
    simp only [hk, hres, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      Bool.not_eq_true', List.contains_iff_mem] at hc
    exact ⟨_, _, hc.1.1, hc.1.2, hc.2⟩

/-! ## 5. The image on the decoded bytes with the read-only regions kept -/

/-- **The read-only regions keep their bytes.** Under the image check `renImageB`, a halting
    run of the virtual body `B` from `emptiedEntry` to `t` that passes `roKeepB`, and a final
    machine state `sa'` whose words at the cells of each slot array that is no cell array
    are the array of `t` and whose memory agrees with that of `sa` outside the stack words
    and the pointer regions: the memory of `sa'` agrees with that of `sa` outside the stack
    words and the regions of an out result. -/
theorem keepRO_of_cells {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    (hg : renImageB σ nm ps R outs body B = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (sa : AState)
    (hreg : σ.Regions sa) {fn : String} {fuel : Nat} {t : LstateMF}
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel
      { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some t)
    (hro : roKeepB σ nm ps R outs body B = true) {prog : List X86Backend.LprogBytesDecode.RInstr}
    {sa' : AState} (hdec : decodeLprog (encodeLfundefBytes body) = some prog)
    (hh : Halts aMachine prog 0 sa sa')
    (hcells : ∀ q A n, slotArrOf σ nm q = some (A, n) → isArrB R (renOf ps A) = false →
      ∃ arr, t.prog.base.getArr (renOf ps A) 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩)
    (hkeep : ∀ x, Loc.mem x ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
      (∀ p ∈ σ.regions, Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
      sa'.mem x = sa.mem x) :
    ∀ x, Loc.mem x ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
      (∀ p ∈ σ.regions, isResRegion σ p = true →
        Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
      sa'.mem x = sa.mem x := by
  intro x hxF hxR
  by_cases hin : ∃ p ∈ σ.regions, Loc.mem x ∈ wordsLocs (regionWords (sa.regs p.1) p.2)
  · obtain ⟨p, hp, hx⟩ := hin
    cases hres : isResRegion σ p
    · obtain ⟨q, A, hq, hab, hc⟩ := roKeepB_spec hro hp hres
      have hb : abiBase (abiReg σ) sa A = sa.regs p.1 := by
        simp [abiBase, hab]
      rcases hc with ⟨hA, hB⟩ | ⟨hR, hK⟩
      · obtain ⟨arr, h1, h2⟩ := hcells q A p.2 hq hA
        obtain ⟨arr0, e1, e2⟩ := emptiedEntry_getArr hg hU sa hreg hq hA
        have he : t.prog.base.getArr (renOf ps A) 64 p.2
            = (emptiedEntry σ ps R body sa).getArr (renOf ps A) 64 p.2 :=
          getArr_of_run hB hrun 64 p.2
        rw [he, e1, Option.some.injEq] at h1
        subst h1
        refine regionWords_keep (base := sa.regs p.1) (fun j hj => ?_) hx
        rw [← hb, h2 j hj, e2 j hj]
      · obtain ⟨prog', sa'', hd', hh', hw⟩ := renImage_cellKeep hg hU sa hreg fn fuel t hrun hR hK
        rw [hdec, Option.some.injEq] at hd'
        subst hd'
        obtain rfl := halts_det hh hh'
        have hun : unren ps (renOf ps A) = A := by
          obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some hq
          exact hU j (List.getElem?_eq_some_iff.mp hj).1
        rw [hun] at hw
        refine regionWords_keep (base := sa.regs p.1) (fun j hj => ?_) hx
        rw [← hb]
        exact hw j hj
    · exact absurd hx (hxR p hp hres)
  · exact hkeep x hxF fun p hp hx => hin ⟨p, hp, hx⟩

/-- **`renImage_bytes` with the read-only regions kept.** Under the hypotheses of
    `renImage_bytes` and the read-only check `roKeepB` of the virtual body, the conclusion of
    `renImage_bytes` holds with its memory clause at every byte outside the stack words and
    outside the regions of an out result. -/
theorem renImage_bytes_ro {σ : AbiLayout} {nm : String → String}
    {ps : List (String × String)} {R : Slots} {outs : List String} {body : Lcmd}
    {B : List LinstrRM} (hg : renImageB σ nm ps R outs body B = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel
      { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some t)
    (hro : roKeepB σ nm ps R outs body B = true) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (∀ q A n, slotArrOf σ nm q = some (A, n) → isArrB R (renOf ps A) = false →
        ∃ arr, t.prog.base.getArr (renOf ps A) 64 n = some arr
        ∧ ∀ j (hj : j < n),
          read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩)
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ x, Loc.mem x ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, isResRegion σ p = true →
          Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x := by
  obtain ⟨prog, sa', hd, hh, hcells, -, -, hsp, hkeep, -⟩ :=
    renImage_bytes hg hU sa hreg fn fuel t hrun
  exact ⟨prog, sa', hd, hh, hcells, hsp,
    keepRO_of_cells hg hU sa hreg hrun hro hd hh hcells hkeep⟩

/-! ## 6. The read-only check of `compileRegion` -/

/-- **The read-only check of the back half**: `roKeepB` at the pairs, the cell arrays and
    the reference of the parts `regionCoParts` that the gate of `compileRegion` computes from
    the export of the legalised program, the first body of the printed program of its
    allocation and the allocation certificate; `false` when a stage declines. -/
def regionROB (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : Bool :=
  match exportR Γ.length a.fname (legalizeRegion p) Γ.length 0,
      regionLprogC a (legalizeRegion p) none (regionWebsEx σ exportReg) with
  | some r, some (P, cert) =>
      match firstBody (printedLprog P) with
      | some b =>
          roKeepB σ exportReg (regionCoParts σ exportReg b t r.code r.res cert).ps
            (regionCoParts σ exportReg b t r.code r.res cert).cells
            ((regionCoParts σ exportReg b t r.code r.res cert).outs
              ++ (regionCoParts σ exportReg b t r.code r.res cert).cellOuts) b
            (regionCoParts σ exportReg b t r.code r.res cert).ref
      | none => false
  | _, _ => false

/-- **The facts of `compileRegion_spec` with the read-only check.** A result of
    `compileRegion σ a p` on a program that passes `regionROB` has the export, the printed
    body, the certificate and the checks of `compileRegion_spec`, and the parts of the gate
    at that body pass `roKeepB`. -/
theorem compileRegion_spec_ro {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p = some (P, bytes))
    (hro : regionROB σ a p = true) :
    regionExportableB (legalizeRegion p) = true ∧ ∃ r b cert,
      exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 = some r
      ∧ X86Backend.LprogBytes.encodeLfundefBytesChecked b = some bytes
      ∧ regionCoB σ exportReg b t r.code r.res cert = true
      ∧ regionCtB σ exportReg b t r.code r.res cert = true
      ∧ (∃ P0, regionLprogC a (legalizeRegion p) none (regionWebsEx σ exportReg)
        = some (P0, cert))
      ∧ roKeepB σ exportReg (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionCoParts σ exportReg b t r.code r.res cert).cells
          ((regionCoParts σ exportReg b t r.code r.res cert).outs
            ++ (regionCoParts σ exportReg b t r.code r.res cert).cellOuts) b
          (regionCoParts σ exportReg b t r.code r.res cert).ref = true := by
  unfold compileRegion at h
  split at h
  · rename_i hB
    split at h
    · rename_i r hr
      split at h
      · rename_i callee hc
        obtain rfl := regionCallee_nil hc
        split at h
        · rename_i P0 cert hP
          unfold regionEncode at h
          split at h
          · rename_i b hb
            split at h
            · rename_i bs hbs
              dsimp only [regionWebsAt_none] at h
              split at h
              · rename_i hg
                obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
                rw [Bool.and_eq_true] at hg
                unfold regionROB at hro
                rw [hr, hP] at hro
                simp only [hb] at hro
                refine ⟨hB, r, b, cert, hr, hbs, ?_, hg.2, ⟨P0, hP⟩, hro⟩
                rw [← regionCoB_none_fn σ exportReg b t r.code r.res cert a.fname]
                exact hg.1
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionArrKeep
