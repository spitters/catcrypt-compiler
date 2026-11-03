/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt

/-!
# The side conditions of the region gate on the allocated function

`RegionPhysImgGate.regionCoStage_ne_physImgB` takes the side conditions `physImgSideB` of the
passes of the printer on the allocated function `regionAllocFn` of the region route. This
module proves the conjuncts of `physImgSideB` that follow from the shape of that function on
the domain of `RegionPhysImgArg.physImgB_regionExport_words`, and states the corollary of the
gate under the conjuncts that remain.

The allocated body is the prologue, the argument materialization, the flat map of the
expansion `physExpand` over the allocator input body, the callee-saved restores and the
return (`PhysImgSideAlloc.lfundefPhysAbiOfVirtCert_body`). The prologue, the materialization
and the restores are `MOVQ` moves. An instruction of the allocator input other than an access
has no register-indexed operand (`idxAcc_regionAllocBody`), so its expansion has none; the
expansion of an access reloads its base into `R14` and addresses through `R14`
(`physExpand_baseR14`). The allocated registers are no array slots, so an expansion reads an
array slot only through the `MOVQ` reload of a base: no `MULXHI` (`physExpand_mulHiOk`) and
no 64-bit copy (`physExpand_copyOk`) of the expansion reads one. These facts on the allocated
body pass to the later bodies through `PhysImgSidePass`, and the dead-write elimination keeps
a sublist (`deadWriteRet_sublist`).

## Main results

* `deadWriteRet_sublist`: the dead-write elimination keeps a sublist of the body.
* `idxAcc_regionAllocBody`: the indexed operands of the allocator input body are in its
  accesses.
* `cellBaseFreeB_lfundefPhysAbiOfVirtCert`, `mulHiNoSlotB_lfundefPhysAbiOfVirtCert`,
  `copyNoSlotB_lfundefPhysAbiOfVirtCert`: no cell base, no high product and no 64-bit copy
  reading an array slot in the call-free looped physical ABI export.
* `regionAllocFn_exportHyps`: the hypotheses of the compiler lemmas on
  `lfundefPhysAbiOfVirtCert` at the allocated function of the region route.
* `sideAlloc_regionAllocFn`: the conditions of the fusion and the fold on the allocated
  function of the region route.
* `physImgSideB_of_export`: `physImgSideB` on the allocated function from the optimizer
  condition on the straight runs, the holder condition of the load CSE, the condition
  `noScratchBaseB` before the compare reload and the tied flag compares of the allocated
  body.
* `regionCoStage_ne_physImgB_of_open`: `RegionPhysImgGate.regionCoStage_ne_physImgB` under
  those conditions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSide

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit (isAccB sibNameSpill_reloadScratch2)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc (noIdxB idxFreeB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt (GoodOp physExpand_forall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (CellOk cellBaseFreeB_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (cellBaseFreeB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse (fuseSiteOkB homeOkB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt (optSideB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (copyNoSlotB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint (flagTiedB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (splitStraightRuns)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (twoAddrBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiBody isMulHiMnem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse (mulHiSiteB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (mulHiNoSlotB memMovFreeB
  copyNoSlotB_postOpt cellBaseFreeB_postOpt flagTiedB_reallocStage cellBaseFreeB_printedChain)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp (noScratchBaseB
  cmpScratchFreeB_of_baseNoScratch)
open RegionPhysImgGate
open RegionPhysImgArg (AccCode renArr_lopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open RegionAllocMapAlign (regionAllocBody)

/-! ## 1. The dead-write elimination -/

/-- **The dead-write elimination `deadWriteRet` keeps a sublist of the body.** -/
theorem deadWriteRet_sublist (b : Lcmd) : (deadWriteRet b).Sublist b := by
  unfold deadWriteRet
  split
  · next r hr =>
    split
    · conv_rhs => rw [← List.dropLast_append_getLast? r hr]
      exact (X86Backend.OwnedLprogTV.dropDeadWriteBody_sublist _).append (List.Sublist.refl _)
    · exact List.Sublist.refl _
  · exact List.Sublist.refl _

/-! ## 2. Indexed operands only in the accesses -/

/-- No operand of an operation other than `LOADIDX` and `STOREIDX` is register-indexed. -/
def IdxAcc (w : LinstrR) : Prop :=
  ∀ ds o ss, w = .Lopn ds o ss → o ≠ "LOADIDX" → o ≠ "STOREIDX" →
    ∀ b y s, LOperand.arrIdx b y s ∉ ds ++ ss

theorem idxAcc_of_not_lopn {w : LinstrR} (h : ∀ ds o ss, w ≠ .Lopn ds o ss) : IdxAcc w :=
  fun ds o ss e => absurd e (h ds o ss)

theorem idxAcc_livepin (ns : List String) :
    IdxAcc (.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg)) := by
  intro ds o ss e _ _ b y s hm
  simp only [LinstrR.Lopn.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  simp at hm

theorem idxAcc_livepin_range (m : Nat) :
    IdxAcc (.Lopn [.reg "%livepin"] "LIVEPIN"
      ((List.range m).map fun j => (.reg (argName j) : LOperand))) := by
  rw [show ((List.range m).map fun j => (.reg (argName j) : LOperand)) =
    ((List.range m).map argName).map LOperand.reg by simp]
  exact idxAcc_livepin _

/-- The renaming of the array positions keeps `IdxAcc` on an instruction of the access form
    `AccCode`. -/
theorem idxAcc_renArr (ρ : String → String) {i : LinstrRM} (hc : AccCode i) :
    IdxAcc (renArr ρ i).1 := by
  intro ds' o ss' he hL hS b y s hb
  obtain ⟨ds, ss, hi, hm⟩ := renArr_lopn ρ he
  obtain ⟨b0, hb0⟩ := hm b y s hb
  exact hc.2.2 ds o ss hi hL hS b0 y s hb0

theorem idxAcc_backEdgePins {C : List LinstrRM} (h : ∀ i ∈ C, IdxAcc i.1) :
    ∀ i ∈ backEdgePins C, IdxAcc i.1 := by
  have hpin : ∀ T k l, ∀ i ∈ backEdgePin T C k l, IdxAcc i.1 := by
    intro T k l i hi
    unfold backEdgePin at hi
    dsimp only at hi
    split at hi
    · split at hi
      · rw [List.mem_singleton.mp hi]
        exact idxAcc_livepin _
      · cases hi
    · cases hi
  intro i hi
  obtain ⟨⟨j, k⟩, hjk, hi⟩ := List.mem_flatMap.mp hi
  have hj : j ∈ C := List.fst_mem_of_mem_zipIdx hjk
  dsimp only at hi
  split at hi
  all_goals first
    | (rw [List.mem_singleton.mp hi]; exact h j hj)
    | (rcases List.mem_append.mp hi with hi | hi
       · exact hpin _ _ _ i hi
       · rw [List.mem_singleton.mp hi]; exact h j hj)

theorem idxAcc_canonicalizeMemrefThread {body : Lcmd} (h : ∀ i ∈ body, IdxAcc i.li_i) :
    ∀ i ∈ canonicalizeMemrefThread body, IdxAcc i.li_i := by
  intro i hi
  unfold canonicalizeMemrefThread at hi
  dsimp only at hi
  split at hi
  · exact h i hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    split
    · rename_i ds o ss heq
      intro ds' o' ss' he hL hS b y s hb
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      rw [← List.map_append] at hb
      obtain ⟨a, ha, hae⟩ := List.mem_map.mp hb
      cases a <;> simp only [canonMemrefOperand, reduceCtorEq, LOperand.arrIdx.injEq] at hae
      exact h j hj ds o ss heq hL hS _ _ _ ha
    · exact h j hj

/-- **The indexed operands of the allocator input body are in its accesses**, at a result
    other than one register, when every instruction of the code given to the renaming has the
    access form `AccCode`. -/
theorem idxAcc_regionAllocBody (a : AbiNames) (nArgs : Nat) {ts : List JasminTy}
    (r : Exported) (hts : ∀ w, ts ≠ [.reg w])
    (hC : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, AccCode i) :
    ∀ i ∈ regionAllocBody a nArgs ts r, IdxAcc i.li_i := by
  have hac : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
      (resAliasOf none (some a.outArg) ts r.res),
      IdxAcc i.1 := by
    refine idxAcc_backEdgePins fun i hi => ?_
    rcases mem_pinSelfMoves hi with hi | ⟨t, c, z, _, _, _, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact idxAcc_renArr _ (hC j hj)
    · show IdxAcc (.Lopn [.reg t] "LIVEPIN" [.reg c, .reg z])
      intro ds o ss e _ _ b y s hm
      simp only [LinstrR.Lopn.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      simp at hm
    · show IdxAcc (.Lopn [.reg "%livepin"] "LIVEPIN" ([c, z, t].map LOperand.reg))
      exact idxAcc_livepin [c, z, t]
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · exact absurd rfl (hts _)
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact idxAcc_livepin_range _
      · cases hi
    · refine idxAcc_canonicalizeMemrefThread (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]; exact idxAcc_livepin _
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
          exact hac l hl
        · rw [List.mem_singleton.mp hj]
          exact idxAcc_of_not_lopn fun _ _ _ e => by cases e

/-- The hypothesis `hidx` of `PhysImgSideAlloc.fuseSiteOkB_lfundefPhysAbiOfVirtCert` from
    `IdxAcc`: an instruction that is no access has no register-indexed operand. -/
theorem noIdxB_of_idxAcc {w : LinstrR} (h : IdxAcc w) (hA : isAccB w = false) :
    ∀ x ∈ lopnOperands w, noIdxB x = true := by
  intro x hx
  cases w with
  | Lopn ds o ss =>
    simp only [isAccB, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hA
    cases x with
    | arrIdx b y s =>
      exact absurd hx (h ds o ss rfl (ne_of_apply_ne _ hA.1) (ne_of_apply_ne _ hA.2) b y s)
    | _ => rfl
  | _ => simp [lopnOperands] at hx

/-! ## 3. The cell bases of the export -/

/-- Every register-indexed first source of the instruction has the base `R14`
    (`reloadScratch2`). -/
def BaseR14 (r : LinstrR) : Prop :=
  ∀ ds o x y sc ss, r = .Lopn ds o (.arrIdx x y sc :: ss) → x = reloadScratch2

theorem baseR14_of_idxFree {r : LinstrR} (h : idxFreeB r = true) : BaseR14 r := by
  intro ds o x y sc ss he
  subst he
  simp [idxFreeB, noIdxB] at h

/-- The register first source of a `ZEROARR` or `STOREIMM`, if any, is `R14`. -/
def ImmBaseR14 (r : LinstrR) : Prop :=
  ∀ ds o x ss, r = .Lopn ds o (.reg x :: ss) → isArrImmB r = true → x = reloadScratch2

theorem immBaseR14_of_ne {r : LinstrR} (h : isArrImmB r = false) : ImmBaseR14 r :=
  fun _ _ _ _ _ hai => by rw [h] at hai; cases hai

theorem cellOk_of_baseR14 {j : Linstr} (h : BaseR14 j.li_i) (h2 : ImmBaseR14 j.li_i) :
    CellOk j := by
  refine ⟨fun ds o x y sc ss he => ?_, fun ds o x ss he hai => ?_⟩
  · rw [h ds o x y sc ss he]
    decide +kernel
  · rw [h2 ds o x ss he hai]
    decide +kernel

/-- The load arm on a base in `R14` has its indexed first sources at `R14`. -/
theorem baseR14_legalizeMemLoad (d : LOperand) (y opn mov : String) :
    ∀ r ∈ legalizeMemLoad d (.arrIdx reloadScratch2 y 8) opn mov, BaseR14 r := by
  intro r hr ds o x y' sc ss he
  subst he
  simp only [legalizeMemLoad, legalizeSibElem, sibNameSpill_reloadScratch2] at hr
  cases hy : sibNameSpill y <;> cases hd : d.isSpill <;>
    simp [hy, hd] at hr <;> grind

/-- The store arm on a base in `R14` has its indexed first sources at `R14`. -/
theorem baseR14_legalizeMemStoreK (kc : Option Nat) (dA : LOperand) (v y opn mov : String) :
    ∀ r ∈ legalizeMemStoreK kc dA (.arrIdx reloadScratch2 y 8) (.reg v) opn mov, BaseR14 r := by
  intro r hr ds o x y' sc ss he
  subst he
  unfold legalizeMemStoreK at hr
  split at hr
  · rename_i l hc
    unfold constIdxStore? at hc
    simp only at hc
    split_ifs at hc
    all_goals
      split at hc
      · split_ifs at hc
        cases hc
        simp at hr
      · cases hc
  · simp only [legalizeMemStore, legalizeSibElem, sibNameSpill_reloadScratch2] at hr
    cases hy : sibNameSpill y <;> cases hv : (LOperand.reg v).isSpill <;>
      simp [hy, hv] at hr <;> grind

/-- **One expansion has its indexed first sources at `R14`**: the expansion of an access
    with a reloaded base addresses through `R14`, and the expansion of an instruction that is
    no access has no indexed source. -/
theorem physExpand_baseR14 {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr)
    (hrmI : ∀ x, noIdxB x = true → noIdxB (rm x) = true)
    (hreg : ∀ n, ∃ n', rm (.reg n) = .reg n')
    (hacc : AccForm slotArr rm mbr i.li_i)
    (hidx : isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true) :
    ∀ r ∈ physExpand shiftImm u64 rm mbr i, BaseR14 r.li_i := by
  cases hA : isAccB i.li_i
  · exact fun r hr =>
      baseR14_of_idxFree (physExpand_idxFree shiftImm u64 rm mbr i hrmI (hidx hA) r hr)
  · obtain ⟨ii, w⟩ := i
    simp only at hA hacc ⊢
    cases w with
    | Lopn ds o ss =>
      have hu : X86Backend.LprogAsmPrinter.untagCaret o = "LOADIDX" ∨
          X86Backend.LprogAsmPrinter.untagCaret o = "STOREIDX" := by
        simpa [isAccB] using hA
      obtain ⟨hL, hS, -, -, hU⟩ := hacc ds o ss rfl
      have ho : o = "LOADIDX" ∨ o = "STOREIDX" := by
        rw [← hU (by tauto)]; exact hu
      rcases ho with rfl | rfl
      · obtain ⟨dn, b, y, rfl, rfl, b', y', q, hrmA, hmb, -, hfa⟩ := hL (by simp)
        obtain ⟨n', hn'⟩ := hreg dn
        simp only [physExpand_eq, isNativeShiftRotate_loadIdx, isMemLoad_loadIdx,
          Bool.false_eq_true, ite_false, ite_true, hrmA, hn', reloadMemrefBase, hmb,
          ptrLoad_qsave hfa]
        intro r hr
        simp only [List.mem_append, List.mem_map] at hr
        rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
        · simp only [List.mem_singleton] at hr'
          subst hr'
          exact baseR14_of_idxFree rfl
        · exact baseR14_legalizeMemLoad _ _ _ _ r' hr'
      · obtain ⟨dn, b, y, v, rfl, rfl, b', y', q, hrmA, hmb, -, hfa⟩ := hS (by simp)
        obtain ⟨n', hn'⟩ := hreg dn
        obtain ⟨v', hv'⟩ := hreg v
        simp only [physExpand_eq, isTwoAddrBinop_storeIdx, isMemStore_storeIdx,
          Bool.false_eq_true, ite_false, ite_true, hrmA, hn', hv', reloadMemrefBase, hmb,
          ptrLoad_qsave hfa]
        intro r hr
        simp only [List.mem_append, List.mem_map] at hr
        rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
        · simp only [List.mem_singleton] at hr'
          subst hr'
          exact baseR14_of_idxFree rfl
        · exact baseR14_legalizeMemStoreK _ _ _ _ _ _ r' hr'
    | _ => simp [isAccB] at hA

/-- **No indexed access of the call-free looped physical ABI export has a cell base**, under
    the access form `hshape` of `physImgB_lfundefPhysAbiOfVirtCert` and the hypothesis `hidx`
    of `PhysImgSideAlloc.fuseSiteOkB_lfundefPhysAbiOfVirtCert`: the prologue, the argument
    materialization and the epilogue are moves, and every expansion addresses through `R14` or
    has no indexed source. -/
theorem cellBaseFreeB_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true) :
    cellBaseFreeB (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body = true := by
  rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
    posBind body1 hb1 mbr hmbr hcf]
  have hrmE : physRmap body1 [] =
      fun o =>
        remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o := by
    simp only [physRmap, hcf, Bool.false_eq_true, ite_false]
  have hplain : ∀ j, X86Backend.PhysImgSideAlloc.PlainB j → CellOk j := fun j h =>
    cellOk_of_baseR14 (baseR14_of_idxFree h.2.1.1) (immBaseR14_of_ne h.2.1.2)
  refine cellBaseFreeB_iff.mpr fun j hj => ?_
  simp only [insertEpilogue, List.mem_append] at hj
  rcases hj with (hj | hj) | hj | (hj | hj) | hj
  · exact hplain j
      (prologue_plainB _ _ abiArgs j (List.mem_append_left (extraSaves abiArgs) hj))
  · exact hplain j (prologue_plainB virt0 #[] abiArgs j
      (List.mem_append_right (buildPrologue virt0 #[] (fun _ => none)) hj))
  · exact hplain j (buildArgPtrMaterialize_plainB _ _ _ _ j hj)
  · have hj' := List.dropLast_subset _ hj
    rw [X86Backend.PhysImgSideAlloc.reloadArrImmBody_filter_flatMap] at hj'
    obtain ⟨i, hi, hj'⟩ := List.mem_flatMap.mp hj'
    replace hj' := List.mem_of_mem_filter hj'
    rw [hrmE] at hj'
    by_cases hz : ∃ ds o ss, i.li_i = .Lopn ds o ss ∧ (o = "ZEROARR" ∨ o = "STOREIMM")
    · obtain ⟨ds, o, ss, hx, hz⟩ := hz
      obtain ⟨ii, w⟩ := i
      simp only at hx
      subst hx
      obtain ⟨b, q, -, -, ⟨n, w, he⟩ | ⟨v, v', k, -, -, he⟩ | ⟨v, v', k, -, -, he⟩⟩ :=
        X86Backend.PhysImgSideAlloc.reloadArrImmBody_physExpand_arrImm _ _ _ mbr ii ds o ss
          (hshape _ hi) hz (fun _ => rfl) (fun n => ⟨_, rfl⟩) <;>
        rw [he] at hj' <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rotate_left 2
      rcases hj' with rfl | rfl | rfl
      all_goals try rcases hj' with rfl | rfl
      all_goals
        refine cellOk_of_baseR14 (fun _ _ _ _ _ _ he' => by cases he') ?_
        first
          | (apply immBaseR14_of_ne; simp [isArrImmB]; done)
          | (intro _ _ _ _ he' _; cases he'; rfl)
    · have hne : ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM" :=
        fun ds o ss hx => not_or.mp fun hz' => hz ⟨ds, o, ss, hx, hz'⟩
      rw [X86Backend.PhysImgSideAlloc.reloadArrImmBody_physExpand_of_ne _ _ _ _ _ _ hne] at hj'
      exact cellOk_of_baseR14
        (physExpand_baseR14 _ _ _ mbr i (fun x hx => noIdxB_remapOperand _ _ hx)
          (fun n => ⟨_, rfl⟩) (hshape i hi) (hidx i hi) j hj')
        (immBaseR14_of_ne (X86Backend.PhysImgSideAlloc.physExpand_arrImmFree _ _ _ mbr i hne
          (fun ds o ss h => (hshape i hi ds o ss h).2.2.2.2) j hj'))
  · exact hplain j (epilogue_plainB j (List.mem_append_left _ hj))
  · exact hplain j (epilogue_plainB j (List.mem_append_right _ hj))

/-! ## 4. The operands of the high products of the export -/

/-- A high product `MULXHI d, [s1, s2]` of the instruction has no array slot among its
    operands. -/
def MulHiOk (slotArr : String → Option (String × Nat)) (r : LinstrR) : Prop :=
  ∀ d o s1 s2, r = .Lopn [.reg d] o [.reg s1, .reg s2] → isMulHiMnem o = true →
    slotArr d = none ∧ slotArr s1 = none ∧ slotArr s2 = none

theorem mulHiOk_of_site {slotArr : String → Option (String × Nat)} {r : Linstr}
    (h : mulHiSiteB r = false) : MulHiOk slotArr r.li_i := by
  intro d o s1 s2 he hm
  simp [mulHiSiteB, he, hm] at h

theorem mulHiOk_map {slotArr : String → Option (String × Nat)} {rm : LOperand → LOperand}
    (hrmR : ∀ x n, rm x = .reg n → slotArr n = none) (A B : List LOperand) (o : String) :
    MulHiOk slotArr (.Lopn (A.map rm) o (B.map rm)) := by
  intro d o' s1 s2 he _
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨hA, -, hB⟩ := he
  rcases A with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp at hA
  rcases B with _ | ⟨b1, _ | ⟨b2, _ | ⟨_, _⟩⟩⟩ <;> simp at hB
  exact ⟨hrmR _ _ hA, hrmR _ _ hB.1, hrmR _ _ hB.2⟩

/-- **The expansion of a high product reads no array slot**: under an operand map whose
    register images are no array slots, every high product the expansion of a `MULXHI`
    emits has its operands among those images. -/
theorem physExpand_mulHiOk {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (ii : Nat) (ds : List LOperand) (o : String)
    (ss : List LOperand) (hm : isMulHiMnem o = true)
    (hrmR : ∀ x n, rm x = .reg n → slotArr n = none) :
    ∀ r ∈ physExpand shiftImm u64 rm mbr ⟨ii, .Lopn ds o ss⟩, MulHiOk slotArr r.li_i := by
  have hs : stripWidthTag o = "MULXHI" := by simpa [isMulHiMnem] using hm
  have hb : isTwoAddrBinop o = false := by simp [isTwoAddrBinop, hs]
  have hst : isMemStore o = false := by simp [isMemStore, hs]
  have hld : isMemLoad o = false := by simp [isMemLoad, hs]
  have hc : o ≠ "CMOV:64" := fun e => by subst e; revert hs; decide
  have hse : isSetccMnem o = false := by simp [isSetccMnem, hs]
  have hmv : stripWidthTag o ≠ "MOV" := by rw [hs]; decide
  have hmq : stripWidthTag o ≠ "MOVQ" := by rw [hs]; decide
  intro r hr
  rw [physExpand_eq] at hr
  simp only at hr
  split at hr
  · rename_i d _ opn s0 s1 _ heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [hb, Bool.false_eq_true, ite_false] at hr
    split at hr
    · next _ d' opn' addr val heq' =>
      simp only [LinstrR.Lopn.injEq] at heq'
      obtain ⟨-, rfl, -⟩ := heq'
      simp only [hst, Bool.false_eq_true, ite_false, legalizeSpillDst_of_ne _ _ hc hse,
        List.map_cons, List.map_nil, List.mem_singleton] at hr
      subst hr
      exact mulHiOk_map hrmR [_] [_, _] _
    · next _ dsts opn' srcs _ heq' =>
      simp only [LinstrR.Lopn.injEq] at heq'
      obtain ⟨-, rfl, -⟩ := heq'
      simp only [legalizeSpillDst_of_ne _ _ hc hse, List.map_cons, List.map_nil,
        List.mem_singleton] at hr
      subst hr
      exact mulHiOk_map hrmR _ _ _
    · next _ _ hne =>
      exact absurd rfl (hne _ _ _)
  · rename_i d opn s heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [hld, Bool.false_eq_true, ite_false, legalizeOneSrc_of_ne _ _ hmv hmq] at hr
    intro d' o' s1 s2 he _
    split_ifs at hr
    all_goals
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      simp only at he
      subst he
      try unfold lowerNativeShiftRotate at hr'
      try split_ifs at hr'
      all_goals simp at hr'
  · rename_i dsts opn srcs _ _ heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [List.mem_singleton] at hr
    subst hr
    exact mulHiOk_map hrmR _ _ _
  · next h1 h2 h3 =>
    first
      | exact (h1 _ _ _ rfl).elim
      | exact (h2 _ _ _ rfl).elim
      | exact (h3 _ _ _ rfl).elim

theorem mulHiNoSlotB_of {slotArr : String → Option (String × Nat)} {b : Lcmd}
    (h : ∀ j ∈ b, MulHiOk slotArr j.li_i) : mulHiNoSlotB slotArr b = true := by
  refine List.all_eq_true.mpr fun j hj => ?_
  split
  · rename_i d opn s1 s2 he
    cases hm : isMulHiMnem opn
    · rfl
    · obtain ⟨h1, h2, h3⟩ := h j hj d opn s1 s2 he hm
      simp [h1, h2, h3]
  · rfl

/-- **No high product of the call-free looped physical ABI export reads an array slot**,
    under the hypotheses of `physImgB_lfundefPhysAbiOfVirtCert`: the prologue, the argument
    materialization and the epilogue are moves, the expansion of an instruction other than a
    `MULXHI` emits no high product, and the expansion of a `MULXHI` has its operands among the
    allocated registers. -/
theorem mulHiNoSlotB_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    mulHiNoSlotB slotArr (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
      abiArgs abiTyin x86Abi posBind).1.lfd_body = true := by
  rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
    posBind body1 hb1 mbr hmbr hcf]
  let rm := fun o =>
    remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o
  have hrmE : physRmap body1 [] = rm := by
    simp only [physRmap, hcf, Bool.false_eq_true, ite_false]
    rfl
  have hcall : ∀ i ∈ body1, ∀ a b, i.li_i ≠ .Lcall a b := by
    intro i hi a b he
    have := List.any_eq_false.mp hcf i hi
    rw [he] at this
    exact this rfl
  have hs15 : slotArr reloadScratch = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hs14 : slotArr reloadScratch2 = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hmem : ∀ c, slotArr ("mem." ++ c) = none := fun c =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_mem c)
  have hP : ∀ p, slotArr (physRegName p x86Abi) = none := fun p =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_physRegName p)
  have hok : ∀ i ∈ body1, ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr (rm x) := by
    intro i hi x hx
    cases x with
    | reg n => exact ⟨fun q hq => by cases hq; exact hP _, nofun, nofun⟩
    | arrIdx b y s => exact ⟨nofun, nofun, fun q j sc hq => by cases hq; exact hP _⟩
    | arr q n => exact ⟨nofun, fun q' n' hq => by cases hq; exact harr i hi q n hx, nofun⟩
    | imm _ => exact ⟨nofun, nofun, nofun⟩
  have hrmR : ∀ x n, rm x = .reg n → slotArr n = none := by
    intro x n h
    cases x with
    | reg m =>
      simp only [rm, remapOperand, LOperand.reg.injEq] at h
      subst h
      exact hP _
    | _ => simp [rm, remapOperand] at h
  have hF : ∀ i ∈ body1, ∀ j ∈ reloadArrImmBody mbr (physExpand (certShiftImm shiftImm body1)
      (X86Backend.LprogAsmPrinter.bodyIsU64 body1) rm mbr i), MulHiOk slotArr j.li_i := by
    intro i hi j hj
    have hblk : BlockOk slotArr i.li_i (reloadArrImmBody mbr (physExpand
        (certShiftImm shiftImm body1) (X86Backend.LprogAsmPrinter.bodyIsU64 body1) rm mbr i)) := by
      rw [← hrmE, ← physPositionEmit_eq_physExpand _ body1 reloadScratch2 reloadScratch2 0
        mbr [] [] i 0 (hcall i hi)]
      exact physPositionEmit_physImg _ body1 reloadScratch2 reloadScratch2 0 mbr [] [] i 0
        rm (by simp [hcf, rm]) (hcall i hi) hs15 hs14 hmem (hok i hi) (fun n => ⟨_, rfl⟩)
        (hshape i hi)
    obtain ⟨ii, w⟩ := i
    by_cases hw : ∃ ds o ss, w = .Lopn ds o ss ∧ isMulHiMnem o = true
    · obtain ⟨ds, o, ss, rfl, hm⟩ := hw
      rw [reloadArrImmBody_physExpand_of_ne _ _ _ _ _ _ fun ds' o' ss' he => ?_] at hj
      · exact physExpand_mulHiOk _ _ rm mbr ii ds o ss hm hrmR j hj
      · simp only [LinstrR.Lopn.injEq] at he
        obtain ⟨-, rfl, -⟩ := he
        constructor <;> rintro rfl <;> revert hm <;> decide +kernel
    · refine mulHiOk_of_site (noSite_of_mnemOk
        (fun r hr ds o ss he => ((hblk.1 r hr ds o ss he).2)) (fun o ho => ?_) j hj)
      cases w with
      | Lopn ds o' ss =>
        simp only [opnOf, Option.some.injEq] at ho
        subst ho
        cases hm : isMulHiMnem o'
        · rfl
        · exact absurd ⟨ds, o', ss, rfl, hm⟩ hw
      | _ => simp [opnOf] at ho
  refine mulHiNoSlotB_of fun j hj => ?_
  simp only [insertEpilogue, List.mem_append] at hj
  rcases hj with (hj | hj) | hj | (hj | hj) | hj
  · exact mulHiOk_of_site
      (prologue_plainB _ _ abiArgs j (List.mem_append_left (extraSaves abiArgs) hj)).1
  · exact mulHiOk_of_site (prologue_plainB virt0 #[] abiArgs j
      (List.mem_append_right (buildPrologue virt0 #[] (fun _ => none)) hj)).1
  · exact mulHiOk_of_site (buildArgPtrMaterialize_plainB _ _ _ _ j hj).1
  · have hj' := List.dropLast_subset _ hj
    rw [reloadArrImmBody_filter_flatMap] at hj'
    obtain ⟨i, hi, hj⟩ := List.mem_flatMap.mp hj'
    rw [hrmE] at hj
    exact hF i hi j (List.mem_of_mem_filter hj)
  · exact mulHiOk_of_site (epilogue_plainB j (List.mem_append_left _ hj)).1
  · exact mulHiOk_of_site (epilogue_plainB j (List.mem_append_right _ hj)).1

/-! ## 5. The 64-bit copies of the export -/

/-- A 64-bit copy into a register of the instruction reads no array slot. -/
def CopyOkR (slotArr : String → Option (String × Nat)) (r : LinstrR) : Prop :=
  ∀ d x, r = .Lopn [.reg d] "MOV:64" [.reg x] → slotArr x = none

theorem copyOkR_lopn {slotArr : String → Option (String × Nat)} {ds : List LOperand}
    {o : String} {ss : List LOperand} (h : ∀ x ∈ ss, GoodOp slotArr x) :
    CopyOkR slotArr (.Lopn ds o ss) := by
  intro d x he
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨-, -, rfl⟩ := he
  exact h _ (List.mem_singleton_self _)

/-- **No 64-bit copy of one expansion reads an array slot** when the operand map sends every
    operand to one naming no array slot and the scratch registers are no array slots. -/
theorem physExpand_copyOk {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr) (hg : ∀ x, GoodOp slotArr (rm x))
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none) :
    ∀ r ∈ physExpand shiftImm u64 rm mbr i, CopyOkR slotArr r.li_i :=
  physExpand_forall (CopyOkR slotArr) (fun _ _ _ h => copyOkR_lopn h)
    (fun q _ _ he => by rcases ptrLoad_cases q with hp | hp <;> simp [hp] at he)
    (fun _ hr _ _ he => absurd he (hr _ _ _)) shiftImm u64 rm mbr i hg hs15 hs14

theorem copyOkR_movq {slotArr : String → Option (String × Nat)} (ds ss : List LOperand) :
    CopyOkR slotArr (.Lopn ds "MOVQ" ss) := by
  intro d x he
  simp at he

/-- **No 64-bit copy of the call-free looped physical ABI export reads an array slot**, when
    every array slot is a `qsave.` slot: the prologue, the argument materialization and the
    epilogue are `MOVQ` moves, and every expansion reads only allocated registers and the
    scratch registers through a 64-bit copy. -/
theorem copyNoSlotB_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    copyNoSlotB slotArr (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
      abiArgs abiTyin x86Abi posBind).1.lfd_body = true := by
  rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
    posBind body1 hb1 mbr hmbr hcf]
  have hrmE : physRmap body1 [] =
      fun o =>
        remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o := by
    simp only [physRmap, hcf, Bool.false_eq_true, ite_false]
  have hs15 : slotArr reloadScratch = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hs14 : slotArr reloadScratch2 = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hP : ∀ p, slotArr (physRegName p x86Abi) = none := fun p =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_physRegName p)
  have hg : ∀ x, GoodOp slotArr
      (remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) x) := by
    intro x
    cases x <;> simp [remapOperand, GoodOp, hP]
  refine X86Backend.PhysImgSidePass.copyNoSlotB_iff.mpr fun j hj => ?_
  show CopyOkR slotArr j.li_i
  simp only [insertEpilogue, List.mem_append] at hj
  rcases hj with (hj | hj) | hj | (hj | hj) | hj
  · simp only [buildPrologue, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact copyOkR_movq _ _
  · obtain ⟨r, s, -, rfl⟩ := mem_extraSaves hj
    exact copyOkR_movq _ _
  · unfold buildArgPtrMaterialize at hj
    obtain ⟨⟨abiReg, k⟩, -, hj⟩ := List.mem_flatMap.mp hj
    simp only at hj
    split at hj
    · simp at hj
    · split_ifs at hj <;>
        rcases hs : abiSlotOfExt abiReg with _ | s <;>
        simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hj <;>
        (try rcases hj with rfl | rfl) <;> exact copyOkR_movq _ _
  · rcases mem_reloadArrImmBody (List.dropLast_subset _ hj) with hj | ⟨i', -, l', hl, -, hx⟩
    · obtain ⟨i, hi, hj⟩ := List.mem_flatMap.mp (List.mem_of_mem_filter hj)
      rw [hrmE] at hj
      exact physExpand_copyOk _ _ _ mbr i hg hs15 hs14 j hj
    · obtain ⟨b, q, -, ⟨n, w, -, rfl⟩ | ⟨d, v, k, -, rfl⟩⟩ := reloadArrImm_eq_some hl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx <;> rw [hx] <;> rcases ptrLoad_cases q with hp | hp <;>
          (try rw [hp]) <;> intro d' x he <;> simp at he
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]
        rcases ptrLoad_cases q with hp | hp <;> rw [hp] <;> intro d' x he <;> simp at he
      unfold storeImmVia at hx
      split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      · next hs =>
        rcases hx with hx | hx <;> rw [hx]
        · intro d' x he
          simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at he
          obtain ⟨-, -, rfl⟩ := he
          refine slotArr_none_of_prefix hslot ?_
          rw [X86Backend.PhysAbiShape.isSpill_eq] at hs
          unfold hasPrefix at hs ⊢
          rcases hl : v.toList with _ | ⟨c, t⟩ <;> simp_all [List.isPrefixOf]
          obtain ⟨rfl, -⟩ := hs
          intro h
          exact absurd h (by decide)
        · intro d' x he
          simp at he
      · rw [hx]
        intro d' x he
        simp at he
  · simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact copyOkR_movq _ _
  · simp only [List.mem_singleton] at hj
    subst hj
    intro d x he
    cases he

/-! ## 6. The allocated function of the region route -/

/-- **The hypotheses of the compiler lemmas on `lfundefPhysAbiOfVirtCert` at the allocated
    function of the region route**, on the domain of
    `RegionPhysImgArg.physImgB_regionExport_words`: the body of `regionAllocFn` is the body of
    `lfundefPhysAbiOfVirtCert` at a virtual function whose allocator input body is
    `regionAllocBody`, that body has no call, its operations have the access form at the slot
    map of the gate, its array operands are no array slots, its operands outside the accesses
    are not indexed, and its instructions have the shape `ShapeB`. -/
theorem regionAllocFn_exportHyps (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) ts r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup) (R : Slots)
    (ps : List (String × String)) :
    ∃ virt0 : Lfundef,
      (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body =
        (lfundefPhysAbiOfVirtCert virt0 (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
          [] (fun _ => none) (nfAbiNames fname σ).abiArgs
          ((nfAbiNames fname σ).abiArgs.map fun _ => 64) x86Abi true).1.lfd_body ∧
      regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r =
        (if (nfAbiNames fname σ).abiArgs.length ≥ 4 then
          [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range (nfAbiNames fname σ).abiArgs.length).map
              (fun j => (.reg (argName j) : LOperand)))⟩]
          else []) ++ canonicalizeMemrefThread
            (([] : List String).foldl (fun b r => aliasRegBody r (nfAbiNames fname σ).outArg b)
              virt0.lfd_body) ∧
      bodyHasCall (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) = false ∧
      (∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r,
        AccForm (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
          (fun o => remapOperand (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)
            (straightCallComposeTable (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)
              (physTableOut (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) [] []))
              o)
          (fun base =>
            (((argBasePairs true (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
              (nfAbiNames fname σ).abiArgs).filterMap (fun p =>
              match abiSlotOfExt p.2 with
              | some saveName => some (physNameForBody
                  (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)
                  (physTableOut (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) [])
                    p.1, saveName)
              | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
          i.li_i) ∧
      (∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r, ∀ q n,
        LOperand.arr q n ∈ lopnOperands i.li_i →
          slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) q = none) ∧
      (∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r,
        isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true) ∧
      ∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r,
        RegionAllocMapDom.ShapeB i.li_i := by
  have hC := RegionPhysImgArg.exportR_accCode_copy (nfAbiNames fname σ) p hc hw hr
  have hacc : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r,
      RegionPhysImg.AccArg σ i.li_i := fun i hi =>
    RegionPhysImgArg.accArg_of_accP (RegionPhysImgArg.accP_regionAllocBody
      (RegionPhysImgArg.ArgSlotName σ) _ _ r hts hC
      (RegionPhysImgArg.exportR_immCode_copy (nfAbiNames fname σ) p hc hr)
      (RegionPhysImgArg.exportR_aliasRoots fname σ p hp hc hσ hr hzr)
      (RegionPhysImgArg.exportR_untagP_copy (nfAbiNames fname σ) p hc hr) i hi)
  have hidx : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r,
      isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true := fun i hi =>
    noIdxB_of_idxAcc (idxAcc_regionAllocBody _ _ r hts hC i hi)
  have harr := RegionPhysImgArg.harr_regionAllocBody (nfAbiNames fname σ) p hc hr hts
  have hB : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r,
      RegionAllocMapDom.ShapeB i.li_i :=
    RegionAllocMapDom.shapeB_regionAllocBody _ _ ts r fun i hi =>
      (RegionAllocMapDom.exportR_mnemDom (nfCtx σ).length fname p hp hc _ _ r hr i hi).2.2
  have hcf := RegionAllocMapDom.bodyHasCall_of_shapeB hB
  have hslot := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  have hsave := RegionPhysImg.nfAbiNames_pairSave fname σ hnd R (renOf ps)
  have hb1 : regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r =
      (if (nfAbiNames fname σ).abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range (nfAbiNames fname σ).abiArgs.length).map
            (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (([] : List String).foldl (fun b r => aliasRegBody r (nfAbiNames fname σ).outArg b)
            (arrBasePins (nfAbiNames fname σ)
                (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts
                  r.code r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))) := by
    unfold regionAllocBody
    split
    · exact absurd rfl (hts _)
    · rfl
  have hshape : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r,
      AccForm (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
        (fun o => remapOperand (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)
          (straightCallComposeTable (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)
            (physTableOut (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) [] [])) o)
        (fun base =>
          (((argBasePairs true (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
            (nfAbiNames fname σ).abiArgs).filterMap (fun p =>
            match abiSlotOfExt p.2 with
            | some saveName => some (physNameForBody
                (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)
                (physTableOut (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) [])
                  p.1, saveName)
            | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
        i.li_i := fun i hi =>
    RegionPhysImg.accForm_of_accArg hcf hsave (RegionPhysImg.argPair_nfAbiNames fname σ)
      (hacc i hi)
  have harr' : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r, ∀ q n,
      LOperand.arr q n ∈ lopnOperands i.li_i →
        slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) q = none :=
    fun i hi q n hx => slotArr_none_of_prefix hslot (harr i hi q n hx)
  exact ⟨{ fd0 with lfd_body :=
      (arrBasePins (nfAbiNames fname σ)
          (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
            r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res))
        ++ ((regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts
            r.code r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) },
    rfl, hb1, hcf, hshape, harr', hidx, hB⟩

/-- **The conditions of the fusion and the fold on the allocated function of the region
    route**, on the domain of `RegionPhysImgArg.physImgB_regionExport_words`: for the body
    `b0` of `regionAllocFn` at the slot map `sl` of the gate, `fuseSiteOkB sl b0`,
    `homeOkB sl [] b0`, `cellBaseFreeB b0`, `mulHiNoSlotB sl b0` and `copyNoSlotB sl b0`
    hold. -/
theorem sideAlloc_regionAllocFn (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) ts r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup) (R : Slots)
    (ps : List (String × String)) :
    fuseSiteOkB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
        (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true ∧
      homeOkB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps))) []
        (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true ∧
      cellBaseFreeB (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true ∧
      mulHiNoSlotB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
        (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true ∧
      copyNoSlotB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
        (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true := by
  obtain ⟨virt0, hbody, hb1, hcf, hshape, harr, hidx, -⟩ :=
    regionAllocFn_exportHyps fname σ p hp hc hw hσ hr hzr hts fd0 hnd R ps
  have hslot := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  rw [hbody]
  exact ⟨fuseSiteOkB_lfundefPhysAbiOfVirtCert _ _ _ [] (fun _ => none) _ _ true _ hb1 _ rfl hcf
      hshape harr hidx hslot,
    homeOkB_lfundefPhysAbiOfVirtCert _ _ _ [] (fun _ => none) _ _ true _ hb1 _ rfl hcf
      hshape harr hidx hslot,
    cellBaseFreeB_lfundefPhysAbiOfVirtCert _ _ _ [] (fun _ => none) _ _ true _ hb1 _ rfl hcf
      hshape hidx,
    mulHiNoSlotB_lfundefPhysAbiOfVirtCert _ _ _ [] (fun _ => none) _ _ true _ hb1 _ rfl hcf
      hshape harr hslot,
    copyNoSlotB_lfundefPhysAbiOfVirtCert _ _ _ [] (fun _ => none) _ _ true _ hb1 _ rfl hcf
      hslot⟩

/-- The result names of the allocated function of the region route are empty. -/
theorem regionAllocFn_lfd_res (a : AbiNames) (ts : List JasminTy) (r : Exported)
    (fd0 : Lfundef) : (regionAllocFn a ts r fd0).lfd_res = [] := rfl

/-! ## 7. The side conditions -/

/-- **The side conditions of the region gate from the conditions that remain open**, on the
    domain of `RegionPhysImgArg.physImgB_regionExport_words`. For the body `b0` of
    `regionAllocFn` and its result names `res`, at the slot map `sl` of the gate,
    `physImgSideB sl res b0` holds when the optimizer condition holds on every straight run of
    the post-pass body (`hopt`), no 64-bit move of the post-pass body is between two memory
    names (`hhold`), the re-allocated and legalised body satisfies `noScratchBaseB` (`hcmp`),
    and every flag-only compare of `b0` with a register first source is tied (`hflag`). The
    site, home, cell-base, high-product and copy conditions on `b0` follow from the export
    (`sideAlloc_regionAllocFn`), the result names are empty, and the conditions on the later
    bodies follow from those on `b0` through the passes (`PhysImgSidePass`) and the sublist
    `deadWriteRet_sublist`. -/
theorem physImgSideB_of_export (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) ts r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup) (R : Slots)
    (ps : List (String × String))
    (hopt : (splitStraightRuns
      (postBody (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body)).all
      (optSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))) = true)
    (hhold : memMovFreeB (postBody (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body)
      = true)
    (hcmp : noScratchBaseB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (twoAddrBody (reallocStage (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_res
        (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body)) = true)
    (hflag : flagTiedB (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true) :
    physImgSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_res
      (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true := by
  obtain ⟨h1, h2, hcell, hmul, hcopy⟩ :=
    sideAlloc_regionAllocFn fname σ p hp hc hw hσ hr hzr hts fd0 hnd R ps
  have hq := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  have hs := deadWriteRet_sublist
    (fuseMulHiBody (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body true)
  simp only [physImgSideB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hopt⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact copyNoSlotB_postOpt hq hcopy hmul hs hhold
  · exact cellBaseFreeB_postOpt hcell hs
  · rw [regionAllocFn_lfd_res]; rfl
  · exact flagTiedB_reallocStage _ hflag hs
  · exact cmpScratchFreeB_of_baseNoScratch hcmp
  · exact cellBaseFreeB_printedChain _ hcell hs

/-- **The region gate never refuses at its image conjunct under the open side conditions**:
    `RegionPhysImgGate.regionCoStage_ne_physImgB` with `hside` replaced by the hypotheses of
    `physImgSideB_of_export` at the slot map of the gate. -/
theorem regionCoStage_ne_physImgB_of_open (fname : String) (σ : AbiLayout) {t : JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) [t] r)
    {fd0 : Lfundef} (hfd : exportRLfundef fname p = some fd0)
    (hts : ∀ w, [t] ≠ [.reg w]) (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (ex : List String) {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC (nfAbiNames fname σ) p none ex = some (P, cert))
    {b : Lcmd} (hb : firstBody (printedLprog P) = some b) (fn : String)
    (hopt : (splitStraightRuns
      (postBody (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_body)).all
      (optSideB (slotArrC (regionCoParts σ exportReg b t r.code r.res cert).cells
        (slotRen (slotArrOf σ exportReg)
          (renOf (regionCoParts σ exportReg b t r.code r.res cert).ps)))) = true)
    (hhold : memMovFreeB (postBody (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_body)
      = true)
    (hcmp : noScratchBaseB (slotArrC (regionCoParts σ exportReg b t r.code r.res cert).cells
        (slotRen (slotArrOf σ exportReg)
          (renOf (regionCoParts σ exportReg b t r.code r.res cert).ps)))
      (twoAddrBody (reallocStage (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_res
        (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_body)) = true)
    (hflag : flagTiedB (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_body = true) :
    regionCoStage σ exportReg b t r.code r.res cert none fn ≠ some "physImgB" :=
  regionCoStage_ne_physImgB fname σ p hp hc hw hσ hr hzr hfd hts hnd ex hP hb fn
    (physImgSideB_of_export fname σ p hp hc hw hσ hr hzr hts fd0 hnd _ _ hopt hhold hcmp hflag)

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSide
