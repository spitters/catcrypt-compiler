/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgPost
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgCell
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp

/-!
# The image conjunct of the region gate on the printed body

The region gate `regionCoStage` takes the conjunct `physImgB sl (cellBody sl b)` at the slot
map `sl = slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps))` of the gate and the first
body `b` of the printed program `printedLprog P` of the allocated program `P` of
`regionLprogC`. The first body of `P` is the allocated body of the export after the fusion
post-pass `regionPostFuse`, and the printed program applies to it, in order, the optimizer
`optimizeBasicBlocks`, the constant-index fold `foldIndexedBody`, the register re-allocation
`reallocBody`, the two-address legalisation `twoAddrBody` and the reload of spilled compare
operands `cmpReload` (`firstBody_printedLprog_regionPostFuse`). Each of these passes and the
cell body keep the image class under a side condition of its own; `physImgSideB` is the
conjunction of these side conditions on the intermediate bodies. The slot map of the gate has
only `qsave.` slots (`RegionPhysImg.regionSl_qsave`) and, at a layout whose word-array
parameters have save slots, no slot at the save slot `scratchSave` of the scratch register
(`regionSl_scratchSave`).

## Main results

* `printedBody`: the first body of the printed program of an allocated program with first
  function body `b0` and result names `res`.
* `firstBody_printedLprog_regionPostFuse`: the first body of the printed program of
  `regionPostFuse P` is `printedBody` of the first function of `P`.
* `physImgSideB`: the side conditions of the passes, a decision on the intermediate bodies.
* `physImgB_printedBody`: the cell body of `printedBody` is in the image class when the
  allocated body is and `physImgSideB` holds.
* `regionSl_scratchSave`: the slot map of the gate has no slot at `scratchSave`.
* `regionAllocFn`, `regionLprogC_lp_funcs`: the allocated function of the region route without
  a callee, and the program of `regionLprogC` as `regionPostFuse` of it.
* `physImgB_printed`: for every program on the domain of
  `RegionPhysImgArg.physImgB_regionExport_words`, the image conjunct of the gate holds on
  the printed body under `physImgSideB`.
* `regionCoStage_ne_physImgB_of`: the stage function names `physImgB` only when the image
  conjunct fails.
* `regionCoStage_ne_physImgB`: on that domain, under `physImgSideB`, the region gate never
  names `physImgB` as the refusing stage.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg physImgB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotRen
  slotArrOf_some)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data scratchSave
  twoAddrBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (optimizeBasicBlocks
  splitStraightRuns)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold (foldIndexedBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc (reallocBody isFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload (cmpReload)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse (fuseSiteOkB homeOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt (optSideB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (copyNoSlotB cellBaseFreeB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint (flagTiedB cmpScratchFreeB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit (isArrImmB)

/-! ## 1. The printed body -/

/-- The body after the fusion post-pass of the allocated body `b0`. -/
def postBody (b0 : Lcmd) : Lcmd := deadWriteRet (fuseMulHiBody b0 true)

/-- The body after the optimizer and the constant-index fold. -/
def foldBody (b0 : Lcmd) : Lcmd := foldIndexedBody (optimizeBasicBlocks (postBody b0))

/-- The body after the register re-allocation at the result names `res`. -/
def reallocStage (res : List String) (b0 : Lcmd) : Lcmd := reallocBody res (foldBody b0)

/-- **The first body of the printed program** of an allocated program whose first function
    has the body `b0` and the result names `res`: the post-pass, the optimizer, the fold, the
    re-allocation, the two-address legalisation and the reload of spilled compare operands. -/
def printedBody (res : List String) (b0 : Lcmd) : Lcmd :=
  cmpReload (twoAddrBody (reallocStage res b0)) x86Data.toIsaAbi

/-- **The first body of the printed program of `regionPostFuse P`** is `printedBody` of the
    first function of `P`. -/
theorem firstBody_printedLprog_regionPostFuse {P : Lprog} {n : String} {f : Lfundef}
    {fs : List (String × Lfundef)} (hP : P.lp_funcs = (n, f) :: fs) :
    firstBody (printedLprog (regionPostFuse P)) = some (printedBody f.lfd_res f.lfd_body) := by
  simp [firstBody, printedLprog, regionPostFuse, X86Backend.LprogOptPipeline.mapBodies,
    X86Backend.LprogOptPipeline.ownedLprog, X86Backend.LprogOptPipeline.optimizeLprogBasicBlocks,
    X86Backend.ConstIndexFold.foldIndexedLprog, X86Backend.LprogGpRealloc.reallocLprog,
    X86Backend.FuseMulHi.fuseMulHiLprog, hP, printedBody, reallocStage, foldBody,
    postBody]

/-! ## 1b. No `ZEROARR` or `STOREIMM` through the passes

Each pass between the allocated body and the cell body emits no `ZEROARR` and no
`STOREIMM`: its instructions are instructions of its input, instructions under the mnemonic of
an input instruction, or instructions under a fixed mnemonic. -/

/-- **The basic-block optimiser emits no `ZEROARR` or `STOREIMM`**: its rewrites keep the
    mnemonic of the rewritten instruction. -/
theorem arrImmFree_optimizeBasicBlocks {b : Lcmd} (h : ∀ j ∈ b, isArrImmB j.li_i = false) :
    ∀ j ∈ optimizeBasicBlocks b, isArrImmB j.li_i = false :=
  X86Backend.PhysImgSidePass.forall_optimizeBasicBlocks_closed
    (P := fun j => isArrImmB j.li_i = false)
    (fun i dsts opn srcs g hi he _ => by
      simp only at hi ⊢
      rw [he] at hi
      simpa [isArrImmB] using hi)
    (fun i d mn s r hi he _ => by
      simp only at hi ⊢
      rw [he] at hi
      simpa [isArrImmB] using hi) h

/-- **The constant-index fold emits no `ZEROARR` or `STOREIMM`**: the folded accesses are
    `LOAD`, `STORE` and `MOV:64`, and their spellings are moves. -/
theorem arrImmFree_foldIndexedBody {b : Lcmd} (h : ∀ j ∈ b, isArrImmB j.li_i = false) :
    ∀ j ∈ foldIndexedBody b, isArrImmB j.li_i = false := by
  have h1 : ∀ j ∈ X86Backend.ConstIndexFold.constIndexFoldBody b, isArrImmB j.li_i = false :=
    fun j hj => (X86Backend.PhysImgFold.mem_constIndexFoldBody_arrImm hj).elim (h j) id
  unfold foldIndexedBody
  refine X86Backend.PhysImgSidePass.forall_spellMemBody (P := fun j => isArrImmB j.li_i = false)
    (fun i hi => ?_) (X86Backend.PhysImgSidePass.forall_dropDeadImmBody h1)
  rcases X86Backend.PhysImgFold.spellMemInstr_cases i.li_i with hf | ⟨d, B, off, -, o, hf, ho⟩ |
      ⟨d, B, off, vn, -, o, hf, ho⟩
  · show isArrImmB (X86Backend.ConstIndexFold.spellMemInstr i.li_i) = false
    rw [hf]; exact hi
  all_goals
    show isArrImmB (X86Backend.ConstIndexFold.spellMemInstr i.li_i) = false
    rw [hf]
    rcases ho with rfl | rfl <;> rfl

/-- **The register re-allocation emits no `ZEROARR` or `STOREIMM`**: an instruction of a
    re-allocated run is under the mnemonic of an instruction of the fragment alphabet, which
    excludes both. -/
theorem arrImmFree_reallocBody (res : List String) {b : Lcmd}
    (h : ∀ j ∈ b, isArrImmB j.li_i = false) :
    ∀ j ∈ reallocBody res b, isArrImmB j.li_i = false := by
  rw [X86Backend.LprogGpReallocLeak.reallocBody_eq]
  have hgood := X86Backend.LprogGpReallocLeak.pieces_good b
  have hps := X86Backend.LprogGpReallocCT.pieces_spec
    (recog := X86Backend.LcmdCopyPropagate.isRecognizedOpn) b
  generalize X86Backend.LprogGpRealloc.labelLiveFrames b = lf
  generalize X86Backend.LprogGpRealloc.pieces b = ps at hps hgood
  induction ps with
  | nil => simp [X86Backend.LprogGpReallocLeak.outSegs]
  | cons p ps ih =>
    simp only [X86Backend.LprogGpReallocLeak.outSegs, List.flatten_cons, List.mem_append]
    rintro j (hj | hj)
    · rcases hps p List.mem_cons_self with ⟨li, hli, rfl⟩ | ⟨is, rfl, -⟩
      · simp only [X86Backend.LprogGpReallocLeak.outSeg, List.mem_singleton] at hj
        subst hj
        exact h _ hli
      · simp only [X86Backend.LprogGpReallocLeak.outSeg] at hj
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
        obtain ⟨i, hi, he⟩ := X86Backend.PhysImgSidePass.reallocRun_opn _ is k hk
        have hne :=
          X86Backend.PhysImgFold.fragOf?_untagCaret_ne ((hgood _ List.mem_cons_self).2 i hi)
        simp [X86Backend.LprogGpRealloc.FI.toL, X86Backend.LprogGpRealloc.FI.toR, isArrImmB, he,
          hne.1, hne.2]
    · exact ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))
        (fun q hq => hgood q (List.mem_cons_of_mem _ hq)) j hj

/-- **The two-address legalisation emits no `ZEROARR` or `STOREIMM`**: it writes each
    operation under its own mnemonic or a move mnemonic. -/
theorem arrImmFree_twoAddrBody {b : Lcmd} (h : ∀ j ∈ b, isArrImmB j.li_i = false) :
    ∀ j ∈ twoAddrBody b, isArrImmB j.li_i = false := by
  intro r hr
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  cases hii : i.li_i with
  | Lopn ds o ss =>
    obtain ⟨ds', o', ss', hr', ho⟩ :=
      X86Backend.PhysImgSidePass.legalizeInstr_mnOf _ i hii r hr
    rw [hr']
    rcases ho with rfl | ho
    · have := h i hi
      rw [hii] at this
      simpa [isArrImmB] using this
    · rcases ho with ho | ⟨w, rfl⟩
      · exact X86Backend.PhysImgEmit.isArrImmB_of_movMnems ho
      · exact X86Backend.PhysImgPrint.isArrImmB_mov (Or.inr (Or.inr ⟨w, rfl⟩))
  | _ =>
    unfold X86Backend.TwoAddrLegalize.legalizeInstr at hr
    split at hr
    · rename_i he; rw [hii] at he; cases he
    · rw [List.mem_singleton.mp hr, hii]; rfl

/-- **The compare-spill reload emits no `ZEROARR` or `STOREIMM`**: it writes a move and the
    compare under its own mnemonic. -/
theorem arrImmFree_cmpReload {b : Lcmd} (h : ∀ j ∈ b, isArrImmB j.li_i = false) :
    ∀ j ∈ cmpReload b, isArrImmB j.li_i = false := by
  intro r hr
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  cases hs : X86Backend.CmpSpillReload.spillCmp? i.li_i with
  | some p =>
    obtain ⟨opn, d, s⟩ := p
    have hii := X86Backend.PhysImgPrint.spillCmp?_some hs
    rw [X86Backend.PhysImgPrint.cmpReloadI_of_some hs] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hmv : X86Backend.CmpSpillReload.movOf opn = "MOV" ∨
          X86Backend.CmpSpillReload.movOf opn = "MOV:64" := by
        unfold X86Backend.CmpSpillReload.movOf; split_ifs <;> simp
      exact X86Backend.PhysImgPrint.isArrImmB_mov (hmv.elim Or.inl (fun h => Or.inr (Or.inl h)))
    · have := h i hi
      rw [hii] at this
      simpa [isArrImmB] using this
  | none =>
    rw [X86Backend.CmpSpillReload.cmpReloadI_of_none hs, List.mem_singleton] at hr
    subst hr
    exact h r hi

/-! ## 2. The side conditions of the passes -/

/-- **The side conditions of the passes of the printed program** at the slot map `sl`, the
    result names `res` and the allocated body `b0`: the site and home conditions of the
    fusion on `b0`, the optimizer condition on every straight run of the post-pass body, the
    copy and base conditions of the fold, no frame cell among the result names of the
    re-allocation, the tied flag compares of the two-address legalisation, the free reload
    scratch of the compare reload, and no cell base in the body given to the cell body. -/
def physImgSideB (sl : String → Option (String × Nat)) (res : List String) (b0 : Lcmd) :
    Bool :=
  fuseSiteOkB sl b0 && homeOkB sl [] b0
    && (splitStraightRuns (postBody b0)).all (optSideB sl)
    && copyNoSlotB sl (optimizeBasicBlocks (postBody b0))
    && cellBaseFreeB (optimizeBasicBlocks (postBody b0))
    && res.all (fun x => !isFrame x)
    && flagTiedB (reallocStage res b0)
    && cmpScratchFreeB sl (twoAddrBody (reallocStage res b0))
    && cellBaseFreeB (printedBody res b0)

/-- **The cell body of the printed body is in the image class** when the allocated body is,
    every array slot of `sl` is a `qsave.` slot, `sl` has no slot at `scratchSave`, the
    side conditions `physImgSideB` hold. -/
theorem physImgB_printedBody {sl : String → Option (String × Nat)}
    (hq : ∀ q, (sl q).isSome = true → hasPrefix q "qsave." = true)
    (hsave : sl scratchSave = none) {res : List String} {b0 : Lcmd}
    (h : physImgB sl b0 = true) (hside : physImgSideB sl res b0 = true) :
    physImgB sl (cellBody sl (printedBody res b0)) = true := by
  simp only [physImgSideB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hside
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsite, hhome⟩, hopt⟩, hcp⟩, hcb⟩, hres⟩, hflag⟩, hfree⟩, hcell⟩ := hside
  have h1 : physImgB sl (postBody b0) = true :=
    RegionPhysImgPost.physImgB_deadWriteRet
      (X86Backend.PhysImgFuse.physImgB_fuseMulHiBody true hq h hsite hhome)
  have h2 := X86Backend.PhysImgOpt.physImgB_optimizeBasicBlocks hq h1
    (List.all_eq_true.mpr hopt)
  have h3 := X86Backend.PhysImgFold.physImgB_foldIndexedBody hq hcp hcb h2
  have h4 : physImgB sl (reallocStage res b0) = true :=
    X86Backend.PhysImgFold.physImgB_reallocBody hq hres h3
  have h5 := X86Backend.PhysImgPrint.physImgB_twoAddrBody hq hsave hflag h4
  have h6 := X86Backend.PhysImgPrint.physImgB_cmpReload hq hfree h5
  exact X86Backend.PhysImgCell.physImgB_cellBody hq hcell h6

/-! ## 3. The slot map of the gate -/

/-- **The slot map of the gate has no slot at `scratchSave`** at a layout whose word-array
    parameters have frame slots: the register of such a parameter is one of `RDI`, `RSI`,
    `RDX`, `RCX`, `R8`, `R9` or a stack word, never the scratch register `R15`. -/
theorem regionSl_scratchSave {σ : AbiLayout} (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    (R : Slots) (ps : List (String × String)) :
    slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) scratchSave = none := by
  have hi := RegionPhysImg.regionSl_isSome R (slotArrOf σ exportReg) (renOf ps) scratchSave
  cases hsl : slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) scratchSave with
  | none => rfl
  | some x =>
    rw [hsl, Option.isSome_some] at hi
    cases hs : slotArrOf σ exportReg scratchSave with
    | none => rw [hs] at hi; cases hi
    | some An =>
      exfalso
      obtain ⟨A, n⟩ := An
      obtain ⟨j, a, ha, hk, -, he⟩ := slotArrOf_some hs
      have hw := List.all_eq_true.mp hσ a (List.mem_of_getElem? ha)
      rw [hk] at hw
      have hr : exportReg a.reg = "R15" := by
        have := congrArg String.toList he
        simp [slotOfReg, scratchSave] at this
        exact String.ext this
      rw [hr] at hw
      simp only at hw
      exact absurd hw (by decide)

/-! ## 4. The image conjunct on the printed body -/

/-- The allocated function of the region route without a callee, at the export `r` and the
    function `fd0` of the export, for a result other than one register. -/
def regionAllocFn (a : AbiNames) (ts : List JasminTy) (r : Exported) (fd0 : Lfundef) :
    Lfundef :=
  (calleeAllocCert none
    { fd0 with lfd_body :=
        (arrBasePins a (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res))
          ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).map
            (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) }
    a.outArg a.inArgs a.abiArgs).1

/-- The allocated program of `regionLprogC` without a callee, for a result other than one
    register, is `regionPostFuse` of the program whose only function is `regionAllocFn` at the
    webs `regionWebsAt ex none r` of the export `r`. -/
theorem regionLprogC_lp_funcs (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) {r : Exported} {fd0 : Lfundef}
    (hr : exportR Γ.length a.fname p Γ.length 0 = some r)
    (hfd : exportRLfundef a.fname p = some fd0) (hts : ∀ w, ts ≠ [.reg w])
    {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ P0 : Lprog, P = regionPostFuse P0
      ∧ P0.lp_funcs = [(a.fname, regionAllocFn a ts (regionWebsAt ex none r) fd0)] := by
  unfold regionLprogC regionAllocC at hP
  rw [hr, hfd] at hP
  simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hP
  exact ⟨_, hP.1.symm, rfl⟩

/-- **The image conjunct of the region gate holds on the printed body** for every program
    on the domain of `RegionPhysImgArg.physImgB_regionExport_words`: without `call`, with
    `64`-bit word arrays (`arrW64B`), whose export zeroes only the result root
    (`ZeroAtRoot`), at a layout whose word-array parameters have save slots (`wordsSlotB`) and
    distinct export registers, and with a result other than one register, on which the webs
    pass leaves the export unchanged (`hwe`; the domain of
    `RegionPhysImgArg.physImgB_regionExport_words` is stated on the export, not on its webs).
    For the allocated program `P` of `regionLprogC` and the first body `b` of its printed
    program, at every slot map `sl` of the gate, `physImgB sl (cellBody sl b)` holds when the
    side conditions `physImgSideB` of the passes hold on the allocated function
    `regionAllocFn`. -/
theorem physImgB_printed (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) ts r)
    {fd0 : Lfundef} (hfd : exportRLfundef fname p = some fd0)
    (hts : ∀ w, ts ≠ [.reg w]) (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (ex : List String) (hwe : regionWebs ex r = r) {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC (nfAbiNames fname σ) p none ex = some (P, cert))
    {b : Lcmd} (hb : firstBody (printedLprog P) = some b)
    (R : Slots) (ps : List (String × String))
    (hside : physImgSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_res
      (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true) :
    physImgB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (cellBody (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps))) b) = true := by
  obtain ⟨P0, rfl, hP0⟩ := regionLprogC_lp_funcs (nfAbiNames fname σ) p ex hr hfd hts hP
  rw [regionWebsAt_none, hwe] at hP0
  rw [firstBody_printedLprog_regionPostFuse hP0, Option.some.injEq] at hb
  subst hb
  exact physImgB_printedBody (RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps))
    (regionSl_scratchSave hσ R ps)
    (RegionPhysImgArg.physImgB_regionExport_words fname σ p hp hc hw hσ hr hzr hts fd0 hnd R ps)
    hside

/-! ## 5. The stage of the gate -/

/-- **The region gate names `physImgB` only when the image conjunct fails**: when
    `physImgB sl (cellBody sl body)` holds at the slot map of the parts
    `regionCoParts σ nm body t (calleeCodeT callee code) res cert callee`, the stage function
    `regionCoStage` does not name `physImgB`. -/
theorem regionCoStage_ne_physImgB_of (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand)
    (cert : List (String × String)) (callee : Option CalleeTab) (fn : String)
    (h : physImgB
      (slotArrC (regionCoParts σ nm body t (calleeCodeT callee code) res cert callee).cells
        (slotRen (slotArrOf σ nm)
          (renOf (regionCoParts σ nm body t (calleeCodeT callee code) res cert callee).ps)))
      (cellBody
        (slotArrC (regionCoParts σ nm body t (calleeCodeT callee code) res cert callee).cells
          (slotRen (slotArrOf σ nm)
            (renOf (regionCoParts σ nm body t (calleeCodeT callee code) res cert callee).ps)))
        body) = true) :
    regionCoStage σ nm body t code res cert callee fn ≠ some "physImgB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by decide) ?_
  exact (Option.some_ne_none _).symm

/-- **The region gate never refuses at its image conjunct** on the domain of
    `physImgB_printed`: for the allocated program `P` of `regionLprogC` without a callee,
    the first body `b` of its printed program and the export `r`, which the webs pass leaves
    unchanged, when the side conditions
    `physImgSideB` hold at the slot map of the gate, `regionCoStage` on `b` does not name
    `physImgB`. -/
theorem regionCoStage_ne_physImgB (fname : String) (σ : AbiLayout) {t : JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) [t] r)
    {fd0 : Lfundef} (hfd : exportRLfundef fname p = some fd0)
    (hts : ∀ w, [t] ≠ [.reg w]) (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (ex : List String) (hwe : regionWebs ex r = r) {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC (nfAbiNames fname σ) p none ex = some (P, cert))
    {b : Lcmd} (hb : firstBody (printedLprog P) = some b) (fn : String)
    (hside : physImgSideB
      (slotArrC (regionCoParts σ exportReg b t r.code r.res cert).cells
        (slotRen (slotArrOf σ exportReg)
          (renOf (regionCoParts σ exportReg b t r.code r.res cert).ps)))
      (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_res
      (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_body = true) :
    regionCoStage σ exportReg b t r.code r.res cert none fn ≠ some "physImgB" :=
  regionCoStage_ne_physImgB_of σ exportReg b t r.code r.res cert none fn
    (physImgB_printed fname σ p hp hc hw hσ hr hzr hfd hts hnd ex hwe hP hb _ _ hside)

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate
