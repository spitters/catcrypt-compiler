/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.PrintedLprogFuel
public import CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxTail
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSem

/-!
# The printed program of the region post-pass on the flag machine

The printed program `printedLprog` is the owned back end followed by the compare reload
`CmpSpillReload.cmpReload`. On a body in which no instruction is a compare on a spilled first
operand (`CmpSpillReload.spillCmp?`), the reload is the identity
(`CmpSpillReload.cmpReload_of_forall`), and the theorem of the owned back end,
`OwnedLprogFuel.ownedLprog_lsemFuelMemF`, holds for the printed program with the final states
related by `OwnedObs` alone.

Applied to the region post-pass read through the width reading of `MULX`,
`mapBodies normMulxBody (regionPostFuse P)`, and composed with
`RegionPostFuseLift.regionPostFuse_lsemFuelMemF` and the commutation
`NormMulxTail.printedLprog_mapBodies_normMulxBody`, a halting run of a function body of `P` gives a
halting run of the corresponding body of `printedLprog (regionPostFuse P)` read through
`normMulxBody`. The source run of the printed theorem is the checked machine; the region post-pass
yields an unchecked run, which is a checked run when its accesses are in bounds
(`JasminLsemMemChecked.lsemFuelMemFk_of_runIdxOk`).

The theorems of these passes are stated on typed bodies `typeBody tag b`, which read an array
through the name of the base operand of an access. The allocation of the region back half reloads
every array base into `R14` before the access, so on typed physical bodies all arrays of an
allocated body are the one array `R14`. The gate of the region back half compares its reference
with the image `JasminLsemAddrImage.virtImg sl (ImageAddrCells.cellBody sl b)`, in which each
access names the array whose pointer its base holds, and the image simulation
`ImageAddrCells.image_addr_simBW` starts from runs of that image. The image is a typed body of the
image body `PhysImgSem.imgL` at a tag of the instruction shape
(`PhysImgSem.virtImg_eq_typeBody_of_imgL_eq`): when a pass commutes with the image (the image
body of the pass output is the pass applied to the image body of its input) and the tags of the
two images are functions of the instruction shape (`PhysImgSem.shapeFunB`), the typed theorem of
the pass holds between the two images. Section 2 states it for the dead-write elimination
`deadWriteRet` and for the block optimiser `optimizeBasicBlocks`.

## Main results

* `printedLprog_lsemFuelMemF_noCmp`: the printed program on a function whose two-address
  body has no compare on a spilled first operand.
* `regionPrinted_lsemFuelMemF`: the printed program of the region post-pass, read through
  `normMulxBody`, on the functions of a program.
* `deadWriteRet_virtImg`: the dead-write elimination between images.
* `optimizeBasicBlocks_virtImg`: the block optimiser between images, as a whole-body simulation
  from states of the bridge invariant `RelInv`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPrintedFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (Agree E64 fuseMulHiOK fuseMulHiRM)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg (TagShape)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrFuelMemF
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFoldFuelMemF
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL (CellRelF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (isRecognizedOpn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.StackZeroize (endsWithLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogFuel
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
  (cmpReload spillCmp? cmpReload_of_forall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.DeadWriteRetSound
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseLift
  (normMulxBody regionPostFuse_lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxFold (MulxShaped)
open CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxTail
  (printedLprog_mapBodies_normMulxBody mulxUntied_x86Data)

/-- **`printedLprog_lsemFuelMemF_noCmp`: the printed program on a body without a compare on a
    spilled first operand.** Every function `(fn, fd)` of `p` whose body ends with `Lret` has
    the function `(fn, fd')` in `printedLprog p`, with the same result registers and the body of
    the four stages of `ownedLprog`, when no instruction of that body is a compare on a spilled
    first operand (`spillCmp?`, decided). When the four stages pass the checks of
    `OwnedLprogFuel.ownedLprog_lsemFuelMemF`, every halting run of the checked machine on the
    typed body without its return, from program counter `0` and a state `s` of `RelInv A`, is
    matched by a halting run of the typed printed body without its return from every state
    `s'` cell-related to `s`, with at most five times the fuel, into a state related to the
    source final state by `OwnedObs R res`. -/
theorem printedLprog_lsemFuelMemF_noCmp (p : Lprog) {fn : String} {fd : Lfundef}
    (hf : (fn, fd) ∈ p.lp_funcs) (hend : endsWithLret fd.lfd_body = true)
    {A : String → Option Nat} {tag : LinstrR → MemTag} (hT : TagShape tag) (hF : TagFirstSrc tag)
    (htag : ∀ d opn srcs, isRecognizedOpn opn = true → opn ≠ "LOADIDX" → opn ≠ "STOREIDX" →
      tag (.Lopn [.reg d] opn srcs) = .reg none)
    {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    (hres : ∀ y ∈ fd.lfd_res, isFrame y = false)
    (hbb : optBlocksOKB A tag fd.lfd_body.dropLast = true)
    (hfold : FoldIndexedOK tag R (optimizeBasicBlocks fd.lfd_body.dropLast))
    (hra : reallocCfgOKB tag isRecognizedOpn
      (foldIndexedBody (optimizeBasicBlocks fd.lfd_body)) = true)
    (htw : twoAddrOK tag (reallocBody fd.lfd_res (foldIndexedBody
      (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn).dropLast = true)
    (hnc : (twoAddrBody (reallocBody fd.lfd_res (foldIndexedBody
      (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn)).all
        (fun i => (spillCmp? i.li_i).isNone) = true) :
    ∃ fd', (fn, fd') ∈ (printedLprog p).lp_funcs ∧ fd'.lfd_res = fd.lfd_res
      ∧ fd'.lfd_body = twoAddrBody (reallocBody fd.lfd_res
          (foldIndexedBody (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn)
      ∧ ∀ {fuel : Nat} {s s' t : LstateMF}, s.prog.base.lpc = 0 → RelInv A s.prog.base →
        CellRelF R [] s s' →
        lsemFuelMemFk true (singletonProgM fn (dropRet (typeBody tag fd.lfd_body))) fuel s
          = some t →
        ∃ fuel' t', fuel' ≤ fuel * 5
          ∧ lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag fd'.lfd_body))) fuel' s'
              = some t'
          ∧ OwnedObs R fd.lfd_res t t' := by
  obtain ⟨fd0, hmem, hres0, hbody0, hsim⟩ :=
    ownedLprog_lsemFuelMemF p hf hend hT hF htag hR hD hres hbb hfold hra htw
  have hid : cmpReload fd0.lfd_body = fd0.lfd_body := by
    refine cmpReload_of_forall fun i hi => ?_
    rw [hbody0] at hi
    simpa using List.all_eq_true.mp hnc i hi
  refine ⟨fd0, ?_, hres0, hbody0, hsim⟩
  have hm : (fn, { fd0 with lfd_body := cmpReload fd0.lfd_body }) ∈ (printedLprog p).lp_funcs := by
    simp only [printedLprog, mapBodies, List.mem_map]
    exact ⟨(fn, fd0), hmem, rfl⟩
  simpa only [hid] using hm

/-- **`regionPrinted_lsemFuelMemF`: the printed program of the region post-pass, read through
    `normMulxBody`.** Let `(fn, fd)` be a function of `P`, and `B` the body
    `normMulxBody (deadWriteRet (fuseMulHiBody fd.lfd_body true))` of its region post-pass read
    through the width reading of `MULX`. The hypotheses are decided on the bodies: those of
    `RegionPostFuseLift.regionPostFuse_lsemFuelMemF` on `fd`; those of
    `printedLprog_lsemFuelMemF_noCmp` on `B`; and those of
    `NormMulxTail.printedLprog_mapBodies_normMulxBody` on every function of `regionPostFuse P`.
    Then `printedLprog (regionPostFuse P)` has a function `(fn, fdp)` with the result registers
    of `fd`, and every halting run of the typed body of `fd` without its return, from program
    counter `0`, function `fn` and a state `s` of `RelInv A` whose registers in `E` have width
    `64`, ends in a state `t` with the following intermediate states. A state `t1` agrees with
    `t` outside `R15`, on the zero flag and the function name; the typed `B` without its return
    halts from `s` in a state `t2` with `Obs outs t1 t2`; and when every access of that run is
    in bounds (`RunIdxOk`), the typed `normMulxBody fdp.lfd_body` without its return halts from
    every state `s'` cell-related to `s` in a state `t3` with `OwnedObs R fd.lfd_res t2 t3`. -/
theorem regionPrinted_lsemFuelMemF (P : Lprog) {fn : String} {fd : Lfundef}
    (hf : (fn, fd) ∈ P.lp_funcs)
    {A : String → Option Nat} {tag : LinstrR → MemTag} (hT : TagShape tag) (hF : TagFirstSrc tag)
    (htag : ∀ d opn srcs, isRecognizedOpn opn = true → opn ≠ "LOADIDX" → opn ≠ "STOREIDX" →
      tag (.Lopn [.reg d] opn srcs) = .reg none)
    {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    {E : List String}
    (hok : fuseMulHiOK E (dropRet (typeBody tag fd.lfd_body)) = true)
    (hty : fuseMulHiRM (dropRet (typeBody tag fd.lfd_body))
      = dropRet (typeBody tag (normMulxBody (fuseMulHiBody fd.lfd_body true))))
    (hdw : ∀ i ∈ normMulxBody (fuseMulHiBody fd.lfd_body true),
      deadWriteStepOK tag i.li_i = true)
    (hfrag : symRun (dropRet (typeBody tag (normMulxBody (fuseMulHiBody fd.lfd_body true))))
      SSt.start ≠ .unk)
    (hcomm : deadWriteRet (normMulxBody (fuseMulHiBody fd.lfd_body true))
      = normMulxBody (deadWriteRet (fuseMulHiBody fd.lfd_body true)))
    {B : Lcmd} (hB : normMulxBody (deadWriteRet (fuseMulHiBody fd.lfd_body true)) = B)
    (hend : endsWithLret B = true)
    (hres : ∀ y ∈ fd.lfd_res, isFrame y = false)
    (hbb : optBlocksOKB A tag B.dropLast = true)
    (hfold : FoldIndexedOK tag R (optimizeBasicBlocks B.dropLast))
    (hra : reallocCfgOKB tag isRecognizedOpn (foldIndexedBody (optimizeBasicBlocks B)) = true)
    (htw : twoAddrOK tag (reallocBody fd.lfd_res (foldIndexedBody
      (optimizeBasicBlocks B)) x86Abi isRecognizedOpn).dropLast = true)
    (hnc : (twoAddrBody (reallocBody fd.lfd_res (foldIndexedBody
      (optimizeBasicBlocks B)) x86Abi isRecognizedOpn)).all
        (fun i => (spillCmp? i.li_i).isNone) = true)
    (hP : ∀ nf ∈ (regionPostFuse P).lp_funcs,
      MulxShaped (optimizeBasicBlocks nf.2.lfd_body) = true
        ∧ bodyIsU64 (optimizeBasicBlocks nf.2.lfd_body) = true
        ∧ bodyIsU64 (dropDeadCore (bodyParams (optimizeBasicBlocks nf.2.lfd_body))
            (constIndexFoldBody (optimizeBasicBlocks nf.2.lfd_body))) = true) :
    ∃ fdp, (fn, fdp) ∈ (printedLprog (regionPostFuse P)).lp_funcs ∧ fdp.lfd_res = fd.lfd_res
      ∧ ∀ (outs : List String) {fuel : Nat} {s s' t : LstateMF}, s.prog.lfn = fn →
        s.prog.base.lpc = 0 → E64 E s.prog.base → RelInv A s.prog.base → CellRelF R [] s s' →
        (∀ f, RunIdxOk (singletonProgM fn (dropRet (typeBody tag B))) f s) →
        lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag fd.lfd_body))) fuel s = some t →
        ∃ t1 t2 fuel' t3, Agree t.prog.base t1.prog.base ∧ t1.zf = t.zf
          ∧ t1.prog.lfn = t.prog.lfn ∧ Obs outs t1 t2
          ∧ lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag (normMulxBody fdp.lfd_body))))
              fuel' s' = some t3
          ∧ OwnedObs R fd.lfd_res t2 t3 := by
  obtain ⟨fd'', hmem'', hres'', hbody'', hsim1⟩ :=
    regionPostFuse_lsemFuelMemF P hf tag hok hty hdw hfrag hcomm
  have hmemN : (fn, { fd'' with lfd_body := B })
      ∈ (mapBodies normMulxBody (regionPostFuse P)).lp_funcs := by
    simp only [mapBodies, List.mem_map]
    exact ⟨(fn, fd''), hmem'', by rw [hbody'', hB]⟩
  rw [← hres''] at hres htw hnc
  obtain ⟨fd', hmem', hres', -, hsim2⟩ :=
    printedLprog_lsemFuelMemF_noCmp _ hmemN hend hT hF htag hR hD hres hbb hfold hra htw hnc
  rw [printedLprog_mapBodies_normMulxBody _ mulxUntied_x86Data hP] at hmem'
  simp only [mapBodies, List.mem_map, Prod.mk.injEq] at hmem'
  obtain ⟨⟨fn0, fdp⟩, hmemp, rfl, rfl⟩ := hmem'
  refine ⟨fdp, hmemp, by simpa [hres''] using hres', ?_⟩
  intro outs fuel s s' t hfn hpc hE hI hC hidx hrun
  obtain ⟨t1, f2, t2, hA, hz, hl, hrun2, hobs⟩ := hsim1 outs hfn hpc hE hrun
  rw [hbody'', hB] at hrun2
  have hck := lsemFuelMemFk_of_runIdxOk true _ f2 s t2 hrun2 (hidx f2)
  obtain ⟨f3, t3, -, hrun3, hobs3⟩ := hsim2 hpc hI hC hck
  exact ⟨t1, t2, f3, t3, hA, hz, hl, hobs, hrun3, by simpa [hres''] using hobs3⟩

/-! ## 2. The passes between images -/

section Image

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSem

/-- **`deadWriteRet_virtImg`: the dead-write elimination between images.** Let the image body
    of `c` be `deadWriteRet` of the image body of `b`, let the tags of the images of `b` and `c`
    together be functions of the instruction shape, let every instruction of the image body of
    `b` pass `deadWriteStepOK` at the tag `shapeTag` of the two images, and let the symbolic run
    of the image of `b` be inside the fragment. Every halting run of the flag machine on the
    image of `b`, from a state at pc `0` of its function, is matched by a halting run on the
    image of `c` from the same state, and the end states agree on the registers `outs`, on the
    arrays and on the word memory (`Obs outs`). -/
theorem deadWriteRet_virtImg (outs : List String) {sl : String → Option (String × Nat)}
    {b c : Lcmd} (hc : imgL sl c = deadWriteRet (imgL sl b))
    (h : shapeFunB (virtImg sl b ++ virtImg sl c) = true)
    (hok : ∀ i ∈ imgL sl b,
      deadWriteStepOK (shapeTag (virtImg sl b ++ virtImg sl c)) i.li_i = true)
    (hfrag : symRun (virtImg sl b) SSt.start ≠ .unk)
    (fn : String) (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (fuel : Nat) (hrun : lsemFuelMemF (singletonProgM fn (virtImg sl b)) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemF (singletonProgM fn (virtImg sl c)) fuel' s = some t'
      ∧ Obs outs t t' := by
  obtain ⟨hb, hc'⟩ := virtImg_eq_typeBody_of_imgL_eq hc h
  rw [hb] at hfrag hrun
  rw [hc']
  exact deadWriteRet_lsemFuelMemF outs _ _ hok hfrag fn s t hfn hpc fuel hrun

/-- **`optimizeBasicBlocks_virtImg`: the block optimiser between images.** Let the image body of
    `c` be `optimizeBasicBlocks` of the image body of `b`, let the tags of the images of `b` and
    `c` together be functions of the instruction shape, and let the image body of `b` without
    its return pass `optBlocksOKB A` at the tag `shapeTag` of the two images. Then every
    checked halting run of the image of `b` from program counter `0` and a state of `RelInv A`
    is matched by a halting run of the image of `c` from the same state with at most the same
    fuel, to a state with the same function name and zero flag and a base equal up to the
    program counter, which satisfies `RelInv A` (`WholeBodySim`). -/
theorem optimizeBasicBlocks_virtImg {A : String → Option Nat}
    {sl : String → Option (String × Nat)} {b c : Lcmd}
    (hc : imgL sl c = optimizeBasicBlocks (imgL sl b))
    (h : shapeFunB (virtImg sl b ++ virtImg sl c) = true)
    (hok : optBlocksOKB A (shapeTag (virtImg sl b ++ virtImg sl c)) (imgL sl b).dropLast = true)
    (fn : String) :
    WholeBodySim true (RelInv A) fn (virtImg sl b) (virtImg sl c) := by
  obtain ⟨hb, hc'⟩ := virtImg_eq_typeBody_of_imgL_eq hc h
  have hT := tagShape_shapeTag (virtImg sl b ++ virtImg sl c)
  generalize shapeTag (virtImg sl b ++ virtImg sl c) = T at hb hc' hok hT
  have hopt : dropRet (typeBody T (optimizeBasicBlocks (imgL sl b)))
      = typeBody T (optimizeBasicBlocks (imgL sl b).dropLast) := by
    cases hj : b.getLast? with
    | none =>
        rw [List.getLast?_eq_none_iff.mp hj]
        rfl
    | some j =>
        rw [imgL_eq_dropLast_append hj, X86Backend.OwnedLprogFuel.optimizeBasicBlocks_append_ret,
          dropRet_typeBody_of_ret T _ _ rfl, List.dropLast_concat]
  rw [hb, hc', dropRet_typeBody_imgL_eq_dropLast, hopt]
  intro fuel s t
  exact optBlocksOKB_sound hT hok fn

end Image

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPrintedFuel
