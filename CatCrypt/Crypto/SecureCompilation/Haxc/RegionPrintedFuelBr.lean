/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPrintedFuel
public import CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracketSim

/-!
# The printed program of the region post-pass with `R15` brackets

The printed program `printedLprog` is the owned back end followed by the compare reload
`CmpSpillReload.cmpReload`. On a two-address body passing the bracket-aware check
`CmpReloadBracket.cmpReloadBrOK`, the reload preserves halting runs
(`CmpReloadBracketSim.cmpReloadBr_lsemFuelMemF`): the final bases agree outside `R15`
(`JasminLsemFuseMulHi.Agree`) and have equal arrays `R15`. Composed with the theorem of the
owned back end, `OwnedLprogFuel.ownedLprog_lsemFuelMemF`, this gives a theorem on the printed
program, and composed further as in `RegionPrintedFuel.regionPrinted_lsemFuelMemF`, a theorem on
the printed program of the region post-pass read through `normMulxBody`. The register `R15` is
callee-saved and observed at return, so the reload's write to `R15` is recorded as one more
intermediate state, related to the final state by `Agree` and equal arrays `R15`.

## Main results

* `printedLprog_lsemFuelMemF_br`: the printed program on a function whose two-address body
  without its return passes `cmpReloadBrOK`.
* `regionPrinted_lsemFuelMemF_br`: the printed program of the region post-pass, read through
  `normMulxBody`, on the functions of a program whose two-address bodies pass `cmpReloadBrOK`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPrintedFuelBr

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.StackZeroize (endsWithLret dropLast_append_Lret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogFuel
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload (cmpReload)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.DeadWriteRetSound
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseLift
  (normMulxBody regionPostFuse_lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxFold (MulxShaped)
open CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxTail
  (printedLprog_mapBodies_normMulxBody mulxUntied_x86Data)
open CatCrypt.Crypto.SecureCompilation.Haxc.PrintedLprogFuel (cmpReload_append_ret)
open CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracket (cmpReloadBrOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracketSim (cmpReloadBr_lsemFuelMemF)

/-- **`printedLprog_lsemFuelMemF_br`: the printed program on a body passing the bracket-aware
    reload check.** Every function `(fn, fd)` of `p` whose body ends with `Lret` has the
    function `(fn, fd')` in `printedLprog p`, with the same result registers and the body
    `cmpReload` of the four stages of `ownedLprog`. When the four stages pass the checks of
    `OwnedLprogFuel.ownedLprog_lsemFuelMemF` and the output of the two-address legalisation
    without its return passes `cmpReloadBrOK`, every halting run of the checked machine on the
    typed body without its return, from program counter `0` and a state `s` of `RelInv A`, is
    matched by a halting run of the typed printed body without its return from every state
    `s'` cell-related to `s`, with at most ten times the fuel. The final state `t''` agrees
    outside `R15` with a state `t'` related to the source final state `t` by `OwnedObs R res`,
    has the array `R15` of `t'`, and the zero flag and function name of `t'`. -/
theorem printedLprog_lsemFuelMemF_br (p : Lprog) {fn : String} {fd : Lfundef}
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
    (hbr : cmpReloadBrOK tag (twoAddrBody (reallocBody fd.lfd_res (foldIndexedBody
      (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn)).dropLast = true) :
    ∃ fd', (fn, fd') ∈ (printedLprog p).lp_funcs ∧ fd'.lfd_res = fd.lfd_res
      ∧ fd'.lfd_body = cmpReload (twoAddrBody (reallocBody fd.lfd_res
          (foldIndexedBody (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn))
      ∧ ∀ {fuel : Nat} {s s' t : LstateMF}, s.prog.base.lpc = 0 → RelInv A s.prog.base →
        CellRelF R [] s s' →
        lsemFuelMemFk true (singletonProgM fn (dropRet (typeBody tag fd.lfd_body))) fuel s
          = some t →
        ∃ fuel' t' t'', fuel' ≤ fuel * 10
          ∧ lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag fd'.lfd_body))) fuel' s'
              = some t''
          ∧ OwnedObs R fd.lfd_res t t'
          ∧ Agree t'.prog.base t''.prog.base
          ∧ t''.prog.base.larr "R15" = t'.prog.base.larr "R15"
          ∧ t''.zf = t'.zf ∧ t''.prog.lfn = t'.prog.lfn := by
  obtain ⟨fd0, hmem, hres0, hbody0, hsim⟩ :=
    ownedLprog_lsemFuelMemF p hf hend hT hF htag hR hD hres hbb hfold hra htw
  have hT0 : ∃ (Y : Lcmd) (k : Nat), twoAddrBody (reallocBody fd.lfd_res (foldIndexedBody
      (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn)
        = twoAddrBody Y ++ [⟨k, .Lret⟩] := by
    obtain ⟨k, hk⟩ := dropLast_append_Lret hend
    obtain ⟨Y, hY⟩ := reallocBody_append_ret fd.lfd_res x86Abi isRecognizedOpn
      (foldIndexedBody (optimizeBasicBlocks fd.lfd_body.dropLast)) k
    refine ⟨Y, k, ?_⟩
    rw [← hk, optimizeBasicBlocks_append_ret, foldIndexedBody_append_ret, hY,
      twoAddrBody_append_ret]
  obtain ⟨Y, k, hYk⟩ := hT0
  refine ⟨{ fd0 with lfd_body := cmpReload fd0.lfd_body }, ?_, hres0, ?_, ?_⟩
  · simp only [printedLprog, mapBodies, List.mem_map]
    exact ⟨(fn, fd0), hmem, rfl⟩
  · simp only [hbody0]
  · intro fuel s s' t hpc hI hC hrun
    obtain ⟨f1, t1, hf1, hrun1, hobs⟩ := hsim hpc hI hC hrun
    rw [hbody0, hYk, dropRet_typeBody_ret] at hrun1
    rw [hYk, List.dropLast_concat] at hbr
    have hpc' : s'.prog.base.lpc = 0 := hC.base.pc.trans hpc
    obtain ⟨f2, t2, hf2, hrun2, hA, h15, hz, hl, -⟩ :=
      cmpReloadBr_lsemFuelMemF hbr fn s' t1 hpc' f1 hrun1
    refine ⟨f2, t1, t2, by omega, ?_, hobs, hA, h15, hz, hl⟩
    simp only [hbody0, hYk, cmpReload_append_ret, dropRet_typeBody_ret]
    exact hrun2

/-- **`regionPrinted_lsemFuelMemF_br`: the printed program of the region post-pass, read
    through `normMulxBody`, on bodies passing the bracket-aware reload check.** Let `(fn, fd)`
    be a function of `P`, and `B` the body
    `normMulxBody (deadWriteRet (fuseMulHiBody fd.lfd_body true))` of its region post-pass read
    through the width reading of `MULX`. The hypotheses are decided on the bodies: those of
    `RegionPostFuseLift.regionPostFuse_lsemFuelMemF` on `fd`; those of
    `printedLprog_lsemFuelMemF_br` on `B`; and those of
    `NormMulxTail.printedLprog_mapBodies_normMulxBody` on every function of `regionPostFuse P`.
    Then `printedLprog (regionPostFuse P)` has a function `(fn, fdp)` with the result registers
    of `fd`, and every halting run of the typed body of `fd` without its return, from program
    counter `0`, function `fn` and a state `s` of `RelInv A` whose registers in `E` have width
    `64`, ends in a state `t` with the following intermediate states. A state `t1` agrees with
    `t` outside `R15`, on the zero flag and the function name; the typed `B` without its return
    halts from `s` in a state `t2` with `Obs outs t1 t2`; and when every access of that run is
    in bounds (`RunIdxOk`), the typed `normMulxBody fdp.lfd_body` without its return halts from
    every state `s'` cell-related to `s` in a state `t4` that agrees outside `R15` with a state
    `t3` of `OwnedObs R fd.lfd_res t2 t3`, has the array `R15` of `t3`, and the zero flag and
    function name of `t3`. -/
theorem regionPrinted_lsemFuelMemF_br (P : Lprog) {fn : String} {fd : Lfundef}
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
    (hbr : cmpReloadBrOK tag (twoAddrBody (reallocBody fd.lfd_res (foldIndexedBody
      (optimizeBasicBlocks B)) x86Abi isRecognizedOpn)).dropLast = true)
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
        ∃ t1 t2 fuel' t3 t4, Agree t.prog.base t1.prog.base ∧ t1.zf = t.zf
          ∧ t1.prog.lfn = t.prog.lfn ∧ Obs outs t1 t2
          ∧ lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag (normMulxBody fdp.lfd_body))))
              fuel' s' = some t4
          ∧ OwnedObs R fd.lfd_res t2 t3
          ∧ Agree t3.prog.base t4.prog.base
          ∧ t4.prog.base.larr "R15" = t3.prog.base.larr "R15"
          ∧ t4.zf = t3.zf ∧ t4.prog.lfn = t3.prog.lfn := by
  obtain ⟨fd'', hmem'', hres'', hbody'', hsim1⟩ :=
    regionPostFuse_lsemFuelMemF P hf tag hok hty hdw hfrag hcomm
  have hmemN : (fn, { fd'' with lfd_body := B })
      ∈ (mapBodies normMulxBody (regionPostFuse P)).lp_funcs := by
    simp only [mapBodies, List.mem_map]
    exact ⟨(fn, fd''), hmem'', by rw [hbody'', hB]⟩
  rw [← hres''] at hres htw hbr
  obtain ⟨fd', hmem', hres', -, hsim2⟩ :=
    printedLprog_lsemFuelMemF_br _ hmemN hend hT hF htag hR hD hres hbb hfold hra htw hbr
  rw [printedLprog_mapBodies_normMulxBody _ mulxUntied_x86Data hP] at hmem'
  simp only [mapBodies, List.mem_map, Prod.mk.injEq] at hmem'
  obtain ⟨⟨fn0, fdp⟩, hmemp, rfl, rfl⟩ := hmem'
  refine ⟨fdp, hmemp, by simpa [hres''] using hres', ?_⟩
  intro outs fuel s s' t hfn hpc hE hI hC hidx hrun
  obtain ⟨t1, f2, t2, hA, hz, hl, hrun2, hobs⟩ := hsim1 outs hfn hpc hE hrun
  rw [hbody'', hB] at hrun2
  have hck := lsemFuelMemFk_of_runIdxOk true _ f2 s t2 hrun2 (hidx f2)
  obtain ⟨f3, t3, t4, -, hrun3, hobs3, hA4, h15, hz4, hl4⟩ := hsim2 hpc hI hC hck
  exact ⟨t1, t2, f3, t3, t4, hA, hz, hl, hobs, hrun3, by simpa [hres''] using hobs3,
    hA4, h15, hz4, hl4⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPrintedFuelBr
