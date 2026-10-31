/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalfBase
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogFuel

/-!
# The printed program on the flag machine

The printed program `printedLprog` of the back half is the owned back end
`LprogOptPipeline.ownedLprog` followed by the reload of spilled compare operands
`CmpSpillReload.cmpReload` on every function body. This module composes the theorem of the
owned back end on the fuel-stepped flag machine, `OwnedLprogFuel.ownedLprog_lsemFuelMemF`, with
the theorem of the reload, `CmpSpillReload.cmpReload_lsemFuelMemF`, into one theorem on
`printedLprog`.

The flag machine takes no step at `Lret`, so both theorems are applied to the bodies without
their trailing return (`OwnedLprogTV.dropRet`); the owned back end keeps the return of a body
that ends with one, and the reload keeps a return (`cmpReload_append_ret`).

## Main results

* `cmpReload_append_ret`: the reload maps a body ending with `Lret` to a body ending with the
  same `Lret`.
* `printedLprog_lsemFuelMemF`: the printed program on every function whose body ends with
  `Lret`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.PrintedLprogFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (Agree)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg (TagShape)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrFuelMemF
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (typeBody dropRet TagFirstSrc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFoldFuelMemF
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL (CellRelF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (isRecognizedOpn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.StackZeroize (endsWithLret dropLast_append_Lret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogFuel
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload (cmpReload cmpReloadOK)

/-- The reload of spilled compare operands maps a body followed by `Lret` to its image
    followed by the same `Lret`. -/
theorem cmpReload_append_ret (abi : IsaAbi) (Y : Lcmd) (ii : Nat) :
    cmpReload (Y ++ [⟨ii, .Lret⟩]) abi = cmpReload Y abi ++ [⟨ii, .Lret⟩] := by
  simp [cmpReload, X86Backend.CmpSpillReload.cmpReloadI, X86Backend.CmpSpillReload.spillCmp?]

/-- **`printedLprog_lsemFuelMemF`: the printed program on the functions of a program.** Every
    function `(fn, fd)` of `p` whose body ends with `Lret` has the function `(fn, fd')` in
    `printedLprog p`, with the same result registers and the body `cmpReload` of the four
    stages of `ownedLprog`. When the four stages pass the checks of
    `OwnedLprogFuel.ownedLprog_lsemFuelMemF` and the output of the two-address legalisation
    without its return passes `cmpReloadOK`, every halting run of the checked machine on the
    typed body without its return, from program counter `0` and a state `s` of `RelInv A`, is
    matched by a halting run of the typed printed body without its return from every state
    `s'` cell-related to `s`, with at most ten times the fuel. The final state `t''` agrees
    outside `R15` (`JasminLsemFuseMulHi.Agree`, with the zero flag and the function name) with
    a state `t'` related to the source final state `t` by `OwnedObs R res`. -/
theorem printedLprog_lsemFuelMemF (p : Lprog) {fn : String} {fd : Lfundef}
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
    (hcmp : cmpReloadOK tag (twoAddrBody (reallocBody fd.lfd_res (foldIndexedBody
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
          ∧ Agree t'.prog.base t''.prog.base ∧ t''.zf = t'.zf ∧ t''.prog.lfn = t'.prog.lfn := by
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
    rw [hYk, List.dropLast_concat] at hcmp
    have hpc' : s'.prog.base.lpc = 0 := hC.base.pc.trans hpc
    obtain ⟨f2, t2, hf2, hrun2, hA, hz, hl, -⟩ :=
      X86Backend.CmpSpillReload.cmpReload_lsemFuelMemF hcmp fn s' t1 hpc' f1 hrun1
    refine ⟨f2, t1, t2, by omega, ?_, hobs, hA, hz, hl⟩
    simp only [hbody0, hYk, cmpReload_append_ret, dropRet_typeBody_ret]
    exact hrun2

end CatCrypt.Crypto.SecureCompilation.Haxc.PrintedLprogFuel
