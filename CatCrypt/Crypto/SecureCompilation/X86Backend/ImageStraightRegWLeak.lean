/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRegW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the decoded bytes of the register arm over the class with carry chains

The gate `ImageStraightRegW.straightRegWB` compiles a register-returning straight-line
program through the cell route `cellRouteB`, at the cell fold of the chain
`ImageStraightLeak.regChain`: the chain of the program followed by the copy of its return
name into the result register, which is the observed name. The statement
`ImageStraightCellsLeak.straightCell_bytes_ct` of the cell route holds for every chain, every
cell fold of it and every list of observed names, so the constant-time statement of this arm
is its instance at `regChain`, with equal traces of the chain between public-equal entries
(`ChainCT`) from `ImageStraightLeak.regChain_run` and constant time of the source.

## Main definitions

* `straightRegWLB`: the check on traced runs of the register arm, `straightCellLB` at the
  cell fold of `regChain` with the result register observed.

## Main results

* `straightRegWB_spec`: the conjuncts of the gate `straightRegWB` used on traced runs.
* `chainCT_of_straightRegWB`: `ChainCT` of `regChain` from constant time of the source.
* `straightRegW_bytes_ct`: constant time of the decoded bytes of the register arm from the
  source, under `straightRegWB` and `straightRegWLB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRegWLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (straightT)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (scalarMemNB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak (StraightPub regChain
  regChain_run)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak (ChainCT
  chainCT_of_trace straightCellLB straightCell_bytes_ct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT
  (bytesTraceW_of_printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRegW (straightRegWB
  straightRegWB_ty)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (cellFold)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime ConstantTimeRel)

/-- **The conjuncts of the gate of the register arm** used on traced runs: the result of the
    layout a register `RA`, the stack-memory fragment, the check of the cell names, and a
    cell fold `C2` of the chain `regChain` at the export name of `RA` that passes
    `cellRouteB` with that name observed. -/
theorem straightRegWB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd} {fuse : Bool}
    {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hg : straightRegWB σ nm body fuse com = true) :
    ∃ RA C2, σ.result = .reg RA ∧ scalarMemNB com = true ∧ cellNamesOkB σ body = true
      ∧ cellFold (cellArrs σ) [] (regChain (nm RA) com) = some C2
      ∧ cellRouteB σ nm body [nm RA] C2 fuse = true := by
  simp only [straightRegWB, Bool.and_eq_true] at hg
  obtain ⟨⟨hmem, -⟩, hres⟩ := hg
  split at hres
  · rename_i RA hσ
    simp only [Bool.and_eq_true] at hres
    obtain ⟨⟨-, hN⟩, hroute⟩ := hres
    split at hroute
    · rename_i C2 hfold
      exact ⟨RA, C2, hσ, hmem, hN, hfold, hroute⟩
    · cases hroute
  · cases hres

/-- **Equal traces of the chain of the register arm from the source.** For a program in the
    stack-memory fragment and a printed body that passes the entry check: if the source
    events of the program are constant time for the labels `L`, the chain `regChain` runs
    and emits equal traces from the states behind the copies of the parameter registers of
    machine states related by `StraightPub`. -/
theorem chainCT_of_straightRegWB (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {w : Nat} (com : Com jasminDialect Γ (.reg w))
    (hmem : scalarMemNB com = true) (hent : ImageAddrRoute.entryB σ nm body = true)
    (R : String) (L : Labels Γ)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com)) :
    ChainCT σ L body (regChain R com) :=
  chainCT_of_trace
    (fun V => straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V))
    (fun sa V hV => (regChain_run Pj com hmem hent R sa V hV).2)
    (fun V₁ V₂ hp => by rw [hct V₁ V₂ hp])

/-- **The check on traced runs of the register arm over the class with carry chains**: on a
    program returning a register, at a layout whose result is a register `RA` and when the
    chain `regChain` at the export name `nm RA` has the cell fold `C2`, `straightCellLB` on
    `C2` with `nm RA` observed, the pair that `straightRegWB` compares with `ownedCheckMC`;
    `false` otherwise. -/
def straightRegWLB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (fuse : Bool) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, .reg _, com =>
      match σ.result with
      | .reg RA =>
          match cellFold (cellArrs σ) [] (regChain (nm RA) com) with
          | some C2 => straightCellLB σ nm body [nm RA] C2 fuse
          | none => false
      | _ => false
  | _, _, _ => false

/-- **Constant time of the decoded bytes of the register arm over the class with carry
    chains, from the source.** Let the program `com` pass the gate `straightRegWB` at the
    fusion flag `fuse` and the check on traced runs `straightRegWLB` against the printed
    body `body`. If the source events of `com` are constant time for the labels `L`, every
    decoding of the function bytes of `body` is constant time under the regime `doitm` and
    any side condition between entry machine states related by `StraightPub`: valuations
    that agree on the public labels, both states separated, equal stack registers and equal
    array-parameter registers. -/
theorem straightRegW_bytes_ct (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {fuse : Bool} {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (hg : straightRegWB σ nm body fuse com = true)
    (hlk : straightRegWLB σ nm body fuse com = true) (L : Labels Γ)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com))
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (StraightPub σ L) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  obtain rfl := straightRegWB_ty hg
  obtain ⟨RA, C2, hσ, hmem, hN, hfold, hroute⟩ := straightRegWB_spec hg
  have hlk' : straightCellLB σ nm body [nm RA] C2 fuse = true := by
    simpa only [straightRegWLB, hσ, hfold] using hlk
  have hC := chainCT_of_straightRegWB Pj com hmem (cellRouteB_entryB hroute) (nm RA) L hct
  have hpr : printedAddrWB body = true := by
    have h := hroute
    simp only [cellRouteB, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.1.1.1.2
  exact straightCell_bytes_ct hroute hlk' hN hfold hC (bytesTraceW_of_printedAddrWB hpr) ok hdec

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRegWLeak
