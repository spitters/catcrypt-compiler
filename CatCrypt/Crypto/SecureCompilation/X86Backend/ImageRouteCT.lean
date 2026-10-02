/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the decoded bytes of the image route from the source

The image route compiles the certified single-loop node through the virtual body `virtB`,
which the register allocation checker compares with the image `virtImg` of the printed body.
Three steps give constant time of the decoded bytes of the printed body from constant time of
the source program:

* `ImageAddrLeak.virtB_memFCT`: constant time of the virtual body on the flag machine from
  public-equal route entries;
* `OwnedTVLeak.memFCT_of_ownedCheckML`: constant time of the image, between public-equal
  entries from which the virtual body has halting checked runs, when the checker on traced
  runs `ownedCheckML` accepts the virtual body against the image;
* `DecodePrintedAddrLeak.image_bytes_ct`: constant time of the decoded bytes from constant
  time of the image, for a printed body without a conditional branch.

## Main results

* `route_bytes_ct`: constant time of the decoded bytes of the printed body under the regime
  `doitm` from constant time of the source events of the single-loop program.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageRouteCT

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (MemFCT)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd (ComExpOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop (certNode loopCertB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (routeB virtB slotRen
  slotArrOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (RouteEntryPub virtB_memFCT)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (singleLoop)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels PubEqV)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn imgGateB_frameMark)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (NoCond)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (ImgBytePub
  image_bytes_ct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML TVPub
  memFCT_of_ownedCheckML)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)

/-- **Constant time of the decoded bytes of the image route from the source.** Let the
    printed body `body`, the certified node `seeds ++ loop`, the renaming `ps` and the fusion
    flag `fuse` pass the route check `routeB`, the seeds emit no event, and the checker on
    traced runs `ownedCheckML` accept the virtual body against the image of `body`. Let
    `body` have no conditional branch, decode, and be separated at its frame below `rsp`.
    If the source events of the single-loop program are constant time for the labels `L`,
    the decoded function bytes of `body` are constant time under the regime `doitm` and any
    side condition, between machine states with the frame address `rsp` that correspond at
    entry to image states public-equal through the image (`ImgBytePub`), for the public
    relation on image states: public-equal route entries (`RouteEntryPub`) at pc `0` from
    which the virtual body has halting checked runs (`TVPub`). -/
theorem route_bytes_ct (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    {σ : AbiLayout} {nm : String → String} {body : Lcmd} {seeds loop : List LinstrRM}
    {ps : List (String × String)} {fuse : Bool} {outR : String}
    (hg : routeB σ nm body seeds loop ps fuse outR = true)
    (hnode : seeds ++ loop = certNode update invs out c)
    (hqs : ∀ i ∈ seeds, ∀ r, JasminLsemMemFLeak.instrLeakB r i = []) (L : Labels Γ)
    (fn : String)
    (hct : CT.ConstantTime (PubEqV L)
      (ComL.ctLeak (jLeakModel Pj) (singleLoop update count init invs)))
    (hlk : ownedCheckML [] (virtB σ nm seeds loop ps fuse)
      (virtImg (slotRen (slotArrOf σ nm) (renOf ps)) body) = true)
    {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : ImgSep (frameIn body (frameP (Params.ofBody body) rsp))
      (slotRen (slotArrOf σ nm) (renOf ps)) base rsp)
    (hnc : NoCond body) (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel
      (ImgBytePub rsp (slotRen (slotArrOf σ nm) (renOf ps)) base body fn
        (TVPub fn (virtB σ nm seeds loop ps fuse) (RouteEntryPub σ body ps fn L)))
      (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  have hg' := hg
  simp only [routeB, Bool.and_eq_true] at hg'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hpr⟩, hphys⟩, hgate⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg'
  have hgate' : ImageAddrSim.imgGateB (frameIn body (frameP (Params.ofBody body) rsp))
      (slotRen (slotArrOf σ nm) (renOf ps)) body = true := by
    rw [imgGateB_frameMark]; exact hgate
  exact image_bytes_ct hpr hphys hgate' hsep hnc fn
    (memFCT_of_ownedCheckML hlk fn (virtB_memFCT Pj update count init invs outArg inArgs
      abiArgs hupd hexp hcert out c hi hcn hg hnode hqs L fn hct)) ok hdec

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageRouteCT
