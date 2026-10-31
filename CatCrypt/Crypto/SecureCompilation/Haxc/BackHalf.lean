/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteProg
public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalfBase
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegions
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVDeadImm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRegW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

@[expose] public section

set_option autoImplicit false

/-!
# The certified loop node, the image gate of a looped program and the `Com` stage on a route

The compiler `compileA` is `haxToNF`, the chain `extChain` and the region back half
`RegionBackend.compileRegion`. This module holds three pieces of the image route of a
looped `ComL` program and the `Com` optimisation stage on a route program.

`ExportCertGate.singleLoop_export_faithful_gate` runs the certified virtual node `certNode`
under `lsemFuelMemF` from every ABI entry state (`ExportCertEntry.AbiEntryM`) to a state
whose output array is the program's denotation. `certNode_eq` splits `certNode` into its
renamed seeds `certSeeds` and the guarded loop over its renamed body `certBody`, the form
the image route checks (generalising `DecodeGenNodeLogic.logicNode_eq` to every certified
node).

The image gate `v1LoopB` compares the renamed seeds and guarded loop of the certified node of
a looped program with the image of a printed body (`X86Backend.ImageAddrRoute.routeB`), and
`v1LoopLB` is its check on traced runs. `ComposeCTProved.v1Loop_bytes_ct` derives constant
time of the decoded bytes of a printed body that passes both.

The stage `RouteProg.opt` rewrites a straight-line program by `ComPipeline.optCom` and every
straight-line piece of a looped program by `optComL`, and keeps the denotation
(`RouteProg.opt_denote`); `RouteProgJ.opt` applies it to a route program and keeps a
structured program.

## Main results

* `certRen`, `certSeeds`, `certBody`, `certNode_eq` — the certified node as seeds and guarded
  loop.
* `v1LoopB`, `v1LoopLB` — the image gate of a looped program and its check on traced runs.
* `optComL`, `optComL_denote`, `RouteProg.opt`, `RouteProg.opt_denote` — the `Com`
  optimisation stage on a looped program and on a route's program, and their denotations.
* `RouteProgJ.opt`, `RouteProgJ.opt_denoteF` — the stage on a `RouteProgJ` program and its
  denotation at every fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (forLoopLcmdNRtRM
  forLoopBodyNRtRM loopSeedsRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (guardedFlagLoopLinstrRM
  lsemFuelMemF LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert (certRho certSlots)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop (certNode loopInvOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate (singleLoopB
  singleLoop_export_faithful_gate)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (arrMemNB comExpOKB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody (loopCertNB comLCertNB
  loopCertB_of_loopCertNB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (singleLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## 1. The certified node as seeds and guarded loop -/

section Node

variable {Γ : Ctxt jasminDialect} {n : Nat} {invTys : Ctxt jasminDialect}

/-- The renaming of the certified node: `certRho` at loop depth `Γ.length`, accumulator
    register `regName Γ.length`, output register `out` and the store slots of `update`. -/
def certRen (update : Com jasminDialect
      (JasminTy.stackArr 64 n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr 64 n))
    (out : String) : String → String :=
  certRho Γ.length (regName Γ.length) out (certSlots update)

/-- The renamed seeds of the certified node. -/
def certSeeds (update : Com jasminDialect
      (JasminTy.stackArr 64 n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr 64 n))
    (out c : String) : List LinstrRM :=
  (loopSeedsRM Γ.length (regName Γ.length) (.reg out) (.reg c)).map
    (renRM (certRen (Γ := Γ) update out))

/-- The renamed looped segment of the certified node. -/
def certBody (update : Com jasminDialect
      (JasminTy.stackArr 64 n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr 64 n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (out : String) : List LinstrRM :=
  (forLoopBodyNRtRM Γ.length (regName Γ.length) update (loopInvOps invs) (fun _ => none)).map
    (renRM (certRen (Γ := Γ) update out))

/-- The certified node is its renamed seeds followed by the guarded loop over its renamed
    looped segment, on the renamed counter. -/
theorem certNode_eq (update : Com jasminDialect
      (JasminTy.stackArr 64 n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr 64 n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (out c : String) :
    certNode update invs out c = certSeeds (Γ := Γ) update out c ++
      guardedFlagLoopLinstrRM Γ.length (Γ.length + 0x40000000)
        (certRen (Γ := Γ) update out (loopCtr Γ.length)) (certBody update invs out) := by
  unfold certNode forLoopLcmdNRtRM
  rw [List.map_append, JasminLsemExportCanon.guardedFlagLoopLinstrRM_map_renRM]
  rfl

end Node

/-! ## 2. The image gate of a looped program -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (argBind slotArrOf synthRen
  routeB routeB_abiEntry image_route_bytes resultOf_words)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg virtImg)

/-- **The image gate of a looped program.** The program is one runtime-count loop over a word
    array of `m` words whose continuation returns the loop's result, its update passes the
    fragment checks `arrMemNB` and `comExpOKB` and it passes `loopCertNB` (so it passes
    `singleLoopB` by `loopCertB_of_loopCertNB`, with no check on the exported body),
    its seed and count resolve to registers `out` and `c`, the result of `σ` is the `m` words
    at the register `RA` of the parameter `out`, the slot of `RA` holds the array `out`, and
    the renamed seeds and guarded loop of its certified node pass the checks of the image
    route `routeB` against the printed body `body`, with the export register names, the
    renaming `synthRen` computes and the fusion flag `fuse`. -/
def v1LoopB (σ : AbiLayout) (a : AbiNames) (fuse : Bool) (body : Lcmd) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → Bool
  | Γ, _, @ComL.forLoopNRt _ (.stackArr 64 m) _ _ update count init invs (.ret .here) =>
      (arrMemNB update && comExpOKB update && loopCertNB update count init invs) &&
        match resolveVar Γ.length Γ.length argName (fun _ => none) init,
            resolveVar Γ.length Γ.length argName (fun _ => none) count with
        | .reg out, .reg c =>
            let seeds := certSeeds (Γ := Γ) update out c
            let loop := guardedFlagLoopLinstrRM Γ.length (Γ.length + 0x40000000)
              (certRen (Γ := Γ) update out (loopCtr Γ.length)) (certBody update invs out)
            let pre := argBind σ exportReg ++ seeds
            let ps := synthRen (pre ++ loop) (virtImg (slotArrOf σ exportReg) body) pre.length
            (match σ.result with
              | .words RA k => k == m && abiReg σ out == some RA
                  && slotArrOf σ exportReg (slotOfReg (exportReg RA)) == some (out, m)
              | _ => false)
            && routeB σ exportReg body seeds loop ps fuse out
        | _, _ => false
  | _, _, _ => false

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (virtB slotRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML)

/-- **The check on traced runs of the image gate of a looped program**: on a program of the
    shape `v1LoopB` accepts, `ownedCheckML` on the virtual body and the image of the printed
    body `body` that `v1LoopB` compares with `ownedCheckMC`; `false` on every other
    program. -/
def v1LoopLB (σ : AbiLayout) (fuse : Bool) (body : Lcmd) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → Bool
  | Γ, _, @ComL.forLoopNRt _ (.stackArr 64 _) _ _ update count init invs (.ret .here) =>
      match resolveVar Γ.length Γ.length argName (fun _ => none) init,
          resolveVar Γ.length Γ.length argName (fun _ => none) count with
      | .reg out, .reg c =>
          let seeds := certSeeds (Γ := Γ) update out c
          let loop := guardedFlagLoopLinstrRM Γ.length (Γ.length + 0x40000000)
            (certRen (Γ := Γ) update out (loopCtr Γ.length)) (certBody update invs out)
          let pre := argBind σ exportReg ++ seeds
          let ps := synthRen (pre ++ loop) (virtImg (slotArrOf σ exportReg) body) pre.length
          ownedCheckML [] (virtB σ exportReg seeds loop ps fuse)
            (virtImg (slotRen (slotArrOf σ exportReg) (renOf ps)) body)
      | _, _ => false
  | _, _, _ => false

/-! ## 3. The `Com` optimisation stage on a route's program -/

/-- The `Com` optimisation stage `ComPipeline.optCom` applied to every straight-line `Com`
    of a looped program: the update of each loop node, the inner count and inner update of a
    nested loop node, and, recursively, the block body of a block-body loop node and every
    continuation. Bindings, seeds, counts and invariants are kept. -/
def optComL : {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → ComL Γ t
  | _, _, .ret v => .ret v
  | _, _, .var e body => .var e (optComL body)
  | _, _, .forLoop loop init body =>
      .forLoop ⟨loop.n, CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom loop.update⟩ init
        (optComL body)
  | _, _, .forLoopN loop init invs body =>
      .forLoopN ⟨loop.n, CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom loop.update⟩ init
        invs (optComL body)
  | _, _, .forLoopNRt update count init invs body =>
      .forLoopNRt (CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom update) count init invs
        (optComL body)
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body =>
      .forLoopNRtNested (CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom innerCount)
        (CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom innerUpdate) outerCount init invs
        (optComL body)
  | _, _, .whileNz update guard init invs body =>
      .whileNz (CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom update) guard init invs
        (optComL body)
  | _, _, .forLoopBlock loopBody count init invs body =>
      .forLoopBlock (optComL loopBody) count init invs (optComL body)

/-- **Denotation of the stage on a looped program.** `optComL c` denotes the same function
    as `c`. -/
theorem optComL_denote : {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : ComL Γ t) →
    (optComL c).denote = c.denote
  | _, _, .ret v => rfl
  | _, _, .var e body => by
      funext V; simp only [optComL, ComL.denote, optComL_denote body]
  | _, _, .forLoop loop init body => by
      funext V
      simp only [optComL, ComL.denote, optComL_denote body, JLoopBody.denote, JLoopBody.stepC,
        CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom_denote]
  | _, _, .forLoopN loop init invs body => by
      funext V
      simp only [optComL, ComL.denote, optComL_denote body, JLoopBodyN.denote,
        JLoopBodyN.stepC, CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom_denote]
  | _, _, .forLoopNRt update count init invs body => by
      funext V
      simp only [optComL, ComL.denote, optComL_denote body, JLoopBodyN.stepC,
        CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom_denote]
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body => by
      funext V
      simp only [optComL, ComL.denote, optComL_denote body, JLoopBodyN.nestedDenote,
        JLoopBodyN.innerTripAtC, JLoopBodyN.stepCNested,
        CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom_denote]
  | _, _, .whileNz update guard init invs body => by
      funext V
      simp only [optComL, ComL.denote, optComL_denote body, JLoopBodyN.stepC,
        CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom_denote]
  | _, _, .forLoopBlock loopBody count init invs body => by
      funext V
      simp only [optComL, ComL.denote, optComL_denote body, optComL_denote loopBody]

/-- **The `Com` optimisation stage on a route's program**: `ComPipeline.optCom` on a
    straight-line program and `optComL` on a looped program. -/
def RouteProg.opt {Γ : Ctxt jasminDialect} {t : JasminTy} : RouteProg Γ t → RouteProg Γ t :=
  RouteProg.elim
    (fun c => .straight (CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom c))
    (fun c => .loop (optComL c))

/-- The stage on a straight-line program is `ComPipeline.optCom`. -/
theorem RouteProg.opt_straight {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) :
    (RouteProg.straight c).opt
      = .straight (CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom c) :=
  RouteProg.elim_straight _ _ c

/-- The stage on a program with a loop node is `optComL`. -/
theorem RouteProg.opt_loop {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (hc : c.toCom? = none) : (RouteProg.loop c).opt = .loop (optComL c) :=
  RouteProg.elim_loop _ _ hc

/-- **Denotation of the stage on a route's program.** `p.opt` denotes the same function as
    `p`. -/
theorem RouteProg.opt_denote {Γ : Ctxt jasminDialect} {t : JasminTy} (p : RouteProg Γ t) :
    p.opt.denote = p.denote := by
  cases p using RouteProg.cases_straight_loop with
  | straight c =>
      funext V
      simp only [RouteProg.opt_straight, RouteProg.denote_straight,
        CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.optCom_denote]
  | loop c hc =>
      funext V
      simp only [RouteProg.opt_loop c hc, RouteProg.denote_loop, optComL_denote]

/-- The `Com` optimisation stage on a `RouteProgJ` program: `RouteProg.opt` on a route
    program; a structured program is kept. -/
def RouteProgJ.opt {Γ : Ctxt jasminDialect} {t : JasminTy} : RouteProgJ Γ t → RouteProgJ Γ t
  | .straightLoop rp => .straightLoop rp.opt
  | .regions p => .regions p

/-- **Denotation of the stage on a `RouteProgJ` program.** `p.opt` denotes, at every fuel,
    the same function as `p`. -/
theorem RouteProgJ.opt_denoteF {Γ : Ctxt jasminDialect} {t : JasminTy} (p : RouteProgJ Γ t)
    (fuel : Nat) : p.opt.denoteF fuel = p.denoteF fuel := by
  cases p with
  | straightLoop rp =>
      funext V
      simp only [RouteProgJ.opt, RouteProgJ.denoteF, RouteProg.opt_denote]
  | regions p => rfl

end CatCrypt.Crypto.SecureCompilation.Haxc
