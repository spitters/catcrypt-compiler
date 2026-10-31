/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend

set_option autoImplicit false

/-!
# The stages of the region back half, one at a time

The stages of `compileRegion` on a structured program with one result and no `call`, as a
trace that is computed one node per stage: each node of a `StageTrace` holds the name of
the stage, a size of its output, and the rest of the trace as a function of `Unit`, so that
forcing a node runs exactly one stage. The census (`haxc-census`) reads the first refusing
stage off the trace (`regionStage`); the profile of `field-bytes-emit` forces the nodes one
after another between two clock reads (`StageTrace.profile`).

## Main results

* `StageTrace`: a trace of named stages with output sizes, ending in acceptance or in the
  refusing stage; `StageTrace.outcome`, its last stage.
* `StageTrace.profile`: forces the nodes of a trace in order and prints one line per stage
  with its wall time and size, flushed as the stage finishes.
* `nfNodes`: the number of nodes of a structured program.
* `gateTrace`, `gateTraceFine`: the gate `regionCoB` followed by the constant-time check
  `regionCtB` on a printed body, as two stages, or as their conjuncts.
* `regionTraceBody`, `regionTrace`: the stages of `compileRegion` on a structured program.
* `regionStageBody`, `regionStage`: the first stage of `compileRegion` that refuses, or
  `accepted`.
* `regionCoStages`: the stages of `regionCoStage` that `RegionDiag.regionCoWhy` explains.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionStages

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (clsB fuseOKL fuseLoPre)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (mulxFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (chainAlias)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (coCfgB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak (leakFixCfgB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot
  boundFacts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC frameMarkC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW (cellNamesRB)
open CatCrypt.Crypto.SecureCompilation.Haxc

/-! ## Stage traces -/

/-- A run of a pipeline as a trace of stages: `accepted` after the last stage, `refused s`
    when the stage `s` refuses, and `stage n z k` when the stage `n` passes with an output of
    size `z` (`none` for a stage whose output is a decision), followed by the rest `k ()`.
    The fields of a node are computed when the node is, and the rest when `k` is applied. -/
inductive StageTrace where
  | accepted
  | refused (stage : String)
  | stage (name : String) (size : Option Nat) (next : Unit → StageTrace)

namespace StageTrace

/-- The last stage of a trace: `accepted`, or the refusing stage. -/
def outcome : StageTrace → String
  | .accepted => "accepted"
  | .refused s => s
  | .stage _ _ k => (k ()).outcome

/-- Forces the nodes of the trace `k ()` in order. For each node it prints the line
    `<row>\t<stage>\t<ms>\t<size>\t<status>` on standard output and flushes it, where `ms` is
    the wall time (`IO.monoMsNow`) of the call `IO.lazyPure k'` that computes the node,
    `size` the size of the stage's output or `-`, and `status` is `ok` for a stage that
    passes and `refused` for the refusing stage; after the last node it prints
    `<row>\ttotal\t<ms>\t-\t<outcome>` with the sum of the wall times and the outcome. -/
partial def profile (row : String) (k : Unit → StageTrace) (total : Nat := 0) : IO Unit := do
  let out ← IO.getStdout
  let t0 ← IO.monoMsNow
  let tr ← IO.lazyPure k
  let t1 ← IO.monoMsNow
  let ms := t1 - t0
  match tr with
  | .accepted =>
      out.putStrLn s!"{row}\ttotal\t{total + ms}\t-\taccepted"
      out.flush
  | .refused s =>
      out.putStrLn s!"{row}\t{s}\t{ms}\t-\trefused"
      out.putStrLn s!"{row}\ttotal\t{total + ms}\t-\t{s}"
      out.flush
  | .stage n z k' =>
      out.putStrLn s!"{row}\t{n}\t{ms}\t{(z.map toString).getD "-"}\tok"
      out.flush
      profile row k' (total + ms)

end StageTrace

/-- The number of nodes of a structured program: one for each `ret`, `var`, `forLoop`,
    `ifThenElse`, `whileLoop` and `call` node, summed over the bodies, the branches and the
    continuations. -/
def nfNodes : {Γ : Ctxt jasminDialect} → {ts : List jasminDialect.Ty} →
    NFProg jasminDialect Γ ts → Nat
  | _, _, .ret _ => 1
  | _, _, .var _ k => nfNodes k + 1
  | _, _, .forLoop _ _ body k => nfNodes body + nfNodes k + 1
  | _, _, .ifThenElse _ thn els k => nfNodes thn + nfNodes els + nfNodes k + 1
  | _, _, .whileLoop _ body k => nfNodes body + nfNodes k + 1
  | _, _, .call _ _ k => nfNodes k + 1

/-! ## The stages of the region back half -/

/-- The gate of `compileRegion` on the printed body `b` of the export with the code `code`
    and the returned operands `res` at the result type `t` and the allocation certificate
    `cert`, as two stages: `regionCoB`, whose refusal is named by its first conjunct that is
    `false` (`regionCoStage`), and `regionCtB`. -/
def gateTrace (σ : AbiLayout) (b : Lcmd) (t : JasminTy) (code : List LinstrRM)
    (res : List LOperand) (cert : List (String × String)) : StageTrace :=
  if regionCoB σ exportReg b t code res cert then
    .stage "regionCoB" none fun _ =>
      if regionCtB σ exportReg b t code res cert then
        .stage "regionCtB" none fun _ => .accepted
      else .refused "regionCtB"
  else .refused ((regionCoStage σ exportReg b t code res cert).getD "regionCoB")

/-- The gate of `compileRegion` on the printed body `b` as its conjuncts, one stage each, at
    no callee and the allocation certificate `cert`. The intermediate values the conjuncts share are stages of their own, computed
    once: the code with the result copy `regionCoCode`, the array liveness table
    `liveArrTab`, the coalesced code `regionCoBody`, the parts `regionCoParts` (size: the
    length of the reference) and the cell body `cellBody`. The conjuncts of `regionCoB` are
    named and ordered as in `regionCoStage`; those of `regionCtB` follow, with the
    conjuncts of `regionLeakB` named `leakFixCfgB`, `constArrFreeB`, `regLeakB`,
    `regLeakBMerged` and `ownedCheckML`, then `printedAddrWB` and `imgGateBW`. -/
def gateTraceFine (σ : AbiLayout) (b : Lcmd) (t : JasminTy) (code : List LinstrRM)
    (res : List LOperand) (cert : List (String × String)) : StageTrace :=
  let nm := exportReg
  let cp := regionCopy σ nm t none code res
  let C := regionCoCode σ nm t code res cp
  .stage "regionCoCode" (some C.length) fun _ =>
  let obs := regionCoObs t (regionOut cp res)
  let LA := liveArrTab C obs
  .stage "liveArrTab" (some LA.size) fun _ =>
  if C.all (fun i => clsB i && mulxFree i) = false then .refused "coClass" else
  .stage "coClass" none fun _ =>
  let ρ := regionAliasN σ nm t res C
  if coCfgB ρ C (tabAt LA) obs = false then .refused "coCfgB" else
  .stage "coCfgB" none fun _ =>
  if (tabAt LA 0).all (fun x => ρ x == x) = false then .refused "coEntryFix" else
  .stage "coEntryFix" none fun _ =>
  let C1 := regionCoBody σ nm t code res
  .stage "regionCoBody" (some C1.length) fun _ =>
  let d := regionCoParts σ nm b t code res cert
  .stage "regionCoParts" (some d.ref.length) fun _ =>
  let sl := slotArrC d.cells (slotRen (slotArrOf σ nm) (renOf d.ps))
  let cb := cellBody sl b
  .stage "cellBody" (some cb.length) fun _ =>
  let outs := d.outs ++ d.cellOuts
  if renB σ nm [] C1 d.ps = false then .refused "renB" else
  .stage "renB" none fun _ =>
  if obs.all (fun A => (loopNames C1).contains (ρ A)) = false then .refused "coResultName" else
  .stage "coResultName" none fun _ =>
  if (regionRet σ nm t res).toList.all (fun p =>
      (loopNames C1).contains p.2 && renOf d.ps p.2 == p.2) = false then
    .refused "coResultCopy" else
  .stage "coResultCopy" none fun _ =>
  if regionResultB σ nm b t ((regionOut cp res).map fun op => .reg (ρ (operandName op)))
      = false then
    .refused "regionResultB" else
  .stage "regionResultB" none fun _ =>
  if regionMergeB d = false then .refused "regMerge" else
  .stage "regMerge" none fun _ =>
  if regionNopB d = false then .refused "regionNopB" else
  .stage "regionNopB" none fun _ =>
  let fE := fuseRegs σ nm
  .stage "fuseRegs" (some fE.length) fun _ =>
  let fL := fuseLoPre d.pre (d.nop.drop d.pre.length)
  .stage "fuseLoPre" (some fL.length) fun _ =>
  if (!d.sites || fuseOKL fE fL (d.pre ++ d.nop.drop d.pre.length)) = false then
    .refused "fuseOKL" else
  .stage "fuseOKL" none fun _ =>
  if regionSitesB (fuseRegs σ nm) d = false then .refused "fuseResultName" else
  .stage "fuseResultName" none fun _ =>
  if regionFoldB d = false then .refused "regionFoldB" else
  .stage "regionFoldB" none fun _ =>
  if ownedCheckMC outs d.ref (calleeImg none sl cb) = false then .refused "ownedCheckMC" else
  .stage "ownedCheckMC" none fun _ =>
  if idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) d.ref) d.ref = false then
    .refused "idxInvCheckB" else
  .stage "idxInvCheckB" none fun _ =>
  if regionPrintedB b = false then .refused "regionPrintedB" else
  .stage "regionPrintedB" none fun _ =>
  if physImgB sl cb = false then .refused "physImgB" else
  .stage "physImgB" none fun _ =>
  if calleeImgB none sl d.cells outs b = false then .refused "regionImgB" else
  .stage "regionImgB" none fun _ =>
  if frameOkB σ b = false then .refused "frameOkB" else
  .stage "frameOkB" none fun _ =>
  if entryB σ nm b = false then .refused "entryB" else
  .stage "entryB" none fun _ =>
  if cellNamesRB d.cells σ b = false then .refused "cellNamesRB" else
  .stage "cellNamesRB" none fun _ =>
  if d.cells.all (fun p =>
      X86Backend.DecodeGenMem.regLen (rsOf σ) (unren d.ps p.1) == p.2
        && renOf d.ps (unren d.ps p.1) == p.1) = false then .refused "cellRegions" else
  .stage "cellRegions" none fun _ =>
  if leakFixCfgB ρ C = false then .refused "leakFixCfgB" else
  .stage "leakFixCfgB" none fun _ =>
  if C1.all constArrFreeB = false then .refused "constArrFreeB" else
  .stage "constArrFreeB" none fun _ =>
  if (d.tau == [] || regLeakB (renOf d.tau) d.pre d.ren (tabAt d.live)) = false then
    .refused "regLeakB" else
  .stage "regLeakB" none fun _ =>
  if regLeakB id d.pre d.merged (tabAt d.liveM) = false then .refused "regLeakBMerged" else
  .stage "regLeakBMerged" none fun _ =>
  if ownedCheckML d.outs d.ref (virtImg sl cb) = false then .refused "ownedCheckML" else
  .stage "ownedCheckML" none fun _ =>
  if printedAddrWB b = false then .refused "printedAddrWB" else
  .stage "printedAddrWB" none fun _ =>
  if imgGateBW (frameMarkC d.cells b) sl cb = false then .refused "imgGateBW" else
  .stage "imgGateBW" none fun _ => .accepted

/-- The stages of `compileRegion σ a p` on the structured program `p` with one result, in
    the order of its definition: `regionExportableB`, `callFree`, the export `exportR` (size:
    the length of its code), the allocated program `regionLprog` with its allocation
    certificate (`regionLprogC`; size: the number of instructions of its functions), the
    first function body of the printed program
    `firstBody` (size: its length), the gated encoder
    `encodeLfundefBytesChecked` (size: the number of bytes), then the gate: `gateTraceFine`
    when `fine` holds and `gateTrace` otherwise. -/
def regionTraceBody (fine : Bool) (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) : StageTrace :=
  if regionExportableB p = false then .refused "regionExportableB" else
  .stage "regionExportableB" none fun _ =>
  if p.callFree = false then .refused "callFree" else
  .stage "callFree" none fun _ =>
  match exportR Γ.length a.fname p Γ.length 0 with
  | none => .refused "exportR"
  | some r =>
  .stage "exportR" (some r.code.length) fun _ =>
  match regionLprogC a p none (regionWebsEx σ exportReg) with
  | none => .refused "regionLprog"
  | some (P, cert) =>
  .stage "regionLprog" (some (P.lp_funcs.foldl (fun n f => n + f.2.lfd_body.length) 0))
    fun _ =>
  match firstBody (printedLprog P) with
  | none => .refused "firstBody"
  | some b =>
  .stage "firstBody" (some b.length) fun _ =>
  match X86Backend.LprogBytes.encodeLfundefBytesChecked b with
  | none => .refused "encodeLfundefBytesChecked"
  | some bs =>
  .stage "encodeLfundefBytesChecked" (some bs.length) fun _ =>
  if fine then gateTraceFine σ b t r.code r.res cert else gateTrace σ b t r.code r.res cert

/-- The stages of `compileRegion`: `.refused "resultTy"` when the result type is neither
    `reg 64` nor `stackArr 64 m`, else `regionTraceBody`. -/
def regionTrace (fine : Bool) (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} :
    {t : JasminTy} → NFProg jasminDialect Γ [t] → StageTrace
  | .stackArr 64 _, p => regionTraceBody fine σ a p
  | .reg 64, p => regionTraceBody fine σ a p
  | _, _ => .refused "resultTy"

/-- The first stage of `compileRegion σ a p` that refuses the structured program `p` with
    one result, or `accepted`: the outcome of `regionTraceBody` with the gate as two
    stages. When the gate `regionCoB` refuses, the value is its first conjunct that is
    `false` (`regionCoStage`). -/
def regionStageBody (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : String :=
  (regionTraceBody false σ a p).outcome

/-- The first stage of `compileRegion` that refuses the structured program `p`, or
    `accepted`: the outcome of `regionTrace` with the gate as two stages. -/
def regionStage (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : String :=
  (regionTrace false σ a p).outcome

/-- The stages of `regionCoStage`, other than `ownedCheckMC` and `regionPrintedB`, whose
    reason is `RegionDiag.regionCoWhy`. -/
def regionCoStages : List String :=
  ["coClass", "coCfgB", "coEntryFix", "renB", "coResultName", "coResultCopy", "regMerge",
    "regionNopB", "fuseOKL", "fuseResultName", "regionFoldB", "idxInvCheckB", "regionImgB",
    "cellNamesRB", "cellRegions"]

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionStages
