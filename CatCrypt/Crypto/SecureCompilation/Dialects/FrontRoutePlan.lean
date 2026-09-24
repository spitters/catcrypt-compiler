/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.RolledFront
public import CatCrypt.Crypto.SecureCompilation.Dialects.RolledFront
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontSiblingLoops
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontSiblingLoops

@[expose] public section

set_option autoImplicit false

/-!
# Route selection for the rolled-loop front

The rolled-loop front is a family of combinators indexed by four independent
axes, not a list of unrelated entry points:

| axis          | values                                   | decided from the `LowCT` source by |
|---------------|------------------------------------------|------------------------------------|
| loop shape    | fixed-`N` / runtime-`N` / runtime-nested / countdown-`while` / block / sibling | which loop constructor heads the spine, whether a second loop follows it, whether its body contains a loop, and which constructor that inner loop is |
| body front    | `frontLoopBodyJ` / `…JC` / `…JV`         | `vsimdTag`-carrying `RCall`s; `CarryChainSelect` windows on the flattened body |
| continuation  | `.ret .here` / caller-supplied `cont`    | whether commands follow the loop node |
| post-pass     | `fuseMulHiLprog (saveRdx := true)`       | `SMulHiU` / `SMulHiS` in the body |

`analyse` computes the axes from the source; `compile` runs `analyse` and
dispatches to the matching existing combinator, returning the plan alongside the
program so the decision is inspectable. Neither reimplements a front: every
route is one of `TranslateDialectRolledLoop`,
`TranslateDialectRuntimeLoop{,CarrySelect}`, `TranslateDialectPhaseCompose`,
`TranslateDialectWhileNode` or `RecursiveForLoopBlockFront`.

The dispatch produces a `RolledFront` — the program together with the
denotation it realises, with the body front's side condition absorbed into the
record — so a consumer reads the denotation off the result rather than
reproving it per route.

Where no combinator covers an axis combination, the result is a `RouteGap`
naming the axis rather than a bare `none`.

## Axis policy

`bodyFrontOf` prefers `carrySelect` over `plain` whenever the body carries at
least one recognised carry/borrow window, and `vsimd` over both whenever the
body carries a `vsimd`-tagged call. Both stronger fronts delegate every
unmatched command to `translateDialectControl`, so their covered fragments are
supersets of the plain one. A caller that wants a different front overrides
`CompilePlan.bodyFront` and calls `compileLoop` directly.

## Main results

* `CompilePlan` / `PlanEvidence` / `RouteGap` — the route record, the syntactic
  measurements it was derived from, and the per-axis failure diagnosis.
* `split` / `analyse` — the source analysis: loop shape, innermost body,
  continuation, post-passes.
* `compileLoop` / `compileLoop_denote` — dispatch over
  `{fixed-N, runtime-N, countdown} × {plain, carry-select, vsimd}` and one
  denotation theorem covering it, stated as the `JLoopBodyN.denote` fold at the
  route's trip count.
* `compileNested` / `compileNested_denote` — dispatch over the nested runtime
  loop and its `JLoopBodyN.nestedDenote` double fold.
* `compileLoopCont` / `compileNestedCont` and their denotation theorems — the
  continuation-carrying twins, available on the plain body front.
* `compileLoopCont_ret_here` / `compileNestedCont_ret_here` — the
  continuation-free routes are the continuation-carrying ones at `.ret .here`.
* `compileLoopFront` / `compileLoopFront_build` / `compileLoopFront_spec` — the
  same single-loop dispatch producing a `RolledFront`, and its agreement with
  `compileLoop` on both the program and the fold.
* `compileBlock` / `compileBlock_denote` — the block route, whose
  per-iteration body carries the inner sweep as a `ComL.whileNz` node.
* `compileSibling` / `compileSibling_denote` / `compileSiblingNested` — the
  sibling route, two loop nodes in sequence threaded through the continuation
  seam (`FrontSiblingLoops`), for the `mpn_mul_basecase` two-phase shape.
* `compile` / `compile_denote` / `CompileResult.denote_prog` — the single entry
  point: source in, plan and bundled front out, with the denotation of the
  produced program both as the fold and as the record's own `spec`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileNode
  (rolledWhileNzComL rolledWhileNzComL_denote rolledWhileNzComLCont)
open CatCrypt.Crypto.SecureCompilation.VIR.RecursiveForLoopBlockFront
  (rolledWhileNzComLCont_denote)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The plan record -/

/-- The loop node a rolled route emits. -/
inductive LoopShape where
  /-- `ComL.forLoopN` at a compile-time trip count. -/
  | fixedN (n : Nat)
  /-- `ComL.forLoopNRt` at a trip count read from a register. -/
  | runtimeN
  /-- `ComL.forLoopNRtNested`: a runtime outer trip with the inner trip
      recomputed each outer pass. -/
  | runtimeNested
  /-- `ComL.whileNz` at a countdown guard register: the trip the guard exit
      realises. -/
  | whileNz
  /-- `ComL.forLoopBlock` over `ComL.whileNz`: a runtime outer trip whose
      per-iteration body carries the inner loop as a node. -/
  | forLoopBlock
  /-- Two loop nodes in sequence on the source spine: a first sweep followed by a
      sibling sweep that reads the first's result. The `mpn_mul_basecase`
      two-phase shape (`mpn_mul_1` then `mpn_addmul_1`). Compiled by
      `FrontSiblingLoops.rolledSiblingLoops{,Nested}` through the continuation
      seam, not by a single loop node. -/
  | siblingLoops
  deriving Repr, DecidableEq, Inhabited

/-- Which `LowCT → catCryptDialect` front the loop body flows through. -/
inductive BodyFront where
  /-- `frontLoopBodyJ`, over `translateDialectControl`. -/
  | plain
  /-- `frontLoopBodyJC`, over `CarryChainSelect.translateDialectCarrySelect`. -/
  | carrySelect
  /-- `frontLoopBodyJV`, over `TranslateDialectVsimd.translateDialectControlV`. -/
  | vsimd
  deriving Repr, DecidableEq, Inhabited

/-- A pass the caller runs on the exported `Lprog`. -/
inductive PostPass where
  /-- `FheMontMulEmit.fuseMulHiLprog (saveRdx := true)`: coalesce the front's
      `MULXHI` high-word binding with its paired low `MUL` into the printer's
      two-output `mulx`. -/
  | fuseMulHiSaveRdx
  deriving Repr, DecidableEq, Inhabited

/-- How far down the pipeline the caller wants the result carried. -/
inductive OutputForm where
  /-- Stop at `ComL`. -/
  | com
  /-- Continue through `ComL.toLprogPhysAbi`. -/
  | lprog
  /-- Continue through `renderLprogAtt`. -/
  | attText
  deriving Repr, DecidableEq, Inhabited

/-- The syntactic measurements each axis decision was read off. -/
structure PlanEvidence where
  /-- Nesting depth of loop nodes in the selected loop. -/
  loopDepth : Nat
  /-- Commands preceding the loop node on the source's flattened spine. -/
  prologueCmds : Nat
  /-- Carry/borrow windows `CarryChainSelect.selectGo` fuses in the body. -/
  carryWindows : Nat
  /-- `vsimdTag`-carrying `RCall`s in the body. -/
  vsimdOps : Nat
  /-- `SMulHiU` / `SMulHiS` occurrences in the body. -/
  mulHiOps : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The route chosen for a source, with the evidence it was chosen on.

    `optPasses` names the `CatCrypt/Crypto/Optimizer/` passes to run between the
    export and the render. It is empty: whether those passes compose with the
    `Lprog` representation this pipeline produces is not settled. -/
structure CompilePlan where
  loopShape : LoopShape
  bodyFront : BodyFront
  /-- Commands follow the loop node, so the route needs a continuation rather
      than `.ret .here`. -/
  hasTail : Bool
  postPasses : List PostPass
  optPasses : List String
  output : OutputForm
  evidence : PlanEvidence
  deriving Repr, DecidableEq, Inhabited

/-- Which axis has no covering combinator, or which input the caller owes. -/
inductive RouteGap where
  /-- No loop node: the source belongs to the straight-line fronts
      (`compileFromHax`, `reifyLowCT`), not the rolled-loop family. -/
  | noLoop
  /-- A loop node inside an `RWhileNz` body: the block route's outer loop is the
      counted `ComL.forLoopBlock`, so a data-dependent outer trip has no rolled
      route. -/
  | whileOuterNested
  /-- A nested loop under a compile-time outer trip: `ComL.forLoopNRtNested`
      reads its outer count from a register. -/
  | nestedFixedOuterTrip
  /-- Three or more nested loop levels. -/
  | loopNestDeeperThanTwo
  /-- Runtime trip with a vsimd body: `rolledForLoopNV` is fixed-trip only. -/
  | vsimdRuntimeTrip
  /-- Nested loop with a vsimd body. -/
  | vsimdNestedTrip
  /-- Countdown trip with a body front other than `plain`: `rolledWhileNzComL`
      is over `frontLoopBodyJ`. -/
  | whileNonPlainBody
  /-- Block loop with a body front other than `plain`: `lowerNestedLoop`'s inner
      node is over `frontLoopBodyJ`. -/
  | blockNonPlainBody
  /-- A tail follows the loop, but the body front is not `plain`: the
      continuation lift exists only for the plain-front combinators. -/
  | tailAfterNonPlainBody
  /-- A tail follows a block loop: `lowerNestedLoop` fixes its continuation at
      `.ret .here`. -/
  | tailAfterBlockLoop
  /-- The shape is runtime-trip or countdown and the caller supplied no count
      variable. -/
  | missingCountVariable
  /-- The shape is nested: dispatch it through `compileNested`, which takes the
      inner-count body as a second source. -/
  | nestedNeedsTwoBodies
  /-- The shape is a block loop: dispatch it through `compileBlock`, which takes
      the inner node's guard, seed and invariant variables in the outer block's
      loop-body context. -/
  | blockNeedsInnerContext
  /-- The shape is two sibling loops: dispatch it through `compileSibling`, which
      takes the second loop's body, seed and invariant variables in the context
      extended by the first loop's result. -/
  | siblingNeedsTwoBodies
  /-- The trip-count and body-front axes have no combinator between them.
      `plan` names the pair; this is the dispatcher's own report of it. -/
  | uncoveredTripBodyPair
  /-- The chosen front declined the body. -/
  | frontDeclined
  /-- A loop body binds the result of a leaf call at a `stackArr` type. The
      loop-body value model gives every body binding a register (`loopReg`), and
      the loop-body call marshaller `callMarshalHere` knows the GP and SSE
      register classes only, so a multi-word result has no location the route can
      name. -/
  | bufferResultCallInBody
  deriving Repr, DecidableEq, Inhabited

/-! ## 2. Reading the axes off the source -/

/-- Nesting depth of loop nodes. `LowCT.fold` treats `RForRuntime` as a leaf, so
    this is a direct structural recursion rather than a fold. -/
def loopDepth : LowCT → Nat
  | .RSeq a b => max (loopDepth a) (loopDepth b)
  | .RIfNz _ a b => max (loopDepth a) (loopDepth b)
  | .RFnDef _ _ _ b c => max (loopDepth b) (loopDepth c)
  | .RLetZero _ _ b => loopDepth b
  | .RLetU64Zero _ b => loopDepth b
  | .RBlock b => loopDepth b
  | .RWhileNz _ b => loopDepth b + 1
  | .RFor _ _ b => loopDepth b + 1
  | .RForRuntime _ _ b => loopDepth b + 1
  | _ => 0

/-- Is there a data-dependent `while` anywhere in the source? -/
def hasWhile : LowCT → Bool
  | .RSeq a b => hasWhile a || hasWhile b
  | .RIfNz _ a b => hasWhile a || hasWhile b
  | .RFnDef _ _ _ b c => hasWhile b || hasWhile c
  | .RLetZero _ _ b => hasWhile b
  | .RLetU64Zero _ b => hasWhile b
  | .RBlock b => hasWhile b
  | .RWhileNz _ _ => true
  | .RFor _ _ b => hasWhile b
  | .RForRuntime _ _ b => hasWhile b
  | _ => false

/-- Widening-multiply nodes in a scalar expression. -/
def mulHiSExpr : SExpr → Nat
  | .SVar _ | .SLit _ | .SLimb _ _ => 0
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b
  | .SAnd a b | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b =>
      mulHiSExpr a + mulHiSExpr b
  | .SMulHiU a b | .SMulHiS a b => 1 + mulHiSExpr a + mulHiSExpr b

/-- Widening-multiply nodes in a command tree. Their presence is what the
    `fuseMulHiLprog` post-pass consumes. -/
def mulHiOps : LowCT → Nat
  | .RSeq a b => mulHiOps a + mulHiOps b
  | .RIfNz _ a b => mulHiOps a + mulHiOps b
  | .RFnDef _ _ _ b c => mulHiOps b + mulHiOps c
  | .RLetZero _ _ b => mulHiOps b
  | .RLetU64Zero _ b => mulHiOps b
  | .RBlock b => mulHiOps b
  | .RWhileNz _ b => mulHiOps b
  | .RFor _ _ b => mulHiOps b
  | .RForRuntime _ _ b => mulHiOps b
  | .RScalarSetExpr _ e => mulHiSExpr e
  | .RLimbStoreExpr _ _ e => mulHiSExpr e
  | _ => 0

/-- `vsimd`-tagged calls in a command tree, the ones only
    `translateDialectControlV` intercepts. -/
def vsimdOps : LowCT → Nat
  | .RSeq a b => vsimdOps a + vsimdOps b
  | .RIfNz _ a b => vsimdOps a + vsimdOps b
  | .RFnDef _ _ _ b c => vsimdOps b + vsimdOps c
  | .RLetZero _ _ b => vsimdOps b
  | .RLetU64Zero _ b => vsimdOps b
  | .RBlock b => vsimdOps b
  | .RWhileNz _ b => vsimdOps b
  | .RFor _ _ b => vsimdOps b
  | .RForRuntime _ _ b => vsimdOps b
  | .RCall f _ _ => if (TranslateDialectVsimd.vsimdTag f).isSome then 1 else 0
  | _ => 0

/-- Is this step a fused carry/borrow window rather than a fall-through? -/
def selIsFused : CarryChainSelect.Sel → Bool
  | .plain _ => false
  | _ => true

/-- Carry/borrow windows the selector fuses in this body, run at the same fuel
    and initial state as `CarryChainSelect.translateDialectCarrySelect`. -/
def carryWindows (body : LowCT) : Nat :=
  let cmds := CarryChainSelect.flattenSeq body
  ((CarryChainSelect.selectGo cmds.length [] [] [] cmds).filter selIsFused).length

/-- The strongest body front the source needs. -/
def bodyFrontOf (body : LowCT) : BodyFront :=
  if vsimdOps body ≠ 0 then .vsimd
  else if carryWindows body ≠ 0 then .carrySelect
  else .plain

/-- Does this command head a loop? -/
def isLoopNode : LowCT → Bool
  | .RFor _ _ _ | .RForRuntime _ _ _ | .RWhileNz _ _ => true
  | _ => false

/-- The direct body of a loop node, or `RSkip` for a non-loop command. -/
def loopBodyOf : LowCT → LowCT
  | .RFor _ _ b | .RForRuntime _ _ b | .RWhileNz _ b => b
  | _ => .RSkip

/-- The source's loop structure: which node, its innermost body, and what
    surrounds it. -/
structure SourceSplit where
  shape : LoopShape
  /-- The innermost loop body — the command tree the body front compiles. -/
  body : LowCT
  hasTail : Bool
  prologueCmds : Nat
  loopDepth : Nat

/-- Locate the source's loop node and read its shape and innermost body. -/
def split (src : LowCT) : Except RouteGap SourceSplit :=
  let cmds := CarryChainSelect.flattenSeq src
  match cmds.findIdx? isLoopNode with
  | none => .error .noLoop
  | some i =>
      let tail := !(cmds.drop (i + 1)).isEmpty
      if (cmds.drop (i + 1)).any isLoopNode then
        -- A second loop node follows the first on the spine: sibling loops.
        .ok { shape := .siblingLoops, body := loopBodyOf cmds[i]!, hasTail := true,
              prologueCmds := i, loopDepth := loopDepth src }
      else
      match cmds[i]! with
      | .RFor _ n b =>
          if loopDepth b == 0 then
            .ok { shape := .fixedN n, body := b, hasTail := tail,
                  prologueCmds := i, loopDepth := 1 }
          else .error .nestedFixedOuterTrip
      | .RWhileNz _ b =>
          if loopDepth b == 0 then
            .ok { shape := .whileNz, body := b, hasTail := tail,
                  prologueCmds := i, loopDepth := 1 }
          else .error .whileOuterNested
      | .RForRuntime _ _ b =>
          if loopDepth b == 0 then
            .ok { shape := .runtimeN, body := b, hasTail := tail,
                  prologueCmds := i, loopDepth := 1 }
          else if loopDepth b == 1 then
            let inner := CarryChainSelect.flattenSeq b
            match inner.findIdx? isLoopNode with
            | none => .error .loopNestDeeperThanTwo
            | some j =>
                match inner[j]! with
                | .RFor _ _ ib =>
                    .ok { shape := .runtimeNested, body := ib, hasTail := tail,
                          prologueCmds := i, loopDepth := 2 }
                | .RForRuntime _ _ ib =>
                    .ok { shape := .runtimeNested, body := ib, hasTail := tail,
                          prologueCmds := i, loopDepth := 2 }
                | .RWhileNz _ ib =>
                    .ok { shape := .forLoopBlock, body := ib, hasTail := tail,
                          prologueCmds := i, loopDepth := 2 }
                | _ => .error .noLoop
          else .error .loopNestDeeperThanTwo
      | _ => .error .noLoop

/-- Turn a located loop into a plan, or name the axis with no combinator. -/
def plan (out : OutputForm) (sp : SourceSplit) : Except RouteGap CompilePlan :=
  let bf := bodyFrontOf sp.body
  let ev : PlanEvidence :=
    { loopDepth := sp.loopDepth, prologueCmds := sp.prologueCmds,
      carryWindows := carryWindows sp.body, vsimdOps := vsimdOps sp.body,
      mulHiOps := mulHiOps sp.body }
  match bf, sp.shape with
  | .vsimd, .runtimeN => .error .vsimdRuntimeTrip
  | .vsimd, .runtimeNested => .error .vsimdNestedTrip
  | .carrySelect, .whileNz | .vsimd, .whileNz => .error .whileNonPlainBody
  | .carrySelect, .forLoopBlock | .vsimd, .forLoopBlock => .error .blockNonPlainBody
  | _, .siblingLoops =>
      -- Both sibling loops are front-compiled per phase by `compileSibling`; the
      -- tail is not dropped, so the plain-tail guards below do not apply.
      .ok { loopShape := .siblingLoops, bodyFront := bf, hasTail := sp.hasTail,
            postPasses := if ev.mulHiOps ≠ 0 then [.fuseMulHiSaveRdx] else [],
            optPasses := [], output := out, evidence := ev }
  | _, _ =>
      if sp.hasTail && sp.shape == .forLoopBlock then .error .tailAfterBlockLoop
      else if sp.hasTail && bf ≠ .plain then .error .tailAfterNonPlainBody
      else .ok { loopShape := sp.shape, bodyFront := bf, hasTail := sp.hasTail,
                 postPasses := if ev.mulHiOps ≠ 0 then [.fuseMulHiSaveRdx] else [],
                 optPasses := [], output := out, evidence := ev }

/-- The route a source takes, with no context or ABI input. -/
def analyse (out : OutputForm) (src : LowCT) : Except RouteGap CompilePlan :=
  (split src).bind (plan out)

/-! ## 3. Dispatch

The single-loop combinators differ only in which body front they call and
whether the trip is a `Nat`, a counter register or a countdown guard register,
so `compileLoop` is a match on those two axes over the existing definitions.
The same holds for the two nested combinators and for the continuation-carrying
twins. -/

/-- A rolled loop's trip count: compile-time, read from an in-scope 64-bit
    counter register, or realised by an in-scope countdown guard register. The
    last two agree on the trip and differ in the loop node they select —
    `ComL.forLoopNRt` against `ComL.whileNz`. -/
inductive TripCount (Γouter : Ctxt jasminDialect) where
  | static (n : Nat)
  | runtime (count : Ctxt.Var Γouter (JasminTy.reg 64))
  | countdown (guard : Ctxt.Var Γouter (JasminTy.reg 64))

/-- The trip count at a valuation. -/
def TripCount.value {Γouter : Ctxt jasminDialect} :
    TripCount Γouter → Ctxt.Valuation Γouter → Nat
  | .static n, _ => n
  | .runtime c, V => (c.lookup V).toNat
  | .countdown g, V => (g.lookup V).toNat

/-- The body front this axis value names. -/
def BodyFront.front (bf : BodyFront) {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com jasminDialect (mapCtx Γbody) (mapTy accCTy)) :=
  match bf with
  | .plain => frontLoopBodyJ (accCTy := accCTy) vmBody accName body
  | .carrySelect => frontLoopBodyJC (accCTy := accCTy) vmBody accName body
  | .vsimd => frontLoopBodyJV (accCTy := accCTy) vmBody accName body

/-- Dispatch a single rolled loop to the combinator for `(bf, trip)`.

    `none` when the front declines the body, and on the uncovered pairs — a
    runtime trip with a vsimd body, and a countdown trip with either of the
    stronger bodies, for which there is no combinator. -/
def compileLoop {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    (bf : BodyFront) (trip : TripCount Γouter)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match bf, trip with
  | .plain, .static n => rolledForLoopN n vmBody accName body init invs
  | .carrySelect, .static n => rolledForLoopNC n vmBody accName body init invs
  | .vsimd, .static n => rolledForLoopNV n vmBody accName body init invs
  | .plain, .runtime c => rolledForLoopNRt vmBody accName body c init invs
  | .carrySelect, .runtime c => rolledForLoopNRtC vmBody accName body c init invs
  | .vsimd, .runtime _ => none
  | .plain, .countdown g => rolledWhileNzComL vmBody accName body g init invs
  | .carrySelect, .countdown _ => none
  | .vsimd, .countdown _ => none

/-- **The dispatched single loop denotes the `JLoopBodyN` fold at its route's
    trip count**, for every `(bf, trip)` pair. When the route's own front
    compiles the body to `update` and the dispatch produces `c`, `c`'s
    denotation at any valuation is the `trip.value V`-fold of `update`, seeded
    by `init` and threading `invs`. -/
theorem compileLoop_denote {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (bf : BodyFront) (trip : TripCount Γouter)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : bf.front (accCTy := accCTy) vmBody accName body = some update)
    {c : ComL Γouter (mapTy accCTy)}
    (hc : compileLoop bf trip vmBody accName body init invs = some c)
    (V : Ctxt.Valuation Γouter) :
    ComL.denote c V
      = JLoopBodyN.denote ⟨trip.value V, update⟩ (Expr.lookupArgs invs V)
          (init.lookup V) := by
  cases bf
  case plain =>
    cases trip
    case static n =>
      have hc' : rolledForLoopN n vmBody accName body init invs = some c := hc
      have h := rolledForLoopN_denote n vmBody accName body init invs hupd V
      rw [hc'] at h
      simpa using! h
    case runtime cv =>
      have hc' : rolledForLoopNRt vmBody accName body cv init invs = some c := hc
      have h := rolledForLoopNRt_denote vmBody accName body cv init invs hupd V
      rw [hc'] at h
      simpa using! h
    case countdown g =>
      have hc' : rolledWhileNzComL vmBody accName body g init invs = some c := hc
      have h := rolledWhileNzComL_denote vmBody accName body g init invs hupd V
      rw [hc'] at h
      simpa using! h
  case carrySelect =>
    cases trip
    case static n =>
      have hc' : rolledForLoopNC n vmBody accName body init invs = some c := hc
      have h := rolledForLoopNC_denote n vmBody accName body init invs hupd V
      rw [hc'] at h
      simpa using! h
    case runtime cv =>
      have hc' : rolledForLoopNRtC vmBody accName body cv init invs = some c := hc
      have h := rolledForLoopNRtC_denote vmBody accName body cv init invs hupd V
      rw [hc'] at h
      simpa using! h
    case countdown g =>
      exact absurd hc (by simp [compileLoop])
  case vsimd =>
    cases trip
    case static n =>
      have hc' : rolledForLoopNV n vmBody accName body init invs = some c := hc
      have h := rolledForLoopNV_denote n vmBody accName body init invs hupd V
      rw [hc'] at h
      simpa using! h
    case runtime cv =>
      exact absurd hc (by simp [compileLoop])
    case countdown g =>
      exact absurd hc (by simp [compileLoop])

/-- Dispatch a nested runtime loop to the combinator for `bf`.

    `none` when a front declines a body, and on the uncovered vsimd value, for
    which there is no nested combinator. -/
def compileNested {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    (bf : BodyFront)
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match bf with
  | .plain =>
      rolledForLoopNRtNested vmCount countName countBody vmBody accName updateBody
        outerCount init invs
  | .carrySelect =>
      rolledForLoopNRtNestedC vmCount countName countBody vmBody accName updateBody
        outerCount init invs
  | .vsimd => none

/-- **The dispatched nested loop denotes the `JLoopBodyN` double fold**, for
    every body front. When the route's own front compiles both bodies and the
    dispatch produces `c`, `c`'s denotation is the outer fold over
    `(outerCount.lookup V).toNat` with the inner trip recomputed per outer
    pass. -/
theorem compileNested_denote {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (bf : BodyFront)
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {innerCount : Com jasminDialect (mapCtx (.sword 64 :: invCTys)) (mapTy (.sword 64))}
    {innerUpdate : Com jasminDialect
      (mapCtx (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hcnt : bf.front (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
      vmCount countName countBody = some innerCount)
    (hupd : bf.front (accCTy := accCTy)
      (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys)
      vmBody accName updateBody = some innerUpdate)
    {c : ComL Γouter (mapTy accCTy)}
    (hc : compileNested bf vmCount countName countBody vmBody accName updateBody
      outerCount init invs = some c)
    (V : Ctxt.Valuation Γouter) :
    ComL.denote c V
      = JLoopBodyN.nestedDenote innerCount innerUpdate (outerCount.lookup V).toNat
          (Expr.lookupArgs invs V) (init.lookup V) := by
  cases bf
  case plain =>
    have hc' : rolledForLoopNRtNested vmCount countName countBody vmBody accName
        updateBody outerCount init invs = some c := hc
    have h := rolledForLoopNRtNested_denote vmCount countName countBody vmBody accName
      updateBody outerCount init invs hcnt hupd V
    rw [hc'] at h
    simpa using! h
  case carrySelect =>
    have hc' : rolledForLoopNRtNestedC vmCount countName countBody vmBody accName
        updateBody outerCount init invs = some c := hc
    have h := rolledForLoopNRtNestedC_denote vmCount countName countBody vmBody accName
      updateBody outerCount init invs hcnt hupd V
    rw [hc'] at h
    simpa using! h
  case vsimd =>
    exact absurd hc (by simp [compileNested])

/-! ### The continuation axis

`rolledForLoopN`, `rolledForLoopNRt`, `rolledWhileNzComL` and
`rolledForLoopNRtNested` are their `Cont` twins at `cont := .ret .here`. The
continuation is therefore a parameter of the plain-front routes rather than a
route of its own; `compileLoopCont_ret_here` and `compileNestedCont_ret_here`
carry that through the dispatcher. The carry-select and vsimd fronts have no
`Cont` twin, which is what `RouteGap.tailAfterNonPlainBody` reports; the block
loop fixes its continuation at `.ret .here`, which is
`RouteGap.tailAfterBlockLoop`. -/

/-- Dispatch a single rolled loop with a caller-supplied continuation. The
    trip-count axis is live over all three of its values; the body front is
    `plain`, the only one with a continuation lift. -/
def compileLoopCont {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    {s : JasminTy} (trip : TripCount Γouter)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) : Option (ComL Γouter s) :=
  match trip with
  | .static n => rolledForLoopNCont n vmBody accName body init invs cont
  | .runtime cv => rolledForLoopNRtCont vmBody accName body cv init invs cont
  | .countdown g => rolledWhileNzComLCont vmBody accName body g init invs cont

/-- **The dispatched loop-with-continuation denotes the continuation applied to
    the fold**, at either trip-count kind. -/
theorem compileLoopCont_denote {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx} {s : JasminTy}
    (trip : TripCount Γouter)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : BodyFront.plain.front (accCTy := accCTy) vmBody accName body = some update)
    {c : ComL Γouter s}
    (hc : compileLoopCont trip vmBody accName body init invs cont = some c)
    (V : Ctxt.Valuation Γouter) :
    ComL.denote c V
      = ComL.denote cont
          (V.extend (JLoopBodyN.denote ⟨trip.value V, update⟩
            (Expr.lookupArgs invs V) (init.lookup V))) := by
  cases trip
  case static n =>
    have hc' : rolledForLoopNCont n vmBody accName body init invs cont = some c := hc
    have h := rolledForLoopNCont_denote n vmBody accName body init invs cont hupd V
    rw [hc'] at h
    simpa using! h
  case runtime cv =>
    have hc' : rolledForLoopNRtCont vmBody accName body cv init invs cont = some c := hc
    have h := rolledForLoopNRtCont_denote vmBody accName body cv init invs cont hupd V
    rw [hc'] at h
    simpa using! h
  case countdown g =>
    have hc' : rolledWhileNzComLCont vmBody accName body g init invs cont = some c := hc
    have h := rolledWhileNzComLCont_denote vmBody accName body g init invs cont hupd V
    rw [hc'] at h
    simpa using! h

/-- The continuation-free plain routes are the continuation-carrying ones at
    `.ret .here`, at every trip-count kind. -/
theorem compileLoopCont_ret_here {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (trip : TripCount Γouter)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    compileLoopCont trip vmBody accName body init invs (.ret .here)
      = compileLoop .plain trip vmBody accName body init invs := by
  cases trip <;> rfl

/-- Dispatch a nested runtime loop with a caller-supplied continuation, on the
    plain body front. -/
def compileNestedCont {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    {s : JasminTy}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) : Option (ComL Γouter s) :=
  rolledForLoopNRtNestedCont vmCount countName countBody vmBody accName updateBody
    outerCount init invs cont

/-- The continuation-free nested plain route is the continuation-carrying one at
    `.ret .here`. -/
theorem compileNestedCont_ret_here {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    compileNestedCont vmCount countName countBody vmBody accName updateBody
        outerCount init invs (.ret .here)
      = compileNested .plain vmCount countName countBody vmBody accName updateBody
          outerCount init invs := rfl

/-! ### The bundled routes

`RolledFront` carries a front's program together with the denotation that
program realises, with the front's own side condition absorbed into the record.
The dispatchers below select a `RolledFront` rather than a bare `ComL`, so a
consumer ranging over routes reads the denotation off the record. -/

/-- Dispatch a single rolled loop to the `RolledFront` for `(bf, trip)`. The
    body front's side condition is an argument, so the record's `denote_eq`
    carries no hypothesis.

    `none` on the pairs `compileLoop` has no combinator for — a runtime trip
    with a vsimd body, and a countdown trip with either of the stronger
    bodies. -/
def compileLoopFront {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    (bf : BodyFront) (trip : TripCount Γouter)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : bf.front (accCTy := accCTy) vmBody accName body = some update) :
    Option (RolledFront Γouter (mapTy accCTy)) :=
  match bf, trip, hupd with
  | .plain, .static n, h =>
      some (RolledFront.forLoopN n vmBody accName body init invs (.ret .here) h)
  | .plain, .runtime c, h =>
      some (RolledFront.forLoopNRt vmBody accName body c init invs (.ret .here) h)
  | .plain, .countdown g, h =>
      some (RolledFront.whileNz vmBody accName body g init invs (.ret .here) h)
  | .carrySelect, .static n, h =>
      some (RolledFront.forLoopNC n vmBody accName body init invs h)
  | .carrySelect, .runtime c, h =>
      some (RolledFront.forLoopNRtC vmBody accName body c init invs h)
  | .carrySelect, .countdown _, _ => none
  | .vsimd, .static n, h =>
      some (RolledFront.forLoopNV n vmBody accName body init invs h)
  | .vsimd, .runtime _, _ => none
  | .vsimd, .countdown _, _ => none

/-- The bundled dispatch's program is the bare dispatch's, at every `(bf, trip)`
    pair it covers. -/
theorem compileLoopFront_build {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (bf : BodyFront) (trip : TripCount Γouter)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : bf.front (accCTy := accCTy) vmBody accName body = some update)
    {F : RolledFront Γouter (mapTy accCTy)}
    (hF : compileLoopFront bf trip vmBody accName body init invs hupd = some F) :
    F.build = compileLoop bf trip vmBody accName body init invs := by
  cases bf <;> cases trip <;>
    simp only [compileLoopFront, compileLoop, Option.some.injEq] at hF ⊢ <;>
    first
      | exact absurd hF (by simp)
      | (subst hF; rfl)

/-- The bundled dispatch's `spec` is the `JLoopBodyN` fold at the route's trip
    count, at every `(bf, trip)` pair it covers. -/
theorem compileLoopFront_spec {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (bf : BodyFront) (trip : TripCount Γouter)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : bf.front (accCTy := accCTy) vmBody accName body = some update)
    {F : RolledFront Γouter (mapTy accCTy)}
    (hF : compileLoopFront bf trip vmBody accName body init invs hupd = some F)
    (V : Ctxt.Valuation Γouter) :
    F.spec V
      = JLoopBodyN.denote ⟨trip.value V, update⟩ (Expr.lookupArgs invs V)
          (init.lookup V) := by
  cases bf <;> cases trip <;>
    simp only [compileLoopFront, Option.some.injEq] at hF <;>
    first
      | exact absurd hF (by simp)
      | (subst hF; rfl)

/-- Dispatch a block loop: a runtime outer trip whose per-iteration body carries
    the inner countdown sweep as a `ComL.whileNz` node, over `lowerNestedLoop`.

    The inner node's guard, accumulator seed and invariant variables live in the
    outer block's loop-body context, and the inner front's side condition is an
    argument, so the record's `denote_eq` carries no hypothesis. The combinator
    fixes the outer continuation at `.ret .here`. -/
def compileBlock {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {outerInvCTys innerInvCTys : Ctx}
    (vmInner : VarMap (accCTy :: .sword 64 :: innerInvCTys)) (innerAccName : String)
    (innerBody : LowCT)
    (innerGuard : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (JasminTy.reg 64))
    (innerInit : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy))
    (innerInvs : HVector
      (fun ty => Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) ty)
      (innerInvCTys.map mapTy))
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (outerInit : Ctxt.Var Γouter (mapTy accCTy))
    (outerInvs : HVector (fun ty => Ctxt.Var Γouter ty) (outerInvCTys.map mapTy))
    {inner : ComL (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy)}
    (hinner : rolledWhileNzComL
                (Γouter := mapCtx (accCTy :: .sword 64 :: outerInvCTys))
                (accCTy := accCTy) (invCTys := innerInvCTys)
                vmInner innerAccName innerBody innerGuard innerInit innerInvs
              = some inner) :
    RolledFront Γouter (mapTy accCTy) :=
  RolledFront.forLoopBlock vmInner innerAccName innerBody innerGuard innerInit
    innerInvs outerCount outerInit outerInvs hinner

/-- **The dispatched block loop denotes the outer fold of the inner node's own
    denotation**: the accumulator threads through, the outer trip index sits at
    the `.reg 64` binder and the outer invariants after it. -/
theorem compileBlock_denote {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {outerInvCTys innerInvCTys : Ctx}
    (vmInner : VarMap (accCTy :: .sword 64 :: innerInvCTys)) (innerAccName : String)
    (innerBody : LowCT)
    (innerGuard : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (JasminTy.reg 64))
    (innerInit : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy))
    (innerInvs : HVector
      (fun ty => Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) ty)
      (innerInvCTys.map mapTy))
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (outerInit : Ctxt.Var Γouter (mapTy accCTy))
    (outerInvs : HVector (fun ty => Ctxt.Var Γouter ty) (outerInvCTys.map mapTy))
    {inner : ComL (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy)}
    (hinner : rolledWhileNzComL
                (Γouter := mapCtx (accCTy :: .sword 64 :: outerInvCTys))
                (accCTy := accCTy) (invCTys := innerInvCTys)
                vmInner innerAccName innerBody innerGuard innerInit innerInvs
              = some inner)
    {c : ComL Γouter (mapTy accCTy)}
    (hc : (compileBlock vmInner innerAccName innerBody innerGuard innerInit innerInvs
            outerCount outerInit outerInvs hinner).build = some c)
    (V : Ctxt.Valuation Γouter) :
    ComL.denote c V
      = (List.range (outerCount.lookup V).toNat).foldl
          (fun acc t => ComL.denote inner
            (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs outerInvs V))))
          (outerInit.lookup V) :=
  RolledFront.denote_of_build _ hc V

/-! ### The sibling-loops route

Two loop nodes in sequence — a first sweep and a sibling sweep that reads the
first's result — are one `ComL` through the continuation seam: the first loop's
continuation is the second loop, run in the context extended by the first's
result. `compileSibling` dispatches two plain runtime loops;
`compileSiblingNested` dispatches a plain first sweep followed by a nested second
sweep (the `mpn_mul_basecase` phases). Both take the second phase's inputs in the
extended context, which `compile` — single-body — cannot supply, so `compile`
reports the shape as `RouteGap.siblingNeedsTwoBodies`. -/

/-- Dispatch two plain sibling runtime loops. Both bodies flow through the plain
    front `frontLoopBodyJ`; the second loop's count, seed and invariants live in
    the context extended by the first loop's result. `none` when either front
    declines. -/
def compileSibling {Γouter : Ctxt jasminDialect}
    {accCTy1 : CryptoTy} {invCTys1 : Ctx} {accCTy2 : CryptoTy} {invCTys2 : Ctx}
    (vm1 : VarMap (accCTy1 :: .sword 64 :: invCTys1)) (acc1Name : String) (body1 : LowCT)
    (count1 : Ctxt.Var Γouter (JasminTy.reg 64))
    (init1 : Ctxt.Var Γouter (mapTy accCTy1))
    (invs1 : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys1.map mapTy))
    (vm2 : VarMap (accCTy2 :: .sword 64 :: invCTys2)) (acc2Name : String) (body2 : LowCT)
    (count2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (JasminTy.reg 64))
    (init2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (mapTy accCTy2))
    (invs2 : HVector (fun ty => Ctxt.Var (mapTy accCTy1 :: Γouter) ty) (invCTys2.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy2)) :=
  FrontSiblingLoops.rolledSiblingLoops vm1 acc1Name body1 count1 init1 invs1
    vm2 acc2Name body2 count2 init2 invs2

/-- **The dispatched two-plain-sibling loop denotes the second fold after the
    first.** When both bodies front-compile, the program denotes to the second
    loop's fold, run on the valuation extended by the first loop's fold. -/
theorem compileSibling_denote {Γouter : Ctxt jasminDialect}
    {accCTy1 : CryptoTy} {invCTys1 : Ctx} {accCTy2 : CryptoTy} {invCTys2 : Ctx}
    (vm1 : VarMap (accCTy1 :: .sword 64 :: invCTys1)) (acc1Name : String) (body1 : LowCT)
    (count1 : Ctxt.Var Γouter (JasminTy.reg 64))
    (init1 : Ctxt.Var Γouter (mapTy accCTy1))
    (invs1 : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys1.map mapTy))
    (vm2 : VarMap (accCTy2 :: .sword 64 :: invCTys2)) (acc2Name : String) (body2 : LowCT)
    (count2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (JasminTy.reg 64))
    (init2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (mapTy accCTy2))
    (invs2 : HVector (fun ty => Ctxt.Var (mapTy accCTy1 :: Γouter) ty) (invCTys2.map mapTy))
    {update1 : Com jasminDialect (mapCtx (accCTy1 :: .sword 64 :: invCTys1)) (mapTy accCTy1)}
    {update2 : Com jasminDialect (mapCtx (accCTy2 :: .sword 64 :: invCTys2)) (mapTy accCTy2)}
    (hupd1 : frontLoopBodyJ (accCTy := accCTy1) vm1 acc1Name body1 = some update1)
    (hupd2 : frontLoopBodyJ (accCTy := accCTy2) vm2 acc2Name body2 = some update2)
    (V : Ctxt.Valuation Γouter) :
    (compileSibling vm1 acc1Name body1 count1 init1 invs1
        vm2 acc2Name body2 count2 init2 invs2).map (fun c => ComL.denote c V)
      = (let r1 : ⟦mapTy accCTy1⟧ :=
           JLoopBodyN.denote
             (⟨(count1.lookup V).toNat, update1⟩ : JLoopBodyN (mapTy accCTy1) (invCTys1.map mapTy))
             (Expr.lookupArgs invs1 V) (init1.lookup V)
         some
           (JLoopBodyN.denote ⟨(count2.lookup (V.extend r1)).toNat, update2⟩
             (Expr.lookupArgs invs2 (V.extend r1)) (init2.lookup (V.extend r1)))) :=
  FrontSiblingLoops.rolledSiblingLoops_denote vm1 acc1Name body1 count1 init1 invs1
    vm2 acc2Name body2 count2 init2 invs2 hupd1 hupd2 V

/-- Dispatch a plain first sweep followed by a nested second sweep — the
    `mpn_mul_basecase` two-phase shape (`mpn_mul_1` then `mpn_addmul_1`). The
    nested phase's inner-count and inner-update bodies flow through the plain
    front; its outer count, seed and invariants live in the context extended by
    the first sweep's result. `none` when any of the three bodies declines. -/
def compileSiblingNested {Γouter : Ctxt jasminDialect}
    {accCTy1 : CryptoTy} {invCTys1 : Ctx} {accCTy2 : CryptoTy} {invCTys2 : Ctx}
    (vm1 : VarMap (accCTy1 :: .sword 64 :: invCTys1)) (acc1Name : String) (body1 : LowCT)
    (count1 : Ctxt.Var Γouter (JasminTy.reg 64))
    (init1 : Ctxt.Var Γouter (mapTy accCTy1))
    (invs1 : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys1.map mapTy))
    (vmCount2 : VarMap (.sword 64 :: invCTys2)) (count2Name : String) (countBody2 : LowCT)
    (vm2 : VarMap (accCTy2 :: .sword 64 :: .sword 64 :: invCTys2)) (acc2Name : String)
    (updateBody2 : LowCT)
    (outerCount2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (JasminTy.reg 64))
    (init2 : Ctxt.Var (mapTy accCTy1 :: Γouter) (mapTy accCTy2))
    (invs2 : HVector (fun ty => Ctxt.Var (mapTy accCTy1 :: Γouter) ty) (invCTys2.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy2)) :=
  FrontSiblingLoops.rolledSiblingLoopsNested vm1 acc1Name body1 count1 init1 invs1
    vmCount2 count2Name countBody2 vm2 acc2Name updateBody2 outerCount2 init2 invs2

-- The sibling-loops shape is covered by a dispatched combinator: the plain twin
-- and the `mpn_mul_basecase` plain-then-nested twin are both well-typed routes.
#check @compileSibling
#check @compileSiblingNested

/-! ## 4. The entry point -/

/-- A source compiled through its selected route: the plan, the route's inputs
    read off the source, and the bundled front the route produced. -/
structure CompileResult (Γouter : Ctxt jasminDialect) (accCTy : CryptoTy) where
  /-- The route chosen, and the evidence it was chosen on. -/
  plan : CompilePlan
  /-- The trip count the route uses. -/
  trip : TripCount Γouter
  /-- The innermost loop body the front compiled. -/
  body : LowCT
  /-- The dispatched front: the program together with the denotation it
      realises. -/
  front : RolledFront Γouter (mapTy accCTy)
  /-- The dispatched program. -/
  prog : ComL Γouter (mapTy accCTy)
  /-- `front` built `prog`. -/
  build_eq : front.build = some prog

/-- **The result's program denotes the result's own `spec`**, with no front
    hypothesis at the call site. -/
theorem CompileResult.denote_prog {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    (r : CompileResult Γouter accCTy) (V : Ctxt.Valuation Γouter) :
    ComL.denote r.prog V = r.front.spec V :=
  RolledFront.denote_of_build r.front r.build_eq V

/-- The trip count a plan calls for, given what the caller supplied. -/
def tripOf {Γouter : Ctxt jasminDialect} (p : CompilePlan)
    (countVar : Option (Ctxt.Var Γouter (JasminTy.reg 64))) :
    Except RouteGap (TripCount Γouter) :=
  match p.loopShape, countVar with
  | .fixedN n, _ => .ok (.static n)
  | .runtimeN, some cv => .ok (.runtime cv)
  | .runtimeN, none => .error .missingCountVariable
  | .whileNz, some gv => .ok (.countdown gv)
  | .whileNz, none => .error .missingCountVariable
  | .runtimeNested, _ => .error .nestedNeedsTwoBodies
  | .forLoopBlock, _ => .error .blockNeedsInnerContext
  | .siblingLoops, _ => .error .siblingNeedsTwoBodies

/-! ### The loop-shape axis on minimal sources

The loop-shape axis is read off the node heading the source's spine and, for a
two-level nest, off the inner node: an inner `RWhileNz` is the block route and
an inner counted loop is the nested route. The decisions and the `RouteGap`
`tripOf` reports for each are pinned below on sources with an empty body. -/

/-- A countdown `while` over an empty body. -/
def whileSource : LowCT := .RWhileNz "n" .RSkip

/-- A runtime-trip loop whose body is a countdown `while`. -/
def blockSource : LowCT := .RForRuntime "i" (.SVar "m") (.RWhileNz "n" .RSkip)

/-- A runtime-trip loop whose body is a runtime-trip loop. -/
def nestedSource : LowCT :=
  .RForRuntime "i" (.SVar "m") (.RForRuntime "j" (.SVar "k") .RSkip)

/-- Two loop nodes in sequence: a first sweep, then a sibling sweep that is itself
    a nested loop. The `mpn_mul_basecase` two-phase spine (`mpn_mul_1` then
    `mpn_addmul_1`). -/
def siblingSource : LowCT :=
  .RSeq (.RForRuntime "t" (.SVar "un") .RSkip)
    (.RForRuntime "jd" (.SVar "vn")
      (.RForRuntime "s" (.SVar "un") .RSkip))

-- The countdown `while` selects the `ComL.whileNz` shape.
#guard ((split whileSource).map (·.shape) == .ok .whileNz)

-- An inner countdown `while` selects the block shape at two loop levels.
#guard ((split blockSource).map (·.shape) == .ok .forLoopBlock)
#guard ((split blockSource).map (·.loopDepth) == .ok 2)

-- An inner counted loop selects the nested shape, not the block shape.
#guard ((split nestedSource).map (·.shape) == .ok .runtimeNested)

-- Two loop nodes on the spine select the sibling-loops shape, rather than
-- silently dropping the second loop as a single-loop route would.
#guard ((split siblingSource).map (·.shape) == .ok .siblingLoops)
#guard ((analyse .com siblingSource).map (·.loopShape) == .ok .siblingLoops)

/-- The `RouteGap` a source's own plan reports when the caller supplies no count
    variable, or `none` when the dispatch has everything it needs. -/
def tripGapOf (src : LowCT) : Option RouteGap :=
  match analyse .com src with
  | .error g => some g
  | .ok p =>
      match tripOf (Γouter := []) p none with
      | .error g => some g
      | .ok _ => none

-- A countdown trip reads its guard from a caller-supplied register.
#guard tripGapOf whileSource == some .missingCountVariable

-- The block route takes the inner node's variables in the outer block's
-- loop-body context, which `compile` does not take.
#guard tripGapOf blockSource == some .blockNeedsInnerContext

-- The nested route takes the inner-count body as a second source.
#guard tripGapOf nestedSource == some .nestedNeedsTwoBodies

-- The sibling route takes the second loop's body in the extended context, which
-- `compile` (single-body) does not supply, so it names the axis by `RouteGap`
-- rather than dropping the second loop.
#guard tripGapOf siblingSource == some .siblingNeedsTwoBodies

/-! ### The buffer-result leaf-call condition

A loop-body binding resolves to a register (`loopResolveVarN`, through
`loopReg d slot`), and the loop-body call marshaller `callMarshalHere` dispatches
a leaf call between the GP and SSE register classes by `callMarshalWidth`, which
sends every non-`reg` type to 64. A leaf whose result is a `stackArr` — a buffer
returned through an out-pointer — therefore has neither a marshalling arm nor a
location for its result. The predicates below decide that condition on a body
`Com` and on a whole `ComL`, and `compile` reports it as
`RouteGap.bufferResultCallInBody`.

An array-typed accumulator or invariant is not this condition: those are
`stackArr`-typed too (`mapTy (.memref n) = .stackArr 64 n`), but they reach the
body as base names that the memref ops index, not as call results. -/

/-- Does a loop-body `Com` bind the result of a leaf call at a `stackArr` type?
    The result type itself is `JasminLprogExport.callResultBufferTy`, which the
    loop-body walk reads to give such a binding its frame slot. -/
def comBodyHasBufferCall :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, _, .ret _ => false
  | _, _, .var e body =>
      (callResultBufferTy e.op).isSome || comBodyHasBufferCall body

/-- Does any loop node of a `ComL` carry a buffer-result leaf call in its body?
    The `comLHasLoopCall` analogue for the buffer-result condition, over the same
    loop nodes. -/
def comLHasBufferCallLoopBody :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → Bool
  | _, _, .ret _ => false
  | _, _, .var _ body => comLHasBufferCallLoopBody body
  | _, _, .forLoop _ _ body => comLHasBufferCallLoopBody body
  | _, _, .forLoopN loop _ _ body =>
      comBodyHasBufferCall loop.update || comLHasBufferCallLoopBody body
  | _, _, .forLoopNRt update _ _ _ body =>
      comBodyHasBufferCall update || comLHasBufferCallLoopBody body
  | _, _, .forLoopNRtNested innerCount innerUpdate _ _ _ body =>
      comBodyHasBufferCall innerCount || comBodyHasBufferCall innerUpdate
        || comLHasBufferCallLoopBody body
  | _, _, .whileNz update _ _ _ body =>
      comBodyHasBufferCall update || comLHasBufferCallLoopBody body
  | _, _, .forLoopBlock loopBody _ _ _ body =>
      comLHasBufferCallLoopBody loopBody || comLHasBufferCallLoopBody body

/-- A loop body whose single binding calls a leaf returning a 16-word buffer, in
    the body context of an array accumulator and the loop index. -/
def bufferCallBody :
    Com jasminDialect [JasminTy.stackArr 64 16, JasminTy.reg 64]
      (JasminTy.stackArr 64 16) :=
  .var (.mk (.extCall "point_add" [.stackArr 64 16] (.stackArr 64 16)) rfl
          (.cons .here .nil))
    (.ret .here)

/-- A loop body whose single binding calls a leaf returning one register word,
    in the body context of a word accumulator and the loop index. -/
def regCallBody :
    Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (.mk (.extCall "prg_node" [.reg 64] (.reg 64)) rfl (.cons .here .nil))
    (.ret .here)

-- Static checks pinning the predicate against silent change: it fires on a
-- buffer-returning leaf call, and not on the register-result in-loop call the
-- emitted rolled kernels already carry.
#guard comBodyHasBufferCall bufferCallBody
#guard !comBodyHasBufferCall regCallBody

-- The same two bodies at the loop-body walk's own starting depth (`2` with no
-- invariant binders): the register-result call lays no buffer, so the loop
-- lowering takes its existing walk, and the buffer-result call lays one slot of
-- the leaf's result size and declares those bytes to the frame.
#guard loopBufBindings regCallBody 2 = []
#guard loopBufTotal (loopBufBindings regCallBody 2) = 0
#guard loopBufBindings bufferCallBody 2 = [(2, 128)]
#guard loopBufTotal (loopBufBindings bufferCallBody 2) = 128
#guard loopBufOff (loopBufBindings bufferCallBody 2) 2 = some 0

/-- Analyse `src`, select the route, and dispatch it.

    The caller supplies everything the source cannot name: the outer
    context `Γouter`, the accumulator seed and loop-invariant variables, the
    body `VarMap`, and — for a runtime or countdown trip — the count or guard
    variable. The choice of combinator comes from the plan, and the result
    carries the bundled front, so the denotation travels with the program.

    `.error` names the axis with no covering route (`RouteGap`), including
    `frontDeclined` when the selected front rejects the body and
    `bufferResultCallInBody` when the front's body binds a leaf-call result at a
    `stackArr` type. -/
def compile {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy} {invCTys : Ctx}
    (out : OutputForm) (src : LowCT)
    (countVar : Option (Ctxt.Var Γouter (JasminTy.reg 64)))
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Except RouteGap (CompileResult Γouter accCTy) :=
  match split src with
  | .error g => .error g
  | .ok sp =>
      match plan out sp with
      | .error g => .error g
      | .ok p =>
          match tripOf p countVar with
          | .error g => .error g
          | .ok trip =>
              match hupd : p.bodyFront.front (accCTy := accCTy) vmBody accName sp.body with
              | none => .error .frontDeclined
              | some u =>
                  if comBodyHasBufferCall u then .error .bufferResultCallInBody
                  else
                  match compileLoopFront p.bodyFront trip vmBody accName sp.body init
                          invs hupd with
                  | none => .error .uncoveredTripBodyPair
                  | some F =>
                      match hb : F.build with
                      | some c => .ok ⟨p, trip, sp.body, F, c, hb⟩
                      | none => .error .frontDeclined

/-- `compile`'s program is exactly its plan's route applied to its body. -/
theorem compile_eq_compileLoop {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (out : OutputForm) (src : LowCT)
    (countVar : Option (Ctxt.Var Γouter (JasminTy.reg 64)))
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {r : CompileResult Γouter accCTy}
    (h : compile out src countVar vmBody accName init invs = .ok r) :
    compileLoop r.plan.bodyFront r.trip vmBody accName r.body init invs
      = some r.prog := by
  unfold compile at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · rename_i F hF
              split at h
              · rename_i c hb
                cases h
                exact (compileLoopFront_build _ _ _ _ _ _ _ _ hF).symm.trans hb
              · exact absurd h (by simp)

/-- **`compile`'s program denotes the `JLoopBodyN` fold at the plan's trip
    count.** The statement is uniform over every route `compile` can select:
    the plan's own body front compiles the body it recorded, and the program it
    returned folds that body `r.trip.value V` times. -/
theorem compile_denote {Γouter : Ctxt jasminDialect} {accCTy : CryptoTy}
    {invCTys : Ctx}
    (out : OutputForm) (src : LowCT)
    (countVar : Option (Ctxt.Var Γouter (JasminTy.reg 64)))
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {r : CompileResult Γouter accCTy}
    (h : compile out src countVar vmBody accName init invs = .ok r)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : r.plan.bodyFront.front (accCTy := accCTy) vmBody accName r.body = some update)
    (V : Ctxt.Valuation Γouter) :
    ComL.denote r.prog V
      = JLoopBodyN.denote ⟨r.trip.value V, update⟩ (Expr.lookupArgs invs V)
          (init.lookup V) :=
  compileLoop_denote r.plan.bodyFront r.trip vmBody accName r.body init invs hupd
    (compile_eq_compileLoop out src countVar vmBody accName init invs h) V

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
