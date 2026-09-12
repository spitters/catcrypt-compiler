/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1CarrySelectEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1CarrySelectEmit

/-!
# The route selector run against hand-routed kernels

`FrontRoutePlan.analyse` reads a route off a `LowCT` source. Three in-tree mpn
kernels were routed by hand; this module runs the analysis on their loop bodies
and pins each axis decision with a `#guard`.

The kernels call `rolledForLoopNRt` / `rolledForLoopNRtC` /
`rolledForLoopNRtNested` on a loop *body* directly, so no kernel holds a `LowCT`
containing its own loop node. The loop-shape axis is therefore pinned on sources
built here from each kernel's body and its documented trip structure
(`mul1Source`, `basecaseSource`); the body-front and post-pass axes are pinned on
the kernels' own bodies with nothing reconstructed.

On `MpnMul1FrontEmit.limbBodyLowCT` and `MpnMulBasecaseFrontEmit.rowBodyLowCT`
the selected body front is `carrySelect` where those two kernels pass the body to
`frontLoopBodyJ`. `MpnMul1CarrySelectEmit` and `MpnMulBasecaseCarrySelectEmit`
route those same bodies through `frontLoopBodyJC`.

## Main results

* `mul1Source` / `basecaseSource` — the loop structures rebuilt from each
  kernel's body and its documented trip structure.
* `shapeOnlyPlan` / `tripGap` — a plan carrying only the loop-shape axis, and
  the `RouteGap` `tripOf` reports for it.
* `mul1_analyse_ne_hand_front` / `basecase_analyse_ne_hand_front` — the selected
  body front on the two sources the kernels front with `frontLoopBodyJ`.

The axis decisions themselves — body front, the carry-window and
widening-multiply counts it is read from, loop shape, and the whole plan
`analyse` returns — are pinned with `#guard`, which declares no name.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlanKernels

open CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The body-front and post-pass axes, on the kernels' own bodies -/

-- The `mpn_mul_1` limb body carries one fusable carry window.
#guard carryWindows MpnMul1FrontEmit.limbBodyLowCT == 1

-- The `mpn_mul_1` limb body carries one widening multiply, which is what the
-- `fuseMulHiLprog` post-pass consumes.
#guard mulHiOps MpnMul1FrontEmit.limbBodyLowCT == 1

-- The `mpn_mul_1` limb body carries no vsimd-tagged call.
#guard vsimdOps MpnMul1FrontEmit.limbBodyLowCT == 0

-- The `mpn_mul_1` limb body is itself loop-free, so it is an innermost body.
#guard loopDepth MpnMul1FrontEmit.limbBodyLowCT == 0

-- The body front selected for the `mpn_mul_1` limb body. Both
-- `MpnMul1FrontEmit` and `MpnMul1CarrySelectEmit` front this same body, the
-- first through `frontLoopBodyJ` and the second through `frontLoopBodyJC`.
#guard bodyFrontOf MpnMul1FrontEmit.limbBodyLowCT == .carrySelect

-- The basecase row body carries two fusable carry windows.
#guard carryWindows MpnMulBasecaseFrontEmit.rowBodyLowCT == 2

-- The basecase row body carries one widening multiply.
#guard mulHiOps MpnMulBasecaseFrontEmit.rowBodyLowCT == 1

-- The body front selected for the basecase row body. `MpnMulBasecaseFrontEmit`
-- fronts it through `frontLoopBodyJ`.
#guard bodyFrontOf MpnMulBasecaseFrontEmit.rowBodyLowCT == .carrySelect

-- The basecase inner-count body carries no carry window.
#guard carryWindows MpnMulBasecaseFrontEmit.cntBodyLowCT == 0

-- The basecase inner-count body carries no widening multiply.
#guard mulHiOps MpnMulBasecaseFrontEmit.cntBodyLowCT == 0

-- The body front selected for the basecase inner-count body, matching the
-- `frontLoopBodyJ` the kernel fronts it with.
#guard bodyFrontOf MpnMulBasecaseFrontEmit.cntBodyLowCT == .plain

/-! ## 2. The loop-shape axis, on sources rebuilt from the kernels' bodies -/

/-- `mpn_mul_1`'s loop structure: a single runtime-trip loop over the limb body,
    the shape `MpnMul1FrontEmit.mul1RtCom` reaches via `rolledForLoopNRt`. -/
def mul1Source : LowCT :=
  .RForRuntime "i" (.SVar "n") MpnMul1FrontEmit.limbBodyLowCT

/-- The basecase's loop structure: a runtime-trip outer loop whose body
    recomputes an inner trip count and runs a runtime-trip inner loop over the
    row body, the shape `MpnMulBasecaseFrontEmit.bcRtCom` reaches via
    `rolledForLoopNRtNested`. -/
def basecaseSource : LowCT :=
  .RForRuntime "i" (.SVar "un")
    (.RSeq MpnMulBasecaseFrontEmit.cntBodyLowCT
      (.RForRuntime "j" (.SVar "cnt") MpnMulBasecaseFrontEmit.rowBodyLowCT))

-- The `mpn_mul_1` source selects the runtime-trip shape.
#guard ((split mul1Source).map (·.shape) == .ok .runtimeN)

-- The basecase source selects the nested runtime-trip shape.
#guard ((split basecaseSource).map (·.shape) == .ok .runtimeNested)

-- `split` reaches the row body as the basecase's innermost body.
#guard ((split basecaseSource).map (·.loopDepth) == .ok 2)

-- Neither source has a tail after its loop node.
#guard ((split mul1Source).map (·.hasTail) == .ok false)

/-! ## 3. The whole plan -/

-- The plan for `mpn_mul_1`: a runtime-trip loop, a carry-select body front, no
-- tail, and the widening-multiply post-pass both mul1 kernels apply.
#guard (analyse .attText mul1Source
  == .ok { loopShape := .runtimeN, bodyFront := .carrySelect, hasTail := false,
           postPasses := [.fuseMulHiSaveRdx], optPasses := [], output := .attText,
           evidence := { loopDepth := 1, prologueCmds := 0, carryWindows := 1,
                         vsimdOps := 0, mulHiOps := 1 } })

-- The plan for the basecase: a nested runtime-trip loop, a carry-select body
-- front, and the widening-multiply post-pass the kernel applies.
#guard (analyse .attText basecaseSource
  == .ok { loopShape := .runtimeNested, bodyFront := .carrySelect, hasTail := false,
           postPasses := [.fuseMulHiSaveRdx], optPasses := [], output := .attText,
           evidence := { loopDepth := 2, prologueCmds := 0, carryWindows := 2,
                         vsimdOps := 0, mulHiOps := 1 } })

/-- A plan carrying `shape`, with every other axis at its neutral value.
    `tripOf` reads only the loop-shape axis. -/
def shapeOnlyPlan (shape : LoopShape) : CompilePlan :=
  { loopShape := shape, bodyFront := .plain, hasTail := false,
    postPasses := [], optPasses := [], output := .com,
    evidence := { loopDepth := 0, prologueCmds := 0, carryWindows := 0,
                  vsimdOps := 0, mulHiOps := 0 } }

/-- The `RouteGap` a `tripOf` call reports, or `none` when it succeeds. -/
def tripGap (shape : LoopShape) : Option RouteGap :=
  match tripOf (Γouter := []) (shapeOnlyPlan shape) none with
  | .error g => some g
  | .ok _ => none

-- Dispatching the basecase plan needs the inner-count body as a second source,
-- which `compile` does not take.
#guard tripGap .runtimeNested == some .nestedNeedsTwoBodies

-- A runtime-trip plan with no count variable names the missing input rather
-- than returning a bare failure.
#guard tripGap .runtimeN == some .missingCountVariable

/-! ## 4. Where the selection and the hand routing differ -/

/-- The body front selected for `mpn_mul_1`'s limb body is not the `plain` one
    `MpnMul1FrontEmit` fronts it with. `MpnMul1CarrySelectEmit` fronts the same
    body through `frontLoopBodyJC`. -/
theorem mul1_analyse_ne_hand_front :
    bodyFrontOf MpnMul1FrontEmit.limbBodyLowCT ≠ BodyFront.plain := by decide

/-- The body front selected for the basecase row body is not the `plain` one
    `MpnMulBasecaseFrontEmit` fronts it with. -/
theorem basecase_analyse_ne_hand_front :
    bodyFrontOf MpnMulBasecaseFrontEmit.rowBodyLowCT ≠ BodyFront.plain := by decide

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlanKernels
