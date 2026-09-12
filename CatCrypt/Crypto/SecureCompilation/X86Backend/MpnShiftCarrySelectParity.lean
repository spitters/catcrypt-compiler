/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# The funnel-shift emit under the carry-selecting front

`CarryChainSelect.translateDialectCarrySelect` rewrites a body's `bSltu` carry
windows to `bvAddCarryLo`/`bvAddCarryHi` pairs, which the owned backend renders
as `adcx`. Its four window matchers (`matchAddStart`, `matchSubStart`,
`matchAddMid`, `matchSubMid`) each require a three-command `matchLtu` window
adjacent to the merge, and `matchAddFin` requires a carry-in name registered by
one of those. `MpnShiftFrontEmit.shiftBodyLowCT` has no such window: the funnel
merge `s := (t << sh) + rp[idx]` is carry-free by construction, since the
spill-in occupies bits `[0, sh)` and the shifted limb bits `[sh, 64)`. The
front's other rewrite, index re-materialisation, applies to an `RArrLoad` /
`RArrStore` whose index name is bound to an `SLit`; the body's indices are the
loop parameter `idx` and `idx1 := idx + 1`.

Every command of the funnel body therefore falls through to
`translateDialectControl`, and the carry-selected emit is the plain emit.

The body-front axis is supplied here rather than derived. `FrontRoutePlan.plan`
selects `carrySelect` only for a body with at least one fusable window, so on
this body it selects `plain`; the comparison this module makes is between the two
fronts on the same body, which is `FrontRoutePlan.compileLoop` at an explicit
`carrySelect`.

## Main results

* `shiftRtProgCOpt` — the funnel-shift loop through the carry-selecting front.
* `#guard`s pinning that its physical body has the same length as the emit
  through the plain front.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftCarrySelectParity

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoopCarrySelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
  (NRS NUS AR AU r64 Gouter vmBody shiftBodyLowCT shiftCount shiftInit shiftInvs
   shiftRtPhysBodyOpt shiftRtAsmOpt)

/-- The funnel-shift runtime-trip loop sourced through the carry-selecting body
    front. `none` if that front declines. -/
def shiftRtProgCOpt : Option (ComL Gouter AR) :=
  Dialects.FrontRoutePlan.compileLoop (Γouter := Gouter) (accCTy := .memref NRS)
    (invCTys := [.memref NUS, .sword 64])
    .carrySelect (.runtime shiftCount)
    vmBody "rp" shiftBodyLowCT shiftInit shiftInvs

-- The carry-selecting front accepts the body and wraps it in a
-- `ComL.forLoopNRt`.
#guard shiftRtProgCOpt.isSome

/-- The 4-argument-ABI physical body of the carry-selected funnel-shift loop. -/
def shiftRtPhysBodyCOpt : Option Lcmd :=
  shiftRtProgCOpt.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]).lfd_body)

/-- The owned AT&T `.s` text for the carry-selected funnel shift. -/
def shiftRtAsmCOpt (fname : String) : Option String :=
  shiftRtProgCOpt.map (fun c =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (ComL.toLprogPhysAbi c fname (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]))

-- The two fronts agree on the emit's instruction count: the funnel body has no
-- carry window for the selector to fuse.
#guard ((match shiftRtPhysBodyCOpt, shiftRtPhysBodyOpt with
  | some bc, some bp => decide (bc.length = bp.length)
  | _, _ => false) : Bool)

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftCarrySelectParity
