/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote

/-!
# The front-compiled `mpn_mul_basecase` inner-count body is a `ScalarMemN` member

The nested machine tie feeds `bcCntUpdate` (the inner-trip-count recompute
`cnt := un + 1`) into the inline-nest export as the `innerCount` chain; the
inner-count bridge `lsemInnerTripMemN_eq_innerTripAtC` requires it to be in the
register-returning stack-memory fragment `ScalarMemN`.

## Main results

* `bcCntUpdate_scalarMemN` — the front-compiled inner-count body is a `ScalarMemN`
  member.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseCntScalarMemN

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (ScalarMemN)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote (bcCntUpdate)

/-- **The front-compiled `mpn_mul_basecase` inner-count body is a `ScalarMemN`
    member.** The body `cnt := un + 1` front-compiles to a `regConst`/`regArith`
    chain terminating in a register `.ret`; the refine cascade peels one head per
    step with no reduction of a long command list. -/
theorem bcCntUpdate_scalarMemN : ScalarMemN bcCntUpdate := by
  unfold bcCntUpdate
  repeat first
    | exact ScalarMemN.ret _
    | refine ScalarMemN.var _ rfl _ ?_
    | refine ScalarMemN.const _ (by decide) rfl _ ?_
    | refine ScalarMemN.shl (by decide) rfl _ ?_
    | refine ScalarMemN.shr (by decide) rfl _ ?_
    | refine ScalarMemN.sel rfl _ ?_

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseCntScalarMemN
