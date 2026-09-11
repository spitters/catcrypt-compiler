/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
public import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-!
# Curve-width (4-limb) Barrett pipeline: bridging the emitted product to the stack

The Barrett reduction `MultiLimbKernel.barrettReduce` (proven `= x mod p` at any width by
`barrettReduce_val`) composes: a wide product `x·mu`, a limb-drop, a product `q·p`, a
subtract, and a conditional subtract. The wide products are the emitted schoolbook
`emitProductBlock` (`SchoolbookProductRunBlock`, proven `runBlock = valLimbs x · valLimbs
y`). This file ties that emitted product to the multi-limb proof stack's `bignumVal
(mulBignum …)`, the first step of routing the full curve-width Barrett pipeline through
the emitted x86 machine.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Bignum4BarrettEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-- **The emitted schoolbook product computes `bignumVal (mulBignum x y)`.** Reading the
    proven `runBlock` product value (`valLimbs x · valLimbs y`) through
    `valLimbs_eq_bignumVal` and `mulBignum_val`, the emitted wide-multiply block realises
    the verified multi-limb schoolbook multiply — the product step of the Barrett (or
    Montgomery) pipeline, in the `bignumVal` world. -/
theorem product_bignumVal
    (accs as ys : List String) (x yv : List (BitVec 64)) (hi lo : String)
    (s : JState 64)
    (haslen : as.length = x.length) (hyslen : ys.length = yv.length)
    (hcap : as.length + ys.length ≤ accs.length)
    (hfresh : ProdFresh accs as ys hi lo)
    (hx : as.map s.get = x) (hy : ys.map s.get = yv)
    (hacc0 : ∀ r ∈ accs, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    runBlockProductValue accs as ys hi lo s = bignumVal (mulBignum x yv) := by
  rw [emitProductBlock_runBlock_value accs as ys x yv hi lo s haslen hyslen hcap hfresh
      hx hy hacc0 hcf hof, mulBignum_val, valLimbs_eq_bignumVal, valLimbs_eq_bignumVal]

end CatCrypt.Crypto.SecureCompilation.Bignum4BarrettEmit
