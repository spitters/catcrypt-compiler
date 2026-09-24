/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckOps

/-!
# Lowering the `pairing_check` GT product onto the `ext12Mul` field schedule

The `pairing_check` op (`EcPairingCheckOps.lean`) is a GT product followed by an
equality-to-one test.  This file lowers the **product** part onto a
`Com fieldDialect` built from `FieldOp.ext12Mul` — the same `Fp12` multiply that
already lowers, via `DialectLoweringChain.extChainDenote_fp12`, to the `Fp6`
schedule → `ModArith` → owned x86 bytes.  The equality tail (`gtIsOneF`) is a
`cmp`-style predicate (bit/sword layer), as in `FieldEcCmpOps`.

So a two-pairing check `e₁ · e₂ == 1` realises as:

    pairingCheck2  ⟶  gtIsOne ( ext12Mul-product-schedule e₁ e₂ )

with `pairingCheck2_lower_denote` proving the realisation denotes to the op
(mirroring `EcLineFieldEmit.ecLine_denote`, which lowers `ECOp.line` to its field
schedule).  The GT inputs `e₁`, `e₂` are the per-pairing `pairingEmit` outputs
(`BLS12381PairingTowerEmit.pairingEmit_realizes`, `= finalExp ∘ miller`); this
file supplies the remaining product+check stage's lowering, so the full
verification equation `∏ e == 1` is expressible end-to-end over proven
field-op schedules.

This is the lowering edge `pairingCheckDialect → fieldDialect` (for the product);
no claim is made that the schedule equals the mathematical Tate/Weil pairing.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Fp12Gt
open CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckOps

variable {p : Nat}

/-! ## 1. The GT-product schedule (one `ext12Mul` over `fieldDialect`)

A two-input `Com fieldDialect` computing `e₁ ·_{ξ₀} e₂ : fp12 p` via a single
`FieldOp.ext12Mul`.  This is the lowering target of the pairing check's product;
`ext12Mul` itself lowers to the `Fp6` schedule via
`DialectLoweringChain.extChainDenote_fp12`. -/

/-- The GT-product schedule: `let r = ext12Mul e₁ e₂; ret r` over
    `[fp12 p, fp12 p]`. -/
def pairingProductProg (p : Nat) (ξ0 : ZMod p) :
    Com fieldDialect [.fp12 p, .fp12 p] (.fp12 p) :=
  .var (.mk (.ext12Mul p ξ0) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The product schedule denotes to the abstract `Fp12` product `Fp12Val.mul ξ₀`
    — the once-per-op tie to `FieldDialect.ext12Mul`. -/
theorem pairingProductProg_denote (ξ0 : ZMod p) (e1 e2 : Fp12Val p) :
    (pairingProductProg p ξ0).denote (.cons e1 (.cons e2 .nil))
      = Fp12Val.mul ξ0 e1 e2 := rfl

/-! ## 2. Lowering preservation: the check is `gtIsOne ∘ product-schedule` -/

/-- **Lowering preservation.** The `pairingCheck2` op denotes to the
    GT-identity test applied to the `ext12Mul` product schedule's denotation — the
    realisation edge `pairingCheckDialect → fieldDialect` for the product, with the
    `gtIsOne` predicate tail.  Mirrors `EcLineFieldEmit.ecLine_denote`. -/
theorem pairingCheck2_lower_denote (ξ0 : ZMod p) (pub : Bool) (e1 e2 : Fp12Val p) :
    pairingCheckDenote.denote (.pairingCheck2 p ξ0 pub) (.cons e1 (.cons e2 .nil))
      = gtIsOneF ((pairingProductProg p ξ0).denote (.cons e1 (.cons e2 .nil))) := by
  rw [pairingProductProg_denote, pairingCheck2_denote]

/-- The lowering is faithful on its accept/reject result: the lowered realisation accepts iff
    the two-pairing product is the GT identity. -/
theorem pairingCheck2_lower_iff (ξ0 : ZMod p) (_pub : Bool) (e1 e2 : Fp12Val p) :
    gtIsOneF ((pairingProductProg p ξ0).denote (.cons e1 (.cons e2 .nil))) = true
      ↔ Fp12Val.mul ξ0 e1 e2 = 1 := by
  rw [pairingProductProg_denote, gtIsOneF_iff]

end CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckLowering
