/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckOps
public import CatCrypt.Crypto.SecureCompilation.VIR.TowerDialect

/-!
# Lowering the `pairing_check` GT product onto the `towerDialect` `Fp12` product

The `pairing_check` op (`EcPairingCheckOps.lean`) is a GT product followed by an
equality-to-one test.  This file lowers the **product** part onto a
`Com towerDialect` built from the `Fp12` product `TowerOp.mul .twelve` at
`u² = −1`, which `towerToField` lowers to a `fieldDialect` program over the
prime-field coordinates (`TowerDialect.towerToField_fundamental`).  The equality
tail (`gtIsOneF`) is a `cmp`-style predicate (bit/sword layer), as in
`FieldEcCmpOps`.

So a two-pairing check `e₁ · e₂ == 1` realises as:

    pairingCheck2  ⟶  gtIsOne ( tower-product-schedule e₁ e₂ )

with `pairingCheck2_lower_denote` proving the realisation denotes to the op
(mirroring `EcLineFieldEmit.ecLine_denote`, which lowers `ECOp.line` to its field
schedule).  The GT inputs `e₁`, `e₂` are the per-pairing `pairingEmit` outputs
(`BLS12381PairingTowerEmit.pairingEmit_realizes`, `= finalExp ∘ miller`); this
file supplies the remaining product+check stage's lowering, so the full
verification equation `∏ e == 1` is expressible end-to-end over proven
field-op schedules.

This is the lowering edge `pairingCheckDialect → towerDialect` (for the product);
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

/-! ## 1. The GT-product schedule (one tower `Fp12` product)

A two-input `Com towerDialect` computing `e₁ ·_{ξ} e₂ : fp12 p (−1) ξ` via a single
`TowerOp.mul .twelve`.  This is the lowering target of the pairing check's product. -/

/-- The GT-product schedule: `let r = mul₁₂ e₁ e₂; ret r` over
    `[fp12 p (−1) ξ, fp12 p (−1) ξ]`. -/
def pairingProductProg (p : Nat) (ξ : Int) :
    Com TowerDialect.towerDialect [.fp12 p (-1) ξ, .fp12 p (-1) ξ] (.fp12 p (-1) ξ) :=
  .var (.mk (.mul .twelve p (-1) ξ) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The product schedule denotes to the abstract `Fp12` product `Fp12Val.mul ξ`. -/
theorem pairingProductProg_denote (ξ : Int) (e1 e2 : Fp12Val p) :
    (pairingProductProg p ξ).denote (.cons e1 (.cons e2 .nil))
      = Fp12Val.mul (ξ : ZMod p) e1 e2 := by
  change Fp12Val.mulBeta ((-1 : Int) : ZMod p) (ξ : ZMod p) e1 e2 = _
  rw [Int.cast_neg, Int.cast_one]
  exact Fp12Val.mulBeta_neg_one _ e1 e2

/-! ## 2. Lowering preservation: the check is `gtIsOne ∘ product-schedule` -/

/-- **Lowering preservation.** The `pairingCheck2` op denotes to the
    GT-identity test applied to the tower product schedule's denotation — the
    realisation edge `pairingCheckDialect → towerDialect` for the product, with the
    `gtIsOne` predicate tail.  Mirrors `EcLineFieldEmit.ecLine_denote`. -/
theorem pairingCheck2_lower_denote (ξ : Int) (pub : Bool) (e1 e2 : Fp12Val p) :
    pairingCheckDenote.denote (.pairingCheck2 p (ξ : ZMod p) pub) (.cons e1 (.cons e2 .nil))
      = gtIsOneF ((pairingProductProg p ξ).denote (.cons e1 (.cons e2 .nil))) := by
  rw [pairingProductProg_denote, pairingCheck2_denote]

/-- The lowering is faithful on its accept/reject result: the lowered realisation accepts iff
    the two-pairing product is the GT identity. -/
theorem pairingCheck2_lower_iff (ξ : Int) (_pub : Bool) (e1 e2 : Fp12Val p) :
    gtIsOneF ((pairingProductProg p ξ).denote (.cons e1 (.cons e2 .nil))) = true
      ↔ Fp12Val.mul (ξ : ZMod p) e1 e2 = 1 := by
  rw [pairingProductProg_denote, gtIsOneF_iff]

end CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckLowering
