/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# GT (`Fp12`) identity, decidable equality, and the `is_one` test

The pairing target group `GT = Fp12` is modelled in `FieldDialect` as `Fp12Val p`
(a pair of `Fp6Val p`, itself a triple of `Fp2Val p`).  `FieldDialect` gives the
tower its `add`/`sub`/`mul` (the multiply carries the curve non-residue `ξ₀`), but
not the multiplicative **identity** nor decidable equality — both needed to state
the GT-membership test `e == 1` a pairing check ends on.

This file adds, for the `FieldDialect` tower carriers:

* `Zero`/`One` instances for `Fp6Val` and `Fp12Val` (the additive and
  multiplicative identities — `Fp2Val` already has them in `FieldDialect`);
* `DecidableEq` for `Fp2Val`/`Fp6Val`/`Fp12Val` (each is a structure over `ZMod p`,
  which is `DecidableEq`);
* `gtIsOneF : Fp12Val p → Bool`, the GT-identity test `decide (x = 1)`, with the
  `Bool ↔ Prop` agreement lemma `gtIsOneF_iff`.

These are the missing ingredients for a first-class `pairing_check` op
(`EcPairingCheckOps.lean`): the multi-pairing product is `Fp12Val.mul ξ₀` folded
from the GT identity `1`, and the check is `gtIsOneF` of that product.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Fp12Gt

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

variable {p : Nat}

/-! ## 1. Decidable equality for the tower carriers

Each tower value is a structure whose leaves are `ZMod p` (which is
`DecidableEq`), so the `deriving` extension supplies the instances. -/

deriving instance DecidableEq for Fp2Val
deriving instance DecidableEq for Fp6Val
deriving instance DecidableEq for Fp12Val

/-! ## 2. Additive and multiplicative identities for `Fp6`/`Fp12`

`Fp2Val` already has `Zero`/`One` in `FieldDialect`.  The cubic and quadratic
extensions get theirs componentwise: `0` is all-zero, `1` is the base `1` in the
constant component and `0` elsewhere. -/

/-- The `Fp6` additive identity `0 + 0·v + 0·v²`. -/
instance : Zero (Fp6Val p) := ⟨⟨0, 0, 0⟩⟩
/-- The `Fp6` multiplicative identity `1 + 0·v + 0·v²`. -/
instance : One (Fp6Val p) := ⟨⟨1, 0, 0⟩⟩
/-- The `Fp12` additive identity `0 + 0·w`. -/
instance : Zero (Fp12Val p) := ⟨⟨0, 0⟩⟩
/-- The `Fp12` (= GT) multiplicative identity `1 + 0·w`. -/
instance : One (Fp12Val p) := ⟨⟨1, 0⟩⟩

@[simp] theorem fp6_zero_a0 : (0 : Fp6Val p).a0 = 0 := rfl
@[simp] theorem fp6_one_a0 : (1 : Fp6Val p).a0 = 1 := rfl
@[simp] theorem fp6_one_a1 : (1 : Fp6Val p).a1 = 0 := rfl
@[simp] theorem fp6_one_a2 : (1 : Fp6Val p).a2 = 0 := rfl
@[simp] theorem fp12_one_c0 : (1 : Fp12Val p).c0 = 1 := rfl
@[simp] theorem fp12_one_c1 : (1 : Fp12Val p).c1 = 0 := rfl

/-! ## 3. The GT-identity test -/

/-- The GT-membership test `e == 1` over `Fp12Val p` (prime-ir's pairing-check
    tail): `true` iff `e` is the GT identity.  Decidable via the tower
    `DecidableEq`. -/
@[reducible] def gtIsOneF (x : Fp12Val p) : Bool := decide (x = 1)

/-- **Agreement.** `gtIsOneF` is `true` iff the GT element is the identity. -/
theorem gtIsOneF_iff (x : Fp12Val p) : gtIsOneF x = true ↔ x = 1 := by
  simp [gtIsOneF]

/-- The GT identity passes its own membership test. -/
@[simp] theorem gtIsOneF_one : gtIsOneF (1 : Fp12Val p) = true := by
  simp [gtIsOneF]

end CatCrypt.Crypto.SecureCompilation.VIR.Fp12Gt
