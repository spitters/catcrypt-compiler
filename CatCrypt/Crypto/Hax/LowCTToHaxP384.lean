/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.LowCTToHax
public import CatCrypt.Crypto.Jasmin.P384DhkemReflect

/-!
# The P-384 kernels in the hax subset

The `LowCT` bodies of the P-384 kernels that `CatCrypt.EmitArtifacts.P384Rust`
renders to Rust have hax translations in the front's subset: each translation
is `AnfShaped` and `haxToLowCT` lowers it to `frontNF` of the body
(`lowCTToImp_inFront_of_isSome`).  The bodies are straight-line chains of leaf
calls, so `frontNF` differs from the body only in the located types of the
calls: the front types a call `f` at `towerOfCallName f`.

Each membership `(lowCTToImp c).isSome = true` is closed by kernel reduction on
the body.  The reduction runs no string comparison, since the call and sequence
arms of `lowCTToImp` carry no side condition; the pins fail if a kernel body
leaves the translated fragment.

The two-ladder ECDSA-verify orchestration body `p384EcdsaVerifyBody` declares
its locals with `RLetZero`s that no leaf call follows, and has no translation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCTReflect
  (p384MsmTermBody p384EcdsaVerifyBody p384EcdsaVerifyFullBody p384EcdsaSignBody
   p384DhkemEncapBody p384DhkemDecapBody)

/-- The ECDSA-P384 verification body translates into the front's subset. -/
theorem p384EcdsaVerifyFull_inFront :
    ∃ e, lowCTToImp p384EcdsaVerifyFullBody = some e ∧
      haxToLowCT e = some (frontNF p384EcdsaVerifyFullBody) ∧ AnfShaped e = true :=
  lowCTToImp_inFront_of_isSome _ rfl

/-- The ECDSA-P384 signing body translates into the front's subset. -/
theorem p384EcdsaSign_inFront :
    ∃ e, lowCTToImp p384EcdsaSignBody = some e ∧
      haxToLowCT e = some (frontNF p384EcdsaSignBody) ∧ AnfShaped e = true :=
  lowCTToImp_inFront_of_isSome _ rfl

/-- The DHKEM(P-384) `Encap` body translates into the front's subset. -/
theorem p384DhkemEncap_inFront :
    ∃ e, lowCTToImp p384DhkemEncapBody = some e ∧
      haxToLowCT e = some (frontNF p384DhkemEncapBody) ∧ AnfShaped e = true :=
  lowCTToImp_inFront_of_isSome _ rfl

/-- The DHKEM(P-384) `Decap` body translates into the front's subset. -/
theorem p384DhkemDecap_inFront :
    ∃ e, lowCTToImp p384DhkemDecapBody = some e ∧
      haxToLowCT e = some (frontNF p384DhkemDecapBody) ∧ AnfShaped e = true :=
  lowCTToImp_inFront_of_isSome _ rfl

/-- The P-384 MSM-term body translates into the front's subset. -/
theorem p384MsmTerm_inFront :
    ∃ e, lowCTToImp p384MsmTermBody = some e ∧
      haxToLowCT e = some (frontNF p384MsmTermBody) ∧ AnfShaped e = true :=
  lowCTToImp_inFront_of_isSome _ rfl

/-- The two-ladder ECDSA-verify orchestration body declares its locals with
    `RLetZero`s that no leaf call follows, a shape no arm of `haxToLowCT`
    produces, and has no translation. -/
theorem p384EcdsaVerify_lowCTToImp : lowCTToImp p384EcdsaVerifyBody = none := rfl

end CatCrypt.Crypto.Hax
