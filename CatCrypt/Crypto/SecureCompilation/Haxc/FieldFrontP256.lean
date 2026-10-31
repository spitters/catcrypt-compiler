/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect
public import CatCrypt.Crypto.Util.P256Verified
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect
public meta import CatCrypt.Crypto.Util.P256Verified
public meta import CatCrypt.Crypto.PrimeIR.Extraction.Fp256Mont_haxpipe
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1

@[expose] public section

set_option autoImplicit false

/-!
# The field front accepts `fe_mul_add` at the P-256 base prime

The hax function `fe_mul_add` (`a * b + c`) of the `primeir_hax` crate extracts to the call
`add (mul a b) c`, whose first argument is a call. The front `impToNF` translates the
arguments of a call in A-normal form (`ImpToNF.impArgsNF`), so the field front
`fieldLeg P256 ["a", "b", "c"]` accepts the extraction under the layout `fieldAbi 3 4`: the
front, `NFProg.dce`, the translation to `fieldDialect` and the route of the Montgomery
template of the P-256 base prime all succeed.

## Main results

* `fieldFront_accepts_p256`: the field front accepts `fe_mul_add` at the P-256 base prime.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldFrontP256

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect
open CatCrypt.Util (P256)

/-- **The field front accepts `fe_mul_add` at the P-256 base prime**, under the layout
    `fieldAbi 3 4`. -/
theorem fieldFront_accepts_p256 :
    ((fieldLeg P256 ["a", "b", "c"]).front (fieldAbi 3 4) Primeir.fe_mul_add_texpr).isSome =
      true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldFrontP256
