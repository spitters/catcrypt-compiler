/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTBorrowCheckInPlace
public import CatCrypt.Crypto.Jasmin.LowCTBorrowCheckInPlace
public meta import CatCrypt.Crypto.Jasmin.S2NBignumSSA
public import CatCrypt.Crypto.Jasmin.S2NBignumSSA

@[expose] public section

set_option autoImplicit false

/-!
# Per-leaf in-place safety certificates (B5.2)

For each of the 4 leaves in `bignumSigDb` with `destAliasOk ≠ []`, we
package an `InPlaceLeafCert` whose `safe : InPlaceSafe body` field is
discharged by `decide` (or `native_decide` for large bodies).

Recall the static discipline (`noLateLoadAfterStore`): a body is
in-place-safe iff no `Pload` follows an `Lmem` store in instruction
order. Each of the 4 leaves below follows the canonical s2n-bignum
"load all inputs first, then carry chain, then store outputs"
pattern, so the predicate evaluates to `true` by inspection.

## Leaf coverage

| Cert name                               | Leaf                       | Discharge       |
|-----------------------------------------|----------------------------|-----------------|
| `cert_bignum_sub_p25519_safe`           | `bignum_sub_p25519`        | `native_decide` |
| `cert_bignum_double_p25519_safe`        | `bignum_double_p25519`     | `native_decide` |
| `cert_bignum_mod_p25519_4_safe`         | `bignum_mod_p25519_4`      | `native_decide` |
| `cert_bignum_inv_p25519_safe`           | `bignum_inv_p25519`        | `native_decide` |

`native_decide` adds the `Lean.ofReduceBool` axiom (acceptable trust
extension for compiled-bool reduction). Per-bench bodies have ~50–150
straight-line instructions; `inv_p25519` has ~600 (Bernstein chain via
Ccalls), still within native_decide's reach.

The certs are gathered into a list `certs : List InPlaceLeafCert`
exposed for downstream callers (e.g., the borrow-check weakening
lemma in `LowCTBorrowCheckSig.lean`). -/

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Crypto.Jasmin.S2NBignumSSA

/-! ## §1. Per-leaf certificates -/

/-- `bignum_sub_p25519`: load 4 limbs of `a`, load 4 limbs of `b`,
SBB chain, conditional-add `mask·p`, store 4 limbs to `op`. All
loads precede all stores. Aliasing `op = ap` is safe. -/
def cert_bignum_sub_p25519_safe : InPlaceLeafCert where
  name := "bignum_sub_p25519"
  body := BignumSubP25519.body
  destAliasOk := [0]
  safe := by native_decide

/-- `bignum_double_p25519`: load 4 limbs of `a`, ADD/ADC chain
producing `2a`, conditional-subtract p via SBB+CMOVc emulated as a
mask, store 4 limbs to `op`. Aliasing `op = ap` safe. -/
def cert_bignum_double_p25519_safe : InPlaceLeafCert where
  name := "bignum_double_p25519"
  body := BignumDoubleP25519.body
  destAliasOk := [0]
  safe := by native_decide

/-- `bignum_mod_p25519_4`: load 4 limbs of `a`, SBB chain against `p`
to test ≥, mask + ADC chain, store 4 limbs to `op`. Aliasing `op = ap`
safe. -/
def cert_bignum_mod_p25519_4_safe : InPlaceLeafCert where
  name := "bignum_mod_p25519_4"
  body := BignumModP25519_4.body
  destAliasOk := [0]
  safe := by native_decide

/-- `bignum_inv_p25519`: Bernstein addition chain via Ccalls into
`bignum_montmul_p25519`. The body is structured as:
  - initial load of 4 limbs of `a` into a scratch buffer,
  - long sequence of pointer-arithmetic + Ccall(montmul, ...),
  - final store of 4 limbs from scratch into `op`.
The pointer-arithmetic uses register ops (no `Pload`); the only
`Pload`s are in the initial loads, and the only `Lmem` stores are at
the end. So `noLateLoadAfterStore` holds.

Note: the Ccalls' arguments include `Pvar`s but no `Pload`s — see
`hasLoad`'s `Ccall` case for the relevant projection. -/
def cert_bignum_inv_p25519_safe : InPlaceLeafCert where
  name := "bignum_inv_p25519"
  body := BignumInvP25519.body
  destAliasOk := [0]
  safe := by native_decide

/-! ## §2. Cross-check: each cert agrees with `bignumSigDb` -/

example : cert_bignum_sub_p25519_safe.matchesSigDb := by native_decide
example : cert_bignum_double_p25519_safe.matchesSigDb := by native_decide
example : cert_bignum_mod_p25519_4_safe.matchesSigDb := by native_decide
example : cert_bignum_inv_p25519_safe.matchesSigDb := by native_decide

/-! ## §3. Aggregated cert list -/

/-- The four certs in this file. Downstream consumers can iterate
this list to discharge `borrowOk'` weakening obligations leaf-by-leaf. -/
def certs : List InPlaceLeafCert :=
  [ cert_bignum_sub_p25519_safe
  , cert_bignum_double_p25519_safe
  , cert_bignum_mod_p25519_4_safe
  , cert_bignum_inv_p25519_safe ]

/-- Smoke: the cert list has length 4. -/
example : certs.length = 4 := by decide

end CatCrypt.Crypto.Jasmin
