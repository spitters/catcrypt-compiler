/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTBorrowCheckInPlace
import CatCrypt.Crypto.Jasmin.S2NBignumSSA

set_option autoImplicit false

/-!
# B5.2 — Per-leaf in-place certs for the 4 in-tree p25519 leaves

Instantiates `InPlaceLeafCert` for each leaf in `bignumSigDb` with
`destAliasOk ≠ []`. Each cert combines:
- The leaf's name (matches `bignumSigDb`'s key).
- The leaf's SSA body (from `S2NBignumSSA.lean`).
- The leaf's declared `destAliasOk` indices.
- A proof that `noLateLoadAfterStore body = true`, discharged by
  `decide` (the predicate is decidable on a closed `List InstrR`).

If `decide` is too slow on a body, we'd fall back to `native_decide`
or a hand decomposition; in practice these p25519 leaves are short
enough (sub_p25519 ~22 instrs, double_p25519 ~50, mod_p25519_4 ~80,
inv_p25519 ~700 — Bernstein chain). For longer bodies we use
`native_decide` to avoid kernel reduction blowup.

The B5.1.b operational soundness proof (Qed in
`LowCTBorrowCheckInPlace.lean` as `bignumExec_noStore_preserves_mem`)
gives the *memory-preservation* half of the in-place reuse claim.
The full `InPlaceSoundnessFull` chain combines it with the dual
`bignumExec_noLoad_preserves_regs` (still TODO) via the
`noLateLoadAfterStore_decompose` structural split.
-/

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.S2NBignumSSA

/-! ## §1. The 4 certs -/

/-- `bignum_sub_p25519` — load both inputs into registers (8 `Pload`s),
then subtract with carry, then store. Output may alias first arg. -/
def cert_bignum_sub_p25519_concrete : InPlaceLeafCert :=
  { name := "bignum_sub_p25519"
    body := BignumSubP25519.body
    destAliasOk := [0]
    safe := by native_decide }

/-- `bignum_double_p25519` — load 4 limbs of input, add to itself with
carry, reduce. Output may alias input. -/
def cert_bignum_double_p25519_concrete : InPlaceLeafCert :=
  { name := "bignum_double_p25519"
    body := BignumDoubleP25519.body
    destAliasOk := [0]
    safe := by native_decide }

/-- `bignum_mod_p25519_4` — canonical-reduction of a 4-limb input mod
p. Single load-pass + single store-pass. -/
def cert_bignum_mod_p25519_4_concrete : InPlaceLeafCert :=
  { name := "bignum_mod_p25519_4"
    body := BignumModP25519_4.body
    destAliasOk := [0]
    safe := by native_decide }

/-- `bignum_inv_p25519` — Bernstein chain modular inverse. Body is
~700 instrs; we use `native_decide` rather than `decide` for kernel
performance. Output may alias input. -/
def cert_bignum_inv_p25519_concrete : InPlaceLeafCert :=
  { name := "bignum_inv_p25519"
    body := BignumInvP25519.body
    destAliasOk := [0]
    safe := by native_decide }

/-! ## §2. Cross-check: each cert agrees with `bignumSigDb` -/

example : cert_bignum_sub_p25519_concrete.matchesSigDb := by native_decide
example : cert_bignum_double_p25519_concrete.matchesSigDb := by native_decide
example : cert_bignum_mod_p25519_4_concrete.matchesSigDb := by native_decide
example : cert_bignum_inv_p25519_concrete.matchesSigDb := by native_decide

/-! ## §3. Registry -/

/-- All 4 in-tree p25519 in-place certs collected. Downstream callers
of `borrowOk' bignumSigDb` use this list to discharge the aliasing
hypotheses without `sorry`. -/
def curve25519InPlaceCerts : List InPlaceLeafCert :=
  [ cert_bignum_sub_p25519_concrete
  , cert_bignum_double_p25519_concrete
  , cert_bignum_mod_p25519_4_concrete
  , cert_bignum_inv_p25519_concrete ]

end CatCrypt.Crypto.Jasmin
