/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Ed25519.PowP58
import CatCrypt.Crypto.Jasmin.S2NBignumSSA

/-!
# Bridge: `fp_pow_p58` (spec) ↔ `bignum_pow_p25519_p58` (chain)

Connects the spec-side `fp_pow_p58 : Fp25519 → Fp25519` axiom (in
`Ed25519/PowP58.lean`) to the bignum-side `BignumPowP58P25519`
chain (in `S2NBignumSSA.lean`).

## What this file establishes

* `bignum_pow_p25519_p58_refSem_correct` — the chain's reference
  semantics matches `(p−5)/8` exponentiation.
* Documentation of how `interp_fp_pow_p58` would be discharged
  through the `BignumPowP58P25519.body` SSA chain via the
  Phase 3/4 framework's `bignumExec`-Hoare-triple machinery
  (analogous to the `bignum_inv_p25519` discharge for
  `interp_fp_inv_pow`).

## Status

The chain itself is verified at the Nat level (its exponent
matches `(p−5)/8`).  The full pipeline-level Hoare triple
discharging the SSA `body` against the chain's algebraic intent
is the multi-day Phase 3/4 framework port.  The
spec-side `interp_fp_pow_p58` axiom is the trust boundary
today; this file documents the discharge path.

## Pipeline

```
  Spec layer:   interp_fp_pow_p58 : interp_fe (fp_pow_p58 x) =
                                     (interp_fe x)^((p−5)/8)
                          ↑ (axiom — Rocq citation today)
  Bridge:       fp_pow_p58 ⇝ BignumPowP58P25519.body
                          ↑ (this file — connect names + reference sem)
  Chain layer:  BignumPowP58P25519.body : List InstrR
                          ↑ (S2NBignumSSA.lean, this commit)
                          ↑ (chain_exponent_correct + Bernstein chain)
  refSem:       a^((p−5)/8) mod p
```
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.PowP58Bridge

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.BignumPowP58P25519
open CatCrypt.Crypto.Jasmin.Ed25519.PowP58

/-! ## §1  Reference-semantics shape match

`refSem` (the chain's algorithmic intent) computes
`a^((p−5)/8) mod p`, and the spec's `interp_fp_pow_p58` claims
`interp_fe (fp_pow_p58 x) = (interp_fe x)^((p−5)/8)` in `ZMod p`.

These match when the input/output `Nat ↔ Fp25519` byte-encodings
agree — which is exactly what `bignum_inv_p25519`'s discharge
relies on for the inv chain. -/

/-- Reference-semantics correctness: for any input `(a0, a1, a2, a3)`
    interpreted as a 256-bit Nat, the chain computes
    `a^((p−5)/8) mod p`. -/
theorem refSem_eq_pow_p58 (a0 a1 a2 a3 : Nat) :
    refSem a0 a1 a2 a3 =
      Nat.pow (a0 + a1 * 2^64 + a2 * 2^128 + a3 * 2^192)
              ((2^255 - 19 - 5) / 8) % (2^255 - 19) := by
  unfold refSem
  -- The chain's `(p − 5) / 8` matches the spec's `(p − 5) / 8` literally.
  -- decide handles the small constant arithmetic difference.
  rfl

/-- The chain's exponent equals `(p−5)/8` for `p = 2²⁵⁵ − 19`. -/
theorem chain_exponent_eq_p58 :
    ((2^255 - 19 : Nat) - 5) / 8 = 2^252 - 3 := by decide

/-! ## §2  Discharge sketch

The full discharge of `interp_fp_pow_p58` from the bignum chain
follows `bignum_inv_p25519`'s pattern (cf. `Ed25519Spec.lean`'s
`interp_fp_inv_pow`):

1. **Layer A — chain Nat correctness**: prove the SSA body's
   Bernstein-chain transcription computes `(p−5)/8`-exponentiation
   at the Nat level, via induction over the 12-block prefix +
   2-square-1-multiply tail.  The exponent identity is in
   `BignumPowP58P25519.chain_exponent_correct`.

2. **Layer B — Hoare triple from `bignumExec`**: lift the Nat
   correctness through `bignumExec_append` chunked composition
   (Phase 3/4 framework, mirroring `double_p25519_triple` from
   `BignumHoare.lean` iter 9).

3. **Layer C — interp bridge**: connect the byte-encoded `Nat`
   output to `Fp25519`'s `interp_fe`, mirroring
   `interp_fp_inv`'s discharge from `bignum_inv_p25519`.

Each layer is mechanical given the Phase 3/4 recipe.  The
estimate is ~450 LoC across the three layers.

## §3  Trust boundary today

Until Layers A/B/C land, the trust set for any consumer of
`interp_fp_pow_p58` is:

```
fp_pow_p58 (axiom; opaque function — discharged by chain)
interp_fp_pow_p58 (axiom; chain correctness — discharged by Layers A+B+C)
```

Both axioms are *local* to `Ed25519/PowP58.lean`; downstream
consumers (Elligator2, Lizard concrete) cite them transitively
through this bridge file.  Once Layers A/B/C close, both axioms
become theorems and the trust set shrinks accordingly. -/

end CatCrypt.Crypto.Jasmin.Ed25519.PowP58Bridge
