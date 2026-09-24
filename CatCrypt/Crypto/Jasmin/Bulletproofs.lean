/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Bulletproofs inner-product argument — architecture + scaled skeleton

Bulletproofs ([BBBPWM18]) is a zero-knowledge range-proof system. Its
core is the *inner-product argument*, a recursive protocol reducing
the claim "⟨a, b⟩ = c" (for length-n vectors a, b) to a constant-size
final check via log₂(n) rounds of halving.

This file sets up the plumbing for a pipeline-(1a) port of the
inner-product argument. The full implementation is ~500 LoC of
protocol orchestration with ~3k gate-level ops per proof; shipping
it end-to-end is a Phase 7+ goal.

## Architecture

```
Bulletproofs inner-product proof (one round, length n → n/2):
  L_i := ⟨a_L, G_R⟩ + ⟨b_R, H_L⟩ + c_L · Q     -- n/2-length MSMs
  R_i := ⟨a_R, G_L⟩ + ⟨b_L, H_R⟩ + c_R · Q
  x_i := Fiat-Shamir(transcript || L_i || R_i)   -- challenge scalar
  a'  := a_L + x_i · a_R          (length n/2)
  b'  := x_i · b_L + b_R          (length n/2)
  G'  := x_i⁻¹ · G_L + G_R        (length n/2)
  H'  := H_L + x_i⁻¹ · H_R        (length n/2)
  -- recurse with (a', b', G', H') of length n/2 until n = 1
```

The "fold" scalars (`a_new = a_L + x · a_R` etc.) are straight-line
FpL25519 arithmetic and reify cleanly. The multi-scalar-muls (MSMs)
reuse `ed_scalarmult_wnaf` from the Ed25519 C harness — they're not
individually reifiable (MSM over variable-length vectors) but each
per-entry product is.

The Merlin-style transcript (`RistrettoChallenge255`) lives on the C
side along with the protocol driver. Reifier handles the per-element
crypto; C handles the protocol loop.

## What this file ships

1. **`ip_fold_scalar`** — one round's scalar fold,
   `a_new = a_L + x · a_R`, reified for n=1 (per-element form).
   The C driver iterates this over the vector at each round.

2. **`ip_fold_point`** — not reifiable (requires `x⁻¹` which
   uses the 253-bit Fermat chain over scalar field, expensive at
   reification time) — stated as the opaque signature `ip_fold_G` (§2).

3. **`Bulletproofs` namespace** — opaque types and the opaque verifier
   `ip_verify` that the C driver calls after Fiat-Shamir challenge generation.

## Next-step expansions (not in this file)

- `CatCrypt/Crypto/Jasmin/Examples/BulletproofsIPEmit.lean`: emit the
  fold-scalar MLIR for the hot-loop body.
- `catcrypt-bench/src/bench_bulletproofs.c`: inner-product proof driver
  wired to MLIR fold + wNAF MSM, compared against `dalek-cryptography/
  bulletproofs` Rust implementation on n ∈ {64, 128, 256, 512}.

## References

* [BBBPWM18] Bünz et al., *Bulletproofs: Short Proofs for Confidential
  Transactions and More*, S&P 2018.
* `dalek-cryptography/bulletproofs` — reference Rust implementation.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Bulletproofs

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## 1. Scalar-side fold step

The per-element formulas for one round of the inner-product
recursion. All operate on `FpL25519` (the Ed25519 scalar field). -/

/-- `ip_fold_a` — new scalar vector entry for `a`:
    `a_new_i = a_L_i + x · a_R_i`. -/
noncomputable def ip_fold_a
    (aL aR x : FpL25519) : FpL25519 :=
  let x_aR := scalar_mul x aR
  scalar_add aL x_aR

/-- `ip_fold_b` — new scalar vector entry for `b`:
    `b_new_i = x · b_L_i + b_R_i`. -/
noncomputable def ip_fold_b
    (bL bR x : FpL25519) : FpL25519 :=
  let x_bL := scalar_mul x bL
  scalar_add x_bL bR

def ipFoldAReified : ReifiedFunc := reifyLowCT% ip_fold_a
def ipFoldBReified : ReifiedFunc := reifyLowCT% ip_fold_b

/-! ## 2. Point-side fold (opaque)

The point fold `G_new = x⁻¹ · G_L + G_R` requires `x⁻¹ mod L` which is
a 253-bit addition-chain; reifying it per-element would emit hundreds
of ops per vector entry. In practice the C driver precomputes `x⁻¹`
once per round (via dalek_shim's `scalar_inv`), then the per-entry
point combination is a 2-scalar MSM handled by `ed_scalarmult_wnaf`.

No reifier function — the C driver calls MLIR-emitted `ed25519_add_*`
and `ed25519_dbl_*` through `ed_scalarmult_wnaf` directly. -/

/-- Abstract signature for the per-element MSM: `G_new_i = xi_inv · G_L_i + G_R_i`.
    Wrapper-implemented via ed_scalarmult_wnaf on each side. -/
noncomputable opaque ip_fold_G : FpL25519 → FpL25519 → Unit

/-! ## 3. Protocol-level API (spec-only)

Opaque types for a minimal surface. The full definition of
`InnerProductProof` is a Merlin transcript + log n (L_i, R_i) points +
a final 2-scalar tail. -/

/-- Witness for an inner-product claim: two same-length scalar vectors. -/
structure IPWitness where
  a : List FpL25519
  b : List FpL25519

/-- Statement: the commitment `P` together with the generators and the
    claimed inner-product value `c`. -/
structure IPStatement where
  P_compressed : List UInt8     -- 32-byte compressed Edwards point
  G            : List FpL25519   -- scalar handles (real Gs live C-side)
  H            : List FpL25519
  c            : FpL25519

/-- Proof: the log n (L, R) challenge-point pairs, plus two final
    scalars a*, b*. Each Edwards point is a 32-byte compressed blob. -/
structure IPProof where
  L_values : List (List UInt8)   -- each 32-byte compressed point
  R_values : List (List UInt8)
  a_final  : FpL25519
  b_final  : FpL25519

/-- Spec-level soundness claim. The actual proof (`reduction_to_DL` in
    [BBBPWM18]) is out of scope; this opaque constant stands in as the interface. -/
noncomputable opaque ip_verify : IPStatement → IPProof → Bool

end CatCrypt.Crypto.Jasmin.Bulletproofs
