/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumHoare.ChainStepAxioms

/-!
# Per-block correctness instances for inv and pow_p58 chains

13 chain-step instances closing each block of the
`bignum_inv_p25519` and `bignum_pow_p25519_p58` chains.  Each is a
direct application of one of the chain-step axioms / theorems from
`ChainStepAxioms.lean`.

## Status

This file is currently **stubbed**: each theorem is stated with the
target post-condition matching the canonical
`block{N}_correctness_via_axiom` from `ChainStepAxioms.lean`, but the
bodies are `sorry`s pending re-instantiation against the widened
chain-step signatures (frame condition on `chain_{sqr,mul}_step_correct`
landed 2026-05-09 in commit `3361273b`; address-derivation /
allocation / non-aliasing widening of
`chain_repeated_sqr_then_mul_correct` landed 2026-05-09 in this
commit).

The block-level correctness facts are still available through
`block{N}_correctness_via_axiom` directly (in `ChainStepAxioms.lean`)
and through `block{N}_correctness_triple` (in
`InvP25519Composition.lean`).  This file's only role was to act as a
short-form gateway, but the new signatures take many extra arguments
(address-derivation hypotheses, scratch bundles, body-shape
hypotheses) that defeat the original "one-line application" goal.

## The 13 blocks

The chain has 12 prefix blocks (shared between inv and pow_p58)
plus 1 protocol-specific tail block.

| Block | Pattern                          | Computes                              |
|-------|----------------------------------|---------------------------------------|
| 2     | sqr_step (1 squaring)            | z2 := ap²                             |
| 3     | repeated_sqr_then_mul n=2        | z9 := (z2²)² · ap                     |
| 4     | mul_step (1 multiply)            | z11 := z9 · z2                        |
| 5     | repeated_sqr_then_mul n=1        | z2_5_0 := z11² · z9                   |
| 6     | repeated_sqr_then_mul n=5        | z2_10_0 := z2_5_0^32 · z2_5_0         |
| 7     | repeated_sqr_then_mul n=10       | z2_20_0 := z2_10_0^1024 · z2_10_0     |
| 8     | repeated_sqr_then_mul n=20       | z2_40_0 := z2_20_0^(2^20) · z2_20_0   |
| 9     | repeated_sqr_then_mul n=10       | z2_50_0 := z2_40_0^1024 · z2_10_0     |
| 10    | repeated_sqr_then_mul n=50       | z2_100_0 := z2_50_0^(2^50) · z2_50_0  |
| 11    | repeated_sqr_then_mul n=100      | z2_200_0 := z2_100_0^(2^100) · z2_100_0 |
| 12    | repeated_sqr_then_mul n=50       | z2_250_0 := z2_200_0^(2^50) · z2_50_0 |
| 13a   | repeated_sqr_then_mul n=5 (inv)  | op := z2_250_0^32 · z11               |
| 13b   | repeated_sqr_then_mul n=2 (pow)  | op := z2_250_0^4 · ap                 |
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.PerBlockInstances

open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.BignumHoare.MontmulAxiom
open CatCrypt.Crypto.Jasmin.BignumHoare.ChainStepAxioms

/-! ## §6  Summary

The per-block instances in this file have been **deprecated** in
favour of `block{N}_correctness_via_axiom` (in `ChainStepAxioms.lean`,
which carries the frame condition + scratch bundle hypotheses
directly) and `block{N}_correctness_triple` (in
`InvP25519Composition.lean`, which lifts to `BignumTripleFuel` for
chain composition).

Use those entry points directly; this file is retained only for
import-graph stability.
-/

end CatCrypt.Crypto.Jasmin.BignumHoare.PerBlockInstances
