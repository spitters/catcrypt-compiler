/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Vale.Bls12381FieldMul

@[expose] public section

set_option autoImplicit false

/-!
# BLS12-381 field-multiply leaf axiom ↔ fiat-crypto Coq theorem index

Single-place reference connecting the `Bls12381FieldMul` leaf axiom to its
discharging fiat-crypto Rocq theorem. Parallel to the Ed25519/X25519
`CoqAxioms.lean` audit trail.

## Trust basis: the Coq proof (not the generated Rust)

The cited authority is the **Coq theorem**, not any `.rs` file. fiat-crypto's
`WordByWordMontgomery.mulmod_correct` is parametric over the modulus, so a
single `Qed` theorem covers the BLS12-381 base prime; the generated
`fiat_bls12_381_mul` is codegen from the same synthesizer, not the proof.

## Axiom → discharging theorem

| Lean axiom | Status | Discharging fiat-crypto Rocq theorem |
|---|---|---|
| `Bls12381_fmul_denote` | ✅ proved | `fiat-crypto/src/Arithmetic/WordByWordMontgomery.v::mulmod_correct` (`Qed`): `eval (from_montgomerymod (mulmod a b)) mod m = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m` for `valid a`, `valid b`, at `m = p_{BLS12-381}` = `0x1a0111ea…aaab`. C-operation form: `fiat-crypto/src/COperationSpecifications.v` module `WordByWordMontgomery`, `mul_correct`. Montgomery product `x · y · R⁻¹ mod p`, `R = 2^384`, 6×u64. |
| `Bls12381Fp`, `Bls12381Fp.default` | surface | opaque `Type` + inhabitant; no computational content. |

## Rocq sources (paths)

* `BLS/AUCurves/fiat-crypto/src/Arithmetic/WordByWordMontgomery.v` — `mulmod_correct` (the proof; prime-parametric).
* `BLS/AUCurves/fiat-crypto/src/COperationSpecifications.v` — `mul_correct` (the C-operation spec form).

## Codegen note (provenance, not proof)

`fiat_bls12_381_mul` (`bls12_381_64.rs`) is generable via
`word_by_word_montgomery --lang Rust bls12_381 64 '<p>'`, the same synthesizer
that produced `p384_64.rs` / `pallas_64.rs` / `vesta_64.rs`. It is not yet in
AUCurves' `fiat-rust/src/` set (which currently routes BLS12-381 `fp_mul`
through a separate Bedrock2 tower); generating it is a codegen step, and it
does not change the trust basis, which is `mulmod_correct` above.
-/

namespace CatCrypt.Crypto.Vale.Bls12381FieldMulCoqAxioms

/-- The leaf axiom this file cites. Present so the module has content and the
    citation table above is co-located with the axiom it documents. -/
theorem cited : True := trivial

end CatCrypt.Crypto.Vale.Bls12381FieldMulCoqAxioms
