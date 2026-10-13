/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
public import CatCrypt.Crypto.Optimizer.Lattice.NegacyclicTransformGeneric

/-!
# Negacyclic NTT-multiply correctness

The cyclic NTT-multiply pipeline (`NTTMultiplyCorrectGeneric.nttMul`,
transform·pointwise·inverse) provably computes the cyclic convolution
(`nttMul_eq_cyclicConv'`). The **negacyclic** multiplier — the operation ML-DSA's
`Z_q[X]/(Xⁿ+1)` NTT actually performs — is the same pipeline conjugated by the
`ψ`-twist: pre-twist both operands, run the cyclic multiply at `ω = ψ²`, then
untwist. This file shows that pipeline computes the negacyclic convolution
(`NegacyclicTransformGeneric.negaConv`), which is the commuting-square content a
*negacyclic* emit→realization seam needs (the cyclic seam in `GenericNttEmitValue`
does not fit a negacyclic leaf).

The proof is immediate from the construction: `negaConv` is *defined* as
`untwist ∘ cyclicConv ∘ twist`, and `nttMul (ψ²) (twist x) (twist y)` collapses to
`cyclicConv (twist x) (twist y)` by the proven `nttMul_eq_cyclicConv'`. So the
negacyclic pipeline equals `negaConv` with no new mathematical content beyond the
cyclic theorem and the twist construction.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NegacyclicMultiplyCorrect

open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Lattice.NegacyclicTransformGeneric

variable {R : Type*} [Field R] {ψ : R} {n : ℕ} [NeZero n]

/-- **The negacyclic NTT-multiply pipeline.** Pre-twist both operands by `ψ`, run
the cyclic NTT-multiply at the inner root `ω = ψ²`, then untwist:

  `nttNegaMul ψ x y = untwist ψ (nttMul n (ψ²) (twist ψ x) (twist ψ y))`.

This is the operation a negacyclic (`Xⁿ+1`) NTT multiplier performs. -/
noncomputable def nttNegaMul (ψ : R) (x y : Fin n → R) : Fin n → R :=
  untwist ψ (nttMul n (ψ ^ 2) (twist ψ x) (twist ψ y))

/-- **Negacyclic NTT-multiply correctness.** The negacyclic pipeline computes the
negacyclic convolution:

  `nttNegaMul ψ x y = negaConv ψ x y`.

Immediate: `nttMul_eq_cyclicConv'` (at the primitive `n`-th root `ω = ψ²`)
rewrites the inner cyclic multiply to `cyclicConv (twist ψ x) (twist ψ y)`, and
`negaConv` is definitionally `untwist ψ` of exactly that. This is the negacyclic
analogue of `nttMul_eq_cyclicConv'` — the commuting-square content for a
negacyclic emit→realization seam. -/
theorem nttNegaMul_eq_negaConv (hω : IsPrimitiveRoot (ψ ^ 2) n)
    (hn : (n : R) ≠ 0) (x y : Fin n → R) :
    nttNegaMul ψ x y = negaConv ψ x y := by
  unfold nttNegaMul negaConv
  rw [nttMul_eq_cyclicConv' hω hn]

end CatCrypt.Crypto.Optimizer.Lattice.NegacyclicMultiplyCorrect
