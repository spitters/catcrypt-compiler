/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots
import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances

/-!
# Concrete emit → realization for the ML-KEM NTT-multiply kernel

This file instantiates the generic NTT-multiply emit → value seam
(`GenericNttEmitValue`) at the **concrete** lattice-crypto primitive root, so the
residual collapses to a single concrete leaf-bytes KAT (`NttKernelRealizes` at
the actual parameters).

Everything above the KAT is a Lean theorem:

* the structural-emit ↔ operational-denotation thread (`emitNttMul_realizes_value`),
* the commuting-square discharge `nttEmitRealizes_of_cyclicConv` — that
  transform·pointwise·inverse equals the cyclic convolution — supplied at the
  ML-KEM parameters by the **proven** primitive-root fact `isPrimitiveRoot_17_256`
  together with `n_ne_zero_3329`.

What remains to trust is exactly the concrete `NttKernelRealizes 256 decode
"ntt_poly_mul_3329_256" leafSpec` hypothesis: that the emitted kernel's leaf-call
bytes decode to the length-`256` cyclic convolution. That is the leaf-bytes KAT.

## Leaf name

The compiler pass `NTTPolyMul.nttPolyMul q n` rewrites every poly-mul call to
`RCall (nttPolyMulName q n)` where `nttPolyMulName q n = s!"ntt_poly_mul_{q}_{n}"`.
For ML-KEM (`nttPolyMulMlkem = nttPolyMul 3329 256`) the leaf string is therefore
`"ntt_poly_mul_3329_256"`; this is the `leaf` literal used below.

## ML-DSA: why the cyclic discharge does not match the compiler leaf

The compiler's ML-DSA pass is `nttPolyMulMldsa = nttPolyMul 8380417 256`, so its
leaf string is `"ntt_poly_mul_8380417_256"` — at degree `n = 256`. But ML-DSA
operates in the **negacyclic** ring `Z_8380417[X]/(X²⁵⁶+1)`; the genuine ML-DSA
NTT operation is the *negacyclic* convolution (`ConcreteNttInstances.mldsa_ndft_negaConv`,
twist root `ψ = 1753`), not the cyclic `X²⁵⁶−1` convolution. The generic seam in
`GenericNttEmitValue` exposes only a **cyclic** emit-realization
(`NttKernelRealizes` is `cyclicConv n …`, and `nttEmitRealizes_of_cyclicConv` is
the cyclic discharge). There is no negacyclic emit-realization seam yet. So the
cyclic discharge would be the *wrong* value content for the compiler's
`ntt_poly_mul_8380417_256` leaf — forcing it would be a semantic mismatch, not a
discharge.

For completeness we record the two ML-DSA *cyclic* realizations that **are**
genuine instantiations of the generic seam — at parameters where a primitive
root of the right order exists:

* `mldsa_cyclic_nttEmitRealizes_of_kernel` at `n = 512`, `ω = 1753` (a real
  primitive `512`-th root, `isPrimitiveRoot_1753_512`). This matches a
  hypothetical `"ntt_poly_mul_8380417_512"` leaf, which the current compiler
  pass does **not** emit.
* `mldsa_cyclic256_nttEmitRealizes_of_kernel` at `n = 256`, `ω = 1753²` (a real
  primitive `256`-th root, `isPrimitiveRoot_1753sq_256`). This is the cyclic
  `X²⁵⁶−1` statement at the ML-DSA modulus; it is *not* the negacyclic operation
  the `"ntt_poly_mul_8380417_256"` leaf computes, so the leaf string is left
  abstract (it is a genuine cyclic emit-realization, but not the compiler's
  ML-DSA leaf).

The honest end-to-end deliverable of this file is therefore the ML-KEM theorem
`mlkem_nttEmitRealizes_of_kernel`. Closing the ML-DSA compiler leaf requires a
*negacyclic* emit-realization seam (a future addition).

## References
* NIST FIPS 203 (ML-KEM), FIPS 204 (ML-DSA)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteNttEmitRealization

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.GenericNttEmitValue
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances

/-! ## §1  ML-KEM (`ZMod 3329`, `n = 256`, `ω = 17`) — the end-to-end deliverable

The ML-KEM ring is `Z_3329[X]/(X²⁵⁶+1)`, but `3329 − 1 = 2⁸·13` has no order-`512`
element, so ML-KEM uses an incomplete NTT whose `256`-th-root value content is the
**cyclic** convolution (see `ConcreteNttInstances`). That is precisely what the
generic cyclic seam discharges. -/

/-- **ML-KEM NTT-multiply emit → value, reduced to the concrete leaf-bytes KAT.**

    From the concrete kernel-realization residual
    `NttKernelRealizes 256 decode "ntt_poly_mul_3329_256" leafSpec` (the emitted
    leaf decodes to the length-`256` cyclic convolution — the leaf-bytes KAT),
    conclude the full NTT-multiply realization
    `NttEmitRealizes 256 17 decode "ntt_poly_mul_3329_256" leafSpec` (the leaf
    decodes to `nttMul 256 17 …`, the transform·pointwise·inverse value).

    The transform·pointwise·inverse = cyclic convolution content is supplied by
    the proven `isPrimitiveRoot_17_256` and `n_ne_zero_3329` via the commuting
    square `nttEmitRealizes_of_cyclicConv`; the only residual is `hker`. -/
theorem mlkem_nttEmitRealizes_of_kernel
    (decode : RustVal .TFp → (Fin 256 → ZMod 3329)) (leafSpec : LeafSpec)
    (hker : NttKernelRealizes 256 decode "ntt_poly_mul_3329_256" leafSpec) :
    NttEmitRealizes 256 (17 : ZMod 3329) decode "ntt_poly_mul_3329_256" leafSpec :=
  nttEmitRealizes_of_cyclicConv decode "ntt_poly_mul_3329_256" leafSpec
    isPrimitiveRoot_17_256 n_ne_zero_3329 hker

/-- **Non-vacuity for the ML-KEM residual.**  A concrete `LeafSpec` built from a
    `cyclicConv`-returning realizer (with a decoder section `encode`) satisfies
    `mlkem_nttEmitRealizes_of_kernel`'s hypothesis — so the localized KAT is
    satisfiable, not an unsatisfiable over-constraint.  The genuine cross-prover
    gap is between this canonical realizer and the emitted ML-KEM kernel's real
    byte semantics. -/
theorem mlkem_nttKernelRealizes_canonical
    (decode : RustVal .TFp → (Fin 256 → ZMod 3329))
    (encode : (Fin 256 → ZMod 3329) → RustVal .TFp)
    (hsection : ∀ p : Fin 256 → ZMod 3329, decode (encode p) = p)
    (limbStore : LimbStoreSpec) :
    NttKernelRealizes 256 decode "ntt_poly_mul_3329_256"
      { call := nttKernelCallSpec decode encode "ntt_poly_mul_3329_256"
      , limbStore := limbStore } :=
  nttKernelRealizes_canonical decode encode hsection "ntt_poly_mul_3329_256" limbStore

/-- **ML-KEM emit-realization is inhabited.**  Composing the canonical kernel
    realizer with the §1 deliverable: the canonical `LeafSpec` satisfies the full
    ML-KEM NTT-multiply realization `NttEmitRealizes 256 17 …`. -/
theorem mlkem_nttEmitRealizes_canonical
    (decode : RustVal .TFp → (Fin 256 → ZMod 3329))
    (encode : (Fin 256 → ZMod 3329) → RustVal .TFp)
    (hsection : ∀ p : Fin 256 → ZMod 3329, decode (encode p) = p)
    (limbStore : LimbStoreSpec) :
    NttEmitRealizes 256 (17 : ZMod 3329) decode "ntt_poly_mul_3329_256"
      { call := nttKernelCallSpec decode encode "ntt_poly_mul_3329_256"
      , limbStore := limbStore } :=
  mlkem_nttEmitRealizes_of_kernel decode _
    (mlkem_nttKernelRealizes_canonical decode encode hsection limbStore)

/-! ## §2  ML-DSA cyclic realizations (genuine seam instantiations, NOT the
compiler's negacyclic `ntt_poly_mul_8380417_256` leaf)

See the module docstring: the compiler's ML-DSA leaf is negacyclic at `n = 256`,
while the generic seam is cyclic. We record the two parameter points where a
primitive root of the matching order exists, so the cyclic discharge is genuine —
but neither matches the compiler's `ntt_poly_mul_8380417_256` leaf semantics. The
leaf strings are kept as generic parameters (not the compiler literal). -/

/-- **ML-DSA cyclic NTT-multiply at `n = 512`** (real primitive `512`-th root
    `ω = 1753`).  This is a genuine instantiation of the generic cyclic seam; it
    would match a hypothetical `"ntt_poly_mul_8380417_512"` leaf, which the
    current compiler pass does **not** emit (it emits `…_8380417_256`). -/
theorem mldsa_cyclic_nttEmitRealizes_of_kernel
    (decode : RustVal .TFp → (Fin 512 → ZMod 8380417))
    (leaf : String) (leafSpec : LeafSpec)
    (hker : NttKernelRealizes 512 decode leaf leafSpec) :
    NttEmitRealizes 512 (1753 : ZMod 8380417) decode leaf leafSpec :=
  nttEmitRealizes_of_cyclicConv decode leaf leafSpec
    isPrimitiveRoot_1753_512 (by decide) hker

/-- **ML-DSA cyclic NTT-multiply at `n = 256`** (real primitive `256`-th root
    `ω = 1753²`).  This is the **cyclic** `X²⁵⁶−1` statement at the ML-DSA modulus;
    it is *not* the negacyclic `Z_8380417[X]/(X²⁵⁶+1)` operation that the
    compiler's `"ntt_poly_mul_8380417_256"` leaf computes, so the leaf string is
    left as a generic parameter rather than that compiler literal. -/
theorem mldsa_cyclic256_nttEmitRealizes_of_kernel
    (decode : RustVal .TFp → (Fin 256 → ZMod 8380417))
    (leaf : String) (leafSpec : LeafSpec)
    (hker : NttKernelRealizes 256 decode leaf leafSpec) :
    NttEmitRealizes 256 ((1753 : ZMod 8380417) ^ 2) decode leaf leafSpec :=
  nttEmitRealizes_of_cyclicConv decode leaf leafSpec
    isPrimitiveRoot_1753sq_256 n_ne_zero_8380417 hker

end CatCrypt.Crypto.SecureCompilation.ConcreteNttEmitRealization
