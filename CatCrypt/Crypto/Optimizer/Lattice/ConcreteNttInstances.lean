/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import Mathlib.Algebra.Field.ZMod

public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots
public import CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
public import CatCrypt.Crypto.Optimizer.Lattice.NegacyclicTransformGeneric

/-!
# Concrete NTT-multiply correctness at the ML-KEM and ML-DSA parameters

This file instantiates the generic NTT-multiply correctness theorems
(`NTTMultiplyCorrectGeneric.nttMul_eq_cyclicConv'`, the unconditional
transform·pointwise·inverse = cyclic convolution; and
`NegacyclicTransformGeneric.ndft_negaConv`, the twisted-transform diagonalization
of negacyclic convolution) at the actual lattice-crypto parameters, using the
concrete primitive roots from `ConcreteNttRoots`.

## ML-KEM is cyclic here, not negacyclic — and why

ML-KEM operates in `Z_3329[X]/(X²⁵⁶+1)` — a **negacyclic** ring. A *full*
negacyclic transform needs a primitive `512`-th root of unity (the twist root
`ψ` with `ψ² = ζ₂₅₆`). But `3329 − 1 = 2⁸·13`, so the multiplicative group has
order `3328 = 2⁸·13`, whose `2`-part is only `2⁸ = 256`: **there is no element of
order `512` in `ZMod 3329`**. Hence ML-KEM has no primitive `512`-th root and uses
an *incomplete* NTT (splitting only down to degree-2 factors). The `256`-th root
`17` we do have gives the **cyclic** (`X²⁵⁶−1`) convolution statement below; the
negacyclic identity is genuinely **not** instantiable at the ML-KEM modulus.

ML-DSA operates in `Z_8380417[X]/(X²⁵⁶+1)` and `8380417 − 1 = 2¹³·…` **does** have
an order-`512` element (`ζ = 1753`), so ML-DSA gets the genuine **negacyclic**
diagonalization (`mldsa_ndft_negaConv`) — the real ML-DSA NTT operation — as well
as the cyclic statement at `n = 512`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances

open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Optimizer.Lattice.NegacyclicTransformGeneric
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots

/-! ## ML-KEM (`ZMod 3329`, `n = 256`, `ω = 17`) — the cyclic statement -/

/-- **ML-KEM NTT-multiply = cyclic convolution.** The transform·pointwise·inverse
pipeline at the ML-KEM parameters (`ZMod 3329`, `n = 256`, root `17`) computes the
length-`256` cyclic convolution. (See the module docstring: this is the cyclic —
not the negacyclic — statement, because `ZMod 3329` has no primitive `512`-th
root.) A pure instantiation of `nttMul_eq_cyclicConv'` at `isPrimitiveRoot_17_256`
and `n_ne_zero_3329`. -/
theorem mlkem_nttMul_eq_cyclicConv (x y : Fin 256 → ZMod 3329) :
    nttMul 256 (17 : ZMod 3329) x y = cyclicConv 256 x y :=
  nttMul_eq_cyclicConv' isPrimitiveRoot_17_256 n_ne_zero_3329 x y

/-! ## ML-DSA (`ZMod 8380417`) — the genuine negacyclic operation -/

/-- The twist root `ψ = 1753` has order `512`, so `ψ² = 1753²` is a primitive
`256`-th root — the `ω` of the negacyclic transform. Derived from
`isPrimitiveRoot_1753_512` via `IsPrimitiveRoot.pow` (`512 = 2 · 256`). -/
theorem isPrimitiveRoot_1753sq_256 :
    IsPrimitiveRoot ((1753 : ZMod 8380417) ^ 2) 256 :=
  isPrimitiveRoot_1753_512.pow (by norm_num) (by norm_num)

/-- **ML-DSA negacyclic NTT-multiply.** The twisted transform `ndft` (with twist
root `ψ = 1753`) diagonalizes the negacyclic convolution at the ML-DSA parameters
(`ZMod 8380417`, `n = 256`): `ndft ψ (negaConv ψ x y) = ndft ψ x · ndft ψ y`. This
is the genuine ML-DSA `Z_8380417[X]/(X²⁵⁶+1)` operation. A pure instantiation of
`ndft_negaConv` at `isPrimitiveRoot_1753sq_256`. -/
theorem mldsa_ndft_negaConv (x y : Fin 256 → ZMod 8380417) (k : Fin 256) :
    ndft (1753 : ZMod 8380417) (negaConv (1753 : ZMod 8380417) x y) k
      = ndft (1753 : ZMod 8380417) x k * ndft (1753 : ZMod 8380417) y k :=
  ndft_negaConv isPrimitiveRoot_1753sq_256 (by decide) x y k

/-- **ML-DSA cyclic statement at `n = 512`.** With the full `512`-th root `1753`,
the length-`512` transform·pointwise·inverse pipeline computes the cyclic
convolution. Instantiation of `nttMul_eq_cyclicConv'` at `isPrimitiveRoot_1753_512`. -/
theorem mldsa_nttMul_eq_cyclicConv (x y : Fin 512 → ZMod 8380417) :
    nttMul 512 (1753 : ZMod 8380417) x y = cyclicConv 512 x y :=
  nttMul_eq_cyclicConv' isPrimitiveRoot_1753_512 (by decide) x y

end CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances
