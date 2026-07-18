/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Lattice.NTTFullInversionGeneric
import CatCrypt.Crypto.Optimizer.Lattice.NTTConvolutionTheorem
import CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric

/-!
# NTT-multiply correctness: transform, pointwise-multiply, inverse-transform

This file closes the NTT-multiply round trip. The forward half
(`NTTConvolutionTheorem` / `NttMultiplyGeneric`) shows the pointwise product of
two forward transforms equals the forward transform of the convolution; the
inversion keystone (`NTTFullInversionGeneric.idft_dft`) shows the synthesis map
`idft` is a left inverse of `dft`. Composing them:

  `nttMul n ω x y := idft n ω (fun k => dft n ω x k · dft n ω y k)`

— forward-transform both operands, multiply pointwise in the evaluation (DFT)
domain, then inverse-transform — recovers the **cyclic convolution** of `x` and
`y`, the length-`n` vector `c` whose forward transform is exactly that pointwise
product.

## What is proved here

* `nttMul` — the full multiply pipeline (analysis · pointwise-mul · synthesis).
* `dft_nttMul` — applying `dft` back to `nttMul` recovers the pointwise product
  (right-inverse round trip), using the forward bridge and `idft`'s left-inverse
  property packaged as `nttMul_dft`.
* `nttMul_dft` — the clean specialisation: when the pointwise product *is* the
  transform of a length-`n` vector `c` (the cyclic-convolution hypothesis
  `hc`), `nttMul` returns exactly `c`. This is the correctness statement,
  reducing to `idft_dft` once the cyclic-convolution premise identifies the
  recovered coefficients.

The cyclic-convolution premise `hc : (fun k => dft n ω x k * dft n ω y k)
= dft n ω c` is the length-`n` (mod `Xⁿ − 1`) shape that the *invertible* DFT
recovers; the acyclic `PolyConvGeneric.conv` (up to `2n − 1` coefficients,
carried by the forward `NttTransform`) does not fit a length-`n` `Fin` vector
and so is not the object `idft` inverts. Stating correctness against the
length-`n` cyclic convolution `c` is what composes cleanly with `idft_dft`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric

open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTFullInversionGeneric
open CatCrypt.Crypto.Optimizer.Lattice.NTTConvolutionTheorem
open CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric

variable {R : Type*} [Field R]

/-- **The NTT-multiply pipeline.** Forward-transform both operands
(`dft n ω x`, `dft n ω y`), multiply pointwise in the evaluation (DFT) domain,
and inverse-transform the result:

  `nttMul n ω x y = idft n ω (fun k => dft n ω x k · dft n ω y k)`. -/
noncomputable def nttMul (n : ℕ) (ω : R) (x y : Fin n → R) : Fin n → R :=
  idft n ω (fun k => dft n ω x k * dft n ω y k)

/-- **NTT-multiply correctness.** If the pointwise product of the two forward
transforms is the forward transform of a length-`n` vector `c` (the *cyclic
convolution* of `x` and `y`, the length-`n` representative the invertible DFT
recovers), then the full pipeline returns exactly `c`:

  `nttMul n ω x y = c`.

The proof rewrites the inner pointwise-product function by `hc` to `dft n ω c`,
then `idft_dft hω hn c` collapses `idft (dft c) = c`. This is the precise sense
in which an NTT-based multiply is correct: transform, pointwise-multiply,
inverse-transform recovers the convolution. The hypothesis `hc` packages the
forward convolution theorem (pointwise product of transforms = transform of the
convolution) at the length-`n` cyclic representative `c`; `idft` then inverts. -/
theorem nttMul_eq_cyclicConv {ω : R} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    (hn : (n : R) ≠ 0) (x y c : Fin n → R)
    (hc : (fun k => dft n ω x k * dft n ω y k) = dft n ω c) :
    nttMul n ω x y = c := by
  rw [nttMul, hc, idft_dft hω hn]

/-- **Round-trip (right inverse).** Forward-transforming the multiply pipeline's
output recovers the original pointwise product, provided that product is the
transform of a length-`n` vector `c` (cyclic-convolution hypothesis `hc`):

  `dft n ω (nttMul n ω x y) = fun k => dft n ω x k · dft n ω y k`.

Immediate from `nttMul_eq_cyclicConv` (`nttMul` returns `c`) and `hc`
(`dft c` is the pointwise product). -/
theorem dft_nttMul {ω : R} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    (hn : (n : R) ≠ 0) (x y c : Fin n → R)
    (hc : (fun k => dft n ω x k * dft n ω y k) = dft n ω c) :
    dft n ω (nttMul n ω x y) = fun k => dft n ω x k * dft n ω y k := by
  rw [nttMul_eq_cyclicConv hω hn x y c hc, hc]

/-- **NTT-multiply correctness, UNCONDITIONAL.** The pipeline computes the
length-`n` cyclic convolution outright — no premise:

  `nttMul n ω x y = cyclicConv n x y`.

The cyclic-convolution hypothesis `hc` of `nttMul_eq_cyclicConv` is *discharged*
here by the cyclic convolution theorem `dft_cyclicConv` (the DFT diagonalizes
cyclic convolution: `dft (cyclicConv x y) k = dft x k · dft y k`), so taking
`c := cyclicConv n x y` the premise becomes `dft_cyclicConv`'s statement read
backwards. This is the end-to-end statement that an NTT-based multiplier — analyze
both operands, multiply pointwise in the evaluation domain, synthesize — computes
exactly the cyclic convolution, for any primitive `n`-th root `ω` over a field. -/
theorem nttMul_eq_cyclicConv' {ω : R} {n : ℕ} [NeZero n]
    (hω : IsPrimitiveRoot ω n) (hn : (n : R) ≠ 0) (x y : Fin n → R) :
    nttMul n ω x y = cyclicConv n x y := by
  refine nttMul_eq_cyclicConv hω hn x y (cyclicConv n x y) ?_
  funext k
  exact (dft_cyclicConv hω x y k).symm

end CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
