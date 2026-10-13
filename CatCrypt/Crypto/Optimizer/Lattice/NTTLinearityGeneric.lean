/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass

/-!
# `R`-linearity of the generic discrete / number-theoretic transform

The forward transform `dft n ω x k = Σⱼ xⱼ ωʲᵏ` (from `NTTRecursionPass`) is
`R`-linear in its input vector `x`, **unconditionally** — over any commutative
ring `R`, with no root-of-unity or primitivity hypothesis on the twiddle `ω`.
Linearity is the assumption-free direction: it is pure distributivity of the
summand `xⱼ ωʲᵏ` over addition and scalar multiplication of the `xⱼ`, so a
`CommRing` suffices (inversion, by contrast, needs `ω` primitive and `n`
invertible).

## Optimizer soundness certificates

These laws are the rewrite certificates that let a generic optimizer **fuse a
linear pre- or post-operation through an NTT stage**:

* `dft_add` — a residual add before the transform commutes with splitting the
  transform across the two summands (`NTT(x + y) = NTT(x) + NTT(y)`). An
  optimizer may hoist/lower an elementwise addition across the stage.
* `dft_smul` — a scalar prescaling before the transform commutes with scaling
  the output (`NTT(c · x) = c · NTT(x)`). An optimizer may move a constant
  multiply to whichever side of the stage is cheaper.
* `dft_linear` — the combined affine-combination law, the general statement an
  optimizer pattern-match can target directly.

All three are `Finset.sum` distributivity identities, so the proofs are one
`simp` line each.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTLinearityGeneric

open Finset
open CatCrypt.Crypto.Lattice.NTTRecursionPass

variable {R : Type*} [CommRing R]

/-- **Additivity certificate.** The forward transform splits over a pointwise
sum of inputs: `dft n ω (x + y) k = dft n ω x k + dft n ω y k`. An optimizer may
push a residual elementwise add through an NTT stage. Needs no hypothesis on
`ω`. -/
theorem dft_add (n : ℕ) (ω : R) (x y : Fin n → R) (k : Fin n) :
    dft n ω (fun i => x i + y i) k = dft n ω x k + dft n ω y k := by
  simp only [dft, add_mul, Finset.sum_add_distrib]

/-- **Scalar-homogeneity certificate.** Prescaling the input by `c` scales the
output by `c`: `dft n ω (c · x) k = c · dft n ω x k`. An optimizer may move a
constant multiply to whichever side of an NTT stage is cheaper. Needs no
hypothesis on `ω`. -/
theorem dft_smul (n : ℕ) (ω : R) (c : R) (x : Fin n → R) (k : Fin n) :
    dft n ω (fun i => c * x i) k = c * dft n ω x k := by
  simp only [dft, Finset.mul_sum, mul_assoc]

/-- **Combined linearity certificate.** The forward transform sends an affine
combination of inputs to the affine combination of outputs:
`dft n ω (a · x + b · y) k = a · dft n ω x k + b · dft n ω y k`. This is the
general `R`-linearity law an optimizer's pattern-match can target directly;
it follows from `dft_add` and `dft_smul`. Needs no hypothesis on `ω`. -/
theorem dft_linear (n : ℕ) (ω : R) (a b : R) (x y : Fin n → R) (k : Fin n) :
    dft n ω (fun i => a * x i + b * y i) k
      = a * dft n ω x k + b * dft n ω y k := by
  rw [dft_add n ω (fun i => a * x i) (fun i => b * y i) k,
    dft_smul n ω a x k, dft_smul n ω b y k]

end CatCrypt.Crypto.Optimizer.Lattice.NTTLinearityGeneric
