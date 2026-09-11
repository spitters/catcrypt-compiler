/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTConvolutionTheorem

/-!
# NTT-based polynomial multiply: the forward (analysis) half

This file assembles the previously-proved pieces into the precise statement that
*"the NTT computes polynomial multiplication via pointwise products"*, in its
**forward** form.

## The pipeline

An NTT-based multiply of two coefficient vectors `a, b : Fin n → R` runs:

1. **Forward NTT** both operands: `Â := dft m ω a`, `B̂ := dft m ω b`
   (`NTTRecursionPass.dft`, evaluation at the powers `ω⁰, …, ωᵐ⁻¹`).
2. **Pointwise product** in the evaluation (DFT) domain: `Ĉ k := Â k · B̂ k`.
3. **Inverse NTT** to recover the convolution coefficients (out of scope — see
   below).

`nttMultiply` packages step 2 (`fun k => dft a k * dft b k`). The content of this
file is the correctness of steps 1–2 together:

  **the pointwise product of the two forward transforms equals the forward
  transform of the convolution `conv a b`.**

Here the *forward transform of a coefficient list* `l` is its evaluation at the
twiddle powers, `fun k => eval l (ωᵏ)` (`NttTransform`) — multi-point evaluation,
which is exactly what `dft` computes on a `Fin n → R` vector
(`NTTConvolutionTheorem.dft_eq_listEval`). Phrasing the target through the *list*
transform is what makes the statement faithful: the convolution `conv a b` has up
to `2n − 1` coefficients, so it does **not** fit back into a length-`n` `Fin`
vector. The list transform carries all of them.

The forward-multiply correctness is then `NttTransform (conv (list a) (list b))`
equals the pointwise product of the two `dft`s — the convolution theorem in the
*"transform of convolution = pointwise product of transforms"* shape, forward
direction.

## Why no primitive-root hypothesis here

The forward direction is a pure algebraic identity: it rests only on the
evaluation homomorphism `eval (conv a b) x = eval a x * eval b x`
(`PolyConvGeneric.eval_conv`) and the index rewrite `ωʲᵏ = (ωᵏ)ʲ`. No relation on
`ω` is assumed. The transform is multi-point polynomial evaluation; pointwise
multiplication of evaluations is multiplication of the underlying polynomials,
hence evaluation of their convolution.

## Out of scope: the inverse (synthesis) half

Recovering the convolution *coefficients* from the pointwise products requires
**inverting** the transform — i.e. interpolation. That step needs `ω` to be a
primitive `n`-th root of unity (so the evaluation/Vandermonde map is invertible,
via root-of-unity orthogonality `∑ₖ ω^{(i−j)k} = n · [i = j]`). That hypothesis,
and the inverse NTT it underwrites, are deliberately **not** developed here; this
file is the forward/analysis half only.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NttMultiplyGeneric

open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTConvolutionTheorem
open CatCrypt.Crypto.Optimizer.Lattice.PolyConvGeneric

variable {R : Type*} [CommRing R]

/-! ## The pipeline pieces -/

/-- **Pointwise product in the DFT (evaluation) domain** — step 2 of an
NTT-based multiply. Given two length-`n` coefficient vectors `a, b`, multiply
their forward transforms index-by-index:

  `nttMultiply n ω a b k = (dft n ω a) k · (dft n ω b) k`.

The whole multiply is `inverseNTT (nttMultiply n ω a b)`; the inverse half is out
of scope, so this captures the forward computation an NTT-multiply performs. -/
def nttMultiply (n : ℕ) (ω : R) (a b : Fin n → R) (k : Fin n) : R :=
  dft n ω a k * dft n ω b k

/-- **The forward NTT of a coefficient list**, sampled at index `k`: evaluate the
list at the twiddle power `ωᵏ`,

  `NttTransform ω l k = eval l (ωᵏ)`.

This is the list-level transform — multi-point polynomial evaluation at the
powers of `ω`. On a length-`n` `Fin` vector it coincides with `dft`
(`NTTConvolutionTheorem.dft_eq_listEval`); we use the list form for the
convolution `conv a b`, whose `2n − 1` coefficients do not fit a length-`n`
vector. -/
def NttTransform (ω : R) (l : List R) (k : ℕ) : R :=
  PolyConvGeneric.eval l (ω ^ k)

/-- The length-`n` coefficient list of a `Fin n → R` vector, low-index first:
`list z = [z 0, z 1, …, z (n−1)]`. This is the list an NTT-multiply transforms;
`NttTransform ω (coeffList n z) = dft n ω z` (see `dft_eq_NttTransform`). -/
def coeffList (n : ℕ) (z : Fin n → R) : List R :=
  (List.range n).map (fun i => if h : i < n then z ⟨i, h⟩ else 0)

/-! ## The forward transform on a `Fin` vector is `dft` -/

/-- The list-level forward transform of a vector's coefficient list agrees with
`dft`: `NttTransform ω (coeffList n z) k.val = dft n ω z k`. So `dft` *is* the
forward NTT, read through the list interface. This is exactly
`NTTConvolutionTheorem.dft_eq_listEval`. -/
theorem dft_eq_NttTransform (n : ℕ) (ω : R) (z : Fin n → R) (k : Fin n) :
    dft n ω z k = NttTransform ω (coeffList n z) k.val := by
  rw [NttTransform, coeffList, dft_eq_listEval]

/-! ## Forward NTT-multiply correctness -/

/-- **NTT-multiply correctness (forward half).** The pointwise product of the two
forward transforms equals the forward transform of the convolution of the
operands' coefficient lists:

  `nttMultiply n ω a b k = NttTransform ω (conv (coeffList a) (coeffList b)) k`,

at every `k`. In words: **the transform of the convolution is the pointwise
product of the transforms** — the convolution theorem, forward direction. This is
the precise sense in which an NTT computes polynomial multiplication: multiply
pointwise in the DFT domain, and you have computed the forward transform of the
convolution. The convolution list carries all `2n − 1` coefficients, so nothing
is truncated.

The inverse (recovering `conv`'s coefficients by interpolation) needs `ω` a
primitive `n`-th root of unity and is out of scope. -/
theorem nttMultiply_eq_transform_conv (n : ℕ) (ω : R) (a b : Fin n → R)
    (k : Fin n) :
    nttMultiply n ω a b k
      = NttTransform ω
          (PolyConvGeneric.conv (coeffList n a) (coeffList n b)) k.val := by
  rw [nttMultiply, NttTransform, coeffList, coeffList, dft_mul_eq_conv]

/-- **NTT-multiply spec in function form.** The full forward statement as an
equality of functions `Fin n → R`: the pointwise-product map equals the
forward-transform-of-convolution map. This is the `nttMultiply_spec` shape — the
pointwise product of the two forward transforms *is* the forward transform of the
convolution. -/
theorem nttMultiply_spec (n : ℕ) (ω : R) (a b : Fin n → R) :
    nttMultiply n ω a b
      = fun k =>
          NttTransform ω
            (PolyConvGeneric.conv (coeffList n a) (coeffList n b)) k.val := by
  funext k
  exact nttMultiply_eq_transform_conv n ω a b k

/-! ## Worked example -/

/-- Worked example over `ℤ`, `n = 2`, with the operand `a = b = (1, 1)`
(the coefficient list `[1, 1]`, encoding `1 + X`). The pointwise product of the
two forward transforms, at any twiddle `ω` and any index `k`, equals the forward
transform of `conv [1,1] [1,1]`, which encodes `(1 + X)² = 1 + 2X + X²`.

Concretely, at `ω` and `k = 0` (`ω⁰ = 1`): both sides equal
`eval [1,1] 1 · eval [1,1] 1 = 2 · 2 = 4 = eval [1,2,1] 1`. -/
example (ω : ℤ) (k : Fin 2) :
    nttMultiply 2 ω (fun _ => (1 : ℤ)) (fun _ => (1 : ℤ)) k
      = NttTransform ω
          (PolyConvGeneric.conv
            (coeffList 2 (fun _ => (1 : ℤ)))
            (coeffList 2 (fun _ => (1 : ℤ)))) k.val :=
  nttMultiply_eq_transform_conv 2 ω _ _ k

/-- The convolution in the worked example really is `1 + 2X + X²`: at every point
`x`, `eval (conv [1,1] [1,1]) x = eval [1,2,1] x`. (The transform then samples
this at `x = ωᵏ`.) -/
example (x : ℤ) :
    PolyConvGeneric.eval
        (PolyConvGeneric.conv ([1, 1] : List ℤ) [1, 1]) x
      = PolyConvGeneric.eval ([1, 2, 1] : List ℤ) x := by
  rw [PolyConvGeneric.eval_conv, PolyConvGeneric.eval_pair,
    PolyConvGeneric.eval_triple]
  ring

end CatCrypt.Crypto.Optimizer.Lattice.NttMultiplyGeneric
