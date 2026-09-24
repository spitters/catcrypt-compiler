/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
public import CatCrypt.Crypto.Optimizer.Lattice.PolyConvGeneric

/-!
# The NTT is multi-point polynomial evaluation at the powers of `ω`

This file is the bridge between the two halves of the NTT-multiply story:

* `NTTRecursionPass.dft` — the definitional length-`n` discrete /
  number-theoretic transform `Xₖ = Σⱼ xⱼ ωʲᵏ`, whose radix-2 butterfly recursion
  is proved generically in `NTTRecursionPass`;
* `PolyConvGeneric.eval` / `PolyConvGeneric.conv` — the polynomial-multiply spec
  (`eval (conv a b) x = eval a x * eval b x`), the convolution theorem's
  algebraic foundation.

## The bridge

`dft_eq_polyEval` says the `k`-th DFT output is the polynomial *with coefficients
`x`* evaluated at the single point `ωᵏ`:

  `dft n ω x k = Σⱼ xⱼ · (ωᵏ)ʲ`.

That is, the DFT is **multi-point polynomial evaluation at the powers of the
twiddle `ω`**. Read across all `k`, the transform `x ↦ (Xₖ)ₖ` is exactly
"evaluate the coefficient polynomial at `ω⁰, ω¹, …, ωⁿ⁻¹`". This needs no
relation on `ω`: it is the single rewrite `ωʲᵏ = (ωᵏ)ʲ` (`pow_mul` after
`mul_comm`).

Composing with `PolyConvGeneric.eval` (a list-indexed evaluation) is just a
reindexing: `dft_eq_listEval` rephrases `dft n ω x k` as the polynomial eval of
the coefficient *list* `(List.range n).map x'` at `ωᵏ`.

## The convolution theorem (the heart of NTT-multiply)

With the bridge in hand, the convolution theorem is a one-line consequence of the
`PolyConvGeneric.eval_conv` theorem: the pointwise product of two DFTs is the DFT
of the cyclic / acyclic convolution at each evaluation point. `dft_mul_eq_conv`
states the per-point form

  `dft a x k · dft a y k = (evaluation of conv at ωᵏ)`,

which is the statement an NTT-based multiply realizes — multiply pointwise in the
evaluation (DFT) domain, then interpolate back. No primitive-root hypothesis is
needed for *this* (forward) direction; the primitive-root / orthogonality
hypothesis is only needed for the *inverse* transform (interpolation), which is
out of scope here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTConvolutionTheorem

open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.PolyConvGeneric
open Finset

variable {R : Type*} [CommRing R]

/-! ## The bridge: DFT = polynomial evaluation at `ωᵏ` -/

/-- **DFT as multi-point polynomial evaluation.** The `k`-th output of the
length-`n` DFT is the polynomial with coefficients `x` evaluated at the single
point `ωᵏ`:

  `dft n ω x k = Σⱼ xⱼ · (ωᵏ)ʲ`.

No relation on `ω` is assumed — this is the pure index identity
`ωʲᵏ = (ωᵏ)ʲ`. Read over all `k`, the transform `x ↦ (Xₖ)ₖ` is exactly
"evaluate the coefficient polynomial at the powers `ω⁰, …, ωⁿ⁻¹`". -/
theorem dft_eq_polyEval (n : ℕ) (ω : R) (x : Fin n → R) (k : Fin n) :
    dft n ω x k = ∑ j : Fin n, x j * (ω ^ k.val) ^ j.val := by
  rw [dft]
  apply Finset.sum_congr rfl
  intro j _
  rw [← pow_mul, Nat.mul_comm j.val k.val]

/-! ### Connecting to `PolyConvGeneric.eval` (list-indexed evaluation) -/

/-- `PolyConvGeneric.eval` of a `(List.range n).map f` list is the matching
`Finset.range` sum `Σ_{i<n} f i · xⁱ`. A reindexing lemma bridging the
list-indexed `eval` and a `Finset.range` sum. -/
theorem eval_range_map (n : ℕ) (f : ℕ → R) (x : R) :
    PolyConvGeneric.eval ((List.range n).map f) x
      = ∑ i ∈ Finset.range n, f i * x ^ i := by
  rw [PolyConvGeneric.eval_eq_polyEval, PolyConvGeneric.toPoly_range_map,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- The bridge expressed against `PolyConvGeneric.eval`: the `k`-th DFT output of
`x : Fin n → R` is the list-eval of the coefficient list `(range n).map x'`
(where `x' i = x ⟨i, _⟩`) at the point `ωᵏ`. This is the precise sense in which
"the DFT evaluates the coefficient polynomial at `ωᵏ`", connecting `dft` to the
`PolyConvGeneric` polynomial-multiply spec. -/
theorem dft_eq_listEval (n : ℕ) (ω : R) (x : Fin n → R) (k : Fin n) :
    dft n ω x k
      = PolyConvGeneric.eval
          ((List.range n).map (fun i => if h : i < n then x ⟨i, h⟩ else 0))
          (ω ^ k.val) := by
  rw [dft_eq_polyEval, eval_range_map,
    ← Fin.sum_univ_eq_sum_range
      (fun j => (if h : j < n then x ⟨j, h⟩ else 0) * (ω ^ k.val) ^ j) n]
  apply Finset.sum_congr rfl
  intro j _
  simp only [j.isLt, dif_pos]

/-! ## The convolution theorem (forward direction) -/

/-- **Convolution theorem, forward direction (pointwise form).** Evaluating the
convolution `conv a b` of two coefficient lists at the DFT point `ωᵏ` equals the
product of the two pointwise evaluations:

  `eval (conv a b) ωᵏ = eval a ωᵏ · eval b ωᵏ`.

This is the `PolyConvGeneric.eval_conv` theorem specialised to the evaluation
points `ωᵏ` that the DFT samples — the algebraic identity an NTT-based multiply
realises: a convolution in the coefficient domain becomes a *pointwise product*
in the evaluation (DFT) domain. No primitive-root hypothesis is needed for this
forward direction. -/
theorem eval_conv_at_twiddle (a b : List R) (ω : R) (k : ℕ) :
    PolyConvGeneric.eval (PolyConvGeneric.conv a b) (ω ^ k)
      = PolyConvGeneric.eval a (ω ^ k) * PolyConvGeneric.eval b (ω ^ k) :=
  PolyConvGeneric.eval_conv a b (ω ^ k)

/-- **Convolution theorem, forward direction (DFT form).** For two length-`n`
coefficient vectors `x, y`, the pointwise product of their DFTs at index `k`
equals the list-eval of the convolution `conv` of their coefficient lists at the
point `ωᵏ`:

  `dft n ω x k · dft n ω y k = eval (conv (list x) (list y)) ωᵏ`,

where `list z := (range n).map z'`. Combining `dft_eq_listEval` (each DFT output
is a polynomial evaluation at `ωᵏ`) with the `eval_conv` theorem, this says the
NTT turns convolution into a pointwise product: to multiply two polynomials,
take their DFTs, multiply pointwise, and the result is the DFT of their
convolution. The inverse direction (recovering the convolution coefficients by
interpolation) needs a primitive `n`-th root of unity and is out of scope. -/
theorem dft_mul_eq_conv (n : ℕ) (ω : R) (x y : Fin n → R) (k : Fin n) :
    dft n ω x k * dft n ω y k
      = PolyConvGeneric.eval
          (PolyConvGeneric.conv
            ((List.range n).map (fun i => if h : i < n then x ⟨i, h⟩ else 0))
            ((List.range n).map (fun i => if h : i < n then y ⟨i, h⟩ else 0)))
          (ω ^ k.val) := by
  rw [dft_eq_listEval, dft_eq_listEval, PolyConvGeneric.eval_conv]

end CatCrypt.Crypto.Optimizer.Lattice.NTTConvolutionTheorem
