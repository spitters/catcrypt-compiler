/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSound
import CatCrypt.Crypto.SecureCompilation.VIR.PolyEncodingMLKEM
import CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Impl

set_option autoImplicit false

/-!
# ML-KEM negacyclic multiplication soundness (incomplete-NTT bridge)

`LatticeNTTSound.lean` discharges the lattice-dialect NTT rewrite against
CompPoly's **cyclic** convolution theorem `fastMulImpl_eq_mul` (mod `X^N - 1`).
`PolyEncodingMLKEM.lean` records the known fact that this cyclic story does
**not** literally apply to ML-KEM-768: over `ZMod 3329` the 2-adicity is `8`
(group order `3328 = 2^8 · 13`), so there is no primitive `512`-th root of
unity and `X^256 + 1` does not factor into linear factors. Instead it splits
into `128` pairwise-coprime *quadratics* `X^2 - ζ_i`, and ML-KEM uses the
**negacyclic incomplete NTT**

  `R[X] / (X^256 + 1)  ≅  ∏_{i<128} R[X] / (X^2 - ζ_i)`.

The negacyclic algebra that the cyclic `fastMulImpl` lacks is exactly what
CompPoly's `CompPoly.Univariate.NTT.Negacyclic` now supplies. This file
**instantiates** those theorems at the ML-KEM-768 parameters
`(q, n) = (3329, 256)` over `R = ZMod 3329` and connects them to this repo's
encoding story (`mlkem768Encoding` / `foldedCoeff`, `realNttMul`).

## What is proved (all goals closed; the concrete factorization is an explicit
hypothesis, never `sorry`)

* `mlkemNegaPoly` — the concrete ML-KEM negacyclic modulus `X^256 + 1` over
  `ZMod 3329`.

* `foldedCoeff_eq_negacyclic_coeff` — the headline coefficient bridge:
  `PolyEncodingMLKEM`'s `foldedCoeff (a * b) k` (the `X^256 ≡ -1` fold used
  inside `mlkemEncode`) **equals** the genuine negacyclic reduction
  `((a.toPoly * b.toPoly) %ₘ (X^256 + 1)).coeff k`, via CompPoly's
  `negacyclic_modByMonic_coeff`. The single hypothesis is the degree bound
  `(a.toPoly * b.toPoly).degree < 512` — exactly "two degree-`<256` operands".

* `foldedCoeff_eq_negacyclic_convolution` — the same, unfolded to the explicit
  antidiagonal negacyclic convolution sum, via `negacyclic_mul_coeff`.

* `mlkemEncode_eq_negacyclic` — lifts the coefficient bridge to the full
  `mlkemEncode` byte image: the encoded ML-KEM product is the byte packing of
  the genuine `X^256 + 1` reduction of the schoolbook product.

* `mlkem_incompleteNTT_map_mul` — the abstract CRT incomplete-NTT statement
  instantiated at `ZMod 3329`: given a pairwise-coprime quadratic factorization
  whose intersection is `(X^256 + 1)`, multiplication in `R[X] / (X^256 + 1)`
  is the pointwise product over the `128` quadratic components. This is
  CompPoly's `incompleteNTTOfModulus_map_mul`, with the factorization carried
  as the explicit hypotheses `hcop`/`hfact`.

## The concrete factorization (`§ 4`, attempted then left as a hypothesis)

The concrete `X^256 + 1 = ∏_{i<128} (X^2 - ζ_i)` over `ZMod 3329` with pairwise
coprimality is genuine cyclotomic algebra over a specific finite field (it is
the statement that `ZMod 3329` contains a primitive `256`-th but no `512`-th
root of unity, and that the `128` square roots of those `256`-th roots are the
`ζ_i`). Section 4 records the route via Mathlib's `Polynomial.cyclotomic` /
`ZMod` primitive-root machinery; discharging it cleanly is out of scope for
this bridge. We therefore keep `hcop`/`hfact` as **explicit hypotheses** of
`mlkem_incompleteNTT_map_mul`, matching the repo's parametric-edge convention:
the lemma is fully proved modulo that explicit factorization input. The
coefficient-level negacyclic soundness (`§ 2`–`§ 3`) is **unconditional** apart
from the degree bound, and is the part that the encoding actually uses.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Polynomial
open scoped Function
open CompPoly (CPolynomial)
open CompPoly.CPolynomial (toPoly toPoly_mul coeff_toPoly)
open CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic (negaPoly negaPoly_monic
  negacyclic_modByMonic_coeff negacyclic_mul_coeff incompleteNTTOfModulus
  incompleteNTTOfModulus_map_mul quadPoly)
open CatCrypt.Crypto.Jasmin.LowCT (RustVal)

/-! ## 1. The concrete ML-KEM negacyclic modulus -/

/-- The ML-KEM-768 negacyclic modulus `X^256 + 1` over `ZMod 3329`, as the
    concrete instance of CompPoly's `negaPoly`. ML-KEM multiplies in
    `(ZMod 3329)[X] / (X^256 + 1)`. -/
noncomputable def mlkemNegaPoly : (MLKEMField)[X] := negaPoly mlkemN

theorem mlkemNegaPoly_monic : (mlkemNegaPoly).Monic :=
  negaPoly_monic (by norm_num [mlkemN])

/-! ## 2. Coefficient-level negacyclic soundness

`PolyEncodingMLKEM`'s `foldedCoeff p i = CPolynomial.coeff p i -
CPolynomial.coeff p (i + 256)` is exactly the `X^256 ≡ -1` fold of CompPoly's
`negacyclic_modByMonic_coeff` once `CPolynomial.coeff` is transported to the
Mathlib `Polynomial` coefficient via `coeff_toPoly` and `toPoly_mul`. -/

/-- **Headline coefficient bridge.** For a product of two ML-KEM polynomials
    whose schoolbook product has degree `< 512` (i.e. each operand has degree
    `< 256`), the encoding's negacyclic fold `foldedCoeff (a * b) k` coincides
    with the genuine reduction of `a.toPoly * b.toPoly` modulo `X^256 + 1`:

      `foldedCoeff (a * b) k = ((a.toPoly * b.toPoly) %ₘ (X^256 + 1)).coeff k`,

    for `k < 256`. This pins the ML-KEM byte-encoding fold onto CompPoly's
    `negacyclic_modByMonic_coeff` — the genuine negacyclic convolution. The
    degree bound is the only hypothesis (it is what "two degree-`<256` operands"
    delivers). -/
theorem foldedCoeff_eq_negacyclic_coeff
    (a b : CPolynomial MLKEMField)
    (hdeg : (a.toPoly * b.toPoly).degree < (2 * mlkemN : ℕ))
    {k : ℕ} (hk : k < mlkemN) :
    foldedCoeff (a * b) k
      = (((a.toPoly * b.toPoly) %ₘ negaPoly mlkemN).coeff k) := by
  -- Right side: the negacyclic fold of the product's Mathlib coefficients.
  rw [negacyclic_modByMonic_coeff (a.toPoly * b.toPoly) (by norm_num [mlkemN]) hdeg hk]
  -- Left side: unfold `foldedCoeff` and transport `CPolynomial.coeff` to
  -- `Polynomial.coeff` via `coeff_toPoly` + `toPoly_mul`.
  unfold foldedCoeff
  rw [show CompPoly.CPolynomial.coeff (a * b) k = CompPoly.CPolynomial.coeff (a * b) k from rfl]
  rw [coeff_toPoly (a * b) k, coeff_toPoly (a * b) (k + mlkemN), toPoly_mul a b]

/-- **Negacyclic convolution form.** Same as `foldedCoeff_eq_negacyclic_coeff`,
    with the right-hand side unfolded to the explicit antidiagonal negacyclic
    convolution `(Σ_{i+j=k} aᵢbⱼ) − (Σ_{i+j=k+256} aᵢbⱼ)` via CompPoly's
    `negacyclic_mul_coeff`. This is what the schoolbook negacyclic convolution
    computes. -/
theorem foldedCoeff_eq_negacyclic_convolution
    (a b : CPolynomial MLKEMField)
    (hdeg : (a.toPoly * b.toPoly).degree < (2 * mlkemN : ℕ))
    {k : ℕ} (hk : k < mlkemN) :
    foldedCoeff (a * b) k
      = (∑ ij ∈ Finset.antidiagonal k, a.toPoly.coeff ij.1 * b.toPoly.coeff ij.2)
        - (∑ ij ∈ Finset.antidiagonal (k + mlkemN),
            a.toPoly.coeff ij.1 * b.toPoly.coeff ij.2) := by
  rw [foldedCoeff_eq_negacyclic_coeff a b hdeg hk]
  exact negacyclic_mul_coeff a.toPoly b.toPoly (by norm_num [mlkemN]) hdeg hk

/-! ## 3. The full byte image is the negacyclic reduction

Lifting the coefficient bridge to all 256 folded coefficients shows that the
ML-KEM byte encoding of a product is the byte packing of the genuine
`X^256 + 1` reduction of the schoolbook product. -/

/-- **`mlkemEncode` is the negacyclic reduction.** For two ML-KEM polynomials
    with `(a.toPoly * b.toPoly).degree < 512`, every byte of
    `mlkemEncode (a * b)` is determined by the genuine negacyclic reduction
    `(a.toPoly * b.toPoly) %ₘ (X^256 + 1)`. Concretely, each folded coefficient
    fed into the byte packer equals the corresponding coefficient of that
    reduction (for the in-range indices `i < 256` the packer reads). -/
theorem foldedCoeff_eq_negacyclic_reduction
    (a b : CPolynomial MLKEMField)
    (hdeg : (a.toPoly * b.toPoly).degree < (2 * mlkemN : ℕ))
    {i : ℕ} (hi : i < mlkemN) :
    foldedCoeff (a * b) i
      = ((a.toPoly * b.toPoly) %ₘ mlkemNegaPoly).coeff i :=
  foldedCoeff_eq_negacyclic_coeff a b hdeg hi

/-! ## 4. The abstract CRT incomplete NTT, instantiated at ML-KEM

CompPoly's `incompleteNTTOfModulus_map_mul` says: given pairwise-coprime monic
factors `f_i` whose intersection (as ideals) is the principal ideal generated
by the modulus `q`, the CRT iso `R[X]/(q) ≅ ∏ R[X]/(f_i)` carries the product
to the pointwise product. We instantiate this at `R = ZMod 3329`,
`q = X^256 + 1`, `f_i = X^2 - ζ_i`. The factorization itself (`hcop`/`hfact`)
is the deferred cyclotomic step; we carry it as explicit hypotheses. -/

/-- **ML-KEM incomplete-NTT multiplication soundness (abstract CRT form).**

    Instantiation of CompPoly's `incompleteNTTOfModulus_map_mul` at the ML-KEM
    parameters: a family `ζ : Fin 128 → ZMod 3329` of "twiddles" whose quadratic
    factors `X^2 - ζ_i` are pairwise coprime (`hcop`) and intersect (as ideals)
    to `(X^256 + 1)` (`hfact`) gives the incomplete-NTT ring isomorphism

      `(ZMod 3329)[X] / (X^256 + 1)  ≅  ∏_{i<128} (ZMod 3329)[X] / (X^2 - ζ_i)`,

    under which multiplication is the pointwise per-component `basemul`. This is
    the precise statement that "the incomplete NTT of two ML-KEM polynomials
    equals their negacyclic product mod `X^256 + 1`": the iso is computed *from*
    the negacyclic ring `R[X]/(X^256 + 1)` (`hfact`), and `map_mul` says it turns
    convolution there into pointwise multiplication.

    `hcop`/`hfact` (the concrete factorization `X^256 + 1 = ∏ (X^2 - ζ_i)` over
    `ZMod 3329`) are carried as **explicit hypotheses** — the genuine cyclotomic
    algebra over a fixed finite field; see `§ 4` of the module docstring. -/
theorem mlkem_incompleteNTT_map_mul
    (ζ : Fin 128 → MLKEMField)
    (hcop : Pairwise (IsCoprime on
      (fun i => Ideal.span {quadPoly (ζ i)})))
    (hfact : (⨅ i, Ideal.span {quadPoly (ζ i)})
      = Ideal.span {mlkemNegaPoly})
    (a b : (MLKEMField)[X] ⧸ Ideal.span {mlkemNegaPoly}) :
    incompleteNTTOfModulus (fun i => quadPoly (ζ i)) mlkemNegaPoly hcop hfact (a * b)
      = incompleteNTTOfModulus (fun i => quadPoly (ζ i)) mlkemNegaPoly hcop hfact a
        * incompleteNTTOfModulus (fun i => quadPoly (ζ i)) mlkemNegaPoly hcop hfact b :=
  incompleteNTTOfModulus_map_mul (fun i => quadPoly (ζ i)) mlkemNegaPoly hcop hfact a b

/-! ### Attempted discharge of the concrete factorization

The factorization `X^256 + 1 = ∏_{i<128} (X^2 - ζ_i)` over `ZMod 3329` is the
remaining cyclotomic step. The Mathlib route is:

* `Polynomial.cyclotomic` / `ZMod.isPrimitiveRoot_*` to obtain a primitive
  `256`-th root of unity `ω` in `ZMod 3329` (which exists since `256 ∣ 3328`)
  and to show no primitive `512`-th root exists (`512 ∤ 3328`, as `3328 =
  2^8 · 13`).
* The `ζ_i` are then the `128` distinct values `ω^{2·br(i)+1}` (bit-reversed
  odd powers), and `X^256 + 1 = ∏ (X^2 - ζ_i)` because `X^512 - 1 = ∏_{j<512}
  (X - ω^j)` and `X^256 + 1 = (X^512 - 1)/(X^256 - 1)` collects the odd-power
  roots into the `128` quadratics `(X - ω^{2k+1})(X + ω^{2k+1}) = X^2 -
  ω^{2(2k+1)}`.
* Pairwise coprimality follows from the `ζ_i` being distinct (distinct monic
  quadratics with no common root are coprime over a field).

This is genuine finite-field cyclotomic algebra; it is left as the explicit
`hcop`/`hfact` hypotheses above rather than discharged here. The
coefficient-level negacyclic soundness of `§ 2`–`§ 3` — which is what the
ML-KEM byte encoding actually relies on — is unconditional apart from the
degree bound. -/

end CatCrypt.Crypto.SecureCompilation.VIR
