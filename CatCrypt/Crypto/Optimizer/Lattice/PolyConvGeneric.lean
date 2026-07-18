/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-!
# Polynomial multiplication as a convolution (generic `CommRing`)

This file gives the *generic spec* that an NTT-based polynomial multiply
implements: multiplying two polynomials, represented low-first as coefficient
lists over a `CommRing R`, is a convolution, and the convolution corresponds to
the product of the evaluations of the operands.

The keystone is the **evaluation homomorphism**

  `eval (conv a b) x = eval a x * eval b x`,

i.e. convolution of coefficient lists corresponds to the product of the
polynomials they encode. An NTT computes `conv` (pointwise multiply in the
evaluation domain, then interpolate back); its correctness is anchored to this
spec.

## Design

We map coefficient lists to Mathlib's `Polynomial R` via `toPoly`, define `conv`
on lists so that `toPoly (conv a b) = toPoly a * toPoly b`, and define `eval` so
that it agrees with `Polynomial.eval`. The keystone then falls out of
`Polynomial.eval_mul`.

* `toPoly l`   — the polynomial `∑ i, l[i] • X^i` encoded by a low-first list.
* `eval l x`   — Horner-free evaluation `∑ i, l[i] * x^i`, defined directly on
                 the list via `zipIdx`.
* `conv a b`   — convolution: `(conv a b)[k] = ∑_{i+j=k} a[i] * b[j]`, defined
                 as the coefficient list of `toPoly a * toPoly b`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.PolyConvGeneric

open Polynomial

variable {R : Type*} [CommRing R]

/-- The polynomial encoded by a low-first coefficient list:
`toPoly [a₀, a₁, …, aₙ] = a₀ + a₁ X + ⋯ + aₙ Xⁿ`. -/
noncomputable def toPoly (l : List R) : Polynomial R :=
  (l.zipIdx.map (fun p => (Polynomial.C p.1) * Polynomial.X ^ p.2)).sum

/-- Direct evaluation of a coefficient list at a point:
`eval [a₀, a₁, …] x = a₀ + a₁ x + a₂ x² + ⋯`. -/
def eval (l : List R) (x : R) : R :=
  (l.zipIdx.map (fun p => p.1 * x ^ p.2)).sum

/-- `eval` agrees with `Polynomial.eval` on the encoded polynomial:
evaluating the list is the same as evaluating its polynomial. -/
theorem eval_eq_polyEval (l : List R) (x : R) :
    eval l x = Polynomial.eval x (toPoly l) := by
  unfold eval toPoly
  rw [show Polynomial.eval x = ⇑(Polynomial.evalRingHom x) from rfl,
    map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp

/-- Convolution of two coefficient lists, defined as the coefficient list of the
product polynomial. By construction `(conv a b)[k] = ∑_{i+j=k} a[i] * b[j]`. -/
noncomputable def conv (a b : List R) : List R :=
  (List.range ((toPoly a * toPoly b).natDegree + 1)).map
    fun k => (toPoly a * toPoly b).coeff k

/-- `toPoly` of a coefficient list `(range n).map f` is the `Finset.range`
sum `∑ i < n, C (f i) * Xⁱ`. -/
theorem toPoly_range_map (n : ℕ) (f : ℕ → R) :
    toPoly ((List.range n).map f)
      = ∑ i ∈ Finset.range n, Polynomial.C (f i) * Polynomial.X ^ i := by
  induction n with
  | zero => simp [toPoly]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    unfold toPoly at *
    rw [List.zipIdx_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    simp

/-- The full reconstruction lemma: a polynomial is recovered from the list of
its coefficients up to `natDegree`. -/
theorem toPoly_coeffList (P : Polynomial R) :
    toPoly ((List.range (P.natDegree + 1)).map P.coeff) = P := by
  rw [toPoly_range_map]
  conv_rhs => rw [P.as_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.C_mul_X_pow_eq_monomial]

/-- `toPoly` recovers the product polynomial from the convolution list:
`toPoly (conv a b) = toPoly a * toPoly b`. -/
theorem toPoly_conv (a b : List R) :
    toPoly (conv a b) = toPoly a * toPoly b := by
  unfold conv
  rw [toPoly_coeffList]

/-- **Keystone (evaluation homomorphism).** Evaluating the convolution of two
coefficient lists equals the product of the two evaluations:

  `eval (conv a b) x = eval a x * eval b x`.

Convolution of coefficient lists corresponds to multiplication of the encoded
polynomials. This is exactly the spec an NTT-based multiply implements. -/
theorem eval_conv (a b : List R) (x : R) :
    eval (conv a b) x = eval a x * eval b x := by
  rw [eval_eq_polyEval, eval_eq_polyEval, eval_eq_polyEval, toPoly_conv,
    Polynomial.eval_mul]

/-- `eval` of an explicit two-element list is the linear polynomial it encodes. -/
theorem eval_pair (a₀ a₁ x : R) : eval [a₀, a₁] x = a₀ + a₁ * x := by
  simp [eval]

/-- `eval` of an explicit three-element list is the quadratic it encodes. -/
theorem eval_triple (a₀ a₁ a₂ x : R) :
    eval [a₀, a₁, a₂] x = a₀ + a₁ * x + a₂ * x ^ 2 := by
  simp [eval]; ring

/-- Worked example over `ℤ`: convolving the coefficient lists of `1 + X` with
itself evaluates, at every point, to `(1 + X)(1 + X) = 1 + 2X + X²`. This is the
keystone `eval_conv` made concrete: the convolution of `[1, 1]` with `[1, 1]`
agrees pointwise with the polynomial `1 + 2X + X²` (list `[1, 2, 1]`). -/
example (x : ℤ) :
    eval (conv [1, 1] [1, 1]) x = eval ([1, 2, 1] : List ℤ) x := by
  rw [eval_conv, eval_pair, eval_triple]
  ring

end CatCrypt.Crypto.Optimizer.Lattice.PolyConvGeneric
