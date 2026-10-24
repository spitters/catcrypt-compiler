/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Complex.Basic

/-!
# Matrix Decision Tactics

Tactics for closing matrix arithmetic goals over `Complex` by exhaustive
case-splitting on `Fin n` indices.

## Tactics

| Tactic | Dimension | Speed | Use case |
|--------|-----------|-------|----------|
| `matrix_decide` | 2x2 -- 4x4 | Fast | Standard matrix equalities |
| `matrix_decide!` | 2x2 -- 4x4 | Slow | Harder goals (full `simp`) |
| `matrix_native` | 2x2 -- 16x16 | Medium | Large concrete matrices |
| `unitary_decide` | 2x2 -- 16x16 | Medium | Unitarity proofs |
| `hermitian_decide` | 2x2 -- 16x16 | Medium | Hermiticity by entry check |

## Strategy

1. `ext i j` to reduce matrix equality to pointwise equality
2. `fin_cases i <;> fin_cases j` to enumerate all entries
3. `simp only [...]` with a carefully chosen lemma set to normalize each entry
4. `ring` / `norm_num` / `field_simp; ring` / `decide` to close arithmetic goals

For dimensions > 4, the key is `Fin.sum_univ_succ` + `Fin.sum_univ_zero` to
iteratively unfold finite sums. The named lemmas `Fin.sum_univ_two`,
`Fin.sum_univ_three`, `Fin.sum_univ_four` only handle those specific sizes.
-/

@[expose] public section

set_option autoImplicit false

/-! ## Core simp lemma sets -/

/-- The base simp set for matrix entry normalization (dimensions 2--4). -/
macro "matrix_simp_core" : tactic => `(tactic|
  simp (config := { decide := true }) only [
    Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.head_fin_const,
    Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
    Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_mk, Fin.ext_iff,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
    Complex.I_re, Complex.I_im, Complex.I_sq,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    starRingEnd_apply, star_trivial,
    Complex.conj_ofReal, Complex.star_def, Complex.normSq_mk,
    Complex.conj_re, Complex.conj_im,
    map_neg, map_zero, map_one, map_inv₀,
    Complex.ofReal_inv, Complex.ofReal_neg,
    ite_true, ite_false, ite_true, ite_false,
    eq_self_iff_true, reduceCtorEq,
    mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero,
    mul_neg, neg_mul, neg_neg, neg_zero, sub_self, sub_zero, zero_sub,
    Matrix.vecHead, Matrix.vecTail])

/-- Extended simp set for dimensions 5--16, using `Fin.sum_univ_succ` to
    iteratively unfold sums of any size. -/
macro "matrix_simp_extended" : tactic => `(tactic|
  simp (config := { decide := true }) only [
    Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.head_fin_const,
    Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
    Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_mk, Fin.ext_iff,
    Fin.divNat, Fin.modNat,
    finProdFinEquiv,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
    Complex.I_re, Complex.I_im, Complex.I_sq,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    starRingEnd_apply, star_trivial,
    Complex.conj_ofReal, Complex.star_def, Complex.normSq_mk,
    Complex.conj_re, Complex.conj_im,
    map_neg, map_zero, map_one, map_inv₀,
    Complex.ofReal_inv, Complex.ofReal_neg,
    ite_true, ite_false, ite_true, ite_false,
    eq_self_iff_true, reduceCtorEq,
    mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero,
    mul_neg, neg_mul, neg_neg, neg_zero, sub_self, sub_zero, zero_sub,
    Matrix.vecHead, Matrix.vecTail])

/-! ## The tactics -/

/-- Close a small matrix goal by exhaustive case analysis on indices.
    Works for dimensions 2x2 through 4x4. For larger matrices, use
    `matrix_native`. Unfold definitions before calling. -/
macro "matrix_decide" : tactic => `(tactic|
  first
  | rfl
  | (ext i j; fin_cases i <;> fin_cases j <;>
     simp (config := { decide := true }) only [
       Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
       Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
       Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
       Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
       Matrix.head_cons, Matrix.head_fin_const,
       Matrix.conjTranspose_apply,
       Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
       Fin.isValue, Fin.val_zero, Fin.val_one,
       Complex.ofReal_re, Complex.ofReal_im,
       Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
       Complex.I_re, Complex.I_im, Complex.I_sq,
       Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
       Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
       starRingEnd_apply, star_trivial,
       Complex.conj_ofReal, Complex.star_def, map_neg, map_zero, map_one,
       map_inv₀, Complex.ofReal_inv, Complex.ofReal_neg,
       ite_true, ite_false, ite_true, ite_false,
       eq_self_iff_true, reduceCtorEq,
       mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero,
       mul_neg, neg_mul, neg_neg, sub_self, sub_zero, zero_sub,
       Matrix.vecHead, Matrix.vecTail] <;>
     first | rfl | ring | norm_num | (field_simp; ring) | (push_cast; ring))
  | (ext i; fin_cases i <;>
     simp (config := { decide := true }) only [
       Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
       Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
       Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
       Matrix.head_cons, Matrix.head_fin_const,
       Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
       Fin.isValue, Fin.val_zero, Fin.val_one,
       ite_true, ite_false, ite_true, ite_false,
       eq_self_iff_true, reduceCtorEq,
       mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero,
       Matrix.vecHead, Matrix.vecTail] <;>
     first | rfl | ring | norm_num | (field_simp; ring) | (push_cast; ring)))

/-- `matrix_decide` variant using full `simp` (not `simp only`).
    Slower but handles more cases automatically. -/
macro "matrix_decide!" : tactic => `(tactic|
  first
  | rfl
  | (ext i j; fin_cases i <;> fin_cases j <;> simp <;>
     first | rfl | ring | norm_num | (field_simp; ring) | (push_cast; ring))
  | (ext i; fin_cases i <;> simp <;>
     first | rfl | ring | norm_num | (field_simp; ring) | (push_cast; ring)))

/-- Close matrix equations up to 16x16 by entry expansion with iterative sum
    unfolding via `Fin.sum_univ_succ` / `Fin.sum_univ_zero`.

    For 8x8 expect ~5s, for 16x16 expect ~30s. Increase `maxHeartbeats`
    if needed. Unfold definitions before calling. -/
macro "matrix_native" : tactic => `(tactic|
  first
  | rfl
  | (ext i j; fin_cases i <;> fin_cases j <;>
     matrix_simp_extended <;>
     first
       | rfl
       | norm_num
       | ring
       | decide
       | (simp; try ring; try norm_num)
       | (field_simp; ring)
       | (push_cast; ring)
       | (simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num)
       | (simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]; ring))
  | (ext i; fin_cases i <;>
     matrix_simp_extended <;>
     first
       | rfl
       | norm_num
       | ring
       | decide
       | (simp; try ring; try norm_num)
       | (field_simp; ring)
       | (push_cast; ring)))

/-- For unitarity proofs: `M * conjTranspose M = I` or vice versa.
    Handles star/conj normalization automatically. Works up to 16x16.
    Unfold definitions before calling. -/
macro "unitary_decide" : tactic => `(tactic|
  first
  | rfl
  | (ext i j; fin_cases i <;> fin_cases j <;>
     simp (config := { decide := true }) only [
       Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
       Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
       Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
       Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
       Matrix.head_cons, Matrix.head_fin_const,
       Matrix.conjTranspose_apply, Matrix.transpose_apply,
       Fin.sum_univ_succ, Fin.sum_univ_zero,
       Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
       Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_mk, Fin.ext_iff,
       Fin.divNat, Fin.modNat,
       finProdFinEquiv,
       Complex.ofReal_re, Complex.ofReal_im,
       Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
       Complex.I_re, Complex.I_im, Complex.I_sq,
       Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
       Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
       starRingEnd_apply, star_trivial,
       Complex.conj_ofReal, Complex.star_def, Complex.normSq_mk,
       Complex.conj_re, Complex.conj_im,
       Complex.ofReal_neg, Complex.ofReal_inv,
       map_neg, map_zero, map_one, map_inv₀,
       ite_true, ite_false, ite_true, ite_false,
       eq_self_iff_true, reduceCtorEq,
       mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero,
       mul_neg, neg_mul, neg_neg, neg_zero, sub_self, sub_zero, zero_sub,
       Matrix.vecHead, Matrix.vecTail] <;>
     first
       | rfl
       | norm_num
       | ring
       | decide
       | (field_simp; ring)
       | (push_cast; ring)
       | (simp; try ring; try norm_num)))

/-- Close hermiticity goals (`conjTranspose M = M`) for concrete matrices by
    entry-wise case analysis. Works up to 16x16. -/
macro "hermitian_decide" : tactic => `(tactic|
  (ext i j; fin_cases i <;> fin_cases j <;>
   simp (config := { decide := true }) only [
     Matrix.conjTranspose_apply,
     Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
     Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
     Matrix.head_cons, Matrix.head_fin_const,
     Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_mk,
     starRingEnd_apply, star_trivial,
     Complex.conj_ofReal, Complex.star_def,
     Complex.conj_re, Complex.conj_im,
     Complex.ofReal_neg, Complex.ofReal_inv,
     map_neg, map_zero, map_one, map_inv₀,
     ite_true, ite_false, ite_true, ite_false,
     eq_self_iff_true, reduceCtorEq,
     mul_zero, zero_mul, mul_one, one_mul,
     neg_neg, neg_zero,
     Fin.sum_univ_succ, Fin.sum_univ_zero,
     Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
     Matrix.vecHead, Matrix.vecTail] <;>
   first | rfl | ring | norm_num | (field_simp; ring) | decide))

/-! ## Smoke tests -/

section MatrixDecideTests

-- 2x2: Pauli X squared via matrix_decide
def _root_.MatrixDecideTests.pauliX : Matrix (Fin 2) (Fin 2) Complex :=
  Matrix.of ![![0, 1], ![1, 0]]

example : MatrixDecideTests.pauliX * MatrixDecideTests.pauliX = 1 := by
  unfold MatrixDecideTests.pauliX; matrix_decide

-- 2x2: Pauli Z squared via matrix_decide
def _root_.MatrixDecideTests.pauliZ : Matrix (Fin 2) (Fin 2) Complex :=
  Matrix.of ![![1, 0], ![0, -1]]

example : MatrixDecideTests.pauliZ * MatrixDecideTests.pauliZ = 1 := by
  unfold MatrixDecideTests.pauliZ; matrix_decide

-- 8x8: XOR permutation matrix via matrix_native
def _root_.MatrixDecideTests.perm8 : Matrix (Fin 8) (Fin 8) Complex :=
  Matrix.of fun (i j : Fin 8) =>
    if i.val ^^^ 4 = j.val then (1 : Complex) else 0

set_option maxHeartbeats 800000 in
example : MatrixDecideTests.perm8 * MatrixDecideTests.perm8 = 1 := by
  unfold MatrixDecideTests.perm8; matrix_native

end MatrixDecideTests
