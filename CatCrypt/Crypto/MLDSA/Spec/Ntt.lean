/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.MLDSA.Spec.Coeffs
public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances
public import CatCrypt.Crypto.Optimizer.Lattice.NTTFullInversionGeneric
public import CatCrypt.Crypto.Optimizer.Lattice.SignedNegacyclicConv
public import CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric

/-!
# The ML-DSA number-theoretic transform (FIPS 204 §7.5)

The ML-DSA NTT as a map on `Fin 256 → ZMod 8380417`, in the coefficient ordering of
FIPS 204 equation (7.1): `ntt w i` is `w` evaluated at `ζ ^ (2 * BitRev8 i + 1)`,
with `ζ = 1753`. The ordering is externally observable, because FIPS 204 samples the
matrix `Â` directly in the NTT domain.

The transform is the twisted transform `ndft` of
`CatCrypt.Crypto.Lattice.NegacyclicTransformGeneric` at the twist root
`ζ = 1753`, composed with the 8-bit bit-reversal permutation. Its properties are
instantiations of the generic library at `isPrimitiveRoot_1753_512`.

## Main definitions

* `zeta`, `bitRev8`, `zetas` — the root, the index permutation, the twiddle table
* `ntt`, `invNtt` — the forward and inverse transforms
* `polyMul` — the negacyclic product on coefficient vectors

## Main statements

* `ntt_eq_sum` — the FIPS 204 (7.1) evaluation form
* `invNtt_ntt`, `ntt_invNtt` — the two inversions
* `ntt_add`, `ntt_sub`, `ntt_const_mul` — linearity
* `ntt_polyMul` — the transform of a negacyclic product is the pointwise product
* `coeffsToRqDsa_polyMul` — `polyMul` is multiplication in `Rq_dsa`
* `rqDsa_mul_eq_invNtt` — the `Rq_dsa` product through the transform

## References

* NIST FIPS 204 (2024), §7.5, Algorithms 41–42, Appendix B
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLDSA.Spec.Ntt

open Polynomial AdjoinRoot Finset
open CatCrypt.Crypto.MLDSA.ConcreteParams
open CatCrypt.Crypto.MLDSA.Spec.Coeffs
open CatCrypt.Crypto.Lattice.NTTRecursionPass (dft)
open CatCrypt.Crypto.Lattice.NTTInverseGeneric (ntt_orthogonality)
open CatCrypt.Crypto.Lattice.NTTFullInversionGeneric (idft idft_dft)
open CatCrypt.Crypto.Lattice.NegacyclicTransformGeneric
  (twist untwist twist_untwist untwist_twist ndft negaConv)
open CatCrypt.Crypto.Lattice.SignedNegacyclicConv (signedNegaConv negaConv_eq_signed)
open CatCrypt.Crypto.Lattice.ConcreteNttRoots (isPrimitiveRoot_1753_512)
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances
  (isPrimitiveRoot_1753sq_256 mldsa_ndft_negaConv)
open CatCrypt.Crypto.Lattice.BitReversalGeneric (bitrevFin bitrevFin_involutive)

/-! ## The inverse discrete transform is a two-sided inverse

`NTTFullInversionGeneric.idft_dft` gives one side. The other side is the same
orthogonality computation with the roles of the two indices exchanged. -/

/-- The analysis map `dft` is a left inverse of the synthesis map `idft`, for `ω`
a primitive `n`-th root of unity over a field in which `n` is invertible. -/
theorem dft_idft {R : Type*} [Field R] {ω : R} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    (hn : (n : R) ≠ 0) (X : Fin n → R) :
    dft n ω (idft n ω X) = X := by
  funext k
  simp only [dft, idft]
  have key : ∀ j : Fin n,
      ((n : R)⁻¹ * ∑ l : Fin n, X l * ω⁻¹ ^ (l.val * j.val)) * ω ^ (j.val * k.val)
        = ∑ l : Fin n, (n : R)⁻¹ * X l * (ω ^ (k.val * j.val) * ω⁻¹ ^ (l.val * j.val)) := by
    intro j
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [mul_comm j.val k.val]
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_comm]
  have hinner : ∀ l : Fin n,
      (∑ j : Fin n, (n : R)⁻¹ * X l * (ω ^ (k.val * j.val) * ω⁻¹ ^ (l.val * j.val)))
        = (n : R)⁻¹ * X l * (if k = l then (n : R) else 0) := by
    intro l
    rw [← ntt_orthogonality hω k l, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun l _ => hinner l)]
  simp only [mul_ite, mul_zero,
    Finset.sum_ite_eq Finset.univ k (fun l => (n : R)⁻¹ * X l * (n : R)),
    Finset.mem_univ, ite_true]
  rw [mul_right_comm, inv_mul_cancel₀ hn, one_mul]

/-! ## The ML-DSA root, the index permutation and the twiddle table -/

/-- The ML-DSA NTT root `ζ = 1753`, a primitive `512`-th root of unity in
`ZMod 8380417` (FIPS 204 §7.5). -/
def zeta : ZMod q_dsa := 1753

/-- `zeta` is nonzero. -/
lemma zeta_ne_zero : zeta ≠ 0 := by decide

/-- `zeta ^ 2` is a primitive `256`-th root of unity. -/
lemma isPrimitiveRoot_zeta_sq : IsPrimitiveRoot (zeta ^ 2) 256 :=
  isPrimitiveRoot_1753sq_256

/-- `256` is invertible in `ZMod q_dsa`. -/
lemma cast_256_ne_zero : ((256 : ℕ) : ZMod q_dsa) ≠ 0 := by decide

/-- The 8-bit bit-reversal permutation `BitRev8` of FIPS 204 §7.5. -/
def bitRev8 (i : Fin 256) : Fin 256 := bitrevFin 8 i

/-- `BitRev8` is an involution. -/
lemma bitRev8_bitRev8 (i : Fin 256) : bitRev8 (bitRev8 i) = i :=
  bitrevFin_involutive 8 i

/-- The FIPS 204 twiddle table (Appendix B): `zetas k = ζ ^ BitRev8 k`. -/
def zetas (k : Fin 256) : ZMod q_dsa := zeta ^ (bitRev8 k).val

/-- The twiddle table is the root raised to the bit-reversed index. -/
theorem zetas_eq (k : Fin 256) : zetas k = (1753 : ZMod q_dsa) ^ (bitRev8 k).val := rfl

/-! ## The transform -/

/-- The ML-DSA forward NTT: the twisted transform at `ζ`, read in bit-reversed order.
FIPS 204 equation (7.1). -/
def ntt (w : Fin 256 → ZMod q_dsa) : Fin 256 → ZMod q_dsa :=
  fun i => ndft zeta w (bitRev8 i)

/-- The ML-DSA inverse NTT (FIPS 204 Algorithm 42): the bit-reversed input is
synthesised by `idft` at `ζ ^ 2` and untwisted by `ζ`. -/
def invNtt (v : Fin 256 → ZMod q_dsa) : Fin 256 → ZMod q_dsa :=
  untwist zeta (idft 256 (zeta ^ 2) (fun k => v (bitRev8 k)))

/-- **FIPS 204 (7.1).** The `i`-th NTT coefficient is `w` evaluated at
`ζ ^ (2 * BitRev8 i + 1)`. -/
theorem ntt_eq_sum (w : Fin 256 → ZMod q_dsa) (i : Fin 256) :
    ntt w i = ∑ j : Fin 256, w j * zeta ^ ((2 * (bitRev8 i).val + 1) * j.val) := by
  simp only [ntt, ndft, dft, twist]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_assoc, ← pow_mul, ← pow_add,
    show j.val + 2 * (j.val * (bitRev8 i).val)
      = (2 * (bitRev8 i).val + 1) * j.val from by ring]

/-! ## Inversion -/

/-- Reindexing the transform by `BitRev8` and synthesising recovers the twisted input. -/
private lemma ntt_bitRev8 (w : Fin 256 → ZMod q_dsa) (k : Fin 256) :
    ntt w (bitRev8 k) = dft 256 (zeta ^ 2) (twist zeta w) k := by
  simp only [ntt, ndft, bitRev8_bitRev8]

/-- **The inverse NTT inverts the NTT** (FIPS 204 Algorithms 41–42). -/
theorem invNtt_ntt (w : Fin 256 → ZMod q_dsa) : invNtt (ntt w) = w := by
  have h : (fun k => ntt w (bitRev8 k)) = dft 256 (zeta ^ 2) (twist zeta w) := by
    funext k; exact ntt_bitRev8 w k
  unfold invNtt
  rw [h, idft_dft isPrimitiveRoot_zeta_sq cast_256_ne_zero, untwist_twist zeta_ne_zero]

/-- **The NTT inverts the inverse NTT.** -/
theorem ntt_invNtt (v : Fin 256 → ZMod q_dsa) : ntt (invNtt v) = v := by
  funext i
  simp only [ntt, ndft, invNtt]
  rw [twist_untwist zeta_ne_zero, dft_idft isPrimitiveRoot_zeta_sq cast_256_ne_zero,
    bitRev8_bitRev8]

/-! ## Linearity -/

/-- The NTT is additive. -/
theorem ntt_add (a b : Fin 256 → ZMod q_dsa) (i : Fin 256) :
    ntt (fun j => a j + b j) i = ntt a i + ntt b i := by
  simp only [ntt, ndft, dft, twist, add_mul, Finset.sum_add_distrib]

/-- The NTT commutes with subtraction. -/
theorem ntt_sub (a b : Fin 256 → ZMod q_dsa) (i : Fin 256) :
    ntt (fun j => a j - b j) i = ntt a i - ntt b i := by
  simp only [ntt, ndft, dft, twist, sub_mul, Finset.sum_sub_distrib]

/-- The NTT commutes with scaling by a constant. -/
theorem ntt_const_mul (c : ZMod q_dsa) (a : Fin 256 → ZMod q_dsa) (i : Fin 256) :
    ntt (fun j => c * a j) i = c * ntt a i := by
  simp only [ntt, ndft, dft, twist, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ## The negacyclic product -/

/-- The negacyclic product of two coefficient vectors: the coefficient `k` of the
product is `∑_i ± a i * b (k - i)`, negative exactly on the wrapped indices. -/
def polyMul (a b : Fin 256 → ZMod q_dsa) : Fin 256 → ZMod q_dsa :=
  signedNegaConv a b

/-- `polyMul` is the twist-defined negacyclic convolution at `ζ`. -/
theorem negaConv_zeta (a b : Fin 256 → ZMod q_dsa) :
    negaConv zeta a b = polyMul a b :=
  negaConv_eq_signed
    (by show IsPrimitiveRoot (1753 : ZMod 8380417) 512; exact isPrimitiveRoot_1753_512) a b

/-- **The NTT diagonalises the negacyclic product**: the transform of a product is
the pointwise product of the transforms. -/
theorem ntt_polyMul (a b : Fin 256 → ZMod q_dsa) (i : Fin 256) :
    ntt (polyMul a b) i = ntt a i * ntt b i := by
  simp only [ntt, ← negaConv_zeta]
  exact mldsa_ndft_negaConv a b (bitRev8 i)

/-! ## The product in `Rq_dsa` -/

/-- `X ^ 256 = -1` in `Rq_dsa`. -/
lemma root_pow_256 : (root mldsa_poly : Rq_dsa) ^ 256 = -1 := by
  have h : (mk mldsa_poly) (X ^ 256 + 1 : (ZMod q_dsa)[X]) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  linear_combination h

/-- `coeffsToRqDsa` as a sum of scaled powers of the root. -/
lemma coeffsToRqDsa_eq_sum (cs : Fin 256 → ZMod q_dsa) :
    coeffsToRqDsa cs
      = ∑ i : Fin 256, of mldsa_poly (cs i) * (root mldsa_poly : Rq_dsa) ^ i.val := by
  unfold coeffsToRqDsa
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X]
  rfl

/-- The wrap-around sign of the negacyclic product, at the level of root powers. -/
lemma root_pow_add (i j : Fin 256) :
    (root mldsa_poly : Rq_dsa) ^ (i.val + j.val)
      = (if i.val ≤ (j + i).val then (1 : Rq_dsa) else -1)
        * (root mldsa_poly : Rq_dsa) ^ ((j + i).val) := by
  have hi := i.isLt
  have hj := j.isLt
  have hval : (j + i).val = (i.val + j.val) % 256 := by
    simp [Fin.add_def, Nat.add_comm]
  rcases lt_or_ge (i.val + j.val) 256 with h | h
  · rw [hval, Nat.mod_eq_of_lt h, ite_eq_left (by omega)]
    ring
  · have hmod : (i.val + j.val) % 256 = i.val + j.val - 256 := by omega
    rw [hval, hmod, ite_eq_right (by omega)]
    have hsplit : i.val + j.val = 256 + (i.val + j.val - 256) := by omega
    conv_lhs => rw [hsplit]
    rw [pow_add, root_pow_256]

/-- **`polyMul` is multiplication in `Rq_dsa`.** -/
theorem coeffsToRqDsa_polyMul (a b : Fin 256 → ZMod q_dsa) :
    coeffsToRqDsa (polyMul a b) = coeffsToRqDsa a * coeffsToRqDsa b := by
  rw [coeffsToRqDsa_eq_sum, coeffsToRqDsa_eq_sum, coeffsToRqDsa_eq_sum,
    Finset.sum_mul_sum]
  have hR : ∀ i j : Fin 256,
      (of mldsa_poly (a i) * (root mldsa_poly : Rq_dsa) ^ i.val)
        * (of mldsa_poly (b j) * (root mldsa_poly : Rq_dsa) ^ j.val)
      = of mldsa_poly (a i * b j) * (root mldsa_poly : Rq_dsa) ^ (i.val + j.val) := by
    intro i j; rw [map_mul, pow_add]; ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hR i j))]
  have hL : ∀ k : Fin 256,
      of mldsa_poly (polyMul a b k) * (root mldsa_poly : Rq_dsa) ^ k.val
        = ∑ i : Fin 256,
            (if i.val ≤ k.val
              then of mldsa_poly (a i * b (k - i)) * (root mldsa_poly : Rq_dsa) ^ k.val
              else -(of mldsa_poly (a i * b (k - i)) * (root mldsa_poly : Rq_dsa) ^ k.val)) := by
    intro k
    simp only [polyMul, signedNegaConv, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hc : i.val ≤ k.val <;> simp [hc, map_neg]
  rw [Finset.sum_congr rfl (fun k _ => hL k), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine (Fintype.sum_equiv (Equiv.addRight i)
    (fun j : Fin 256 =>
      (if i.val ≤ (j + i).val
        then of mldsa_poly (a i * b ((j + i) - i)) * (root mldsa_poly : Rq_dsa) ^ ((j + i)).val
        else -(of mldsa_poly (a i * b ((j + i) - i))
          * (root mldsa_poly : Rq_dsa) ^ ((j + i)).val))) _ (fun j => rfl)).symm.trans ?_
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_sub_cancel_right, root_pow_add i j]
  by_cases hc : i.val ≤ (j + i).val <;> simp [hc]

/-- **The `Rq_dsa` product through the transform**: multiplication in `Rq_dsa` is the
inverse transform of the pointwise product of the transforms. -/
theorem rqDsa_mul_eq_invNtt (a b : Fin 256 → ZMod q_dsa) :
    coeffsToRqDsa a * coeffsToRqDsa b
      = coeffsToRqDsa (invNtt (fun i => ntt a i * ntt b i)) := by
  have h : (fun i => ntt a i * ntt b i) = ntt (polyMul a b) :=
    funext (fun i => (ntt_polyMul a b i).symm)
  rw [← coeffsToRqDsa_polyMul, h, invNtt_ntt]

/-! ## Pinned constants

Each evaluation below is a permanent static check: it pins a definition in this
module against the value FIPS 204 publishes, so a change to `zeta`, to `bitRev8`
or to the ring parameters is caught where it is made. -/

/-- `BitRev8 1 = 128`. -/
theorem bitRev8_one : bitRev8 1 = 128 := by decide

/-- The first twiddle of the FIPS 204 table (Appendix B, standard domain). -/
theorem zetas_one : zetas 1 = 4808194 := by decide +kernel

/-- The inverse of the transform length used by FIPS 204 Algorithm 42. -/
theorem inv_256 : (256 : ZMod q_dsa)⁻¹ = 8347681 :=
  inv_eq_of_mul_eq_one_right (by decide)

end CatCrypt.Crypto.MLDSA.Spec.Ntt
