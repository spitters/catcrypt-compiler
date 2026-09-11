/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass
public import CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec
public import CatCrypt.Crypto.Optimizer.Lattice.MlkemNttLayout
public import CatCrypt.Crypto.Optimizer.Lattice.NTTConvolutionTheorem
public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots

/-!
# The ML-KEM NTT butterfly stage computes the number-theoretic transform

The emitted ML-KEM-768 forward NTT
(`SecureCompilation/VIR/LatticeNttEmit.lean`, §6b) runs the in-place iterative
Cooley–Tukey transform as a fixed sequence of radix-2 butterfly **stages**. This
file gives the value-level model of one such stage over the coefficient ring
`ZMod 3329`, ties it to the proven butterfly `ctButterfly` of
`NTTButterflyPass`, and composes the stage sequence to the definitional
`dft`/polynomial-evaluation specification of `NTTConvolutionTheorem`.

## The stage object

`ctMergeStage e ω L U` assembles one length-`2^(e+1)` merge stage from the two
half-length transforms `L`, `U`. Each output pair `(k, k + 2^e)` is one
`ctButterfly (ω^k) (L k) (U k) = (L k + ω^k · U k, L k − ω^k · U k)`.

`nttIter_succ_eq_ctMergeStage` proves this stage is exactly the outer step of the
iterative transform `nttIter` (from `IterativeNttEqRec`), under the negacyclic
condition `ω^(2^e) = −1`. `ctMergeStage_butterfly` reads off the atomic per-pair
step: the two stage outputs at indices `k` and `k + 2^e` are the two lanes of one
`ctButterfly`.

## Composition to the transform

`nttIter` is proved equal to the recursive transform and to `dft` in
`IterativeNttEqRec`. Chaining that with `dft_eq_polyEval`, the whole ML-KEM
transform — every stage of which is a `ctButterfly` bank by the above — computes
the polynomial evaluation `Σⱼ xⱼ · (ωᵏ)ʲ` at each output index, up to the
decimation-in-time bit-reversal permutation `bitrevPerm 8`
(`MlkemNttLayout.mlkemNttStorageLayout` is the identity storage layout, so the
only index permutation is `bitrevPerm 8`).

## Scope

The reduction is: emitted stage sequence ≡ `nttIter` value model
(`nttIter_succ_eq_ctMergeStage`, per stage) ≡ `dft`
(`IterativeNttEqRec.mlkem_nttIter_eq_dft`) ≡ polynomial evaluation
(`dft_eq_polyEval`). The single link not established in Lean is the equality
between the `.jazz` string produced by `emitMlkemNttFull16wayJazz` and this
value-level `nttIter` model: there is no `Com`/machine denotation of the emitted
string to rewrite against, so that one step remains checked by the bench-level
byte-KAT against `PQCLEAN_MLKEM768_CLEAN_ntt`. Everything algebraic below is a
machine-checked proof.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NttEmitDenotationBridge

open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass
open CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTConvolutionTheorem

variable {R : Type*} [CommRing R]

/-! ## 1. The radix-2 merge stage as a bank of `ctButterfly` -/

/-- One length-`2^(e+1)` Cooley–Tukey merge stage, assembled from the two
half-length transforms `L`, `U`. For each `k < 2^e` the low output at index `k`
and the high output at index `k + 2^e` are the two lanes of the butterfly
`ctButterfly (ω^k) (L k) (U k) = (L k + ω^k · U k, L k − ω^k · U k)`. This is the
`(a, b, ω) ↦ (a + ω·b, a − ω·b)` map assembled across the `2^(e+1)` coefficients
of a stage. -/
def ctMergeStage (e : ℕ) (ω : R) (L U : Fin (2 ^ e) → R) :
    Fin (2 ^ (e + 1)) → R := fun k =>
  if h : k.val < 2 ^ e then
    (ctButterfly (ω ^ k.val) (L ⟨k.val, h⟩) (U ⟨k.val, h⟩)).1
  else
    (ctButterfly (ω ^ (k.val - 2 ^ e))
        (L ⟨k.val - 2 ^ e, by
          have hk : k.val < 2 ^ (e + 1) := k.isLt
          have _he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
          omega⟩)
        (U ⟨k.val - 2 ^ e, by
          have hk : k.val < 2 ^ (e + 1) := k.isLt
          have _he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
          omega⟩)).2

/-- **Atomic step.** The two outputs of one merge stage at indices `k` and
`k + 2^e` are the two lanes of a single Cooley–Tukey butterfly with twiddle
`ω^k` on the half-transform values `L k`, `U k`. -/
theorem ctMergeStage_butterfly (e : ℕ) (ω : R) (L U : Fin (2 ^ e) → R)
    (k : Fin (2 ^ e)) :
    (ctMergeStage e ω L U ⟨k.val, by
        have hk : k.val < 2 ^ e := k.isLt
        have _he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
        omega⟩,
      ctMergeStage e ω L U ⟨k.val + 2 ^ e, by
        have hk : k.val < 2 ^ e := k.isLt
        have _he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
        omega⟩)
      = ctButterfly (ω ^ k.val) (L k) (U k) := by
  have hlo : k.val < 2 ^ e := k.isLt
  have hhi : ¬ (k.val + 2 ^ e < 2 ^ e) := by omega
  refine Prod.ext ?_ ?_
  · simp only [ctMergeStage, dif_pos hlo]
  · simp only [ctMergeStage, dif_neg hhi]
    have hsub : k.val + 2 ^ e - 2 ^ e = k.val := by omega
    simp only [hsub]

/-- **The merge stage is the outer step of `nttIter`.** Under the negacyclic
condition `ω^(2^e) = −1`, the length-`2^(e+1)` iterative transform equals one
`ctMergeStage` applied to the two half-length transforms of the contiguous
halves. Together with `ctMergeStage_butterfly` this exhibits every stage of the
iterative transform as a bank of `ctButterfly` operations. -/
theorem nttIter_succ_eq_ctMergeStage (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1)
    (x : Fin (2 ^ (e + 1)) → R) :
    nttIter (e + 1) ω x
      = ctMergeStage e ω (nttIter e (ω ^ 2) (lowerHalf e x))
          (nttIter e (ω ^ 2) (upperHalf e x)) := by
  funext k
  simp only [nttIter, ctMergeStage]
  by_cases h : k.val < 2 ^ e
  · simp only [dif_pos h, ctButterfly_fst]
  · simp only [dif_neg h, ctButterfly_snd]
    rw [hω]
    ring

/-! ## 2. ML-KEM instantiation -/

/-- `(17 : ZMod 3329)^128 = −1`. Derived from `17^256 = 1` and `17^128 ≠ 1`
(`ConcreteNttRoots`): in the field `ZMod 3329`, `(17^128)^2 = 17^256 = 1` forces
`17^128 ∈ {1, −1}`, and it is not `1`. -/
theorem mlkem_omega_pow_128 : (17 : ZMod 3329) ^ 128 = -1 := by
  have hsq : (17 : ZMod 3329) ^ 128 * (17 : ZMod 3329) ^ 128 = 1 := by
    rw [← pow_add]; exact ConcreteNttRoots.pow_256_17_eq_one
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h ConcreteNttRoots.pow_128_17_ne_one
  · exact h

open CatCrypt.Crypto.Optimizer.Lattice.MlkemNttLayout in
/-- **ML-KEM top-stage recursion.** The length-256 ML-KEM forward NTT
(`nttIter 8 17`) is the length-256 merge stage applied to the two length-128
iterative transforms of the contiguous input halves. The negacyclic twiddle
condition `17^(2^7) = 17^128 = −1` is `mlkem_omega_pow_128`. Iterating this down
the recursion exhibits the full transform as a sequence of `ctButterfly`
stages. -/
theorem mlkem_nttIter_succ_eq_ctMergeStage (x : Fin (2 ^ 8) → ZMod 3329) :
    nttIter 8 (17 : ZMod 3329) x
      = ctMergeStage 7 (17 : ZMod 3329)
          (nttIter 7 ((17 : ZMod 3329) ^ 2) (lowerHalf 7 x))
          (nttIter 7 ((17 : ZMod 3329) ^ 2) (upperHalf 7 x)) :=
  nttIter_succ_eq_ctMergeStage 7 (17 : ZMod 3329) mlkem_omega_pow_128 x

/-! ## 3. Composition to the `dft` / polynomial-evaluation spec -/

/-- **The ML-KEM stage sequence computes the DFT (polynomial-evaluation form).**
Running the iterative transform — every stage of which is a `ctButterfly` bank by
`mlkem_nttIter_succ_eq_ctMergeStage` and `ctMergeStage_butterfly` — on the
bit-reversed input evaluates, at each output index `k`, the coefficient
polynomial of `x` at the point `(17^k)`:

  `nttIter 8 17 (x ∘ bitrevPerm 8) k = Σⱼ xⱼ · (17^k)ʲ`.

Chains `IterativeNttEqRec.mlkem_nttIter_eq_dft` (stage sequence ≡ `dft`) with
`NTTConvolutionTheorem.dft_eq_polyEval` (`dft` ≡ multi-point polynomial
evaluation). The bit-reversal `bitrevPerm 8` is the decimation-in-time
transform-order permutation; the storage layout is the identity
(`MlkemNttLayout.mlkemNttStorageLayout_apply`). -/
theorem mlkem_ntt_eq_polyEval (x : Fin (2 ^ 8) → ZMod 3329) (k : Fin (2 ^ 8)) :
    nttIter 8 (17 : ZMod 3329)
        (fun j => x ((BitReversalGeneric.bitrevPerm 8) j)) k
      = ∑ j : Fin (2 ^ 8), x j * ((17 : ZMod 3329) ^ k.val) ^ j.val := by
  rw [mlkem_nttIter_eq_dft x k]
  exact dft_eq_polyEval (2 ^ 8) (17 : ZMod 3329) x k

open CatCrypt.Crypto.Optimizer.Lattice.MlkemNttLayout in
/-- **The kernel spec computes the DFT (polynomial-evaluation form).** The
whole-transform specification `mlkemNttKernelSpec` the emit must satisfy, run on
the bit-reversed input, evaluates the coefficient polynomial of `x` at `17^k`.
This is the emit's target spec (`MlkemNttLayout.mlkemNttKernelSpec`) reduced to
`NTTConvolutionTheorem`'s polynomial-evaluation identity. -/
theorem mlkemNttKernelSpec_eq_polyEval (x : Fin (2 ^ 8) → ZMod 3329)
    (k : Fin (2 ^ 8)) :
    mlkemNttKernelSpec (fun j => x ((BitReversalGeneric.bitrevPerm 8) j)) k
      = ∑ j : Fin (2 ^ 8), x j * (mlkemOmega ^ k.val) ^ j.val := by
  have hω : mlkemOmega ^ (2 ^ 8) = 1 := by
    have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
    rw [h256]; exact ConcreteNttRoots.pow_256_17_eq_one
  rw [mlkemNttKernelSpec_bitrev_eq_dft x hω k]
  exact dft_eq_polyEval (2 ^ 8) mlkemOmega x k

end CatCrypt.Crypto.Optimizer.Lattice.NttEmitDenotationBridge
