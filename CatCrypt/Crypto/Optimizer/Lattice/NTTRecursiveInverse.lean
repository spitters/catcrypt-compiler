/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull
public import CatCrypt.Crypto.Optimizer.Lattice.NTTFullInversionGeneric

/-!
# Recursive (butterfly-network) inverse NTT

`NTTRecursiveFull` defines the concrete radix-2 butterfly recursion `nttRec` and
proves it computes the abstract `dft` (`nttRec_eq_dft`). `NTTFullInversionGeneric`
defines the abstract synthesis map `idft` and proves it inverts the forward
transform (`idft_dft`). This module defines a *concrete* inverse transform — a
butterfly network — and proves it equals `idft` and inverts the recursive forward
NTT.

## The algebraic observation

`idft n ω X k = (n)⁻¹ · dft n (ω⁻¹) X k`: the synthesis sum
`∑ⱼ Xⱼ (ω⁻¹)^(j·k)` is *literally* `dft n (ω⁻¹) X k`, so `idft` is just the
forward transform at the inverse root, scaled by `(n)⁻¹`. This is the bridge
lemma `idft_eq_scaled_dft`, proved by unfolding both definitions.

## The recursive inverse

`nttRecInv e ω X = (2^e)⁻¹ · nttRec e (ω⁻¹) X`. Running the same butterfly
network `nttRec` at the inverse twiddle `ω⁻¹` is the decimation-in-frequency
inverse network, and the `(2^e)⁻¹` factor is the normalisation.

## Main results

* `nttRecInv_eq_idft` — the recursive inverse equals the abstract `idft`. By
  `nttRec_eq_dft` (at `ω⁻¹`, whose root-of-unity premise comes from `inv_pow`)
  and the bridge lemma.
* `nttRecInv_nttRec` — round trip: `nttRecInv` undoes the forward `nttRec`. By
  reducing both concrete transforms to their abstract counterparts and invoking
  `idft_dft`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveInverse

open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull
open CatCrypt.Crypto.Optimizer.Lattice.NTTFullInversionGeneric

variable {R : Type*} [Field R]

/-- **The synthesis map is a scaled forward transform at the inverse root.** The
sum defining `idft n ω X k`, namely `∑ⱼ Xⱼ (ω⁻¹)^(j·k)`, is exactly the forward
transform `dft n (ω⁻¹) X k`; the only extra ingredient in `idft` is the `(n)⁻¹`
normalisation. -/
theorem idft_eq_scaled_dft (n : ℕ) (ω : R) (X : Fin n → R) (k : Fin n) :
    idft n ω X k = (n : R)⁻¹ * dft n (ω⁻¹) X k := by
  simp only [idft, dft]

/-- The **recursive (butterfly-network) inverse NTT** on a length-`2^e` input:
run the forward butterfly recursion `nttRec` at the inverse twiddle `ω⁻¹`, then
normalise by `(2^e)⁻¹`. This is an inverse butterfly network — `nttRec`
at `ω⁻¹` is the inverse decimation network and `(2^e)⁻¹` the scaling. -/
noncomputable def nttRecInv (e : ℕ) (ω : R) (X : Fin (2 ^ e) → R) :
    Fin (2 ^ e) → R :=
  fun k => ((2 ^ e : ℕ) : R)⁻¹ * nttRec e (ω⁻¹) X k

/-- **The recursive inverse NTT computes the abstract `idft`.** For a `2^e`-th
root of unity `ω`, the butterfly network `nttRecInv` agrees with the synthesis
map `idft`:

`nttRecInv e ω X k = idft (2^e) ω X k`.

The forward recursion at `ω⁻¹` equals `dft (2^e) (ω⁻¹)` by `nttRec_eq_dft` (its
root-of-unity premise `(ω⁻¹)^(2^e) = 1` follows from `ω^(2^e) = 1` via
`inv_pow`), and `idft_eq_scaled_dft` rewrites `idft` into the matching scaled
forward transform. -/
theorem nttRecInv_eq_idft (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = 1)
    (X : Fin (2 ^ e) → R) (k : Fin (2 ^ e)) :
    nttRecInv e ω X k = idft (2 ^ e) ω X k := by
  have hinv : (ω⁻¹) ^ (2 ^ e) = 1 := by rw [inv_pow, hω, inv_one]
  rw [nttRecInv, nttRec_eq_dft e (ω⁻¹) hinv X k, idft_eq_scaled_dft]

/-- **Round trip: the recursive inverse undoes the recursive forward NTT.** For
`ω` a primitive `2^e`-th root of unity over a field with `((2^e : ℕ) : R) ≠ 0`,

`nttRecInv e ω (nttRec e ω x) = x`.

Both concrete transforms are reduced to their abstract counterparts —
`nttRecInv` to `idft` (`nttRecInv_eq_idft`) and the inner `nttRec` to `dft`
(`nttRec_eq_dft`, pointwise via `funext`) — and the abstract inversion theorem
`idft_dft` closes the result. -/
theorem nttRecInv_nttRec (e : ℕ) (ω : R) (hω : IsPrimitiveRoot ω (2 ^ e))
    (hn : ((2 ^ e : ℕ) : R) ≠ 0) (x : Fin (2 ^ e) → R) :
    nttRecInv e ω (nttRec e ω x) = x := by
  have hω1 : ω ^ (2 ^ e) = 1 := hω.pow_eq_one
  funext k
  rw [nttRecInv_eq_idft e ω hω1 (nttRec e ω x) k]
  have hfun : nttRec e ω x = dft (2 ^ e) ω x := by
    funext j; exact nttRec_eq_dft e ω hω1 x j
  rw [hfun]
  exact congrFun (idft_dft hω hn x) k

end CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveInverse
