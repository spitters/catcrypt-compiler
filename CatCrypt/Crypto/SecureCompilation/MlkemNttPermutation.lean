/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull

/-!
# The single-layer even/odd deinterleave permutation of the OWNED ML-KEM NTT

`MlkemNttFullTie.lean` closed the *arithmetic* recursion of the owned
Montgomery NTT (`dft256_is_iterated_owned_combine` : the abstract `dft 256` is an
8-fold iteration of the owned `combine2` atom) and the *Montgomery domain*
composition across stages.  Its open item is the
**butterfly-position permutation** that routes one Cooley–Tukey layer's output
addressing into the next layer's `evenPart` / `oddPart` operand layout — the
even/odd deinterleave that, iterated across `log₂ 256 = 8` layers, is the
ML-KEM NTT's bit-reversal.

This module supplies **one layer** of that combinatorics:

1. The single-layer even/odd **deinterleave permutation** `deinterleave n :
   Fin (2 * n) → Fin (2 * n)`, mapping a *blocked* layout `[evens ‖ odds]` onto
   the *interleaved* layout the next `nttRec` layer's `evenPart` / `oddPart`
   index split reads.  Its inverse `interleave n` is given explicitly, and the
   two are packaged as an `Equiv` `deinterleaveEquiv n` — so `deinterleave` is a
   **bijection** of `Fin (2 * n)` (`deinterleave_bijective`).

2. A single-layer **routing lemma** `deinterleave_routes_even_odd`: precomposing
   any `x : Fin (2 * n) → R` with `deinterleave n` lands the even-indexed
   sub-sequence (`evenPart x`) on the **lower** half `[0, n)` and the
   odd-indexed sub-sequence (`oddPart x`) on the **upper** half `[n, 2n)` of the
   result — exactly the `[E ‖ O]` operand layout `nttRec (e+1)`'s split consumes
   (`reindex` / `evenPart` / `oddPart` of `NTTRecursiveFull`).  So one layer's
   deinterleave realises one layer's even/odd routing.

## Scope — what is and is NOT closed

CLOSED here:

* the single-layer deinterleave is a **bijection** of `Fin (2 * n)`
  (`deinterleave_bijective`, via the explicit two-sided inverse `interleave`);
* applying it routes `evenPart` to the lower half and `oddPart` to the upper
  half (`deinterleave_routes_even_odd`, `deinterleave_lower_is_even`,
  `deinterleave_upper_is_odd`) — **one** layer of the even/odd wiring.

NOT closed (the precisely-named remaining mechanical step):

* **iterating** the single-layer deinterleave across the `log₂ 256 = 8` layers
  to assemble the full ML-KEM **bit-reversal** permutation, and tying that
  8-fold composite to the owned register/lane addressing across all 8 stages.
  The single-layer permutation and its routing are proved here; the 8-fold
  composition (a mechanical induction on layer depth, threading the half-size
  `n = 2^k` at each layer) is the named open work.

No `jasminc_preserves_ct` appears in any theorem here.

## References
* NIST FIPS 203 (ML-KEM); Cooley & Tukey 1965 (radix-2 FFT, bit-reversal).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MlkemNttPermutation

open CatCrypt.Crypto.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull

/-! ## §1  The single-layer even/odd deinterleave permutation -/

/-- The single-layer even/odd **deinterleave** map on `Fin (2 * n)`.  The lower
half `[0, n)` is sent to the even positions `2·j`, the upper half `[n, 2n)` to
the odd positions `2·(j - n) + 1`.  Precomposing a vector with this map gathers
the even-indexed entries into the lower half and the odd-indexed entries into the
upper half — the `[evens ‖ odds]` layout the next `nttRec` layer consumes. -/
def deinterleave (n : ℕ) (j : Fin (2 * n)) : Fin (2 * n) :=
  if h : j.val < n then ⟨2 * j.val, by omega⟩
  else ⟨2 * (j.val - n) + 1, by omega⟩

/-- The inverse single-layer **interleave** map on `Fin (2 * n)`: an even index
`2·i` comes from lower slot `i`, an odd index `2·i+1` from upper slot `n + i`. -/
def interleave (n : ℕ) (j : Fin (2 * n)) : Fin (2 * n) :=
  if j.val % 2 = 0 then ⟨j.val / 2, by omega⟩
  else ⟨n + j.val / 2, by omega⟩

theorem interleave_deinterleave (n : ℕ) (j : Fin (2 * n)) :
    interleave n (deinterleave n j) = j := by
  apply Fin.ext
  unfold deinterleave
  by_cases h : j.val < n
  · rw [dite_eq_left h]
    unfold interleave
    rw [ite_eq_left (by simp only []; omega)]
    simp only []; omega
  · rw [dite_eq_right h]
    unfold interleave
    rw [ite_eq_right (by simp only []; omega)]
    simp only []; omega

theorem deinterleave_interleave (n : ℕ) (j : Fin (2 * n)) :
    deinterleave n (interleave n j) = j := by
  apply Fin.ext
  unfold interleave
  by_cases h : j.val % 2 = 0
  · rw [ite_eq_left h]
    unfold deinterleave
    rw [dite_eq_left (by simp only []; omega)]
    simp only []; omega
  · rw [ite_eq_right h]
    unfold deinterleave
    rw [dite_eq_right (by simp only []; omega)]
    simp only []; omega

/-- The single-layer even/odd deinterleave is an `Equiv` of `Fin (2 * n)` — its
explicit inverse is `interleave`. -/
def deinterleaveEquiv (n : ℕ) : Fin (2 * n) ≃ Fin (2 * n) where
  toFun := deinterleave n
  invFun := interleave n
  left_inv := interleave_deinterleave n
  right_inv := deinterleave_interleave n

/-- **The single-layer deinterleave is a bijection** of `Fin (2 * n)`. -/
theorem deinterleave_bijective (n : ℕ) : Function.Bijective (deinterleave n) :=
  (deinterleaveEquiv n).bijective

/-! ## §2  The single-layer routing lemma -/

/-- **Lower half is the even sub-sequence.**  For a lower slot `i < n`, the
deinterleaved vector reads the `2i`-th entry — exactly `evenPart x i`. -/
theorem deinterleave_lower_is_even {R : Type*} [CommRing R] (n : ℕ)
    (x : Fin (2 * n) → R) (i : Fin n) :
    (x ∘ deinterleave n) ⟨i.val, by omega⟩ = evenPart x i := by
  simp only [Function.comp, deinterleave, evenPart]
  have h : (⟨i.val, by omega⟩ : Fin (2 * n)).val < n := i.isLt
  simp only [h, dite_eq_left]

/-- **Upper half is the odd sub-sequence.**  For an upper slot `n + i`, the
deinterleaved vector reads the `2i+1`-th entry — exactly `oddPart x i`. -/
theorem deinterleave_upper_is_odd {R : Type*} [CommRing R] (n : ℕ)
    (x : Fin (2 * n) → R) (i : Fin n) :
    (x ∘ deinterleave n) ⟨n + i.val, by omega⟩ = oddPart x i := by
  simp only [Function.comp, oddPart]
  unfold deinterleave
  rw [dite_eq_right (by simp only []; omega)]
  congr 1
  apply Fin.ext
  simp only []
  omega

/-- **Single-layer even/odd routing.**  Precomposing `x` with the deinterleave
permutation puts `evenPart x` on the lower half `[0, n)` and `oddPart x` on the
upper half `[n, 2n)` — the `[E ‖ O]` operand layout the next `nttRec` layer's
`evenPart` / `oddPart` index split consumes.  This is one layer of the owned
NTT's even/odd butterfly routing, realised by the bijection of §1. -/
theorem deinterleave_routes_even_odd {R : Type*} [CommRing R] (n : ℕ)
    (x : Fin (2 * n) → R) :
    (∀ i : Fin n, (x ∘ deinterleave n) ⟨i.val, by omega⟩ = evenPart x i) ∧
    (∀ i : Fin n, (x ∘ deinterleave n) ⟨n + i.val, by omega⟩ = oddPart x i) :=
  ⟨deinterleave_lower_is_even n x, deinterleave_upper_is_odd n x⟩

end CatCrypt.Crypto.SecureCompilation.MlkemNttPermutation
