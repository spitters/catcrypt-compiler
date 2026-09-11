/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull
public import CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric
public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteRecursiveNtt

/-!
# Iterative radix-2 Cooley–Tukey NTT, proved equal to the recursive `nttRec`

`NTTRecursiveFull.nttRec` is the *recursive* radix-2 decimation-in-time (DIT)
number-theoretic transform: at depth `e+1` it **de-interleaves** the input into
its even- and odd-indexed sub-sequences (`evenPart`/`oddPart`), recurses at the
squared twiddle `ω²`, and butterfly-combines. That is the divide-and-conquer
form. SIMD NTT kernels instead run the *iterative* DIT form: a fixed sequence of
butterfly **layers** over contiguous blocks, applied to a **bit-reversed** copy
of the input.

This file defines that iterative form `nttIter` and proves the textbook
equivalence with `nttRec`, *including* the bit-reversal permutation that relates
the two index orders.

## Objects

* `nttIter e ω x` — the iterative DIT transform. At depth `e+1` it recurses on
  the two **contiguous halves** (`lowerHalf`/`upperHalf`) of `x` at `ω²`, then
  applies the radix-2 merge butterfly (lower output `Lₖ + ωᵏ·Uₖ`, upper output
  `Lₖ + ω^(2^e)·ωᵏ·Uₖ`). Recursing on contiguous halves — rather than `nttRec`'s
  even/odd de-interleave — is exactly the layer-fold an in-place iterative kernel
  performs once its input has been bit-reversed.

## Main theorem

`nttIter_comp_bitrev (e) (ω) (x) (k) :`
`    nttIter e ω (fun j => x ((bitrevPerm e) j)) k = nttRec e ω x k`

i.e. running the iterative transform on the **bit-reversed** input reproduces the
recursive transform on the natural-order input. The bit-reversal is *not* papered
over: it appears explicitly, and the proof is an induction on `e` that uses the
single structural fact relating bit-reversal at width `e+1` to de-interleaving and
bit-reversal at width `e` (`bitrev_succ_*`). Re-arranged, the iterative transform
on natural input equals the recursive transform on the bit-reversed input
(`nttIter_eq_nttRec_comp_bitrev`).

## Corollaries

* `nttIter_comp_bitrev_eq_dft` — `nttIter` on bit-reversed input computes the
  definitional `dft` (via `nttRec_eq_dft`).
* `mlkem_nttIter_eq_dft` — the ML-KEM instantiation (`ZMod 3329`, `e = 8`,
  `ω = 17`), via `mlkem_nttRec_eq_dft` + the primitive-root fact.

## Scope

This proves the in-Lean **NTT-algorithm** correctness: the iterative
Cooley–Tukey transform equals the recursive one (hence the `dft`), with the
bit-reversal index permutation made explicit. It does **not** tie the SIMD emit's
machine bytes, nor the lane↔coefficient memory layout, to this spec — that
remains KAT-gated. This file is the *semantic specification* that the
emit-denotation step will later target (replacing the current `:= id` placeholder
spec).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec

open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull
open CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric

variable {R : Type*} [CommRing R]

/-! ## Contiguous halves of a length-`2^(e+1)` input -/

/-- Lower contiguous half of a length-`2^(e+1)` input: `(lowerHalf x) i = x i`. -/
def lowerHalf (e : ℕ) (x : Fin (2 ^ (e + 1)) → R) (i : Fin (2 ^ e)) : R :=
  x ⟨i.val, by have := i.isLt; have h2 : (2:ℕ) ^ (e+1) = 2 * 2 ^ e := by rw [pow_succ]; ring
               omega⟩

/-- Upper contiguous half of a length-`2^(e+1)` input:
`(upperHalf x) i = x (i + 2^e)`. -/
def upperHalf (e : ℕ) (x : Fin (2 ^ (e + 1)) → R) (i : Fin (2 ^ e)) : R :=
  x ⟨i.val + 2 ^ e, by have := i.isLt; have h2 : (2:ℕ) ^ (e+1) = 2 * 2 ^ e := by rw [pow_succ]; ring
                       omega⟩

/-! ## The iterative radix-2 DIT NTT -/

/-- The iterative radix-2 decimation-in-time NTT on a length-`2^e` input.

* `e = 0`: the length-1 transform is the identity.
* `e + 1`: recurse the iterative transform at `ω²` on the two **contiguous
  halves** (`lowerHalf`/`upperHalf`), then radix-2 merge-butterfly. Output index
  `k` is routed by whether `k.val < 2^e` (lower output, twiddle `ωᵏ`) or not
  (upper output, twiddle `ω^(2^e)·ωᵏ`).

Recursing on contiguous halves — instead of `nttRec`'s even/odd de-interleave —
is precisely the layer fold an in-place iterative kernel performs on a
bit-reversed input. -/
def nttIter : (e : ℕ) → R → (Fin (2 ^ e) → R) → (Fin (2 ^ e) → R)
  | 0, _, x => x
  | (e + 1), ω, x => fun k =>
    let L := nttIter e (ω ^ 2) (lowerHalf e x)
    let U := nttIter e (ω ^ 2) (upperHalf e x)
    if h : k.val < 2 ^ e then
      L ⟨k.val, h⟩ + ω ^ k.val * U ⟨k.val, h⟩
    else
      L ⟨k.val - 2 ^ e, by
            have hk : k.val < 2 ^ (e + 1) := k.isLt
            have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
            omega⟩
        + ω ^ (2 ^ e) * ω ^ (k.val - 2 ^ e)
            * U ⟨k.val - 2 ^ e, by
                have hk : k.val < 2 ^ (e + 1) := k.isLt
                have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
                omega⟩

/-! ## Bit-reversal structural facts: how `bitrev` at width `e+1` relates to
de-interleaving and `bitrev` at width `e`. These are the single algebraic
ingredients of the main induction: reversing one extra (top) bit turns the
contiguous-half split (`lowerHalf`/`upperHalf`) into the even/odd de-interleave
(`evenPart`/`oddPart`). -/

/-- The `(e+1)`-bit list of `i` is the `e`-bit list with the top bit appended. -/
theorem toBits_snoc (w i : ℕ) : toBits (w + 1) i = toBits w i ++ [i.testBit w] := by
  simp [toBits, List.range_succ]

/-- Adding `2^e` to `i < 2^e` leaves the bottom `e` bits unchanged. -/
theorem toBits_add_pow (e i : ℕ) (_h : i < 2 ^ e) : toBits e (i + 2 ^ e) = toBits e i := by
  unfold toBits
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hk]

/-- **Lower half ↦ even.** For `i < 2^e`, reversing the `(e+1)`-bit representation
of `i` doubles the `e`-bit reversal: `bitrev (e+1) i = 2 · bitrev e i`. (The new
top bit is `0`, becoming the new least-significant bit after reversal.) -/
theorem bitrev_succ_lower (e i : ℕ) (h : i < 2 ^ e) :
    bitrev (e + 1) i = 2 * bitrev e i := by
  have hbit : i.testBit e = false := Nat.testBit_lt_two_pow (by simpa using h)
  unfold bitrev
  rw [toBits_snoc, hbit]
  simp [List.reverse_append, fromBits]

/-- **Upper half ↦ odd.** For `i < 2^e`, reversing the `(e+1)`-bit representation
of `i + 2^e` gives `2 · bitrev e i + 1`. (The new top bit is `1`, becoming the
new least-significant bit after reversal.) -/
theorem bitrev_succ_upper (e i : ℕ) (h : i < 2 ^ e) :
    bitrev (e + 1) (i + 2 ^ e) = 2 * bitrev e i + 1 := by
  have hbit : (i + 2 ^ e).testBit e = true := by
    rw [Nat.add_comm]; simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow, h]
  unfold bitrev
  rw [toBits_snoc, hbit, toBits_add_pow e i h]
  simp [List.reverse_append, fromBits]
  ring

omit [CommRing R] in
/-- The contiguous lower half of a bit-reversed length-`2^(e+1)` input is the
even-indexed sub-sequence of the bit-reversed half-width reindex: the extra top
bit, after reversal, becomes the new least-significant `0`. -/
@[simp] theorem lowerHalf_bitrev (e : ℕ) (x : Fin (2 ^ (e + 1)) → R) :
    lowerHalf e (fun j => x ((bitrevPerm (e + 1)) j))
      = (fun j => (evenPart (reindex e x)) ((bitrevPerm e) j)) := by
  funext i
  simp only [lowerHalf, bitrevPerm, Function.Involutive.coe_toPerm, bitrevFin,
    evenPart, reindex]
  congr 1
  apply Fin.ext
  simp [bitrev_succ_lower e i.val i.isLt]

omit [CommRing R] in
/-- The contiguous upper half of a bit-reversed length-`2^(e+1)` input is the
odd-indexed sub-sequence of the bit-reversed half-width reindex: the extra top
bit, after reversal, becomes the new least-significant `1`. -/
@[simp] theorem upperHalf_bitrev (e : ℕ) (x : Fin (2 ^ (e + 1)) → R) :
    upperHalf e (fun j => x ((bitrevPerm (e + 1)) j))
      = (fun j => (oddPart (reindex e x)) ((bitrevPerm e) j)) := by
  funext i
  simp only [upperHalf, bitrevPerm, Function.Involutive.coe_toPerm, bitrevFin,
    oddPart, reindex]
  congr 1
  apply Fin.ext
  simp [bitrev_succ_upper e i.val i.isLt]

/-! ## Main theorem: iterative-on-bit-reversed = recursive -/

/-- **Iterative = recursive, with bit-reversal.** Running the iterative DIT
transform on the **bit-reversed** input reproduces the recursive DIT transform on
the natural-order input. The bit-reversal permutation is explicit.

Proof by induction on the depth `e`. The base case `e = 0` is `rfl` (length-1
transform). At `e + 1`, the iterative transform recurses on the contiguous halves
`lowerHalf`/`upperHalf` of the bit-reversed input; `bitrev_succ_lower` and
`bitrev_succ_upper` identify those exactly with the even- and odd-indexed
sub-sequences (`evenPart`/`oddPart` of the `Fin (2·2^e)` reindex) of the
bit-reversed *half*-width input. The induction hypothesis then turns the two
half-iteratives into the two half-recursives `nttRec e (ω²) ·`, and the merge
butterfly is shared verbatim by both definitions. -/
theorem nttIter_comp_bitrev :
    ∀ (e : ℕ) (ω : R) (x : Fin (2 ^ e) → R) (k : Fin (2 ^ e)),
      nttIter e ω (fun j => x ((bitrevPerm e) j)) k = nttRec e ω x k := by
  intro e
  induction e with
  | zero =>
    intro ω x k
    show x ((bitrevPerm 0) k) = x k
    congr 1
    apply Fin.ext
    simp [bitrevPerm, bitrevFin, bitrev]
  | succ e ih =>
    intro ω x k
    simp only [nttIter, lowerHalf_bitrev, upperHalf_bitrev, nttRec, ih]

/-- The main theorem re-arranged: the iterative transform on the **natural-order**
input equals the recursive transform on the **bit-reversed** input. (Follows from
`nttIter_comp_bitrev` by substituting the bit-reversed input and cancelling the
involution `bitrevPerm`.) -/
theorem nttIter_eq_nttRec_comp_bitrev (e : ℕ) (ω : R) (x : Fin (2 ^ e) → R)
    (k : Fin (2 ^ e)) :
    nttIter e ω x k = nttRec e ω (fun j => x ((bitrevPerm e) j)) k := by
  have h := nttIter_comp_bitrev e ω (fun j => x ((bitrevPerm e) j)) k
  rw [← h]
  congr 1
  funext j
  simp only [bitrevPerm, Function.Involutive.coe_toPerm, bitrevFin_involutive e j]

/-! ## Corollary: the iterative NTT computes the DFT -/

/-- **Iterative NTT computes the DFT.** With `ω` a `2^e`-th root of unity, the
iterative DIT transform on the bit-reversed input computes the definitional
length-`2^e` transform `dft`. Chains `nttIter_comp_bitrev` with
`NTTRecursiveFull.nttRec_eq_dft`. -/
theorem nttIter_comp_bitrev_eq_dft (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = 1)
    (x : Fin (2 ^ e) → R) (k : Fin (2 ^ e)) :
    nttIter e ω (fun j => x ((bitrevPerm e) j)) k = dft (2 ^ e) ω x k := by
  rw [nttIter_comp_bitrev e ω x k, nttRec_eq_dft e ω hω x k]

/-! ## ML-KEM instantiation (`ZMod 3329`, `e = 8`, `ω = 17`) -/

open CatCrypt.Crypto.Optimizer.Lattice.ConcreteRecursiveNtt in
/-- **ML-KEM iterative NTT computes the DFT.** At the ML-KEM parameters
(`ZMod 3329`, length `2^8 = 256`, root `ω = 17`), the iterative DIT transform on
the bit-reversed input computes the length-256 DFT. Instantiation of
`nttIter_comp_bitrev` tied to the recursive ML-KEM result `mlkem_nttRec_eq_dft`. -/
theorem mlkem_nttIter_eq_dft (x : Fin (2 ^ 8) → ZMod 3329) (k : Fin (2 ^ 8)) :
    nttIter 8 (17 : ZMod 3329) (fun j => x ((bitrevPerm 8) j)) k
      = dft (2 ^ 8) (17 : ZMod 3329) x k := by
  rw [nttIter_comp_bitrev 8 (17 : ZMod 3329) x k, mlkem_nttRec_eq_dft x k]

end CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec
