/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass

/-!
# Full recursive radix-2 NTT, proved equal to the DFT

`NTTRecursionPass` proves the *single* Cooley–Tukey decimation-in-time recursion
step (`dft_even_odd_split` for the lower half, `dft_upper_split` for the upper
half) over a generic commutative ring `R`. This file iterates that step: it
defines the **full recursive radix-2 number-theoretic transform** `nttRec` on
length-`2^e` inputs and proves it computes the definitional `dft`, by induction
on the recursion depth `e`.

## Objects

* `nttRec e ω x` — the radix-2 decimation-in-time transform of a length-`2^e`
  input `x : Fin (2^e) → R` at twiddle `ω`. The base case `e = 0` is the
  identity (a length-1 transform). The step at depth `e+1` splits `x` into its
  even- and odd-indexed sub-sequences (`evenPart` / `oddPart` of
  `NTTRecursionPass`), recurses on each at the squared twiddle `ω²` and depth
  `e`, and combines the two half-transforms with the radix-2 butterfly:

  - lower-half output `k < 2^e`:   `Eₖ + ωᵏ·Oₖ`;
  - upper-half output `k + 2^e`:   `Eₖ + ω^(2^e)·ωᵏ·Oₖ`.

## Main theorem

`nttRec_eq_dft (e) (ω) (hω : ω ^ (2^e) = 1) (x) (k) :`
`    nttRec e ω x k = dft (2^e) ω x k`

proved by induction on `e`. The inductive step is exactly `dft_even_odd_split`
(lower half) and `dft_upper_split` (upper half) applied to the two recursive
calls, which by the induction hypothesis already equal the half-DFTs `E`, `O`.
The root-of-unity hypothesis `ω ^ (2^e) = 1` threads through the halving: at
depth `e+1` it provides `(ω²) ^ (2^e) = ω ^ (2^(e+1)) = 1` for the recursive
calls and `ω ^ (2 · 2^e) = 1` for `dft_upper_split`.

## Index bookkeeping

The only friction is `2^(e+1) = 2 · 2^e`: `evenPart` / `oddPart` and the split
lemmas are stated over `Fin (2 * n)`, while `nttRec` is indexed by `Fin (2^e)`.
We bridge with `pow_succ'` (`2^(e+1) = 2 * 2^e`) and `Fin.cast` of the
length-`2^(e+1)` input to length-`2 * 2^e`, plus a single `Fin.val`-level case
split (`k.val < 2^e` vs `≥ 2^e`) to route a lower- or upper-half output to the
matching split lemma.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull

open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass

variable {R : Type*} [CommRing R]

/-- Re-index a length-`2^(e+1)` input as a length-`2 * 2^e` input, so the
`Fin (2 * n)`-stated `evenPart` / `oddPart` / split lemmas of
`NTTRecursionPass` apply at depth `e`. -/
def reindex (e : ℕ) (x : Fin (2 ^ (e + 1)) → R) : Fin (2 * 2 ^ e) → R :=
  fun j => x (Fin.cast (by rw [pow_succ']) j)

/-- The full recursive radix-2 decimation-in-time NTT on a length-`2^e` input.

* `e = 0`: the length-1 transform is the identity.
* `e + 1`: split into even / odd sub-sequences, recurse at `ω²` and depth `e`,
  then butterfly-combine. Output index `k` is routed by whether `k.val < 2^e`
  (lower half, twiddle `ωᵏ`) or not (upper half, twiddle `ω^(2^e)·ωᵏ`). -/
def nttRec : (e : ℕ) → R → (Fin (2 ^ e) → R) → (Fin (2 ^ e) → R)
  | 0, _, x => x
  | (e + 1), ω, x => fun k =>
    let xe := evenPart (reindex e x)
    let xo := oddPart (reindex e x)
    let E := nttRec e (ω ^ 2) xe
    let O := nttRec e (ω ^ 2) xo
    if h : k.val < 2 ^ e then
      E ⟨k.val, h⟩ + ω ^ k.val * O ⟨k.val, h⟩
    else
      E ⟨k.val - 2 ^ e, by
            have hk : k.val < 2 ^ (e + 1) := k.isLt
            have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
            omega⟩
        + ω ^ (2 ^ e) * ω ^ (k.val - 2 ^ e)
            * O ⟨k.val - 2 ^ e, by
                have hk : k.val < 2 ^ (e + 1) := k.isLt
                have he : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
                omega⟩

/-! ## Bridging the `Fin (2^(e+1))` and `Fin (2 * 2^e)` indexings -/

/-- A `dft` over a `Fin m` index equals the `dft` over a `Fin n` index obtained
by re-indexing both the input and the output frequency through `Fin.cast`. This
is the bridge between the `2^(e+1)`-indexed `nttRec` and the `2 * 2^e`-indexed
`evenPart` / `oddPart` / split lemmas of `NTTRecursionPass`. -/
theorem dft_cast {m n : ℕ} (hmn : m = n) (ω : R) (x : Fin m → R) (k : Fin m) :
    dft m ω x k
      = dft n ω (fun j => x (Fin.cast hmn.symm j)) (Fin.cast hmn k) := by
  subst hmn
  rfl

/-! ## Full recursive NTT correctness -/

/-- **Full radix-2 NTT correctness.** For any depth `e`, twiddle `ω` that is a
`2^e`-th root of unity, length-`2^e` input `x`, and frequency `k`, the recursive
decimation-in-time transform `nttRec` computes the definitional `dft`:

`nttRec e ω x k = dft (2^e) ω x k`.

Proved by induction on the depth `e`. The base case `e = 0` is `rfl` (length-1
transform). The step at `e + 1` is exactly the Cooley–Tukey recursion of
`NTTRecursionPass`: the two recursive calls equal the half-length DFTs `E`, `O`
by the induction hypothesis (whose root-of-unity premise `(ω²) ^ (2^e) = 1`
follows from `ω ^ (2^(e+1)) = 1`), and `dft_even_odd_split` (lower half) /
`dft_upper_split` (upper half) reassemble them into the length-`2^(e+1)` DFT. -/
theorem nttRec_eq_dft :
    ∀ (e : ℕ) (ω : R), ω ^ (2 ^ e) = 1 → ∀ (x : Fin (2 ^ e) → R) (k : Fin (2 ^ e)),
      nttRec e ω x k = dft (2 ^ e) ω x k
  | 0, ω, _, x, k => by
    -- Length-1 transform: `nttRec 0 = id`, and `dft 1 ω x k = x k * ω^0 = x k`.
    have hk : k = (0 : Fin (2 ^ 0)) := by apply Fin.ext; have := k.isLt; omega
    rw [show nttRec 0 ω x = x from rfl, hk]
    simp [dft]
  | (e + 1), ω, hω, x, k => by
    -- `2^(e+1) = 2 * 2^e`, the shape the split lemmas of NTTRecursionPass want.
    have hmn : (2 : ℕ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    -- The induction-hypothesis root-of-unity premise: `(ω²)^(2^e) = ω^(2^(e+1)) = 1`.
    have hω2 : (ω ^ 2) ^ (2 ^ e) = 1 := by
      rw [← pow_mul, ← pow_succ'] at *
      simpa using hω
    -- `ω` is a `(2 * 2^e)`-th root of unity, for `dft_upper_split`.
    have hωup : ω ^ (2 * 2 ^ e) = 1 := by rw [← hmn]; exact hω
    -- Recast the input to the `Fin (2 * 2^e)` shape `evenPart`/`oddPart` expect.
    set x' : Fin (2 * 2 ^ e) → R := reindex e x with hx'
    -- The half-transforms, as `Fin (2^e) → R`.
    set E : Fin (2 ^ e) → R := nttRec e (ω ^ 2) (evenPart x') with hE
    set O : Fin (2 ^ e) → R := nttRec e (ω ^ 2) (oddPart x') with hO
    -- IH wires each recursive call to the half-DFT.
    have hEdft : ∀ j : Fin (2 ^ e), E j = dft (2 ^ e) (ω ^ 2) (evenPart x') j :=
      fun j => nttRec_eq_dft e (ω ^ 2) hω2 (evenPart x') j
    have hOdft : ∀ j : Fin (2 ^ e), O j = dft (2 ^ e) (ω ^ 2) (oddPart x') j :=
      fun j => nttRec_eq_dft e (ω ^ 2) hω2 (oddPart x') j
    -- Bridge the LHS-target `dft (2^(e+1))` to the `dft (2 * 2^e)` of `x'`.
    have hbridge : dft (2 ^ (e + 1)) ω x k
        = dft (2 * 2 ^ e) ω x' (Fin.cast hmn k) := by
      rw [dft_cast hmn ω x k]; rfl
    rw [hbridge]
    -- Unfold `nttRec (e+1)` and route by the lower/upper half case split.
    show (if h : k.val < 2 ^ e then
            E ⟨k.val, h⟩ + ω ^ k.val * O ⟨k.val, h⟩
          else
            E ⟨k.val - 2 ^ e, _⟩ + ω ^ (2 ^ e) * ω ^ (k.val - 2 ^ e)
              * O ⟨k.val - 2 ^ e, _⟩)
        = dft (2 * 2 ^ e) ω x' (Fin.cast hmn k)
    by_cases h : k.val < 2 ^ e
    · -- Lower half: `(Fin.cast hmn k)` is `Fin.castLE` of `⟨k.val, h⟩`.
      rw [dif_pos h]
      set k' : Fin (2 ^ e) := ⟨k.val, h⟩ with hk'
      have hidx : (Fin.cast hmn k) = Fin.castLE (by omega) k' := by
        apply Fin.ext; simp [hk']
      rw [hidx, dft_even_odd_split ω x' k']
      rw [hEdft k', hOdft k']
    · -- Upper half: `(Fin.cast hmn k) = ⟨k''.val + 2^e, _⟩` for `k'' = k.val - 2^e`.
      rw [dif_neg h]
      have hb : k.val - 2 ^ e < 2 ^ e := by
        have hk : k.val < 2 ^ (e + 1) := k.isLt
        omega
      set k'' : Fin (2 ^ e) := ⟨k.val - 2 ^ e, hb⟩ with hk''
      have hidx : (Fin.cast hmn k) = ⟨k''.val + 2 ^ e, by omega⟩ := by
        apply Fin.ext; simp [hk'']; omega
      rw [hidx, dft_upper_split ω hωup x' k'']
      rw [hEdft k'', hOdft k'']

/-! ## Concrete depths: the 4- and 8-point networks are `nttRec` at `e = 2, 3` -/

/-- The 4-point radix-2 NTT (`nttRec` at depth `e = 2`) computes the length-4
DFT. This is the unrolling `NTT4PointPass` exhibits concretely. -/
theorem nttRec_two_eq_dft (ω : R) (hω : ω ^ 4 = 1) (x : Fin 4 → R) (k : Fin 4) :
    nttRec 2 ω x k = dft 4 ω x k :=
  nttRec_eq_dft 2 ω (by norm_num at hω ⊢; exact hω) x k

/-- The 8-point radix-2 NTT (`nttRec` at depth `e = 3`) computes the length-8
DFT. This is the unrolling `NTT8PointPass` exhibits concretely. -/
theorem nttRec_three_eq_dft (ω : R) (hω : ω ^ 8 = 1) (x : Fin 8 → R) (k : Fin 8) :
    nttRec 3 ω x k = dft 8 ω x k :=
  nttRec_eq_dft 3 ω (by norm_num at hω ⊢; exact hω) x k

end CatCrypt.Crypto.Optimizer.Lattice.NTTRecursiveFull
