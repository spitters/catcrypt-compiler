/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

/-!
# Verified 4-point radix-2 Cooley–Tukey NTT (base case of the recursion)

This file proves the correctness of the smallest non-trivial number-theoretic
transform: the **4-point** decimation-in-time (DIT) radix-2 Cooley–Tukey NTT,
built entirely from the `ctButterfly` of
`CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass`. It is the base case of the
Cooley–Tukey recursion — a size-4 transform is exactly two butterfly stages — so
this is the leaf that an NTT-lowering pass unfolds to.

Everything is generic over a `CommRing R` carrying a *primitive 4th root of
unity* `ω`, captured by the single hypothesis `ω² = -1` (which entails
`ω⁴ = 1`, `ω³ = -ω`). No concrete prime, modulus, or root is fixed, so the
result specialises to every NTT-bearing protocol (ML-KEM, ML-DSA, BabyBear, …)
that supplies a 4th root of unity.

## The two objects compared

* `dft4 ω x0 x1 x2 x3` — the **definitional** length-4 DFT: `Xₖ = Σⱼ xⱼ ωʲᵏ`,
  written out as four explicit sums.
* `ntt4 ω x0 x1 x2 x3` — the **butterfly network**: two DIT stages of
  `ctButterfly`. Stage 1 splits even/odd lanes with twiddle `1`; stage 2 recombines
  with twiddles `1` and `ω`.

## Output ordering (bit reversal)

A DIT radix-2 network produces its outputs in **bit-reversed** lane order
*internally*; the network here is wired so that, after reading the four output
lanes as `(top.1, bottom.1, top.2, bottom.2)`, they line up with the natural
`(X0, X1, X2, X3)` order of `dft4`. Concretely, with `a = x0+x2`, `b = x0-x2`,
`c = x1+x3`, `d = x1-x3`:

* `X0 = a + c`   (stage-2 top, sum lane)
* `X1 = b + ω·d` (stage-2 bottom, sum lane)
* `X2 = a - c`   (stage-2 top, difference lane)
* `X3 = b - ω·d` (stage-2 bottom, difference lane)

`ntt4` is defined to emit `(X0, X1, X2, X3)` in this order, so
`ntt4_eq_dft4` is a *literal* tuple equality — no external permutation needed.

The single arithmetic fact used to close the proof is `ω² = -1`, from which
`ring` (after rewriting `ω³ = ω·ω² = -ω`) discharges every lane.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTT4PointPass

open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

variable {R : Type*} [CommRing R]

/-- The definitional length-4 discrete/number-theoretic transform:
`Xₖ = Σⱼ xⱼ ωʲᵏ` for `k = 0,1,2,3`, written as four explicit sums.

* `X0 = x0 + x1 + x2 + x3`
* `X1 = x0 + ω·x1 + ω²·x2 + ω³·x3`
* `X2 = x0 + ω²·x1 + ω⁴·x2 + ω⁶·x3`
* `X3 = x0 + ω³·x1 + ω⁶·x2 + ω⁹·x3`

No relation on `ω` is assumed by the definition itself; the primitivity
hypothesis enters only in `ntt4_eq_dft4`. -/
def dft4 (ω x0 x1 x2 x3 : R) : R × R × R × R :=
  ( x0 + x1 + x2 + x3
  , x0 + ω * x1 + ω ^ 2 * x2 + ω ^ 3 * x3
  , x0 + ω ^ 2 * x1 + ω ^ 4 * x2 + ω ^ 6 * x3
  , x0 + ω ^ 3 * x1 + ω ^ 6 * x2 + ω ^ 9 * x3 )

/-- The 4-point DIT radix-2 Cooley–Tukey NTT as a butterfly network.

*Stage 1* (even/odd split, twiddle `1`):
`ctButterfly 1 x0 x2 = (x0+x2, x0-x2)` and `ctButterfly 1 x1 x3 = (x1+x3, x1-x3)`.

*Stage 2* (recombine): the top butterfly carries twiddle `1` and the bottom
butterfly carries twiddle `ω`:
`ctButterfly 1 (x0+x2) (x1+x3)` and `ctButterfly ω (x0-x2) (x1-x3)`.

Outputs are emitted as `(top.1, bottom.1, top.2, bottom.2)`, the lane order that
matches `dft4` (see the module docstring). -/
def ntt4 (ω x0 x1 x2 x3 : R) : R × R × R × R :=
  let s1a := ctButterfly 1 x0 x2          -- (x0+x2, x0-x2)
  let s1b := ctButterfly 1 x1 x3          -- (x1+x3, x1-x3)
  let top := ctButterfly 1 s1a.1 s1b.1    -- (a+c, a-c)
  let bot := ctButterfly ω s1a.2 s1b.2    -- (b+ω·d, b-ω·d)
  (top.1, bot.1, top.2, bot.2)

/-- **4-point radix-2 Cooley–Tukey NTT correctness.** With `ω` a primitive 4th
root of unity (`ω² = -1`), the butterfly network `ntt4` computes exactly the
length-4 DFT `dft4`, lane-for-lane.

This is the base case of the Cooley–Tukey recursion: the size-4 transform is two
butterfly stages, and they reproduce the definitional DFT. Closed by rewriting
`ω²`, `ω³`, `ω⁴`, `ω⁶`, `ω⁹` via `ω² = -1` and finishing with `ring`. -/
theorem ntt4_eq_dft4 (ω : R) (hω : ω ^ 2 = -1) (x0 x1 x2 x3 : R) :
    ntt4 ω x0 x1 x2 x3 = dft4 ω x0 x1 x2 x3 := by
  -- Reduce all powers of `ω` to `1`, `ω`, or `-1` using `ω² = -1`.
  have h3 : ω ^ 3 = -ω := by
    have : ω ^ 3 = ω ^ 2 * ω := by ring
    rw [this, hω]; ring
  have h4 : ω ^ 4 = 1 := by
    have : ω ^ 4 = ω ^ 2 * ω ^ 2 := by ring
    rw [this, hω]; ring
  have h6 : ω ^ 6 = -1 := by
    have : ω ^ 6 = ω ^ 2 * ω ^ 2 * ω ^ 2 := by ring
    rw [this, hω]; ring
  have h9 : ω ^ 9 = ω := by
    have : ω ^ 9 = ω ^ 2 * ω ^ 2 * ω ^ 2 * ω ^ 2 * ω := by ring
    rw [this, hω]; ring
  simp only [ntt4, dft4, ctButterfly, hω, h3, h4, h6, h9]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp <;> ring

end CatCrypt.Crypto.Optimizer.Lattice.NTT4PointPass
