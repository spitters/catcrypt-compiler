/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

/-!
# Verified 8-point radix-2 Cooley–Tukey NTT

This file proves the correctness of the **8-point** decimation-in-time (DIT)
radix-2 Cooley–Tukey NTT, built entirely from the `ctButterfly` of
`CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass`. It is the next size up
from the size-4 base case (`NTT4PointPass`): an 8-point transform is exactly
three butterfly stages, so this is the leaf an NTT-lowering pass unfolds to for
length 8.

Everything is generic over a `CommRing R` carrying a *primitive 8th root of
unity* `ω`, captured by the single hypothesis `ω⁴ = -1` (which entails
`ω⁸ = 1`, `ω⁵ = -ω`, `ω⁶ = -ω²`, `ω⁷ = -ω³`, and that `ω` is primitive of
order 8). No concrete prime, modulus, or root is fixed.

## The two objects compared

* `dft8 ω x0 … x7` — the **definitional** length-8 DFT: `Xₖ = Σⱼ xⱼ ωʲᵏ`,
  written out as eight explicit sums.
* `ntt8 ω x0 … x7` — the **butterfly network**: three DIT stages of
  `ctButterfly`. Stage 1 splits even/odd lanes (twiddle `1`); stage 2 recombines
  even and odd sub-blocks with twiddles `1`, `ω²`; stage 3 recombines with
  twiddles `1`, `ω`, `ω²`, `ω³`.

## Decimation-in-time decomposition (output ordering / bit reversal)

`Xₖ = Eₖ + ωᵏ Oₖ` where `E` is the 4-point DFT of the even-indexed inputs
`(x0,x2,x4,x6)` and `O` is the 4-point DFT of the odd-indexed inputs
`(x1,x3,x5,x7)`, both evaluated at `ω²` (a primitive 4th root). Using
`ωᵏ⁺⁴ = -ωᵏ` and `E,O` being 4-periodic, the eight outputs are

* `X0 = E0 + ω⁰·O0`,  `X4 = E0 − ω⁰·O0`
* `X1 = E1 + ω¹·O1`,  `X5 = E1 − ω¹·O1`
* `X2 = E2 + ω²·O2`,  `X6 = E2 − ω²·O2`
* `X3 = E3 + ω³·O3`,  `X7 = E3 − ω³·O3`

The network is wired so that, reading the stage-3 output lanes in the right
order, the result lands in natural `(X0, …, X7)` order — bit reversal is
absorbed into the input pairing and the output wiring, exactly as in
`NTT4PointPass`. `ntt8_eq_dft8` is then a *literal* tuple equality.

The single arithmetic fact used is `ω⁴ = -1`; after reducing every `ωⁿ` to
`±ωⁿ mod 4`, `ring` discharges each lane.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTT8PointPass

open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

variable {R : Type*} [CommRing R]

/-- The definitional length-8 discrete/number-theoretic transform:
`Xₖ = Σⱼ xⱼ ωʲᵏ` for `k = 0,…,7`, written as eight explicit sums.

No relation on `ω` is assumed by the definition itself; the primitivity
hypothesis `ω⁴ = -1` enters only in `ntt8_eq_dft8`. -/
def dft8 (ω x0 x1 x2 x3 x4 x5 x6 x7 : R) : R × R × R × R × R × R × R × R :=
  ( x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7
  , x0 + ω ^ 1 * x1 + ω ^ 2 * x2 + ω ^ 3 * x3 + ω ^ 4 * x4 + ω ^ 5 * x5
      + ω ^ 6 * x6 + ω ^ 7 * x7
  , x0 + ω ^ 2 * x1 + ω ^ 4 * x2 + ω ^ 6 * x3 + ω ^ 8 * x4 + ω ^ 10 * x5
      + ω ^ 12 * x6 + ω ^ 14 * x7
  , x0 + ω ^ 3 * x1 + ω ^ 6 * x2 + ω ^ 9 * x3 + ω ^ 12 * x4 + ω ^ 15 * x5
      + ω ^ 18 * x6 + ω ^ 21 * x7
  , x0 + ω ^ 4 * x1 + ω ^ 8 * x2 + ω ^ 12 * x3 + ω ^ 16 * x4 + ω ^ 20 * x5
      + ω ^ 24 * x6 + ω ^ 28 * x7
  , x0 + ω ^ 5 * x1 + ω ^ 10 * x2 + ω ^ 15 * x3 + ω ^ 20 * x4 + ω ^ 25 * x5
      + ω ^ 30 * x6 + ω ^ 35 * x7
  , x0 + ω ^ 6 * x1 + ω ^ 12 * x2 + ω ^ 18 * x3 + ω ^ 24 * x4 + ω ^ 30 * x5
      + ω ^ 36 * x6 + ω ^ 42 * x7
  , x0 + ω ^ 7 * x1 + ω ^ 14 * x2 + ω ^ 21 * x3 + ω ^ 28 * x4 + ω ^ 35 * x5
      + ω ^ 42 * x6 + ω ^ 49 * x7 )

/-- The 8-point DIT radix-2 Cooley–Tukey NTT as a three-stage butterfly network.

*Stage 1* (even/odd split within each radix-2 sub-block, twiddle `1`): pair the
bit-reversed inputs and apply `ctButterfly 1`. With the DIT bit-reversed input
order `(x0, x4, x2, x6, x1, x5, x3, x7)`, stage 1 forms the four pairs
`(x0±x4), (x2±x6), (x1±x5), (x3±x7)`.

*Stage 2* (combine pairs into 4-point sub-DFTs of the even and odd halves,
twiddles `1` and `ω²`): the even half produces `E` at `(x0,x2,x4,x6)` and the
odd half produces `O` at `(x1,x3,x5,x7)`.

*Stage 3* (combine `E` and `O` with twiddles `1, ω, ω², ω³`):
`Xₖ = Eₖ + ωᵏ·Oₖ`, `X_{k+4} = Eₖ − ωᵏ·Oₖ`.

Outputs are emitted directly in natural `(X0, …, X7)` order (see the module
docstring). -/
def ntt8 (ω x0 x1 x2 x3 x4 x5 x6 x7 : R) :
    R × R × R × R × R × R × R × R :=
  -- Stage 1: butterflies on bit-reversed pairs, twiddle 1.
  let a0 := ctButterfly 1 x0 x4   -- (x0+x4, x0-x4)
  let a1 := ctButterfly 1 x2 x6   -- (x2+x6, x2-x6)
  let a2 := ctButterfly 1 x1 x5   -- (x1+x5, x1-x5)
  let a3 := ctButterfly 1 x3 x7   -- (x3+x7, x3-x7)
  -- Stage 2: 4-point sub-DFTs of even half (a0,a1) and odd half (a2,a3).
  -- Even half E = dft4 ω² on (x0,x2,x4,x6):
  let e0 := ctButterfly 1 a0.1 a1.1          -- E0 = a0.1 + a1.1
  let e1 := ctButterfly (ω ^ 2) a0.2 a1.2    -- E1 = a0.2 + ω²·a1.2
  -- e0.1 = E0, e0.2 = E2, e1.1 = E1, e1.2 = E3
  -- Odd half O = dft4 ω² on (x1,x3,x5,x7):
  let o0 := ctButterfly 1 a2.1 a3.1          -- O0 = a2.1 + a3.1
  let o1 := ctButterfly (ω ^ 2) a2.2 a3.2    -- O1 = a2.2 + ω²·a3.2
  -- o0.1 = O0, o0.2 = O2, o1.1 = O1, o1.2 = O3
  -- Stage 3: combine E and O with twiddles 1, ω, ω², ω³.
  let g0 := ctButterfly 1       e0.1 o0.1   -- (E0+O0, E0-O0)   → X0, X4
  let g1 := ctButterfly ω       e1.1 o1.1   -- (E1+ω·O1, E1-ω·O1) → X1, X5
  let g2 := ctButterfly (ω ^ 2) e0.2 o0.2   -- (E2+ω²·O2, E2-ω²·O2) → X2, X6
  let g3 := ctButterfly (ω ^ 3) e1.2 o1.2   -- (E3+ω³·O3, E3-ω³·O3) → X3, X7
  (g0.1, g1.1, g2.1, g3.1, g0.2, g1.2, g2.2, g3.2)

/-- **8-point radix-2 Cooley–Tukey NTT correctness.** With `ω` a primitive 8th
root of unity (`ω⁴ = -1`), the three-stage butterfly network `ntt8` computes
exactly the length-8 DFT `dft8`, lane-for-lane.

This extends the size-4 base case (`NTT4PointPass.ntt4_eq_dft4`) to the next
radix-2 size. Closed by reducing every power of `ω` modulo `ω⁴ = -1` and
finishing each output coordinate with `ring`. -/
theorem ntt8_eq_dft8 (ω : R) (hω : ω ^ 4 = -1)
    (x0 x1 x2 x3 x4 x5 x6 x7 : R) :
    ntt8 ω x0 x1 x2 x3 x4 x5 x6 x7 = dft8 ω x0 x1 x2 x3 x4 x5 x6 x7 := by
  -- Reduce all powers of `ω` to `±ωⁿ` with `n < 4`, using `ω⁴ = -1`.
  have h5  : ω ^ 5  = -ω      := by
    have : ω ^ 5 = ω ^ 4 * ω := by ring
    rw [this, hω]; ring
  have h6  : ω ^ 6  = -ω ^ 2  := by
    have : ω ^ 6 = ω ^ 4 * ω ^ 2 := by ring
    rw [this, hω]; ring
  have h7  : ω ^ 7  = -ω ^ 3  := by
    have : ω ^ 7 = ω ^ 4 * ω ^ 3 := by ring
    rw [this, hω]; ring
  have h8  : ω ^ 8  = 1        := by
    have : ω ^ 8 = ω ^ 4 * ω ^ 4 := by ring
    rw [this, hω]; ring
  have h9  : ω ^ 9  = ω        := by
    have : ω ^ 9 = ω ^ 8 * ω := by ring
    rw [this, h8]; ring
  have h10 : ω ^ 10 = ω ^ 2   := by
    have : ω ^ 10 = ω ^ 8 * ω ^ 2 := by ring
    rw [this, h8]; ring
  have h12 : ω ^ 12 = -1       := by
    have : ω ^ 12 = ω ^ 8 * ω ^ 4 := by ring
    rw [this, h8, hω]; ring
  have h14 : ω ^ 14 = -ω ^ 2  := by
    have : ω ^ 14 = ω ^ 8 * ω ^ 4 * ω ^ 2 := by ring
    rw [this, h8, hω]; ring
  have h15 : ω ^ 15 = -ω ^ 3  := by
    have : ω ^ 15 = ω ^ 8 * ω ^ 4 * ω ^ 3 := by ring
    rw [this, h8, hω]; ring
  have h16 : ω ^ 16 = 1        := by
    have : ω ^ 16 = ω ^ 8 * ω ^ 8 := by ring
    rw [this, h8]; ring
  have h18 : ω ^ 18 = ω ^ 2   := by
    have : ω ^ 18 = ω ^ 16 * ω ^ 2 := by ring
    rw [this, h16]; ring
  have h20 : ω ^ 20 = -1       := by
    have : ω ^ 20 = ω ^ 16 * ω ^ 4 := by ring
    rw [this, h16, hω]; ring
  have h21 : ω ^ 21 = -ω       := by
    have : ω ^ 21 = ω ^ 16 * ω ^ 4 * ω := by ring
    rw [this, h16, hω]; ring
  have h24 : ω ^ 24 = 1        := by
    have : ω ^ 24 = ω ^ 16 * ω ^ 8 := by ring
    rw [this, h16, h8]; ring
  have h25 : ω ^ 25 = ω        := by
    have : ω ^ 25 = ω ^ 24 * ω := by ring
    rw [this, h24]; ring
  have h28 : ω ^ 28 = -1       := by
    have : ω ^ 28 = ω ^ 24 * ω ^ 4 := by ring
    rw [this, h24, hω]; ring
  have h30 : ω ^ 30 = -ω ^ 2  := by
    have : ω ^ 30 = ω ^ 24 * ω ^ 4 * ω ^ 2 := by ring
    rw [this, h24, hω]; ring
  have h35 : ω ^ 35 = ω ^ 3   := by
    have : ω ^ 35 = ω ^ 32 * ω ^ 3 := by ring
    have h32 : ω ^ 32 = 1 := by
      have : ω ^ 32 = ω ^ 16 * ω ^ 16 := by ring
      rw [this, h16]; ring
    rw [this, h32]; ring
  have h36 : ω ^ 36 = -1       := by
    have h32 : ω ^ 32 = 1 := by
      have : ω ^ 32 = ω ^ 16 * ω ^ 16 := by ring
      rw [this, h16]; ring
    have : ω ^ 36 = ω ^ 32 * ω ^ 4 := by ring
    rw [this, h32, hω]; ring
  have h42 : ω ^ 42 = ω ^ 2   := by
    have h40 : ω ^ 40 = 1 := by
      have : ω ^ 40 = ω ^ 8 * ω ^ 8 * ω ^ 8 * ω ^ 8 * ω ^ 8 := by ring
      rw [this, h8]; ring
    have : ω ^ 42 = ω ^ 40 * ω ^ 2 := by ring
    rw [this, h40]; ring
  have h49 : ω ^ 49 = ω        := by
    have h48 : ω ^ 48 = 1 := by
      have : ω ^ 48 = ω ^ 24 * ω ^ 24 := by ring
      rw [this, h24]; ring
    have : ω ^ 49 = ω ^ 48 * ω := by ring
    rw [this, h48]; ring
  -- Unfold the network and DFT, rewriting every `ωⁿ` appearing literally in the
  -- definitions to `±ωᵏ` with `k < 4`.
  simp only [ntt8, dft8, ctButterfly, pow_one,
    hω, h5, h6, h7, h8, h9, h10, h12, h14, h15, h16, h18, h20, h21, h24, h25,
    h28, h30, h35, h36, h42, h49]
  -- Split into the eight output coordinates. `ring_nf` collects the products of
  -- twiddles (e.g. the stage-3 `ω³` against a stage-2 `ω²`) into a single literal
  -- `ω⁵` on the two lanes that need it (X3, X7); `rw [h5]` then cancels it and
  -- `ring` closes every lane.
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_
    (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))))) <;>
    ring_nf <;>
    (try rw [h5]) <;>
    ring
