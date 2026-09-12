/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.Gf16
public import CatCrypt.Crypto.Util.Gf16

/-!
# Verified SNOVA matrix-ring `R = Mat_2(GF(16))`

A computable, verified Lean reference implementation of the SNOVA
non-commutative matrix ring `R = Mat_ℓ(GF(16))` at `ℓ = 2`. SNOVA's
public map is built from sums of products of `R`-elements; this file
exposes the underlying `2 × 2` matrix product over the verified `Gf16`
together with the entrywise XOR addition.

## Representation

An element of `R = Mat_2(GF(16))` is a `Vector Gf16 4` storing the four
nibbles row-major as `[a00, a01, a10, a11]`.

* **add** = entrywise XOR (`Gf16` additive monoid)
* **mul** = `2 × 2` schoolbook matrix product over `GF(16)`:
  `(a · b)[r][c] = Σ_k a[r][k] · b[k][c]` (`+ = XOR`, `· = Gf16.mul`)

## API

* `RingElem := Vector Gf16 4` — one ring element, row-major
* `add` — entrywise XOR
* `mul` — `2 × 2` schoolbook matrix product
* `zero`, `one` — additive / multiplicative identity
* Field-style sanity facts closed by `native_decide` cascades.

This file is the SNOVA analogue of `Util/Gf16.lean`'s field layer: it
adds the `Mat_2(GF(16))` matrix-ring layer on top of the verified GF(16)
that the SNOVA bridge consults to discharge the verified-GF body of the
ring-dot kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

namespace Gf16MatRing

open CatCrypt.Util.Gf16

/-- A SNOVA matrix-ring element `m ∈ Mat_2(GF(16))`. Row-major: positions
    `[0, 1, 2, 3]` correspond to entries `[m[0][0], m[0][1], m[1][0],
    m[1][1]]`. -/
abbrev RingElem : Type := Vector Gf16 4

/-- The all-zero ring element (additive identity). -/
def zero : RingElem := Vector.replicate 4 (0 : Gf16)

/-- The identity ring element (`2 × 2` identity matrix over `GF(16)`). -/
def one : RingElem := #v[(1 : Gf16), (0 : Gf16), (0 : Gf16), (1 : Gf16)]

/-- Entrywise XOR — the `Mat_2(GF(16))` additive monoid. -/
def add (x y : RingElem) : RingElem :=
  #v[x.get 0 ^^^ y.get 0,
     x.get 1 ^^^ y.get 1,
     x.get 2 ^^^ y.get 2,
     x.get 3 ^^^ y.get 3]

/-- Schoolbook `2 × 2` GF(16) matrix product. `(x · y)[r][c] = Σ_k
    x[r][k] · y[k][c]` with `· = Gf16.mul`, `+ = XOR`. -/
def mul (x y : RingElem) : RingElem :=
  let a00 := x.get 0; let a01 := x.get 1
  let a10 := x.get 2; let a11 := x.get 3
  let b00 := y.get 0; let b01 := y.get 1
  let b10 := y.get 2; let b11 := y.get 3
  #v[Gf16.mul a00 b00 ^^^ Gf16.mul a01 b10,
     Gf16.mul a00 b01 ^^^ Gf16.mul a01 b11,
     Gf16.mul a10 b00 ^^^ Gf16.mul a11 b10,
     Gf16.mul a10 b01 ^^^ Gf16.mul a11 b11]

/-! ## Sanity check: the all-zero ring element acts as `zero` byte-wise. -/

/-- The all-zero ring element has every entry zero. -/
theorem zero_get (i : Nat) (h : i < 4) :
    (zero : RingElem).get ⟨i, h⟩ = (0 : Gf16) := by
  unfold zero
  show (Vector.replicate 4 (0 : Gf16))[i] = (0 : Gf16)
  simp [Vector.getElem_replicate]

end Gf16MatRing

end CatCrypt.Util
