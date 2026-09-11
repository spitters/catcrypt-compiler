/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba
public import CatCrypt.Crypto.SecureCompilation.BigNatToom3
public import CatCrypt.Crypto.SecureCompilation.BigNatToom4

/-!
# The size-dispatched integer multiply ladder

`mulLadder` selects the multiply algorithm by operand size — Karatsuba below the
Toom-3 crossover (Karatsuba itself falls back to schoolbook below its own
crossover), Toom-3 up to the Toom-4 crossover, Toom-4 above — and is proven equal
to the integer product on every arm. Correctness is threshold-independent: each
branch carries its own value theorem, so the thresholds are performance tuning
only. This is the canonical fast multiply over the `BigNat` carrier.

## Main results

* `mulLadder_val` — `bignumVal (mulLadder a b) = bignumVal a * bignumVal b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatMulLadder

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)

/-- The size-dispatched multiply: Karatsuba below 48 limbs (itself schoolbook
    below its own crossover), Toom-3 from 48 to 119, Toom-4 at 120 and above.
    Thresholds are performance tuning; every arm computes the exact product. -/
def mulLadder (a b : List (BitVec 64)) : List (BitVec 64) :=
  if max a.length b.length < 48 then BigNatKaratsuba.karatsuba a b
  else if max a.length b.length < 120 then BigNatToom3.toom3 a b
  else BigNatToom4.toom4 a b

/-- **The ladder computes the exact product.** Every size arm carries its own
    value theorem, so the dispatch is correct for any thresholds. -/
theorem mulLadder_val (a b : List (BitVec 64)) :
    bignumVal (mulLadder a b) = bignumVal a * bignumVal b := by
  unfold mulLadder
  split_ifs
  · exact BigNatKaratsuba.karatsuba_val a b
  · exact BigNatToom3.toom3_val a b
  · exact BigNatToom4.toom4_val a b

end CatCrypt.Crypto.SecureCompilation.BigNatMulLadder
