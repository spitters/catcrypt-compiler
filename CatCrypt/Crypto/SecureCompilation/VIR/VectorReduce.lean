/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.BitVec

/-!
# Verified vectorization core: sequential scalar fold = horizontal reduction

This is the **denotation-preservation heart** of the verified vectorizer. A
straight-line emitter computes a length-`L` reduction (e.g. one row of a matmul,
`out = Σ_i a_i * b_i`) as a **sequential left-fold**
`((0 + t_0) + t_1) + … + t_{L-1}` over the lane terms `t_i`. A SIMD realization
instead packs the lanes into a vector, applies a lane-wise op (`#VPMULL_16u16`),
and finishes with a **horizontal reduction** that sums the lanes in a *different*
association/order (a pairwise tree of `#VPADD_16u16` + shuffles).

Replacing the scalar fold by the vector op + horizontal sum is therefore sound
**exactly** when the lane type is an `AddCommMonoid`: associativity and
commutativity are what let the horizontal reduction reassociate and reorder the
scalar sequential accumulation without changing the result. `scalarFold_eq_hsum`
below is that fact, stated over any `AddCommMonoid`; `hsum` models the horizontal
reduction by its mathematical value (`∑`), the abstraction the specific AVX2 tree
realizes.

The Frodo matmul lane type is `BitVec 16` (`Z/2^16`), a `CommRing` (hence
`AddCommMonoid`) via `Mathlib.Data.BitVec` — so the vectorization of its rows is
denotation-preserving (`vmul_hsum_eq_scalarFold`). This is the verified content
the `Com → Com` vectorization pass carries; the dialect ops + AVX2 emission +
per-opcode `psem` alignment for `#VPMULL`/`#VPADD` are the separate (engineering /
TCB) layers built on top.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce

open scoped BigOperators

variable {M : Type*} [AddCommMonoid M] {L : ℕ}

/-- The horizontal reduction of `L` lanes, modelled by its mathematical value
    over the additive commutative monoid of the lane type. The concrete AVX2
    horizontal-sum sequence (a pairwise tree of adds + shuffles) is one
    realization of this `∑`. -/
def hsum (v : Fin L → M) : M := ∑ i, v i

/-- The reduction as the straight-line emitter actually produces it: the
    sequential left-fold of the lane terms, `((0 + v 0) + v 1) + …`. -/
def scalarFold (v : Fin L → M) : M := (List.ofFn v).foldl (· + ·) 0

/-- `foldl (+) a l = a + l.sum` in an additive commutative monoid: the running
    accumulator factors out of the left-fold. -/
theorem foldl_add_eq (l : List M) (a : M) :
    l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, List.sum_cons, ih, add_assoc]

/-- **Heart of the vectorizer.** The sequential scalar fold equals the horizontal
    reduction: a length-`L` straight-line accumulation can be replaced by a packed
    lane-wise op + horizontal sum without changing the denotation, because the
    lane type is an `AddCommMonoid` (the horizontal reduction reassociates and
    reorders the sequential sum). -/
theorem scalarFold_eq_hsum (v : Fin L → M) : scalarFold v = hsum v := by
  rw [scalarFold, hsum, foldl_add_eq, zero_add, List.sum_ofFn]

/-! ## Specialization to packed `u16` vectors (the Frodo / AVX2 case) -/

/-- A packed vector: `L` lanes of `w`-bit words — the semantic model of a
    `reg u(L*w)` SIMD register (AVX2 `16u16` is `L = 16`, `w = 16`). -/
abbrev Vec (L w : ℕ) := Fin L → BitVec w

/-- Lane-wise product — the `#VPMULL_{L}u{w}` packed multiply (low `w` bits per
    lane), modelled lane-by-lane. -/
def vmul {L w : ℕ} (a b : Vec L w) : Vec L w := fun i => a i * b i

/-- **Denotation preservation for a dot product.** The vectorized path
    (lane-wise product `vmul` then horizontal sum `hsum`) equals the scalar
    straight-line path (sequential fold of the lane products). This is exactly
    `scalarFold_eq_hsum` instantiated at the lane products over `BitVec w`
    (a `CommRing`, hence `AddCommMonoid`), so it requires no new content beyond
    the core lemma — the vectorization of one matmul row / one dot product is
    sound. -/
theorem vmul_hsum_eq_scalarFold {L w : ℕ} (a b : Vec L w) :
    hsum (vmul a b) = scalarFold (vmul a b) :=
  (scalarFold_eq_hsum (vmul a b)).symm

/-- The vectorized dot is the mathematical dot product `∑_i a_i * b_i` (the spec
    a Frodo matmul row computes). -/
theorem hsum_vmul {L w : ℕ} (a b : Vec L w) :
    hsum (vmul a b) = ∑ i, a i * b i := by
  simp only [hsum, vmul]

end CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
