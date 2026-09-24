/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Algebra.Group.Defs

/-!
# CoqEAL `seqpoly`, ported to Lean — `List R` refines the coefficient function

CoqEAL's `seqpoly` refines MathComp polynomials `{poly R}` to lists `seq R`. Here
we port the **data-refinement core** of that example into the `ReprTransfer`
framework: a coefficient list `List R` refines the abstract coefficient function
`ℕ → R`, and the concrete list addition `addSeq` refines the abstract
coefficient-wise addition — the CoqEAL `Radd_seqpoly` refinement square.

This is a representative CoqEAL example. The refinement *mechanism* CoqEAL is
built on (a relation between an abstract and a concrete representation + transfer
of operations) is exactly the `ReprTransfer` layer; this file is one worked
instance over the `seqpoly` representation.

## Scope (the rest of CoqEAL)

CoqEAL is a whole library. Its first-order data refinements — `binnat`
(`N` refines `nat`), `binint`, `binrat`, `seqpoly` add (here), `seqmatrix` add —
port via this same pattern. Its **algorithms** — Karatsuba / Toom-Cook polynomial
multiply, Strassen matrix multiply, Bareiss / Sasaki-Murao determinant, Smith /
Jordan / Frobenius normal forms, Gaussian elimination, rank — are multi-month
developments requiring MathComp-grade matrix/polynomial infrastructure (mostly not
yet in Mathlib in the needed form), and are NOT ported here. Polynomial/matrix
*multiplication* (convolution / row-col fold) is a `foldl`-shaped refinement
reachable via `Trocq.foldl_transfer`; the fast algorithms (Karatsuba/Strassen) and
the normal-form/determinant developments are outside the scope of this port.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.CoqEAL.SeqPoly

variable {R : Type*} [AddZeroClass R]

/-- The CoqEAL `seqpoly` refinement relation: a coefficient list denotes the
    abstract coefficient function (absent coefficients are `0`). -/
def coeff (l : List R) (i : ℕ) : R := l.getD i 0

/-- The concrete (computational) polynomial addition on coefficient lists. -/
def addSeq : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addSeq p q

/-- **The CoqEAL `Radd_seqpoly` refinement square.** The concrete list addition
    refines the abstract coefficient-wise addition. -/
theorem coeff_addSeq (p q : List R) (i : ℕ) :
    coeff (addSeq p q) i = coeff p i + coeff q i := by
  induction p generalizing q i with
  | nil => simp [addSeq, coeff]
  | cons a p ih =>
    cases q with
    | nil => simp [addSeq, coeff]
    | cons b q =>
      cases i with
      | zero => simp [addSeq, coeff]
      | succ i => simp only [addSeq, coeff, List.getD_cons_succ]; exact ih q i

/-- Functional form of the refinement square — the commuting square the
    `ReprTransfer` registry consumes (concrete add ↦ abstract pointwise add). -/
theorem coeff_addSeq_fun (p q : List R) :
    coeff (addSeq p q) = fun i => coeff p i + coeff q i := by
  funext i; exact coeff_addSeq p q i

end CatCrypt.Crypto.Bridges.CoqEAL.SeqPoly
