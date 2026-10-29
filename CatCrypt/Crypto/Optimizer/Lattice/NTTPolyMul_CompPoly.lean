/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul

/-!
# Algebraic Bridge from the NTT poly-mul pass to CompPoly's `fastMulImpl_eq_mul`

This module is the **bridge** between the NTT poly-mul
rewrite (`CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul`) and the
algebraic correctness statement that lives in the external `CompPoly`
library.

The pass's soundness anchor `nttPolyMul_denote_eq` is parameterised by
the per-leaf agreement predicate `nttAgreesPolyMul`.  To use the pass
against a concrete NTT-backed `LeafSpec` we must discharge that
predicate.  This module provides the **trivial-lift transport lemma**
`nttAgreesPolyMul_of_pointwise`: a pointwise leaf equality (one for
each of the two source name spellings) directly yields the universal
agreement predicate.

## CompPoly algebraic content

The algebraic content is supplied by the external `CompPoly` library
(at `CompPoly.Univariate.NTT.FastMul`):

```
theorem CompPoly.CPolynomial.NTT.fastMulImpl_eq_mul
    (D : Domain R) (p q : CPolynomial R)
    (hfit : Domain.fits D p.val q.val) :
  fastMulImpl D p q = p * q
```

Under the `Domain.fits` precondition the NTT-backed implementation
agrees with canonical multiplication in `CPolynomial R`.

### The reification layer

The trivial-lift lemma below reduces the agreement obligation to one
pointwise equality per spelling.  Closing that pointwise equality for a
concrete NTT-backed `LeafSpec` requires a thin reification layer, kept
**outside** this module:

* **`PolyEncoding (q n : Nat)`** — a structure relating
  `RustVal (TPolyMod q n)` (the runtime representation of degree-`<n`
  polynomials mod `q` inside `LowCT`) to `CPolynomial (ZMod q)` (the
  algebraic representation `CompPoly` operates on).  Must include
  `encode`, `decode`, `decode_encode = id`, and a coefficient-by-
  coefficient agreement lemma.
* **`Domain.fits` discharge** — a side condition asserting that the
  encoded polynomial degrees fit within the chosen evaluation domain.
  For NTT-friendly parameters (e.g. ML-KEM's `(q = 3329, n = 256)` with
  a 512-point NTT) this is a once-per-parameter numeric check.

`PolyEncoding` and the leaf-agreement theorem `polyMul_leaf_agreement` live in
`NTTPolyEncoding.lean`, which imports CompPoly directly; the `Domain.fits` side
condition is a hypothesis of `polyMul_leaf_agreement`.  This module keeps the link as a **prose
pointer** so the optimizer's core build is not coupled to the
CompPoly library.

## Composition

This module sits between the rewrite + per-leaf-agreement soundness
theorem (`NTTPolyMul`) and the concrete discharge
(`NTTPolyMul_CompPolyConcrete`).  It is
imported by any concrete instantiation that wants to discharge the
agreement assumption — e.g. an ML-KEM `LeafSpec` whose NTT leaf is built
on a verified Rust transcription of `CompPoly.NTT.fastMulImpl`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Trivial lift: pointwise → universal -/

/-- Trivial lift: if the `LeafSpec` returns identical values for the NTT
    name and **both** source poly-mul names (`"poly_mul"` and
    `"polymul"`), the agreement obligation discharges.

    Concrete `LeafSpec`s typically define the NTT-backed leaf to call
    canonical multiplication when the name spells matches; both
    hypotheses are then `rfl`. -/
theorem nttAgreesPolyMul_of_pointwise
    {leafSpec : LeafSpec} {q n : Nat}
    (h_poly_mul : ∀ (dt : TowerType) (argTs : List TowerType)
        (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
        leafSpec.call (nttPolyMulName q n) dt argTs oldV args =
          leafSpec.call "poly_mul" dt argTs oldV args)
    (h_polymul : ∀ (dt : TowerType) (argTs : List TowerType)
        (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
        leafSpec.call (nttPolyMulName q n) dt argTs oldV args =
          leafSpec.call "polymul" dt argTs oldV args) :
    nttAgreesPolyMul leafSpec q n := by
  intro f dt argTs oldV args hf
  -- `hf : isPolyMulName f = true` unfolds to a Boolean `||`.
  unfold isPolyMulName at hf
  rw [Bool.or_eq_true] at hf
  rcases hf with hpm | hpm
  · -- f == "poly_mul"
    have hf_eq : f = "poly_mul" := by
      have := (beq_iff_eq (a := f) (b := "poly_mul")).mp hpm
      exact this
    subst hf_eq
    exact h_poly_mul dt argTs oldV args
  · -- f == "polymul"
    have hf_eq : f = "polymul" := by
      have := (beq_iff_eq (a := f) (b := "polymul")).mp hpm
      exact this
    subst hf_eq
    exact h_polymul dt argTs oldV args

end CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
