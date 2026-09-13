/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaBench
public import CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaBench
public meta import CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaRec
public import CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaRec
public import CompPoly.Univariate.ToPoly
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops

/-!
# Correctness + agreement check for the Karatsuba benchmark harness

This companion module keeps the elaboration-heavy material out of the runnable
benchmark `KaratsubaBench.lean` (so a compiled `lake exe` does not pay for it),
while still being built in CI. It provides:

* `karatsubaMul_toPoly`, `karatsubaComp_toPoly_eq_schoolbook`: a **correctness
  theorem** stating that the computable `karatsubaComp` denotes the same
  polynomial as the schoolbook product `schoolbookComp`. Equality is taken on
  the *denoted* Mathlib `Polynomial Int` (`CPolynomial.Raw.toPoly`) rather than
  on the raw coefficient `Array`, because two raw arrays may differ by trailing
  zeros while denoting the same polynomial (the recursion's recombination
  introduces high-order zero coefficients). This is the natural and provable
  correctness statement; on canonical (trimmed) forms it upgrades to literal
  equality via `CompPoly.CPolynomial.Raw.Trim.eq_of_equiv`.

* the small `native_decide` agreement check that used to sit inline in the
  benchmark module.

The proof mirrors `CatCrypt.Crypto.Bridges.CoqEAL.Karatsuba.karatsubaRec_eq`
(over the abstract `CPolynomial Int`): induction on the explicit `fuel`, with
the base case `Raw.toPoly_mul` and the step case discharged by pushing `toPoly`
through the recombination (`add`/`sub`/`mulPowX`), rewriting the three recursive
subproducts via the induction hypothesis, recomposing each input from its
`loPart`/`hiPart` split, and finishing with `ring` in `Polynomial Int`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaBench

open CompPoly CompPoly.CPolynomial CompPoly.CPolynomial.Raw

/-- `mulPowX k` denotes multiplication by `Xᵏ` after `toPoly`. The Raw library
    proves `coeff_mulPowX`; we lift it to the `Polynomial` denotation. -/
theorem toPoly_mulPowX (k : Nat) (p : P) :
    (CPolynomial.Raw.mulPowX k p).toPoly = (Polynomial.X ^ k) * p.toPoly := by
  ext n
  rw [Raw.coeff_toPoly, CPolynomial.Raw.coeff_mulPowX, _root_.mul_comm,
    Polynomial.coeff_mul_X_pow', Raw.coeff_toPoly]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- `toPoly` pushes through the explicit `Raw.add` used by the harness. -/
theorem toPoly_addFn (p q : P) :
    (CPolynomial.Raw.add p q).toPoly = p.toPoly + q.toPoly := by
  change (p + q).toPoly = _
  exact Raw.toPoly_add p q

/-- `toPoly` pushes through `Raw.neg`. -/
theorem toPoly_negFn (p : P) :
    (CPolynomial.Raw.neg p).toPoly = -p.toPoly := by
  ext n
  rw [Polynomial.coeff_neg, Raw.coeff_toPoly, Raw.coeff_toPoly]
  exact Raw.neg_coeff p n

/-- `toPoly` pushes through the explicit `Raw.sub` used by the harness. -/
theorem toPoly_subFn (p q : P) :
    (CPolynomial.Raw.sub p q).toPoly = p.toPoly - q.toPoly := by
  rw [CPolynomial.Raw.sub, toPoly_addFn, toPoly_negFn, sub_eq_add_neg]

/-- `toPoly` pushes through the explicit `Raw.mul` used by the harness. -/
theorem toPoly_mulFn (p q : P) :
    (CPolynomial.Raw.mul p q).toPoly = p.toPoly * q.toPoly := by
  change (p * q).toPoly = _
  exact Raw.toPoly_mul p q

/-- **Split–recompose identity** (denoted form). With `loPart k p` defined as the
    complement of `Xᵏ · hiPart k p`, recomposing the two parts returns `p`'s
    denotation. Mirrors `Karatsuba.loPart_add_hiPart`; here it is a `ring` fact
    after pushing `toPoly` through `add`/`sub`/`mulPowX`. -/
theorem loPart_add_hiPart_toPoly (k : Nat) (p : P) :
    (loPart k p).toPoly + (Polynomial.X ^ k) * (hiPart k p).toPoly = p.toPoly := by
  unfold loPart
  rw [toPoly_subFn, toPoly_mulPowX]
  ring

/-- **Correctness of the computable recursive Karatsuba (denoted form).** For
    every fuel value, `karatsubaMul fuel p q` denotes the true product
    `p.toPoly * q.toPoly`.

    Induction on `fuel`, mirroring `Karatsuba.karatsubaRec_eq`: the base case is
    `toPoly_mulFn`; the `degree ≤ 1` short-circuit is also `toPoly_mulFn`; the
    recursive case pushes `toPoly` through the recombination, rewrites the three
    subproducts via the induction hypothesis, recomposes both inputs via
    `loPart_add_hiPart_toPoly`, and closes with `ring`. -/
theorem karatsubaMul_toPoly (fuel : Nat) (p q : P) :
    (karatsubaMul fuel p q).toPoly = p.toPoly * q.toPoly := by
  induction fuel generalizing p q with
  | zero => simpa [karatsubaMul, schoolbookMul] using toPoly_mulFn p q
  | succ fuel ih =>
    rw [karatsubaMul]
    split
    · simpa [schoolbookMul] using toPoly_mulFn p q
    · set k := splitPoint p q
      set plo := loPart k p with hplo
      set phi := hiPart k p with hphi
      set qlo := loPart k q with hqlo
      set qhi := hiPart k q with hqhi
      -- Recompose the two inputs from their halves.
      have hp : p.toPoly = plo.toPoly + (Polynomial.X ^ k) * phi.toPoly :=
        (loPart_add_hiPart_toPoly k p).symm
      have hq : q.toPoly = qlo.toPoly + (Polynomial.X ^ k) * qhi.toPoly :=
        (loPart_add_hiPart_toPoly k q).symm
      -- Push toPoly through the recombination; rewrite subproducts via ih.
      simp only [toPoly_addFn, toPoly_subFn, toPoly_mulPowX, ih]
      rw [hp, hq]
      ring

/-- **Karatsuba ≡ schoolbook (denoted).** The benchmarked `karatsubaComp`
    denotes exactly the same `Polynomial Int` as the baseline `schoolbookComp`.
    Equality is on `toPoly` (the canonical product), not on the raw coefficient
    `Array`, since the recursion can introduce trailing zero coefficients. -/
theorem karatsubaComp_toPoly_eq_schoolbook (p q : P) :
    (karatsubaComp p q).toPoly = (schoolbookComp p q).toPoly := by
  rw [schoolbookComp, schoolbookMul, toPoly_mulFn, karatsubaComp, karatsubaMul_toPoly]

/-- The two computable products agree coefficientwise (`CPolynomial.Raw.equiv`),
    a direct corollary of `karatsubaComp_toPoly_eq_schoolbook` via `coeff_toPoly`. -/
theorem karatsubaComp_equiv_schoolbook (p q : P) :
    CPolynomial.Raw.Trim.equiv (karatsubaComp p q) (schoolbookComp p q) := by
  intro i
  rw [← Raw.coeff_toPoly, ← Raw.coeff_toPoly, karatsubaComp_toPoly_eq_schoolbook]

/-- On their canonical (trimmed) forms, the two products are literally equal
    arrays — the strongest available statement, upgrading the coefficientwise
    `equiv` via `CompPoly.CPolynomial.Raw.Trim.eq_of_equiv`. -/
theorem karatsubaComp_trim_eq_schoolbook (p q : P) :
    (karatsubaComp p q).trim = (schoolbookComp p q).trim :=
  CPolynomial.Raw.Trim.eq_of_equiv (karatsubaComp_equiv_schoolbook p q)

/-- **Correspondence with the verified abstract recursion.** The computable
    `karatsubaComp` over `CPolynomial.Raw Int` denotes the same `Polynomial Int`
    as the `noncomputable`, transfer-verified
    `Karatsuba.karatsubaRec` over `CPolynomial Int`, for any fuel and any
    canonical inputs `p' q'` whose denotations match the raw inputs. Both sides
    equal the true product `p.toPoly * q.toPoly`: the left by
    `karatsubaMul_toPoly` (this file), the right by
    `Karatsuba.karatsubaRec_eq` (the CoqEAL refinement transferred across
    `CPolynomial.ringEquiv`). This makes precise that `karatsubaComp` is the
    computable mirror of the verified algorithm. -/
theorem karatsubaComp_toPoly_eq_karatsubaRec
    (fuel : ℕ) (p q : P) (p' q' : CPolynomial Int)
    (hp : p'.toPoly = p.toPoly) (hq : q'.toPoly = q.toPoly) :
    (karatsubaComp p q).toPoly
      = (Karatsuba.karatsubaRec fuel p' q').toPoly := by
  rw [karatsubaComp, karatsubaMul_toPoly, Karatsuba.karatsubaRec_eq, hp, hq]

/-- Sanity check: Karatsuba and schoolbook agree on a small dense pair. This is
    the agreement check that used to sit inline in `KaratsubaBench.lean`; it is
    kept here so the runnable harness pays no elaboration cost for it. -/
example : (karatsubaComp (densePoly 8 0) (densePoly 8 17)
    == schoolbookComp (densePoly 8 0) (densePoly 8 17)) = true := by native_decide

end CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaBench
