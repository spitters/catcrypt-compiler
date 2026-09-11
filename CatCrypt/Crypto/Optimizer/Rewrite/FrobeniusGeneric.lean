/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.Finite.Basic


@[expose] public section
set_option autoImplicit false

/-!
# The Frobenius endomorphism as a generic optimizer rewrite

The **Frobenius endomorphism** `x ↦ x ^ p` over a commutative ring `R` of
(exponential) characteristic `p` is the algebraic backbone of extension-field
arithmetic in pairing-based cryptography: the final-exponentiation step of a
pairing, sparse subfield multiplication, and the `p`-power tower maps of an
extension `𝔽_{p^k}` are all expressed through it. A rewrite pass that wants to
replace a `p`-power (or a `p^k`-power) by a single Frobenius application — or to
push a Frobenius through a sum / product / power — needs the fact that this map
is a **ring endomorphism**, the so-called *freshman's dream*
`(a + b) ^ p = a ^ p + b ^ p`.

Mathlib already proves all of this generically: `frobenius R p : R →+* R` is the
Frobenius `RingHom` for `[CommRing R] [ExpChar R p]`, with `add_pow_char` /
`map_add` for the additive law and `iterateFrobenius` for the `p^k`-fold
iterate. **This file does not re-prove that core.** It re-exports the Mathlib
API as the clean "Frobenius is a ring endomorphism" surface that the
extension-field / pairing passes consume, plus the worked `ZMod p` example where
Frobenius collapses to the identity (Fermat's little theorem).

* `frobeniusHom R p : R →+* R` — the endomorphism itself (`= frobenius R p`),
  with `frobeniusHom_apply : frobeniusHom R p a = a ^ p`.
* The ring-endomorphism laws as standalone rewrite certificates:
  `frob_add` (freshman's dream), `frob_mul`, `frob_one`, `frob_zero`,
  `frob_pow`, `frob_mul_eq` (`p`-power of a product).
* `frob_iterate` / `frobIterateHom` — the `k`-fold iterate is the `p^k`-power,
  i.e. the Frobenius of the degree-`k` subfield, the shape the tower map uses.
* `frobenius_zmod_id` / `frob_zmod_eq_self` — over `ZMod p` the Frobenius is the
  identity (Fermat), the degenerate base case of any extension tower.

All laws are discharged by reduction to the Mathlib core; only the standard
`propext` / `Classical.choice` / `Quot.sound` axioms are used.
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.FrobeniusGeneric

open scoped Classical

section CommRing

variable (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p]

/-- The Frobenius endomorphism `x ↦ x ^ p` of a commutative ring `R` of
exponential characteristic `p`, packaged as a `RingHom`. This is definitionally
Mathlib's `frobenius R p`; we expose it under the optimizer namespace so a
rewrite pass can name the canonical endomorphism it folds `p`-powers into. -/
noncomputable def frobeniusHom : R →+* R := frobenius R p

@[simp] theorem frobeniusHom_eq : frobeniusHom R p = frobenius R p := rfl

/-- `frobeniusHom` evaluates to the `p`-power: the defining equation of the
rewrite `x ^ p ⤳ frobeniusHom R p x`. -/
@[simp] theorem frobeniusHom_apply (a : R) : frobeniusHom R p a = a ^ p := by
  rw [frobeniusHom_eq, frobenius_def]

variable {R p}

/-- **Freshman's dream.** The additive law of the Frobenius endomorphism:
`(a + b) ^ p = a ^ p + b ^ p`. This is the soundness certificate for a pass that
distributes a `p`-power over a sum. -/
theorem frob_add (a b : R) : (a + b) ^ p = a ^ p + b ^ p := by
  rw [add_pow_expChar]

/-- The Frobenius `RingHom` is additive: `frobeniusHom R p (a + b)
= frobeniusHom R p a + frobeniusHom R p b`. -/
theorem frob_hom_add (a b : R) :
    frobeniusHom R p (a + b) = frobeniusHom R p a + frobeniusHom R p b :=
  map_add _ a b

omit [ExpChar R p] in
/-- Multiplicativity: `(a * b) ^ p = a ^ p * b ^ p`. -/
theorem frob_mul_eq (a b : R) : (a * b) ^ p = a ^ p * b ^ p :=
  mul_pow a b p

/-- The Frobenius `RingHom` is multiplicative. -/
theorem frob_mul (a b : R) :
    frobeniusHom R p (a * b) = frobeniusHom R p a * frobeniusHom R p b :=
  map_mul _ a b

/-- The Frobenius `RingHom` fixes `1`. -/
@[simp] theorem frob_one : frobeniusHom R p 1 = 1 := map_one _

/-- The Frobenius `RingHom` fixes `0`. -/
@[simp] theorem frob_zero : frobeniusHom R p 0 = 0 := map_zero _

/-- The Frobenius `RingHom` commutes with powers: it pushes through `(· ^ n)`. -/
theorem frob_pow (a : R) (n : ℕ) :
    frobeniusHom R p (a ^ n) = frobeniusHom R p a ^ n :=
  map_pow _ a n

end CommRing

section Iterate

variable (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p]

/-- The `k`-fold iterate of Frobenius, `x ↦ x ^ (p ^ k)`, packaged as a
`RingHom`. This is the Frobenius of the degree-`k` extension `𝔽_{p^k}` — the
map an extension-field tower threads as it walks up the degrees. -/
noncomputable def frobIterateHom (k : ℕ) : R →+* R := iterateFrobenius R p k

@[simp] theorem frobIterateHom_eq (k : ℕ) :
    frobIterateHom R p k = iterateFrobenius R p k := rfl

variable {R p}

/-- The `k`-fold Frobenius is the `p ^ k`-power: the rewrite
`x ^ (p ^ k) ⤳ frobIterateHom R p k x` that collapses a repeated `p`-power
(e.g. a pairing final exponentiation exponent of the form `p^k`) into one
iterated Frobenius. -/
theorem frob_iterate (a : R) (k : ℕ) : frobIterateHom R p k a = a ^ p ^ k := by
  rw [frobIterateHom_eq, iterateFrobenius_def]

/-- The iterated Frobenius `RingHom` is additive — the freshman's dream at the
subfield `𝔽_{p^k}`: `(a + b) ^ (p ^ k) = a ^ (p ^ k) + b ^ (p ^ k)`. -/
theorem frob_iterate_add (a b : R) (k : ℕ) :
    (a + b) ^ p ^ k = a ^ p ^ k + b ^ p ^ k := by
  have h := map_add (iterateFrobenius R p k) a b
  simpa only [iterateFrobenius_def] using h

end Iterate

section ZMod

variable (p : ℕ) [Fact p.Prime]

/-- Over the prime field `ZMod p` the Frobenius endomorphism is the **identity**:
`x ^ p = x` for all `x` (Fermat's little theorem). This is the degenerate base
case of any `𝔽_{p^k}` tower — the bottom field is Frobenius-fixed. -/
theorem frobenius_zmod_id : frobeniusHom (ZMod p) p = RingHom.id (ZMod p) := by
  simpa only [frobeniusHom_eq] using ZMod.frobenius_zmod p

/-- Pointwise form of `frobenius_zmod_id`: `x ^ p = x` in `ZMod p`. -/
theorem frob_zmod_eq_self (a : ZMod p) : frobeniusHom (ZMod p) p a = a := by
  rw [frobenius_zmod_id]; rfl

/-- The raw `p`-power identity over `ZMod p` (Fermat), the form a constant-fold
pass uses directly on a `ZMod p` literal. -/
theorem zmod_pow_card (a : ZMod p) : a ^ p = a := ZMod.pow_card a

end ZMod

end CatCrypt.Crypto.Optimizer.Rewrite.FrobeniusGeneric
