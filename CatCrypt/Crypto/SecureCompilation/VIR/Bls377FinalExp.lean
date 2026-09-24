/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp12Inv

/-!
# A CONCRETE BLS12-377 final-exponentiation schedule on the relational `Fp12_377`

`RelationalFrontBls377Fp12Inv` makes the dodecic pairing field `Fp12_377 =
Fp6_377[w]/(w² − v)` operationally a field over the relational `bls12_377`
carrier: `Fp12_377.conj12` is the cyclotomic (`p⁶`-power) conjugation
`c0 + c1·w ↦ c0 − c1·w`, `Fp12_377.inv12` is the conjugate-over-norm inverse, and
`Fp12_377.commRing ξ₂ ξ₆` is the `CommRing`.

`Bls377MillerSteps` builds the concrete optimal-ate Miller value `concreteMiller`
and post-composes the final exponentiation `f ↦ f^((q¹²−1)/r)`.  This module
provides that final exponentiation as a **concrete total function** `finalExp377`
(noncomputable but constructed), so `Bls377MillerSteps.finalExp` is a built endomap
rather than a postulated constant.  The standard easy/hard factorisation of the
final exponent is

    (q¹²−1)/r = (q⁶−1)·(q²+1) · ((q⁴−q²+1)/r).
                └──── easy ────┘ └──── hard ────┘

## The easy part `f^((q⁶−1)(q²+1))` (CONSTRUCTED, tower algebra)

`finalExpEasy377 ξ₂ ξ₆ f = m · Frob²(m)` with `m = conj12 f · (inv12 f)`:

* `m = conj12 f · f⁻¹` is the `f^(q⁶−1)` step — the cyclotomic conjugation
  divided by `f`, both reused from `RelationalFrontBls377Fp12{Conj,Inv}` (the
  conjugation is the structural `p⁶`-Frobenius; `inv12` the conjugate-over-norm
  inverse, requiring `[Fact (Nat.Prime bls377Q)]` for the base-field inverse).
* `Frob²(m) = m^(q²)` is the `p²`-power Frobenius, here realised **literally** as
  the `q²`-power map `frobP2_377`.  In characteristic `q` the Frobenius
  endomorphism is `x ↦ x^q`, so `x ↦ x^(q²)` IS the second Frobenius power — a
  concrete total function, not a carried stand-in.
* `m · Frob²(m) = m^(q²+1)` is the `(q²+1)` step.

## The hard part `f^((q⁴−q²+1)/r)` (CONSTRUCTED as a fixed-exponent power)

`finalExpHard377 ξ₂ ξ₆ f = f ^ hardExp377` over the `Fp12_377` `CommRing`
(`Monoid.npow`), where `hardExp377 = (q⁴ − q² + 1)/r` is the BLS12-377 hard-part
exponent — the `12`th cyclotomic polynomial `Φ₁₂(q) = q⁴ − q² + 1` evaluated at
the base prime, divided by the subgroup order `r`.  `q = bls377Q` is the
`bls12_377` base-field prime (already defined); `r = bls377R` is the `bls12_377`
subgroup order (the Zexe / Aleo BLS12-377 `Fr` modulus,
`0x12ab655e…0a11800000000001`), added here.

## `finalExp377 = hard ∘ easy` (CONSTRUCTED)

`finalExp377 ξ₂ ξ₆ f = finalExpHard377 ξ₂ ξ₆ (finalExpEasy377 ξ₂ ξ₆ f)`.

`Bls377MillerSteps` instantiates this at the fixed tower nonresidues
`bls377Xi2, bls377Xi6` to obtain its `finalExp`, replacing the former axiom.

## Honesty boundary

The deliverable is a **concrete schedule** for the final exponentiation: one
fewer axiom-as-data in the pairing.  What is *constructed* here is the schedule —
the easy-part tower algebra (`conj12`, `inv12`, the `q²`-power Frobenius, two
multiplies) and the hard-part fixed-exponent power.  What is **NOT** claimed
proved is the *algebraic correctness* equality

    finalExp377 ξ₂ ξ₆ f = f ^ ((bls377Q¹² − 1) / bls377R)

i.e. that this schedule computes the `(q¹²−1)/r` power map landing the
Miller value in the order-`r` target group.  That equality rests on
`conj12 = (·)^(q⁶)` (the structural conjugation being the `p⁶`-Frobenius), the
tower Frobenius identities, and the easy/hard factorisation of the exponent —
deep facts about the concrete `bls12_377` tower parameters not formalised here.
It is stated above as a documented mathematical claim, **not** as an axiom and
**not** faked by a vacuous `rfl`.  What we *do* prove cleanly below: the hard
part and the `q²`-Frobenius are multiplicative monoid maps and fix `1`, and the
cyclotomic conjugation is an involution.

**0 sorries.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Bls377FinalExp

open CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. The BLS12-377 subgroup order and hard-part exponent constants -/

/-- The **`bls12_377` subgroup order `r`** (the `Fr` modulus, 253-bit): the Zexe /
    Aleo / SnarkVM BLS12-377 scalar-field prime
    `r = 0x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001`.
    Provenance: the published BLS12-377 `Fr` modulus (arkworks `ark-bls12-377`,
    Zexe). -/
def bls377R : Nat :=
  0x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001

/-- The **BLS12-377 hard-part exponent** `(q⁴ − q² + 1)/r = Φ₁₂(q)/r`, the
    `12`th cyclotomic polynomial evaluated at the base prime `q = bls377Q`,
    divided by the subgroup order `r = bls377R`.  This is the `r`-dependent factor
    of the final exponent `(q¹²−1)/r = (q⁶−1)(q²+1)·Φ₁₂(q)/r`.  A concrete `Nat`
    derived from the published BLS12-377 parameters. -/
def hardExp377 : Nat := (bls377Q ^ 4 - bls377Q ^ 2 + 1) / bls377R

/-! ## 2. The `q²`-power Frobenius `Frob²` as a literal power map

In characteristic `q` the Frobenius endomorphism of `Fp12_377` is `x ↦ x^q`, so
the second Frobenius power is the literal `q²`-power map.  We use it for the
`(q²+1)` step of the easy part. -/

/-- **The `p²`-power Frobenius on `Fp12_377`** realised as the literal `q²`-power
    map `f ↦ f^(q²)` over the `Fp12_377` `CommRing`.  Concrete and total. -/
noncomputable def frobP2_377 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377) :
    Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  f ^ (bls377Q ^ 2)

/-! ## 3. The easy part `f^((q⁶−1)(q²+1))`

`m = conj12 f · f⁻¹` is the `f^(q⁶−1)` step (conjugation over `f`); the easy part
is `m · Frob²(m) = m^(q²+1)`. -/

/-- **The easy part of the BLS12-377 final exponentiation**,
    `finalExpEasy377 ξ₂ ξ₆ f = m · Frob²(m)` with `m = conj12 f · (inv12 ξ₂ ξ₆ f)`.
    `m` is `f^(q⁶−1)` (the cyclotomic conjugation `conj12` divided by `f` via the
    conjugate-over-norm inverse `inv12`); `m · Frob²(m) = m^(q²+1)`.  Requires
    `[Fact (Nat.Prime bls377Q)]` for the base-field inverse inside `inv12`. -/
noncomputable def finalExpEasy377 [Fact (Nat.Prime bls377Q)]
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377) : Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  let m := Fp12_377.conj12 f * Fp12_377.inv12 ξ₂ ξ₆ f
  m * frobP2_377 ξ₂ ξ₆ m

/-! ## 4. The hard part `f^((q⁴−q²+1)/r)` as a fixed-exponent power -/

/-- **The hard part of the BLS12-377 final exponentiation**,
    `finalExpHard377 ξ₂ ξ₆ f = f ^ hardExp377` over the `Fp12_377` `CommRing`
    (`Monoid.npow`), the `r`-dependent `Φ₁₂(q)/r`-power. -/
noncomputable def finalExpHard377 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377) :
    Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  f ^ hardExp377

/-! ## 5. The full concrete final exponentiation `hard ∘ easy` -/

/-- **The concrete BLS12-377 final exponentiation** `finalExp377 ξ₂ ξ₆ =
    finalExpHard377 ξ₂ ξ₆ ∘ finalExpEasy377 ξ₂ ξ₆`.  A concrete total endomap of
    `Fp12_377` (the schedule `Bls377MillerSteps.finalExp` uses).  Its equality to the
    mathematical `(q¹²−1)/r` power map is documented in the module header, **not**
    asserted here. -/
noncomputable def finalExp377 [Fact (Nat.Prime bls377Q)]
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377) : Fp12_377 :=
  finalExpHard377 ξ₂ ξ₆ (finalExpEasy377 ξ₂ ξ₆ f)

/-! ## 6. Clean structural facts about the schedule

The hard part and the `q²`-Frobenius are multiplicative monoid maps fixing `1`
(`mul_pow` / `one_pow` over the `Fp12_377` `CommMonoid`), and the cyclotomic
conjugation is an involution (re-exported from `RelationalFrontBls377Fp12Conj`).
These are the parts that hold cleanly; algebraic correctness of the full
exponent is NOT among them (see the header). -/

/-- **`Frob²` fixes `1`** (`frobP2_377 ξ₂ ξ₆ 1 = 1`) — `1^(q²) = 1`. -/
theorem frobP2_377_one (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    frobP2_377 ξ₂ ξ₆ 1 = 1 := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  simp only [frobP2_377]
  exact one_pow _

/-- **`Frob²` is multiplicative** (`frobP2_377 (a·b) = frobP2_377 a · frobP2_377 b`)
    — the Frobenius is a monoid homomorphism; `(a·b)^(q²) = a^(q²)·b^(q²)` over the
    commutative `Fp12_377` monoid. -/
theorem frobP2_377_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (a b : Fp12_377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    frobP2_377 ξ₂ ξ₆ (a * b) = frobP2_377 ξ₂ ξ₆ a * frobP2_377 ξ₂ ξ₆ b := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  simp only [frobP2_377]
  exact mul_pow a b (bls377Q ^ 2)

/-- **The hard part fixes `1`** (`finalExpHard377 ξ₂ ξ₆ 1 = 1`) — `1^e = 1`. -/
theorem finalExpHard377_one (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    finalExpHard377 ξ₂ ξ₆ 1 = 1 := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  simp only [finalExpHard377]
  exact one_pow _

/-- **The hard part is multiplicative** (`finalExpHard377 (a·b) = finalExpHard377 a
    · finalExpHard377 b`) — the fixed-exponent power is a monoid homomorphism over
    the commutative `Fp12_377` monoid (`(a·b)^e = a^e·b^e`). -/
theorem finalExpHard377_mul (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (a b : Fp12_377) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    finalExpHard377 ξ₂ ξ₆ (a * b)
      = finalExpHard377 ξ₂ ξ₆ a * finalExpHard377 ξ₂ ξ₆ b := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  simp only [finalExpHard377]
  exact mul_pow a b hardExp377

/-- **`finalExp377` unfolds to `hard ∘ easy`** (definitional). -/
theorem finalExp377_eq [Fact (Nat.Prime bls377Q)]
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377) :
    finalExp377 ξ₂ ξ₆ f = finalExpHard377 ξ₂ ξ₆ (finalExpEasy377 ξ₂ ξ₆ f) := rfl

/-- **The cyclotomic conjugation is an involution** (`conj12 (conj12 f) = f`),
    re-exported from `RelationalFrontBls377Fp12Conj` — the `f^(q⁶−1)` step's
    `conj12` is the order-2 element of `Gal(Fp12 / Fp6)`. -/
theorem conj12_involutive (f : Fp12_377) :
    Fp12_377.conj12 (Fp12_377.conj12 f) = f :=
  Fp12_377.conj12_conj12 f

end CatCrypt.Crypto.SecureCompilation.VIR.Bls377FinalExp
