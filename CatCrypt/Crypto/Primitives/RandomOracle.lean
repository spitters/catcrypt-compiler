/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.SHAKE128
public import CatCrypt.Crypto.Advantage

/-!
# Random Oracle Game for SHAKE-128

This file defines the random-oracle distinguishing game for SHAKE-128:
the real game gives a distinguisher `shake128`, the ideal game a given
random function, and `RO_Advantage` is the difference of the two
probabilities of `true`. Protocols modelled in the random oracle model
state their bounds in terms of `RO_Advantage`.

## Design

The random oracle model (ROM) treats SHAKE-128 as a uniformly random
function. `RO_Advantage` is the distinguishing probability
between the real SHAKE-128 and a lazy-sampled random function.

This is standard in hash-based cryptography (SLH-DSA, XMSS, SPHINCS+)
and is the assumption made by NIST FIPS 205.

## References

* Bellare, Rogaway — *Random Oracles are Practical*, CCS 1993
* FIPS 202 — SHA-3 Standard
* FIPS 205 — SLH-DSA (assumes SHAKE is a random oracle)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.RandomOracle

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Primitives.SHAKE128
open scoped ENNReal

/-! ## Random Oracle Game -/

/-- A random oracle distinguisher: given oracle access to a function
    `List UInt8 → Nat → List UInt8`, outputs a boolean guess. -/
abbrev RODistinguisher :=
  (List UInt8 → Nat → List UInt8) → SDistr Bool

/-- Probability of `true` in a Bool sub-distribution. -/
noncomputable def prTrue' (d : SDistr Bool) : ℝ≥0∞ := d (some true)

/-- Random oracle real game: the distinguisher gets access to the
    real SHAKE-128 function. -/
noncomputable def RO_Real (D : RODistinguisher) : SDistr Bool :=
  D shake128

/-- Random oracle ideal game: the distinguisher gets access to a
    lazily-sampled random function.

    In the formal model, this is a uniformly random function
    `List UInt8 → Nat → List UInt8`. We model it as an abstract
    random oracle distribution. -/
noncomputable def RO_Ideal (randomOracle : List UInt8 → Nat → List UInt8)
    (D : RODistinguisher) : SDistr Bool :=
  D randomOracle

/-- Absolute difference for ENNReal. -/
noncomputable def absDiff' (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) ⊔ (b - a)

/-- Random oracle advantage: the distinguishing probability between
    SHAKE-128 and an ideal random function. -/
noncomputable def RO_Advantage
    (randomOracle : List UInt8 → Nat → List UInt8)
    (D : RODistinguisher) : ℝ≥0∞ :=
  absDiff' (prTrue' (RO_Real D)) (prTrue' (RO_Ideal randomOracle D))

end CatCrypt.Crypto.Primitives.RandomOracle
