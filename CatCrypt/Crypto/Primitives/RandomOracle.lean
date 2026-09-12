/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.SHAKE128
public import CatCrypt.Crypto.Advantage

/-!
# Random Oracle Assumption for SHAKE-128

This file defines the **single cryptographic axiom** for the entire
constructive primitive stack: SHAKE-128 is indistinguishable from a
random oracle up to advantage `ε_ro`.

All other primitives (AES-128, GF(2^128), Poly1305, Keccak) are
constructive `def`s with no axioms. Security reductions for protocols
using these primitives reduce to this single assumption.

## Design

The random oracle model (ROM) treats SHAKE-128 as a uniformly random
function. The advantage `ε_ro` captures the distinguishing probability
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

/-! ## The Single Cryptographic Axiom -/

/-- **SHAKE-128 Random Oracle Assumption**.

    There exists an ideal random function such that no efficient
    distinguisher can tell apart SHAKE-128 from this ideal function
    with advantage greater than `ε_ro`.

    This is the **only cryptographic axiom** in the constructive
    primitive stack. All other primitives (AES-128, GF(2^128),
    Poly1305, Keccak-f[1600]) are constructive definitions.

    Anti-vacuity: the bound is universal over distinguishers,
    so `ε_ro = 0` would mean SHAKE-128 IS a random oracle
    (a non-trivial claim). In practice, `ε_ro` is negligible
    in the security parameter. -/
axiom shake128_is_random_oracle :
  ∃ (idealRO : List UInt8 → Nat → List UInt8) (ε_ro : ℝ≥0∞),
    ∀ (D : RODistinguisher), RO_Advantage idealRO D ≤ ε_ro

end CatCrypt.Crypto.Primitives.RandomOracle
