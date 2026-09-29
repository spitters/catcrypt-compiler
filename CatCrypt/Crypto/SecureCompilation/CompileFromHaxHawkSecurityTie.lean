/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMulTie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie
public import Transfer.Examples.PrimeWord

/-!
# Security tie: the compile-from-hax HAWK MAC leaf realizes the
  abstract `Zq1024` negacyclic-ring multiply-accumulate the security reference
  reasons over

`CompileFromHaxHawkMul` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `hawkMacForm` — the integer multiply-accumulate
`acc + a·b` followed by the `& 0x3FF` mask that is the HAWK `mod 2^10`
reduction — and `CompileFromHaxHawkMulTie` closes the last hop to the abstract
ring: reading the leaf's output back as a `Zq1024 = ZMod 1024` element via
`Zq1024.fromNat ∘ toNat`, it is exactly the ring multiply-accumulate
`accZ + aZ · bZ` (`CompileFromHaxHawkMulTie.hawkMacForm_eq_ring`).

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism, as the
FrodoKEM/NTRU/sntrup SecurityTie modules do): it packages that ring
multiply-accumulate as a one-field abstract `MacDeps` dependency record over
`Zq1024`, exhibits the *spec* instance (the abstract ring MAC the HAWK
negacyclic-convolution reference `HAWK/RingMul4WayVerified.ringMulCoeff` is
built from) and the *compiled-realization* instance (the function the
verified-compiled leaf actually computes, read back into `Zq1024`), proves them
equal field-by-field, and feeds that equality to `tie_transfer` so that **any**
property the security layer proves of the abstract ring MAC transfers verbatim
to the compiler-emitted leaf, with no new axioms.

## Why this is parametric-correct for HAWK (scope)

HAWK's security is parametric over the negacyclic lattice ring `Zq1024` and
reasons over it *abstractly* (through `ringMulCoeff`/`ringMul`, themselves
`Finset.sum`s of the ring MAC `acc + a·b mod 2^10`). The compiled leaf computes
exactly that ring MAC (`hawkMacForm_eq_ring`, unconditional: `1024 = 2^10`
divides `2^64`, so the `& 0x3FF` mask is exactly `% 1024` and handles full
`Z/1024` wraparound for any 64-bit inputs — no domain restriction, unlike the
prime-field GF(127)/sntrup ties). Therefore the tie is at the **arithmetic
building block** the parametric proof quantifies over: the realization equality
`toMacDeps = macDepsSpec` holds unconditionally and `tie_transfer` carries any ring-MAC
property onto the compiled artifact. It does **not** discharge the
NTRU/module-lattice (one-more-SIS / NTRU) assumption HAWK rests on, nor the
negacyclic index permutation `b[(k-i) mod N]` — those remain the parametric
hypotheses of `HAWK/Security.lean`; this ties the *emitted arithmetic* to the
*abstract arithmetic* the proof uses.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkSecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMul
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkMulTie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)
open CatCrypt.Util

/-! ## §1  The abstract one-field MAC dependency record

`MacDeps R` is the miniature `Dependencies` for a ring multiply-accumulate: the
single arithmetic primitive `mac : R → R → R → R` the HAWK negacyclic-ring
reference sums over. A security proof over the lattice ring is parametric over a
`MacDeps Zq1024` and reasons only through the *spec* the ring satisfies. -/

/-- The abstract ring multiply-accumulate dependency record over a ring `R`. -/
structure MacDeps (R : Type*) where
  /-- The multiply-accumulate primitive `acc a b ↦ acc + a · b`. -/
  mac : R → R → R → R

/-! ## §2  The abstract spec instance (what the security reference assumes)

`macDepsSpec` fills the field with the ring formula `acc + a · b` — exactly the
inner step `HAWK/RingMul4WayVerified.ringMulCoeff` accumulates over `Zq1024`. -/

/-- The abstract spec instance: the `Zq1024` ring multiply-accumulate
    `accZ ↦ accZ + aZ · bZ` that the HAWK negacyclic-ring reference sums. -/
def macDepsSpec : MacDeps Zq1024 where
  mac := fun acc a b => acc + a * b

/-! ## §3  The compiled realization instance (what the verified compiler emits)

`compiledMacFn` is the function the verified-compiled jasmin `Com` actually
computes, read back as a `Zq1024` element via `Zq1024.fromNat ∘ toNat` of the
emitted `hawkMacForm`. -/

/-- Encode a `Zq1024` ring element as a `BitVec 64` (its canonical residue). -/
def encZ (x : Zq1024) : BitVec 64 := Transfer.PrimeWord.primeWord 1024 x

/-- The function the verified-compiled HAWK MAC `Com` computes, read back into
    `Zq1024`: each of `acc`, `a`, `b` is encoded as the `BitVec 64` of its
    canonical residue (`encZ`), and the leaf output is read back via
    `Zq1024.fromNat ∘ toNat`. -/
noncomputable def compiledMacFn (acc a b : Zq1024) : Zq1024 :=
  Zq1024.fromNat (hawkMacForm (encZ acc) (encZ a) (encZ b)).toNat

/-- The compiled-realization instance: the abstract `MacDeps Zq1024` filled with
    the function the **verified compiler emits** for the HAWK MAC. -/
noncomputable def toMacDeps : MacDeps Zq1024 where
  mac := compiledMacFn

/-! ## §4  The realization theorem and the generic transfer

The compiled MAC, applied to `Zq1024` ring elements, equals the abstract ring
MAC. This is `hawkMacForm_eq_ring` reading the `BitVec` inputs back via
`Zq1024.fromNat ∘ toNat`, plus the `Zq1024` encode round-trip
`Zq1024.fromNat (encZ x).toNat = x`. -/

/-- **The realization theorem (unconditional on the abstract ring layer).** The
    compiler-emitted MAC instance equals the abstract ring-MAC spec instance: on
    every triple of `Zq1024` ring elements, the verified-compiled HAWK leaf
    computes exactly the ring multiply-accumulate `acc + a · b`. Closed by
    `hawkMacForm_eq_ring` (the power-of-two `mod 2^10` reduce identity) plus the
    `Zq1024` round-trip `Zq1024.fromNat ∘ ZMod.val = id`. No domain restriction:
    the `& 0x3FF` mask handles full `Z/1024` wraparound for any 64-bit inputs. -/
theorem toMacDeps_eq_spec : toMacDeps = macDepsSpec := by
  have hround : ∀ x : Zq1024, Zq1024.fromNat (encZ x).toNat = x :=
    Transfer.PrimeWord.primeDec_primeWord (by decide)
  unfold toMacDeps macDepsSpec compiledMacFn
  congr 1
  funext acc a b
  rw [hawkMacForm_eq_ring, hround, hround, hround]

/-- **Compiled HAWK MAC inherits any abstract ring-MAC property.** For every
    property `P` of `MacDeps Zq1024`, if `P` holds of the abstract ring-MAC spec
    instance then it holds of the compiler-emitted realization instance. The
    mechanized statement that the verified-compiled HAWK arithmetic leaf plugs
    into the abstract negacyclic-lattice security layer: any property the
    parametric `HAWK/Security.lean` proof establishes over the abstract ring MAC
    transfers verbatim to `toMacDeps`, the verified compiler's emitted primitive
    — with no new axioms. Instantiates `CompileFromHaxSecurityTie.tie_transfer`
    at `Deps := MacDeps Zq1024` with the HAWK realization equality. -/
theorem appliesToCompiledHawk (P : MacDeps Zq1024 → Prop) (h : P macDepsSpec) :
    P toMacDeps :=
  tie_transfer P toMacDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxHawkSecurityTie
