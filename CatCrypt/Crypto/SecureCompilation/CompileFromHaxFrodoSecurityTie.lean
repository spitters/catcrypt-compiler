/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMacTie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie
public import Transfer.Examples.PrimeWord

/-!
# Security tie: the compile-from-hax FrodoKEM MAC leaf realizes the
  abstract `Zq65536` ring multiply-accumulate the security reference reasons over

`CompileFromHaxFrodoMac` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `frodoMacForm`, and `CompileFromHaxFrodoMacTie`
closes the last hop to the abstract ring: reading the leaf's output back as a
`Zq65536 = ZMod 65536` element via `Zq65536.fromNat ∘ toNat`, it is exactly the
ring multiply-accumulate `accZ + aZ · bZ`
(`CompileFromHaxFrodoMacTie.frodoMacForm_eq_field`).

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism, as the ML-KEM/ML-DSA
Category-B wiring does): it packages that ring multiply-accumulate as a one-field
abstract `MacDeps` dependency record, exhibits the *spec* instance (the abstract
ring MAC the FrodoKEM matrix–vector reference `Frodo/FrodoMatmulVerified.matmulRow`
is built from) and the *compiled-realization* instance (the function the
verified-compiled leaf actually computes, read back into `Zq65536`), proves them
equal field-by-field, and feeds that equality to `tie_transfer` so that **any**
property the security layer proves of the abstract ring MAC transfers verbatim to
the compiler-emitted leaf, with no new axioms.

## Why this is parametric-correct for FrodoKEM (scope)

FrodoKEM's `SurfaceDeps` is `@canonical_parametric`: the security predicate
`FrodoSecure` is parametric over the plain-LWE parameters and reasons over the
ring `Zq65536` *abstractly* (through `matmulVerified`/`matmulRow`, themselves
`Finset.sum`s of the ring MAC `acc + a·b`). The compiled leaf computes exactly
that ring MAC (`frodoMacForm_eq_field`). Therefore the tie is at the **arithmetic
building block** the parametric proof quantifies over: the realization equality
`toMacDeps = macDepsSpec` holds unconditionally and `tie_transfer` carries any ring-MAC
property onto the compiled artifact. It does **not** discharge the LWE assumption
or instantiate the matrix dimension — those remain the parametric hypotheses of
`Frodo/Security.lean`; this ties the *emitted arithmetic* to the *abstract
arithmetic* the proof uses.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoSecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMac
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoMacTie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)
open CatCrypt.Util

/-! ## §1  The abstract one-field MAC dependency record

`MacDeps R` is the miniature `Dependencies` for a ring multiply-accumulate: the
single arithmetic primitive `mac : R → R → R → R` the FrodoKEM matrix–vector
reference sums over. A security proof over the dense-LWE kernel is parametric
over a `MacDeps Zq65536` and reasons only through the *spec* the field satisfies. -/

/-- The abstract ring multiply-accumulate dependency record over a ring `R`. -/
structure MacDeps (R : Type*) where
  /-- The multiply-accumulate primitive `acc a b ↦ acc + a · b`. -/
  mac : R → R → R → R

/-! ## §2  The abstract spec instance (what the security reference assumes)

`macDepsSpec` fills the field with the ring formula `acc + a · b` — exactly the
inner step `Frodo/FrodoMatmulVerified.matmulRow` accumulates over `Zq65536`. -/

/-- The abstract spec instance: the `Zq65536` ring multiply-accumulate
    `accZ ↦ accZ + aZ · bZ` that the FrodoKEM LWE matrix–vector reference sums. -/
def macDepsSpec : MacDeps Zq65536 where
  mac := fun acc a b => acc + a * b

/-! ## §3  The compiled realization instance (what the verified compiler emits)

`compiledMacFn` is the function the verified-compiled jasmin `Com` actually
computes, read back as a `Zq65536` element via `Zq65536.fromNat ∘ toNat` of the
emitted `frodoMacForm`. -/

/-- Encode a `Zq65536` ring element as a `BitVec 64` (its canonical residue). -/
def encZ (x : Zq65536) : BitVec 64 := Transfer.PrimeWord.primeWord 65536 x

/-- The function the verified-compiled FrodoKEM MAC `Com` computes, read back into
    `Zq65536`: each of `acc`, `a`, `b` is encoded as the `BitVec 64` of its
    canonical residue (`encZ`), and the leaf output is read back via
    `Zq65536.fromNat ∘ toNat`. -/
noncomputable def compiledMacFn (acc a b : Zq65536) : Zq65536 :=
  Zq65536.fromNat (frodoMacForm (encZ acc) (encZ a) (encZ b)).toNat

/-- The compiled-realization instance: the abstract `MacDeps Zq65536` filled with
    the function the **verified compiler emits** for the FrodoKEM MAC. -/
noncomputable def toMacDeps : MacDeps Zq65536 where
  mac := compiledMacFn

/-! ## §4  The realization theorem and the generic transfer

The compiled MAC, applied to inputs whose `BitVec 64` encoding round-trips
(`Zq65536.fromNat acc.val.toNat = acc`, etc.), equals the abstract ring MAC. This
is `frodoMacForm_eq_field` reading the `BitVec` inputs as their own `fromNat`. -/

/-- **The realization theorem.** The compiler-emitted MAC instance equals the
    abstract ring-MAC spec instance: on every triple of `Zq65536` ring elements,
    the verified-compiled FrodoKEM leaf computes exactly the ring multiply-
    accumulate `acc + a · b`. Closed by `frodoMacForm_eq_field` (the
    power-of-two reduce identity) plus the `Zq65536` round-trip
    `Zq65536.fromNat ∘ ZMod.val = id`. -/
theorem toMacDeps_eq_spec : toMacDeps = macDepsSpec := by
  have hround : ∀ x : Zq65536, Zq65536.fromNat (encZ x).toNat = x :=
    Transfer.PrimeWord.primeDec_primeWord (by decide)
  unfold toMacDeps macDepsSpec compiledMacFn
  congr 1
  funext acc a b
  rw [frodoMacForm_eq_field, hround, hround, hround]

/-- **Compiled FrodoKEM MAC inherits any abstract ring-MAC property.** For every
    property `P` of `MacDeps Zq65536`, if `P` holds of the abstract ring-MAC spec
    instance then it holds of the compiler-emitted realization instance. The
    mechanized statement that the verified-compiled FrodoKEM arithmetic leaf plugs
    into the abstract dense-LWE security layer: any property the parametric
    `Frodo/Security.lean` proof establishes over the abstract ring MAC transfers
    verbatim to `toMacDeps`, the verified compiler's emitted primitive — with no
    new axioms. Instantiates `CompileFromHaxSecurityTie.tie_transfer` at
    `Deps := MacDeps Zq65536` with the FrodoKEM realization equality. -/
theorem appliesToCompiledFrodo (P : MacDeps Zq65536 → Prop) (h : P macDepsSpec) :
    P toMacDeps :=
  tie_transfer P toMacDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxFrodoSecurityTie
