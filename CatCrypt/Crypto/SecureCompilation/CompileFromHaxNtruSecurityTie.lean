/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMulTie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie
public import Transfer.Examples.PrimeWord

/-!
# Security tie: the compile-from-hax NTRU-HRSS MAC leaf realizes the
  abstract `Zq8192` ring multiply-accumulate the security reference reasons over

`CompileFromHaxNtruMul` proves the verified compiler *emits* a jasmin `Com` whose
`BitVec 64` denotation is `ntruMacForm`, and `CompileFromHaxNtruMulTie` closes the
last hop to the abstract ring: reading the leaf's output back as a
`Zq8192 = ZMod 8192` element via `Zq8192.fromNat ∘ toNat`, it is exactly the ring
multiply-accumulate `accZ + aZ · bZ`
(`CompileFromHaxNtruMulTie.ntruMacForm_eq_ring`).

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism): it packages that ring
multiply-accumulate as a one-field abstract `MacDeps` dependency record, exhibits
the *spec* instance (the abstract ring MAC the NTRU-HRSS cyclic-convolution
reference `NTRU/NtruhrssRingMulVerified.ringMulCoeff` is built from) and the
*compiled-realization* instance (the function the verified-compiled leaf computes,
read back into `Zq8192`), proves them equal field-by-field, and feeds that
equality to `tie_transfer`: **any** property the security layer proves of the
abstract ring MAC transfers verbatim to the compiler-emitted leaf, with no new
axioms.

## Parametric-correct scope

NTRU-HRSS's `NTRU/SurfaceDeps.lean` reasons over the ring `Zq8192` abstractly
(through `ringMulVerified`/`ringMulCoeff`, themselves cyclic `Finset.sum`s of the
ring MAC `acc + a·b`). The compiled leaf computes exactly that ring MAC
(`ntruMacForm_eq_ring`, no domain restriction — the `mod 2^13` mask handles full
wraparound). The tie is therefore at the **arithmetic building block** the proof
quantifies over; the realization equality `toMacDeps = macDepsSpec` holds and
`tie_transfer` carries any ring-MAC property onto the compiled artifact. It does
**not** discharge the NTRU one-wayness assumption or the SXY/FO transform — those
remain the hypotheses of `NTRU/Security.lean`; this ties the *emitted arithmetic*
to the *abstract arithmetic* the proof uses, which is the scope of this module.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruSecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMul
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruMulTie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)
open CatCrypt.Util

/-! ## §1  The abstract one-field MAC dependency record -/

/-- The abstract ring multiply-accumulate dependency record over a ring `R`. -/
structure MacDeps (R : Type*) where
  /-- The multiply-accumulate primitive `acc a b ↦ acc + a · b`. -/
  mac : R → R → R → R

/-! ## §2  The abstract spec instance (what the security reference assumes) -/

/-- The abstract spec instance: the `Zq8192` ring multiply-accumulate
    `accZ ↦ accZ + aZ · bZ` that the NTRU-HRSS cyclic-convolution reference sums. -/
def macDepsSpec : MacDeps Zq8192 where
  mac := fun acc a b => acc + a * b

/-! ## §3  The compiled realization instance (what the verified compiler emits) -/

/-- Encode a `Zq8192` ring element as a `BitVec 64` (its canonical residue). -/
def encZ (x : Zq8192) : BitVec 64 := Transfer.PrimeWord.primeWord 8192 x

/-- The function the verified-compiled NTRU-HRSS MAC `Com` computes, read back into
    `Zq8192`. -/
noncomputable def compiledMacFn (acc a b : Zq8192) : Zq8192 :=
  Zq8192.fromNat (ntruMacForm (encZ acc) (encZ a) (encZ b)).toNat

/-- The compiled-realization instance: the abstract `MacDeps Zq8192` filled with the
    function the **verified compiler emits** for the NTRU-HRSS MAC. -/
noncomputable def toMacDeps : MacDeps Zq8192 where
  mac := compiledMacFn

/-! ## §4  The realization theorem and the generic transfer -/

/-- **The realization theorem.** The compiler-emitted MAC instance equals the
    abstract ring-MAC spec instance: on every triple of `Zq8192` ring elements, the
    verified-compiled NTRU-HRSS leaf computes exactly the ring multiply-accumulate
    `acc + a · b`. Closed by `ntruMacForm_eq_ring` (the power-of-two reduce
    identity) plus the `Zq8192` round-trip. -/
theorem toMacDeps_eq_spec : toMacDeps = macDepsSpec := by
  have hround : ∀ x : Zq8192, Zq8192.fromNat (encZ x).toNat = x :=
    Transfer.PrimeWord.primeDec_primeWord (by decide)
  unfold toMacDeps macDepsSpec compiledMacFn
  congr 1
  funext acc a b
  rw [ntruMacForm_eq_ring, hround, hround, hround]

/-- **Compiled NTRU-HRSS MAC inherits any abstract ring-MAC property.** Instantiates
    `CompileFromHaxSecurityTie.tie_transfer` at `Deps := MacDeps Zq8192` with the
    NTRU-HRSS realization equality: any property the parametric `NTRU/Security.lean`
    proof establishes over the abstract ring MAC transfers verbatim to `toMacDeps`,
    the verified compiler's emitted primitive — with no new axioms. -/
theorem appliesToCompiledNtru (P : MacDeps Zq8192 → Prop) (h : P macDepsSpec) :
    P toMacDeps :=
  tie_transfer P toMacDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxNtruSecurityTie
