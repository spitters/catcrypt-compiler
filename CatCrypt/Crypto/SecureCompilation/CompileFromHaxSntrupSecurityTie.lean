/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMulTie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie

/-!
# Security tie: the compile-from-hax sntrup761 MAC leaf realizes the
  abstract `Zq4591` field multiply-accumulate the security reference reasons over

`CompileFromHaxSntrupMul` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `sntrupMacForm` (the unreduced integer
multiply-accumulate `acc + a·b`), and `CompileFromHaxSntrupMulTie` closes the last
hop to the abstract prime field: reading the leaf's output back as a
`Zq4591 = ZMod 4591` element via `Zq4591.fromNat ∘ toNat`, it is exactly the field
multiply-accumulate `accZ + aZ · bZ`
(`CompileFromHaxSntrupMulTie.sntrupMacForm_eq_ring`) **on the schoolbook domain**.

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism), packaging that field
multiply-accumulate as a one-field abstract `MacDeps` record over `Zq4591`,
exhibiting the *spec* instance (the abstract field MAC the Streamlined NTRU Prime
schoolbook reference `NTRU/Sntrup761MulVerified.coeffSum` is built from) and the
*compiled-realization* instance, proving them equal field-by-field, and feeding
that equality to `tie_transfer`.

## The prime-modulus differential and why the abstract-layer tie is unconditional

`4591` is prime and does not divide `2^64`, so `sntrupMacForm_eq_ring` carries a
**domain restriction** (`a, b < 4591`, `acc < 2^63`): a `BitVec 64` wrap would
corrupt the mod-`4591` residue (cf. the GF(127) tie). When we represent the
operands as **abstract `Zq4591` field elements** (the representation
`coeffSum` actually sums over — it is a `Finset.sum` of `Zq4591` products, so
every partial accumulator is already reduced `< 4591`), encoding via `encZ` gives
`(encZ x).toNat = x.val < 4591`, which discharges *all three* domain hypotheses
automatically (`4591 < 2^63`). Hence on the abstract field layer the realization
equality `toMacDeps = macDepsSpec` is **unconditional**, and `tie_transfer` carries
any field-MAC property onto the compiled artifact with no new axioms.

Honest note on the schoolbook running accumulator: a hand-written inner loop that
defers reduction would carry an *unreduced* `acc` (up to `16·4591² < 2^63`); for
that representation the domain-restricted `sntrupMacForm_eq_ring` (with its
explicit `acc < 2^63` hypothesis) is the relevant tie. The abstract `coeffSum`
reference reduces each step, so the per-step ring elements stay `< 4591` and the
unconditional form here is the right one for the security-consumed reference. The
tie does **not** discharge the NTRU-Prime one-wayness / SXY assumption — that
remains the hypothesis of `NTRU/Security.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupSecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMul
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupMulTie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)
open CatCrypt.Util

/-! ## §1  The abstract one-field MAC dependency record -/

/-- The abstract field multiply-accumulate dependency record over a ring `R`. -/
structure MacDeps (R : Type*) where
  /-- The multiply-accumulate primitive `acc a b ↦ acc + a · b`. -/
  mac : R → R → R → R

/-! ## §2  The abstract spec instance -/

/-- The abstract spec instance: the `Zq4591` field multiply-accumulate
    `accZ ↦ accZ + aZ · bZ` that the sntrup761 schoolbook reference sums. -/
def macDepsSpec : MacDeps Zq4591 where
  mac := fun acc a b => acc + a * b

/-! ## §3  The compiled realization instance -/

/-- Encode a `Zq4591` field element as a `BitVec 64` (its canonical residue
    `< 4591`). -/
def encZ (x : Zq4591) : BitVec 64 := BitVec.ofNat 64 x.val

/-- `(encZ x).toNat = x.val` (the residue `< 4591 < 2^64` does not wrap). -/
theorem encZ_toNat (x : Zq4591) : (encZ x).toNat = x.val := by
  unfold encZ
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega)]

/-- The function the verified-compiled sntrup761 MAC `Com` computes, read back into
    `Zq4591`. -/
noncomputable def compiledMacFn (acc a b : Zq4591) : Zq4591 :=
  Zq4591.fromNat (sntrupMacForm (encZ acc) (encZ a) (encZ b)).toNat

/-- The compiled-realization instance: the abstract `MacDeps Zq4591` filled with the
    function the **verified compiler emits** for the sntrup761 MAC. -/
noncomputable def toMacDeps : MacDeps Zq4591 where
  mac := compiledMacFn

/-! ## §4  The realization theorem and the generic transfer -/

/-- **The realization theorem (unconditional on the abstract field layer).** The
    compiler-emitted MAC instance equals the abstract field-MAC spec instance: on
    every triple of `Zq4591` field elements, the verified-compiled sntrup761 leaf
    computes exactly the field multiply-accumulate `acc + a · b`. The
    domain-restricted `sntrupMacForm_eq_ring` applies because `encZ` of a residue
    is `< 4591 < 2^63` (all three schoolbook bounds discharged automatically), plus
    the `Zq4591` round-trip. -/
theorem toMacDeps_eq_spec : toMacDeps = macDepsSpec := by
  have hround : ∀ x : Zq4591, Zq4591.fromNat (encZ x).toNat = x := by
    intro x
    unfold Zq4591.fromNat
    rw [encZ_toNat, ZMod.natCast_val, ZMod.cast_id]
  have hlt4591 : ∀ x : Zq4591, encZ x < 4591#64 := by
    intro x
    rw [BitVec.lt_def, encZ_toNat]
    have := ZMod.val_lt x
    simpa using this
  have hacc : ∀ x : Zq4591, (encZ x).toNat < 2 ^ 63 := by
    intro x
    rw [encZ_toNat]
    have := ZMod.val_lt x; omega
  unfold toMacDeps macDepsSpec compiledMacFn
  congr 1
  funext acc a b
  rw [sntrupMacForm_eq_ring (encZ acc) (encZ a) (encZ b)
      (hacc acc) (hlt4591 a) (hlt4591 b), hround, hround, hround]

/-- **Compiled sntrup761 MAC inherits any abstract field-MAC property.** Instantiates
    `CompileFromHaxSecurityTie.tie_transfer` at `Deps := MacDeps Zq4591` with the
    sntrup761 realization equality: any property the parametric `NTRU/Security.lean`
    proof establishes over the abstract field MAC transfers verbatim to `toMacDeps`,
    the verified compiler's emitted primitive — with no new axioms. -/
theorem appliesToCompiledSntrup (P : MacDeps Zq4591 → Prop) (h : P macDepsSpec) :
    P toMacDeps :=
  tie_transfer P toMacDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSntrupSecurityTie
