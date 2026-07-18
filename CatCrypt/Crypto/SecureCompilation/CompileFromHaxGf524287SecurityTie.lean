/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287Tie
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie

/-!
# #607 security tie: the compile-from-hax GF(524287) multiply leaf realizes the
  abstract `Zq524287` Mersenne-19 base-field multiply

`CompileFromHaxGf524287` proves the verified compiler *emits* a jasmin `Com` whose
`BitVec 64` denotation is `gf524287MulFold` — the Mersenne `2¹⁹ ≡ 1` double-fold
plus branch-free conditional subtract — and `CompileFromHaxGf524287Tie` closes the
last hop to the abstract field `Zq524287 = ZMod 524287`: reading the leaf's residue
back as a `Zq524287` element via `fromNat ∘ toNat`, on the residue domain it is
exactly the field product `aF · bF`
(`CompileFromHaxGf524287Tie.gf524287MulFold_eq_field`).

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism, as the
NTRU/sntrup/Frodo/UOV/Ring8192/Mersenne31 SecurityTie modules do): it packages
the field multiply as a one-field abstract `MulDeps` record over `Zq524287`,
exhibits the *spec* instance (the abstract field product) and the
*compiled-realization* instance (what the verified-compiled leaf computes, read
back into `Zq524287`), proves them equal field-by-field, and feeds that equality
to `tie_transfer` so that **any** property a parametric field-arithmetic security
argument proves of the abstract multiply transfers verbatim to the
compiler-emitted leaf, with no new axioms.

## Honest scope

`Zq524287 = GF(2¹⁹−1)` is a small Mersenne prime field; this tie is at the
**field-arithmetic-building-block** level — it exhibits the verified-compiled
Mersenne-19 multiply leaf as a faithful realization of the abstract `Zq524287`
field product over which a parametric proof reasons. It is a generic building
block (`MulDeps Zq524287`) rather than wired to one named protocol's hardness
assumption; the realization equality `toMulDeps = mulDepsSpec` is genuine on the
residue domain (`encF` produces canonical residues `< 524287`), the domain on
which `gf524287MulFold_eq_field` is stated.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287SecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287Tie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)

/-! ## §1  The abstract one-field multiply dependency record -/

/-- The abstract field-multiply dependency record over a type `R`. -/
structure MulDeps (R : Type*) where
  /-- The field-multiply primitive `a b ↦ a · b`. -/
  mul : R → R → R

/-! ## §2  The abstract spec instance -/

/-- The abstract spec instance: the `Zq524287` field product `aF · bF`. -/
def mulDepsSpec : MulDeps Zq524287 where
  mul := fun a b => a * b

/-! ## §3  The compiled realization instance -/

/-- Encode a `Zq524287` field element as a `BitVec 64` (its canonical residue
    `< 524287`). -/
def encF (x : Zq524287) : BitVec 64 := BitVec.ofNat 64 x.val

/-- The canonical residue encoding lands below `524287#64`. -/
theorem encF_lt (x : Zq524287) : encF x < 524287#64 := by
  have hv : x.val < 524287 := ZMod.val_lt x
  unfold encF
  apply BitVec.lt_def.mpr
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simpa using hv

/-- The function the verified-compiled GF(524287) multiply `Com` computes, read
    back into `Zq524287` via `fromNat ∘ toNat`. -/
noncomputable def compiledMulFn (a b : Zq524287) : Zq524287 :=
  fromNat (gf524287MulFold (encF a) (encF b)).toNat

/-- The compiled-realization instance. -/
noncomputable def toMulDeps : MulDeps Zq524287 where
  mul := compiledMulFn

/-! ## §4  The realization theorem and the generic transfer -/

/-- **The realization theorem.** The compiler-emitted multiply instance equals the
    abstract field-multiply spec instance: on every pair of `Zq524287` field
    elements, the verified-compiled GF(524287) leaf (read back via the residue
    projection) computes exactly the abstract field product `a · b`. Closed by
    `gf524287MulFold_eq_field` plus the `Zq524287` round-trip on canonical
    residues. -/
theorem toMulDeps_eq_spec : toMulDeps = mulDepsSpec := by
  have hround : ∀ x : Zq524287, fromNat (encF x).toNat = x := by
    intro x
    unfold encF fromNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (by have := ZMod.val_lt x; omega), ZMod.natCast_val, ZMod.cast_id]
  unfold toMulDeps mulDepsSpec compiledMulFn
  congr 1
  funext a b
  rw [gf524287MulFold_eq_field _ _ (encF_lt a) (encF_lt b), hround, hround]

/-- **Compiled GF(524287) multiply inherits any abstract field-multiply
    property.** For every property `P` of `MulDeps Zq524287`, if `P` holds of the
    abstract field-multiply spec instance then it holds of the compiler-emitted
    realization instance — with no new axioms. Instantiates
    `CompileFromHaxSecurityTie.tie_transfer` at `Deps := MulDeps Zq524287` with the
    realization equality. -/
theorem appliesToCompiledGf524287 (P : MulDeps Zq524287 → Prop) (h : P mulDepsSpec) :
    P toMulDeps :=
  tie_transfer P toMulDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxGf524287SecurityTie
