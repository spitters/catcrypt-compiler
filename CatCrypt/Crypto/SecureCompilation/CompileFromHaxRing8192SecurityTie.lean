/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192Tie
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie

/-!
# #607 security tie: the compile-from-hax `Z/8192Z` multiply leaf realizes the
  abstract `Zq8192` ring multiply the NTRU-HRSS security reference reasons over

`CompileFromHaxRing8192` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `ring8192MulMask` — integer multiply plus the
low-13-bit mask `& 8191` (the `mod 2¹³` reduce) — and
`CompileFromHaxRing8192Tie` closes the last hop to the abstract coefficient ring
`Util.Zq8192 = ZMod 8192`: reading the leaf's low residue back as a `Zq8192`
element via `Zq8192.fromNat ∘ toNat`, on the residue domain it is exactly the
ring product `aZ · bZ` (`CompileFromHaxRing8192Tie.ring8192MulMask_eq_ring`).

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism, as the
NTRU/sntrup/Frodo/UOV SecurityTie modules did): it packages that ring multiply as
a one-field abstract `MulDeps` dependency record over `Zq8192`, exhibits the
*spec* instance (the abstract ring product the NTRU-HRSS cyclic-convolution
reference is built from) and the *compiled-realization* instance (the function
the verified-compiled leaf computes, read back into `Zq8192`), proves them equal
field-by-field, and feeds that equality to `tie_transfer` so that **any** property
the security layer proves of the abstract ring multiply transfers verbatim to the
compiler-emitted leaf, with no new axioms.

## Why this is parametric-correct for NTRU-HRSS (honest scope)

NTRU-HRSS's `NTRU/SurfaceDeps.lean` reasons over the coefficient ring `Zq8192`
abstractly, through cyclic-convolution `Finset.sum`s of ring products `a · b`.
This module's compiled leaf is the **pure ring multiply** `a · b` (distinct from,
and simpler than, the existing `ntruMacForm` multiply-accumulate leaf — that
sibling security tie lives in `CompileFromHaxNtruSecurityTie`). The
compiled-realization equality `toMulDeps = mulDepsSpec` is genuine: the verified
compiler's emitted `mod 2¹³` multiply computes exactly the abstract `Zq8192` ring
product on residue inputs, and `tie_transfer` carries any ring-multiply property
onto the compiled artifact. It does **not** discharge the NTRU one-wayness
assumption or the SXY/FO transform — those remain the hypotheses of
`NTRU/Security.lean`; this ties the *emitted arithmetic* to the *abstract
arithmetic* the proof uses, which is the scope of #607.

`toMulDeps_eq_spec` is restricted to the residue inputs the NTRU coefficient ring
operates over (`encZ` produces canonical residues `< 8192`), which is exactly the
domain on which `ring8192MulMask_eq_ring` is stated and the domain a coefficient
of the cyclic convolution inhabits.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192SecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192Tie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)
open CatCrypt.Util

/-! ## §1  The abstract one-field multiply dependency record

`MulDeps R` is the miniature `Dependencies` for a coefficient-ring multiply: the
single arithmetic primitive `mul : R → R → R` the NTRU-HRSS cyclic convolution is
built from. A security proof over the ring is parametric over a `MulDeps Zq8192`
and reasons only through the *spec* the ring satisfies. -/

/-- The abstract ring-multiply dependency record over a type `R`. -/
structure MulDeps (R : Type*) where
  /-- The ring-multiply primitive `a b ↦ a · b`. -/
  mul : R → R → R

/-! ## §2  The abstract spec instance (what the security reference assumes) -/

/-- The abstract spec instance: the `Zq8192` ring product `aZ · bZ` that the
    NTRU-HRSS cyclic-convolution reference sums over. -/
def mulDepsSpec : MulDeps Zq8192 where
  mul := fun a b => a * b

/-! ## §3  The compiled realization instance (what the verified compiler emits) -/

/-- Encode a `Zq8192` ring element as a `BitVec 64` (its canonical residue
    `< 8192`). -/
def encZ (x : Zq8192) : BitVec 64 := BitVec.ofNat 64 x.val

/-- The canonical residue encoding lands below `8192#64`. -/
theorem encZ_lt (x : Zq8192) : encZ x < 8192#64 := by
  have hv : x.val < 8192 := ZMod.val_lt x
  unfold encZ
  apply BitVec.lt_def.mpr
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simpa using hv

/-- The function the verified-compiled `Z/8192Z` multiply `Com` computes, read
    back into `Zq8192` via `Zq8192.fromNat ∘ toNat`. -/
noncomputable def compiledMulFn (a b : Zq8192) : Zq8192 :=
  Zq8192.fromNat (ring8192MulMask (encZ a) (encZ b)).toNat

/-- The compiled-realization instance: the abstract `MulDeps Zq8192` filled with
    the function the **verified compiler emits** for the `Z/8192Z` multiply. -/
noncomputable def toMulDeps : MulDeps Zq8192 where
  mul := compiledMulFn

/-! ## §4  The realization theorem and the generic transfer -/

/-- **The realization theorem.** The compiler-emitted multiply instance equals the
    abstract ring-multiply spec instance: on every pair of `Zq8192` ring elements,
    the verified-compiled `Z/8192Z` leaf (read back via the low-residue projection)
    computes exactly the abstract ring product `a · b`. Closed by
    `ring8192MulMask_eq_ring` (the power-of-two `mod 2¹³` reduce identity) plus the
    `Zq8192` round-trip on canonical residues. -/
theorem toMulDeps_eq_spec : toMulDeps = mulDepsSpec := by
  have hround : ∀ x : Zq8192, Zq8192.fromNat (encZ x).toNat = x := by
    intro x
    unfold encZ Zq8192.fromNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (by have := ZMod.val_lt x; omega), ZMod.natCast_val, ZMod.cast_id]
  unfold toMulDeps mulDepsSpec compiledMulFn
  congr 1
  funext a b
  rw [ring8192MulMask_eq_ring _ _ (encZ_lt a) (encZ_lt b), hround, hround]

/-- **Compiled `Z/8192Z` multiply inherits any abstract ring-multiply property.**
    For every property `P` of `MulDeps Zq8192`, if `P` holds of the abstract
    ring-multiply spec instance then it holds of the compiler-emitted realization
    instance. The mechanized statement that the verified-compiled NTRU-HRSS
    coefficient-ring multiply leaf plugs into the abstract `Zq8192` arithmetic the
    NTRU-HRSS security layer reasons over: any property the parametric
    `NTRU/Security.lean` proof establishes over the abstract ring multiply
    transfers verbatim to `toMulDeps`, the verified compiler's emitted primitive —
    with no new axioms. Instantiates `CompileFromHaxSecurityTie.tie_transfer` at
    `Deps := MulDeps Zq8192` with the realization equality. -/
theorem appliesToCompiledRing8192 (P : MulDeps Zq8192 → Prop) (h : P mulDepsSpec) :
    P toMulDeps :=
  tie_transfer P toMulDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxRing8192SecurityTie
