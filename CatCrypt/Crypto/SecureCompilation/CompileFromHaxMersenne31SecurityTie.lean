/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie

/-!
# #607 security tie: the compile-from-hax Mersenne-31 multiply leaf realizes the
  abstract `Zm31` base-field multiply the CircleSTARK / Plonky3-M31 layer reasons over

`CompileFromHaxMersenne31` proves the verified compiler *emits* a jasmin `Com`
whose `BitVec 64` denotation is `m31MulFold` — the Mersenne `2³¹ ≡ 1` double-fold
plus a branch-free conditional subtract — and `CompileFromHaxMersenne31Tie` closes
the last hop to the abstract base field `Zm31 = ZMod 2147483647`: reading the
leaf's residue back as a `Zm31` element via `fromNat ∘ toNat`, on the residue
domain it is exactly the field product `aF · bF`
(`CompileFromHaxMersenne31Tie.m31MulFold_eq_field`).

This module performs the **security-tie composition** (the
`CompileFromHaxSecurityTie.tie_transfer` mechanism, as the
NTRU/sntrup/Frodo/UOV/Ring8192 SecurityTie modules do): it packages that field
multiply as a one-field abstract `MulDeps` dependency record over `Zm31`,
exhibits the *spec* instance (the abstract field product the CircleSTARK /
Plonky3-Mersenne31 arithmetic-circuit reference is built from) and the
*compiled-realization* instance (the function the verified-compiled leaf
computes, read back into `Zm31`), proves them equal field-by-field, and feeds
that equality to `tie_transfer` so that **any** property the security layer
proves of the abstract field multiply transfers verbatim to the
compiler-emitted leaf, with no new axioms.

## Why this is parametric-correct for CircleSTARK / Plonky3-M31 (honest scope)

CircleSTARK and Plonky3-Mersenne31 reason over the base field `Zm31`
abstractly, through the arithmetic-circuit / AIR constraint polynomials that are
sums and products of field elements `a · b`. This module's compiled leaf is the
**field multiply** `a · b`. The compiled-realization equality
`toMulDeps = mulDepsSpec` is genuine: the verified compiler's emitted Mersenne
fold computes exactly the abstract `Zm31` field product on residue inputs, and
`tie_transfer` carries any field-multiply property onto the compiled artifact.
It does **not** discharge the STARK soundness / FRI low-degree-test assumption —
those remain the hypotheses of the CircleSTARK / Plonky3 `Security.lean`; this
ties the *emitted arithmetic* to the *abstract arithmetic* the proof uses, which
is the scope of #607.

`toMulDeps_eq_spec` is restricted to the residue inputs the field operates over
(`encF` produces canonical residues `< 2147483647`), which is exactly the domain
on which `m31MulFold_eq_field` is stated and the domain a base-field element of
the trace / constraint polynomials inhabits.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31SecurityTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)

/-! ## §1  The abstract one-field multiply dependency record -/

/-- The abstract field-multiply dependency record over a type `R`. -/
structure MulDeps (R : Type*) where
  /-- The field-multiply primitive `a b ↦ a · b`. -/
  mul : R → R → R

/-! ## §2  The abstract spec instance (what the security reference assumes) -/

/-- The abstract spec instance: the `Zm31` field product `aF · bF` that the
    CircleSTARK / Plonky3-Mersenne31 constraint polynomials are built from. -/
def mulDepsSpec : MulDeps Zm31 where
  mul := fun a b => a * b

/-! ## §3  The compiled realization instance (what the verified compiler emits) -/

/-- Encode a `Zm31` field element as a `BitVec 64` (its canonical residue
    `< 2147483647`). -/
def encF (x : Zm31) : BitVec 64 := BitVec.ofNat 64 x.val

/-- The canonical residue encoding lands below `2147483647#64`. -/
theorem encF_lt (x : Zm31) : encF x < 2147483647#64 := by
  have hv : x.val < 2147483647 := ZMod.val_lt x
  unfold encF
  apply BitVec.lt_def.mpr
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simpa using hv

/-- The function the verified-compiled Mersenne-31 multiply `Com` computes, read
    back into `Zm31` via `fromNat ∘ toNat`. -/
noncomputable def compiledMulFn (a b : Zm31) : Zm31 :=
  fromNat (m31MulFold (encF a) (encF b)).toNat

/-- The compiled-realization instance: the abstract `MulDeps Zm31` filled with
    the function the **verified compiler emits** for the Mersenne-31 multiply. -/
noncomputable def toMulDeps : MulDeps Zm31 where
  mul := compiledMulFn

/-! ## §4  The realization theorem and the generic transfer -/

/-- **The realization theorem.** The compiler-emitted multiply instance equals the
    abstract field-multiply spec instance: on every pair of `Zm31` field elements,
    the verified-compiled Mersenne-31 leaf (read back via the residue projection)
    computes exactly the abstract field product `a · b`. Closed by
    `m31MulFold_eq_field` (the Mersenne reduce identity, itself proved by `Nat`
    arithmetic) plus the `Zm31` round-trip on canonical residues. -/
theorem toMulDeps_eq_spec : toMulDeps = mulDepsSpec := by
  have hround : ∀ x : Zm31, fromNat (encF x).toNat = x := by
    intro x
    unfold encF fromNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (by have := ZMod.val_lt x; omega), ZMod.natCast_val, ZMod.cast_id]
  unfold toMulDeps mulDepsSpec compiledMulFn
  congr 1
  funext a b
  rw [m31MulFold_eq_field _ _ (encF_lt a) (encF_lt b), hround, hround]

/-- **Compiled Mersenne-31 multiply inherits any abstract field-multiply
    property.** For every property `P` of `MulDeps Zm31`, if `P` holds of the
    abstract field-multiply spec instance then it holds of the compiler-emitted
    realization instance. The mechanized statement that the verified-compiled
    Mersenne-31 base-field multiply leaf plugs into the abstract `Zm31` arithmetic
    the CircleSTARK / Plonky3-Mersenne31 security layer reasons over: any property
    the parametric STARK proof establishes over the abstract field multiply
    transfers verbatim to `toMulDeps`, the verified compiler's emitted primitive —
    with no new axioms. Instantiates `CompileFromHaxSecurityTie.tie_transfer` at
    `Deps := MulDeps Zm31` with the realization equality. -/
theorem appliesToCompiledMersenne31 (P : MulDeps Zm31 → Prop) (h : P mulDepsSpec) :
    P toMulDeps :=
  tie_transfer P toMulDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31SecurityTie
