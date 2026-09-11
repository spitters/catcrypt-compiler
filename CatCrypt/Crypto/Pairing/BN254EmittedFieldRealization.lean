/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.BN254Verified

/-!
# The emitted BN254 base-field kernels realize the field of the BN254 `G1` group

`Util/BN254Verified.lean` states the BN254 affine point-add coordinate
formula (`bn254AffineRx`, `bn254AffineRy`, `bn254AffineAdd`)
**field-agnostically** over the abstract prime field `FpBN254 = ZMod p`:
every coordinate is a `ZMod p` element and the body uses `ZMod`'s native
`+`, `−`, `*`.

The verified compiler **emits** the BN254 base-field arithmetic as
straight-line reduce-mod-`p` kernels on the canonical residue (the packed
4×u64 fiat-crypto limb bundle of a field element, modelled here as its
`Nat` value in `[0, p)`):

* `feMul a b = (a * b) % p`   — the bn254-safe-rust multiply-then-reduce (`fp_mul`);
* `feAdd a b = (a + b) % p`   — the add-then-conditional-subtract (`fp_add`);
* `feSub a b = (a + (p − b)) % p` — the borrow-free subtract (`fp_sub`).

These are exactly the AUCurves-verified `bn254-safe-rust` field ops
(`fp_add/sub/mul`, the verified-bedrock2 tower over the fiat leaves). This
module closes the gap between the emitted residue kernels and the abstract
field. Writing `feToFp x = (x : FpBN254)` for the canonical-residue
interpretation, the standard `ZMod` mod-invariance laws give the
**commuting square**

```
   Nat × Nat   ──emitted op──▶   Nat
      │ feToFp×feToFp               │ feToFp
      ▼                             ▼
   Fp × Fp     ──── Fp's *,+,- ──▶  Fp
```

i.e. `feToFp (emitted_op a b) = feToFp a ⋆ feToFp b` for `FpBN254`'s native
`*`/`+`/`-`. Composing these field kernels exactly as the short-Weierstrass
affine point-add prescribes yields an **emitted affine point-add** whose
canonical-residue interpretation equals `bn254AffineAdd` over `FpBN254`.

This is the CONN-3b/3c P-256 pattern transposed to the BN254 base-field
prime; the proofs are curve-generic in shape (only the modulus changes).
The full pairing tower (`Fp2`/`Fp6`/`Fp12` + Miller loop + final
exponentiation) is **not** lifted here — it remains the documented
opaque-leaf edge of `Pairing/Bn254Emit.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.BN254.EmittedFieldRealization

open CatCrypt.Util

/-! ## §1  The emitted residue kernels (over the BN254 base-field modulus `p`) -/

/-- Emitted field multiply: multiply the residues, reduce mod `p` (`fp_mul`). -/
def feMul (a b : Nat) : Nat := (a * b) % BN254

/-- Emitted field add: add the residues, reduce mod `p` (`fp_add`). -/
def feAdd (a b : Nat) : Nat := (a + b) % BN254

/-- Emitted field subtract: add `p` (after reducing `b`) to avoid a borrow,
    subtract, reduce mod `p` (the borrow-free `fp_sub`). On the emitted path
    `b` is a canonical residue (`< p`); reducing `b` mod `p` first is a no-op
    there and makes the realization law unconditional. -/
def feSub (a b : Nat) : Nat := (a + (BN254 - b % BN254)) % BN254

/-- The canonical-residue interpretation of an emitted residue word as an
    `FpBN254 = ZMod p` element. -/
def feToFp (x : Nat) : FpBN254 := (x : FpBN254)

/-! ## §2  The commuting-square realization theorems

Each says: the emitted residue kernel, transported by `feToFp`, equals
`FpBN254`'s native operation on the transported arguments — the `ZMod`
mod-invariance of the natural cast (`ZMod.natCast_mod`) plus the ring
homomorphism laws of `Nat.cast`. No canonicity hypothesis is needed. -/

/-- **Emitted multiply realizes `FpBN254`'s multiplication.** -/
theorem feMul_realizes_mul (a b : Nat) :
    feToFp (feMul a b) = feToFp a * feToFp b := by
  unfold feToFp feMul
  rw [ZMod.natCast_mod, Nat.cast_mul]

/-- **Emitted add realizes `FpBN254`'s addition.** -/
theorem feAdd_realizes_add (a b : Nat) :
    feToFp (feAdd a b) = feToFp a + feToFp b := by
  unfold feToFp feAdd
  rw [ZMod.natCast_mod, Nat.cast_add]

/-- **Emitted subtract realizes `FpBN254`'s subtraction.** -/
theorem feSub_realizes_sub (a b : Nat) :
    feToFp (feSub a b) = feToFp a - feToFp b := by
  unfold feToFp feSub
  rw [ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (by norm_num)))]
  have hp : (BN254 : FpBN254) = 0 := ZMod.natCast_self BN254
  rw [hp, ZMod.natCast_mod]
  ring

/-- **The emitted BN254 field arithmetic realizes the BN254 group's field.** -/
theorem emitted_realizes_bn254_field (a b : Nat) :
    feToFp (feMul a b) = feToFp a * feToFp b
    ∧ feToFp (feAdd a b) = feToFp a + feToFp b
    ∧ feToFp (feSub a b) = feToFp a - feToFp b :=
  ⟨feMul_realizes_mul a b, feAdd_realizes_add a b, feSub_realizes_sub a b⟩

/-! ## §3  Lifting to the affine point-add coordinate formulas -/

/-- Emitted `x₃ = λ² − x₁ − x₂` over residues. -/
def feRx (lam x1 x2 : Nat) : Nat := feSub (feSub (feMul lam lam) x1) x2

/-- Emitted `y₃ = λ·(x₁ − x₃) − y₁` over residues. -/
def feRy (lam x1 x3 y1 : Nat) : Nat := feSub (feMul lam (feSub x1 x3)) y1

/-- **`feRx` realizes the abstract `bn254AffineRx` (`λ² − x₁ − x₂`).** -/
theorem feRx_realizes (lam x1 x2 : Nat) :
    feToFp (feRx lam x1 x2)
      = bn254AffineRx (feToFp lam) (feToFp x1) (feToFp x2) := by
  unfold feRx bn254AffineRx
  rw [feSub_realizes_sub, feSub_realizes_sub, feMul_realizes_mul]

/-- **`feRy` realizes the abstract `bn254AffineRy` (`λ·(x₁ − x₃) − y₁`).** -/
theorem feRy_realizes (lam x1 x3 y1 : Nat) :
    feToFp (feRy lam x1 x3 y1)
      = bn254AffineRy (feToFp lam) (feToFp x1) (feToFp x3) (feToFp y1) := by
  unfold feRy bn254AffineRy
  rw [feSub_realizes_sub, feMul_realizes_mul, feSub_realizes_sub]

/-! ## §4  The emitted affine point-add realizes `bn254AffineAdd` -/

/-- A residue-encoded affine point: the two coordinates as canonical residues. -/
structure FePoint where
  /-- Affine `x`-coordinate (residue). -/
  x : Nat
  /-- Affine `y`-coordinate (residue). -/
  y : Nat

/-- Interpret a residue-encoded point as an abstract `BN254Point`. -/
def FePoint.toAlg (P : FePoint) : BN254Point :=
  { x := feToFp P.x, y := feToFp P.y }

/-- The emitted affine point-add (distinct points), built from the residue
    kernels, given the precomputed slope-residue `lam`. -/
def feAffineAdd (lam : Nat) (P Q : FePoint) : FePoint :=
  let x3 := feRx lam P.x Q.x
  { x := x3, y := feRy lam P.x x3 P.y }

/-- **The emitted affine point-add realizes the abstract `bn254AffineAdd`.** -/
theorem feAffineAdd_realizes (lam : Nat) (P Q : FePoint) :
    (feAffineAdd lam P Q).toAlg = bn254AffineAdd (feToFp lam) P.toAlg Q.toAlg := by
  unfold feAffineAdd bn254AffineAdd FePoint.toAlg
  refine BN254Point.mk.injEq .. ▸ ?_
  refine ⟨?_, ?_⟩
  · exact feRx_realizes lam P.x Q.x
  · rw [feRy_realizes]
    rw [feRx_realizes]

end CatCrypt.Crypto.BN254.EmittedFieldRealization
