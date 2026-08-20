/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# Prime-ir structural / reinterpret ops — `poly.to_tensor` / `poly.from_tensor`
  and `field.bitcast` / `mod_arith.bitcast`

The leaf functions and round-trip laws for the prime-ir *structural / reinterpret*
ops, which move data between equivalent representations without doing arithmetic:

* `poly.to_tensor` / `poly.from_tensor` — the coefficient-vector ↔ polynomial
  maps (a polynomial in coefficient form *is* its coefficient tensor);
* `field.bitcast` / `mod_arith.bitcast` — the reinterpret-bits map between a
  field / mod-arith residue and its fixed-width `BitVec` storage.

It is the CatCrypt counterpart of prime-ir's `poly.to_tensor` /
`poly.from_tensor` (§3 of `PRIME_IR_OP_CORRESPONDENCE.md`) and `field.bitcast` /
`mod_arith.bitcast` (§1 / §2).

## Why this dialect exists (the gaps it closes)

Per `PRIME_IR_OP_CORRESPONDENCE.md` (repo root), these reinterpret maps were already
*used* — but only **implicitly**, never factored as standalone ops:

* `poly.to_tensor` (§3, line 89) — "`polyC`↔coeff-tensor via `from_tensor`
  leaf; implicit" — **PARTIAL**.
* `poly.from_tensor` (§3, line 90) — "implicit coeff construction" — **PARTIAL**.
* `field.bitcast` (§1, line 25) — "via leaf decode; no dedicated op" — **PARTIAL**.
* `mod_arith.bitcast` (§2, line 56) — "leaf decode" — **PARTIAL**.

This file **factors all four as first-class ops** with concrete denotations and
the round-trip lemmas a reinterpret op must satisfy — WITHOUT modifying the
`FieldDialect` / `ModArithDialect` / `PolyDialect` `Op` sets (additive only).

## The representations

* **Poly ↔ tensor.** prime-ir's `poly.to_tensor : PolyType → RankedTensor` and
  `poly.from_tensor : RankedTensor → PolyType` move between a degree-`< n`
  polynomial and its rank-1 length-`n` coefficient tensor.  We model **both
  sides in coefficient form** as the coefficient vector `Fin n → ZMod q`: a
  polynomial of degree `< n` over `Z_q` *is* its `n`-coefficient vector, and the
  tensor *is* that same vector viewed as a rank-1 array.  The two maps are
  therefore the identity on the coefficient vector — the reinterpret carries no
  arithmetic content — and the round-trips
  `polyFromTensor (polyToTensor p) = p`, `polyToTensor (polyFromTensor t) = t`
  hold by `rfl`.  (This is the honest "the poly IS its coeff tensor" model: it
  factors the *reinterpret*, not any NTT/transform content, which lives in
  `PolyDialect`'s `ntt`/`nttMul` ops.)

* **Field / mod-arith ↔ bits.** prime-ir's `field.bitcast` / `mod_arith.bitcast`
  reinterpret a residue's bits as a fixed-width integer storage and back.  We
  model the storage as `BitVec w` and the residue as `ZMod p`:

  * encode `ZMod p → BitVec w` is `a ↦ BitVec.ofNat w a.val` (the canonical
    little-endian residue bits);
  * decode `BitVec w → ZMod p` is `b ↦ (b.toNat : ZMod p)`.

  The round-trip `decode (encode a) = a` holds when the storage is wide enough
  to hold the modulus (`p ≤ 2^w`, no truncation); the reverse
  `encode (decode b) = b` holds when `b` already stores a canonical residue
  (`b.toNat < p`).  Both are the no-truncation conditions a bit-reinterpret
  needs; we state them as explicit hypotheses rather than baking in a width.

## Where the ops live

`ModArithOp.polyToTensor`, `.polyFromTensor`, `.residueEncode` and
`.residueDecode` in `ModArithDialect`, tied to the leaves below by
`VIR/FoldedOpAgreement.lean`. They sit there rather than in a dialect of their
own because a `Com` carries ops from one dialect, and an op alone in its dialect
cannot appear beside the arithmetic it reinterprets for. A coproduct with an
injection (`VIR/DialectCoproduct.lean`) was the alternative; folding was chosen
because all four carriers already have `ModArithTy` counterparts — `poly` and
`tensor` are `fpVec q n`, `residue` is `fp p`, `bits` is `word w`.

Lowering status: `VIR/DIALECTS.md`.

## What this file does NOT close (still-PARTIAL)

* `elliptic_curve.pairing_check` (§4, line 123) — we have the Miller-loop / Fp12
  pieces (`RelationalFrontBls377MillerLoop.lean`, `…Fp12*.lean`) but a *fused*
  single `pairing_check` op that packages them is **deliberately skipped here**.
  Packaging it faithfully requires routing through those relational-front pieces
  (not a clean carrier-level identity like the maps above), so it would not be
  the additive, denotation-by-leaf shape this file keeps.  It remains a
  **PARTIAL**; this file does not claim to close it.
* `elliptic_curve.bitcast` (§4, line 125) — the EC-point bit reinterpret — is
  also left as PARTIAL: an EC point is a multi-coordinate aggregate, so its
  bitcast is a tuple-of-residues reinterpret, not the single-residue map factored
  here.

## Pure-only + constant-time

Every op here is a **data-oblivious** reinterpret: `to_tensor`/`from_tensor`
relabel the same vector, and the field/mod bitcast is a fixed-width bit copy
(`BitVec.ofNat` / `toNat`) with no branch on the operand value and no
data-dependent index.  So `ctSafe` is `true` for every op — exactly the
`FieldDerivedOps`/`PolyDialect` data-oblivious story (and unlike the
equality-test ops of `cmpDialect`, these never branch on a secret value).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PrimeIrStructuralOps

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. The leaf functions (the denotation targets)

Each is a total reinterpret function.  The poly/tensor leaves are the identity
on the coefficient vector `Fin n → ZMod q`; the bitcast leaves are the canonical
encode/decode between `ZMod p` and `BitVec w`. -/

/-- `poly.to_tensor` leaf: reinterpret a degree-`< n` coefficient-form polynomial
    (modeled as its coefficient vector `Fin n → ZMod q`) as its rank-1 length-`n`
    coefficient tensor.  Since both sides are the coefficient vector, this is the
    identity — the reinterpret carries no arithmetic. -/
@[reducible] def polyToTensorF (q n : Nat) (p : Fin n → ZMod q) : Fin n → ZMod q := p

/-- `poly.from_tensor` leaf: reinterpret a rank-1 length-`n` coefficient tensor
    as the coefficient-form polynomial whose coefficients it lists.  The inverse
    of `polyToTensorF`; again the identity on the coefficient vector. -/
@[reducible] def polyFromTensorF (q n : Nat) (t : Fin n → ZMod q) : Fin n → ZMod q := t

/-- `field.bitcast` / `mod_arith.bitcast` **encode** leaf: reinterpret a residue
    `a : ZMod p` as its canonical fixed-width `BitVec w` storage, the
    little-endian bits of `a.val`. -/
@[reducible] def residueEncodeF (p w : Nat) (a : ZMod p) : BitVec w :=
  BitVec.ofNat w a.val

/-- `field.bitcast` / `mod_arith.bitcast` **decode** leaf: reinterpret a
    fixed-width `BitVec w` storage `b` as the residue `b.toNat : ZMod p`.  The
    inverse of `residueEncodeF` under the no-truncation / canonical-storage
    conditions. -/
@[reducible] def residueDecodeF (p w : Nat) (b : BitVec w) : ZMod p :=
  (b.toNat : ZMod p)

/-! ## 2. Round-trip / agreement lemmas (reinterpret correctness)

The once-per-op correctness ties.  Poly↔tensor round-trips are `rfl` (identity
on the coefficient vector).  The bitcast round-trips carry the
no-truncation hypotheses: `decode ∘ encode = id` needs the storage wide enough
for the modulus (`p ≤ 2^w`); `encode ∘ decode = id` needs the stored value to be
a canonical residue (`b.toNat < p`). -/

/-- **Poly↔tensor round-trip.** `from_tensor (to_tensor p) = p` — the
    coefficient vector survives the reinterpret untouched. -/
theorem polyFromTensor_polyToTensor {q n : Nat} (p : Fin n → ZMod q) :
    polyFromTensorF q n (polyToTensorF q n p) = p := rfl

/-- **Poly↔tensor round-trip (other side).** `to_tensor (from_tensor t) = t`. -/
theorem polyToTensor_polyFromTensor {q n : Nat} (t : Fin n → ZMod q) :
    polyToTensorF q n (polyFromTensorF q n t) = t := rfl

/-- `to_tensor` and `from_tensor` are mutually inverse reinterprets (both the
    identity on the coefficient vector). -/
theorem polyToTensor_eq_polyFromTensor {q n : Nat} (v : Fin n → ZMod q) :
    polyToTensorF q n v = polyFromTensorF q n v := rfl

/-- **Bitcast round-trip (decode ∘ encode).** Reinterpreting a residue as bits
    and back recovers the residue, provided the storage is wide enough to hold
    the modulus (`p ≤ 2^w`), so the canonical value `a.val < p ≤ 2^w` is not
    truncated. -/
theorem residueDecode_residueEncode {p w : Nat} [NeZero p] (a : ZMod p)
    (hp : p ≤ 2 ^ w) :
    residueDecodeF p w (residueEncodeF p w a) = a := by
  have hlt : a.val < 2 ^ w := lt_of_lt_of_le (ZMod.val_lt a) hp
  simp only [residueDecodeF, residueEncodeF, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt, ZMod.natCast_val, ZMod.cast_id]

/-- **Bitcast round-trip (encode ∘ decode).** Reinterpreting a `BitVec` storage
    as a residue and back recovers the storage, provided the storage already
    holds a canonical residue (`b.toNat < p`). -/
theorem residueEncode_residueDecode {p w : Nat} [NeZero p] (b : BitVec w)
    (hb : b.toNat < p) :
    residueEncodeF p w (residueDecodeF p w b) = b := by
  simp only [residueEncodeF, residueDecodeF, ZMod.val_natCast,
    Nat.mod_eq_of_lt hb, BitVec.ofNat_toNat, BitVec.setWidth_eq]
