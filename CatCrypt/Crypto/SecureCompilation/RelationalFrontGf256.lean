/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RelationalFront
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public meta import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenGf256
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenGf256
public import Std.Tactic.BVDecide

/-!
# The relational front over a BINARY field: GF(2⁸) multiply, relationally emitted

`RelationalFrontInstances.lean` exercises the relational front over a **prime**
field (`ZMod 251`, the GF(251) Solinas base): an injective-not-surjective
encoding of residues into `BitVec 64`, with a reducing kernel. This module is the
**characteristic-2 customer** — the AES / FAEST / MAYO / SNOVA structure — showing
the relational compiler handles a *binary* field `GF(2^8)` (the Rijndael field
`GF(2)[x]/(x⁸+x⁴+x³+x+1)`), not just prime fields. It reuses the existing
GF(2⁸) golden-path emit (`FieldEmitGoldenGf256.gf256MulBuilt`) unchanged as the
`Com`.

## The spec, its encoding, and the operator

* **Spec**: `A = BitVec 8` — a byte, the carrier of `GF(2^8)` (one byte per field
  element; this is exactly how AES/FAEST represent field elements). The abstract
  operation `op = gf256MulByte` is the Rijndael field multiply on bytes (defined
  below as the golden-path reference truncated to the byte, so the spec is *the
  same operation the kernel computes*, stated at byte width).
* **Encoding**: `enc : BitVec 8 → BitVec 64 := BitVec.setWidth 64`, the
  zero-extension of the byte into the 64-bit register carrier. This is
  * **injective**: zero-extension is width-preserving on the low 8 bits, so
    distinct bytes have distinct 64-bit images (`BitVec.setWidth` is injective
    when the target width is larger);
  * **NOT surjective**: every image is `< 256`, so e.g. `(256 : BitVec 64)` (let
    alone `2^63`) has no preimage. The image is the 256-element subset
    `{0,…,255}` of the `2^64`-element register carrier — the
    injective-not-onto regime (`map4` level: equality-reflecting embedding, no
    surjectivity, no Type-equivalence).
* **Operator** `bop = gf256Ref` (`FieldEmitGoldenGf256.gf256Ref`): the bit-serial
  Russian-peasant `GF(2^8)` multiply on `BitVec 64` that the emitted kernel
  `gf256MulBuilt` denotes. It is **all-XOR/AND/shift** — characteristic-2
  arithmetic with the reduction polynomial `0x11b`, no carry chain — the binary-
  field analogue of the prime field's conditional-subtract.

## The commuting square (the binary-field tie)

`enc (gf256MulByte a b) = gf256Ref (enc a) (enc b)`: the abstract `GF(2^8)`
byte multiply, zero-extended, equals the emitted kernel's operator run on the
zero-extended operands. Because `gf256MulByte` is *defined* as `gf256Ref`
truncated to the byte, and `gf256Ref`'s output is always in `[0,255]` (the
reduction polynomial keeps the bit-serial product in byte range), the square is
a width round-trip that `bv_decide` discharges.

## What this demonstrates

`spec_eq_transfers_to_emit` instantiated here decides an **abstract `GF(2^8)`
equation** (`a · b = a' · b'` in the Rijndael field, on bytes) by the emitted
GF(2⁸) machine kernel's denotation on the *serialized* (zero-extended) operands —
through an injective, not-onto byte encoding, over a **characteristic-2** field.
That is the relational front carrying the AES/FAEST binary-field structure end-to-
end, the char-2 sibling of the `ZMod 251` prime-field instance.

## Scope

* The abstract spec `A = BitVec 8` with `op = gf256MulByte` is the **byte-level**
  Rijndael multiply, *defined as the golden-path reference truncated to the byte*.
  We do **not** reduce against Mathlib's `GaloisField 2 8` / a `GF(2)[x]/(p)`
  quotient — that needs a `Field`/`GaloisField` isomorphism (the obstruction the
  `ReprTransferInstancesBinius` docstring flags), not provided here. The spec is
  thus the operation-on-bytes, not the abstract algebraic field object; this is
  the same specification level as the golden path itself (validated as the bit-serial
  multiply by FIPS-197 KATs, `gf256Ref_kats` / `gf256MulBuilt_kats`).
* `com_denotes_bop` is the **all-inputs** seam `Com.denote gf256MulBuilt = gf256Ref`
  (`gf256MulBuilt_denote_gf256Ref`), *not* a closed-vector KAT — the golden path's
  own `gf256MulBuilt_kats` is `native_decide` on four vectors, whereas the seam
  here is the symbolic `rfl` identifying the kernel's denotation with the
  reference on **every** input, which is what the `RealizedKernel` contract needs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenGf256

/-! ## 1. The seam: the emitted GF(2⁸) kernel denotes `gf256Ref`, all inputs

The golden path validates `gf256MulBuilt` against FIPS-197 vectors by
`native_decide` (`gf256MulBuilt_kats`). The `RealizedKernel` contract needs the
stronger **all-inputs** identity `Com.denote gf256MulBuilt = gf256Ref x1 x0`. The
generated `Com` is laid out binding-for-binding to match `gf256Step`/`gf256Ref`
(see the `FieldEmitGoldenGf256` table), so this is a symbolic `rfl`. -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **The IR seam, all inputs.** The emitted 91-binding GF(2⁸) kernel denotes the
    bit-serial reference `gf256Ref` on **every** input (not just the closed KAT
    vectors). The `x1 + x0` ↦ `gf256Ref x1 x0` orientation matches the
    `RealizedKernel.bop x1 x0` seam (`a = .there .here`, `b = .here`). -/
theorem gf256MulBuilt_denote_gf256Ref (x0 x1 : BitVec 64) :
    Com.denote gf256MulBuilt (.cons x0 (.cons x1 .nil)) = gf256Ref x1 x0 := by
  rfl

/-! ## 2. The byte-level GF(2⁸) multiply spec and its range -/

/-- The abstract `GF(2^8)` byte multiply: the golden-path bit-serial reference,
    truncated to the byte. This *is* the Rijndael field multiply on bytes (the
    operation `gf256MulBuilt` computes, validated against FIPS-197 in
    `gf256MulBuilt_kats`), stated at byte width. -/
def gf256MulByte (a b : BitVec 8) : BitVec 8 :=
  BitVec.setWidth 8 (gf256Ref (BitVec.setWidth 64 a) (BitVec.setWidth 64 b))

/-! ## 3. The injective-not-surjective byte encoding and its `EndoOpRealization` -/

/-- The byte encoding `BitVec 8 → BitVec 64`: zero-extension into the register
    carrier. Injective (distinct bytes ↦ distinct `< 256` words) but not
    surjective (image is `{0,…,255}`). -/
def encByte (a : BitVec 8) : BitVec 64 := BitVec.setWidth 64 a

/-- **`encByte` is injective** (equality-reflecting): zero-extension to a wider
    width preserves the low byte, so distinct bytes have distinct images. The
    `map4`-level `enc_inj` — note it is **not** surjective (`(256 : BitVec 64)`
    has no preimage), the injective-not-onto case. -/
theorem encByte_injective : Function.Injective encByte := by
  intro a b hab
  have h : (encByte a).toNat = (encByte b).toNat := congrArg BitVec.toNat hab
  simp only [encByte, BitVec.toNat_setWidth] at h
  have ha := a.isLt
  have hb := b.isLt
  exact BitVec.eq_of_toNat_eq (by omega)

/-- **The commuting square.** The abstract `GF(2^8)` byte multiply `a · b`,
    zero-extended, equals the emitted kernel's operator `gf256Ref` run on the
    zero-extended operands. `gf256MulByte` is `gf256Ref` truncated to the byte and
    `gf256Ref`'s bit-serial product is always in `[0,255]`, so the zero-extension
    of the truncation is the value itself — a width round-trip `bv_decide` closes. -/
theorem encByte_commutes (a b : BitVec 8) :
    encByte (gf256MulByte a b) = gf256Ref (encByte a) (encByte b) := by
  unfold encByte gf256MulByte gf256Ref gf256Step
  dsimp only
  bv_decide

/-- **The `EndoOpRealization` for `GF(2^8)` multiply via byte zero-extension.**
    `op = gf256MulByte` on `BitVec 8`; `bop = gf256Ref` on `BitVec 64`;
    `enc = encByte` (injective-not-surjective). The char-2 (binary-field)
    relational tie. -/
def gf256MulRealization :
    EndoOpRealization gf256MulByte gf256Ref where
  enc := encByte
  enc_inj := encByte_injective
  commutes := encByte_commutes

/-! ## 4. The `RealizedKernel`: the abstract GF(2⁸) multiply, emitted -/

/-- **The relationally-emitted `GF(2^8)`-multiply kernel — the characteristic-2
    customer.** Its abstract source is the Rijndael field byte multiply
    (`BitVec 8`), its computational side is the emitted bit-serial GF(2⁸) kernel
    `gf256MulBuilt`, and its encoding is an injective-not-surjective byte
    serialization. The binary-field sibling of `addMod251RealizedKernel`. -/
def gf256MulRealizedKernel : RealizedKernel gf256MulByte where
  bop := gf256Ref
  realization := gf256MulRealization
  com := gf256MulBuilt
  com_denotes_bop := gf256MulBuilt_denote_gf256Ref
  com_ok := gf256MulBuilt_ok

/-! ## 5. The demonstration: an abstract GF(2⁸) equation decided by emitted code -/

/-- **The transfer demonstration.** An abstract `GF(2^8)` equation
    `a · b = a' · b'` (Rijndael field multiply on bytes) transfers to an equation
    between the emitted kernel's operator `gf256Ref` on the zero-extended operands.
    This is `spec_eq_transfers_to_emit` for the binary-field kernel — the
    relational front deciding an abstract char-2 field equation through a real
    (injective-not-onto) byte serialization. -/
theorem gf256Mul_spec_transfers (a a' b b' : BitVec 8) :
    gf256MulByte a b = gf256MulByte a' b' ↔
      gf256Ref (encByte a) (encByte b) = gf256Ref (encByte a') (encByte b') :=
  gf256MulRealizedKernel.spec_eq_transfers_to_emit a a' b b'

/-- A concrete *true* instance from FIPS-197: `0x57 · 0x83 = 0x01 · 0xc1` in
    GF(2⁸) (`0x57·0x83 = 0xc1` and `0x01·0xc1 = 0xc1`), decided by the emitted
    GF(2⁸) kernel on the serialized (zero-extended) operands. -/
example :
    gf256Ref (encByte 0x57) (encByte 0x83) = gf256Ref (encByte 0x01) (encByte 0xc1) :=
  (gf256Mul_spec_transfers 0x57 0x01 0x83 0xc1).mp (by decide)

/-- A concrete *commutativity* instance: `0x53 · 0xca = 0xca · 0x53 = 0x01` in
    GF(2⁸) (the Rijndael field is commutative; `0x53` and `0xca` are
    multiplicative inverses, FIPS-197), decided by the emitted reducing kernel —
    exercising that the char-2 reduction (the `0x11b` fold) is performed by the
    emitted code on the serialized operands. -/
example :
    gf256Ref (encByte 0x53) (encByte 0xca) = gf256Ref (encByte 0xca) (encByte 0x53) :=
  (gf256Mul_spec_transfers 0x53 0xca 0xca 0x53).mp (by decide)

end CatCrypt.Crypto.SecureCompilation.RelationalFront
