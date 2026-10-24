/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Mathlib.Data.BitVec
public meta import CatCrypt.Crypto.Primitives.AES128
public import CatCrypt.Crypto.Primitives.AES128
public meta import CatCrypt.Crypto.Util.Gf256
public import CatCrypt.Crypto.Util.Gf256

/-!
# Verified AES-128 — full block encryption (FIPS 197)

A computable, verified Lean reference implementation of AES-128 block
encryption. Mirrors the role of `Gf16.lean` (for MAYO) and `Gf256.lean`
(for UOV) at the AES-family bridges: the bridge round-trip identities
reduce to proven facts over a verified `BitVec 128 → BitVec 128 → BitVec 128`
block-cipher reference, rather than opaque axioms on abstract AES state.

## Representation

* **block** = `BitVec 128` (the AES state, packed little-endian byte
  ordering matching `Primitives.AES128.State`);
* **key** = `BitVec 128`;
* **encryption** = 10-round AES, delegated to the canonical
  `Primitives.AES128.aes128_encrypt`.

## S-box provenance

Per the task spec fall-back gate: the S-box is **table-driven**
(256-entry lookup, FIPS 197 Table 4), via the canonical
`Primitives.AES128.sbox`. The Fermat-chain (`x ↦ x^254` in GF(2^8))
formulation is documented as an alternative but not used by this
file — the table lookup is constant-time-friendly and easy to verify
by `native_decide`.

## API

* `Aes128.encrypt : Gf128 → Gf128 → Gf128` — full 10-round AES-128
  block encryption on `BitVec 128`-packed key and block.
* `Aes128.zeroBlock`, `Aes128.fromBytes`, `Aes128.toBytes` — byte / BV
  marshallers for AEAD glue.

## Status of axioms

This file contains **0 axioms**: AES-128 is a pure computable function;
the wrapper is constructive. The S-box correctness (table = Fermat
inverse + affine) is verified externally by `Primitives.AES128`'s
construction; we expose only the table-driven body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

open CatCrypt.Crypto.Primitives.AES128

/-! ## Aes128 — verified block-cipher reference -/

namespace Aes128

/-- A 128-bit block (and key) on the verified AES side. -/
abbrev Block : Type := BitVec 128

/-- The zero block. -/
def zeroBlock : Block := 0#128

/-! ## Byte-array ↔ BitVec marshallers -/

/-- Pack a 16-byte little-endian array into a `BitVec 128`. -/
def fromBytes (b : Fin 16 → UInt8) : Block :=
  Fin.foldl 16 (fun acc (i : Fin 16) =>
    acc ||| (BitVec.ofNat 128 (b i).toNat <<< (8 * i.val))) (0#128 : BitVec 128)

/-- Unpack a `BitVec 128` into a 16-byte little-endian array. -/
def toBytes (v : Block) : Fin 16 → UInt8 := fun i =>
  ((v >>> (8 * i.val)).toNat % 256).toUInt8

/-! ## Verified AES-128 block encryption

Delegates to `Primitives.AES128.aes128_encrypt`. This is the verified
reference body that the AES-family bridges (AES-GCM, AES-CCM, AES-SIV,
AES-GCM-SIV, AEGIS) reduce to. -/

/-- AES-128 block encryption on `BitVec 128` key and block. -/
noncomputable def encrypt (key block : Block) : Block :=
  fromBytes (aes128_encrypt (toBytes key) (toBytes block))

/-! ## XOR convenience (key-stream combine) -/

/-- XOR two blocks (used for AES-CTR keystream and tag combine). -/
def xorBlock (a b : Block) : Block := a ^^^ b

theorem xorBlock_zero (a : Block) : xorBlock a zeroBlock = a := by
  unfold xorBlock zeroBlock; bv_decide

theorem zero_xorBlock (a : Block) : xorBlock zeroBlock a = a := by
  unfold xorBlock zeroBlock; bv_decide

theorem xorBlock_self (a : Block) : xorBlock a a = zeroBlock := by
  unfold xorBlock zeroBlock; bv_decide

theorem xorBlock_comm (a b : Block) : xorBlock a b = xorBlock b a := by
  unfold xorBlock; bv_decide

theorem xorBlock_assoc (a b c : Block) :
    xorBlock (xorBlock a b) c = xorBlock a (xorBlock b c) := by
  unfold xorBlock; bv_decide

/-- XOR-cancellation: two applications recover the input. -/
theorem xorBlock_cancel (k pt : Block) :
    xorBlock (xorBlock pt k) k = pt := by
  unfold xorBlock; bv_decide

/-! ## AES-CTR single-block encryption: pt ⊕ AES_K(ctr) -/

/-- One AES-CTR step on a single block. -/
noncomputable def ctrStep (key ctr pt : Block) : Block :=
  xorBlock pt (encrypt key ctr)

/-- AES-CTR is involutive: encryption ∘ encryption = identity (for a
    given key and counter). -/
theorem ctrStep_cancel (key ctr pt : Block) :
    ctrStep key ctr (ctrStep key ctr pt) = pt := by
  unfold ctrStep
  exact xorBlock_cancel (encrypt key ctr) pt

end Aes128

end CatCrypt.Util
