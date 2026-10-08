/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Std.Tactic.BVDecide

/-!
# ML-KEM per-coefficient leaf forms

Two closed `BitVec` bodies of ML-KEM-768 (FIPS 203) per-coefficient leaves, as
plain definitions:

* `mlkemDecompress10Form` — `Decompress_10` on a 10-bit codeword `t`,
  `((t & 0x3ff)·3329 + 512) >> 10` over `BitVec 64` (PQClean `polyvec.c`);
* `mlkemFrombytesC1Form` — the high coefficient of the 12-bit `ByteDecode₁₂`
  unpack of bytes `b1, b2`, `((b1 >> 4) | (b2 << 4)) & 0xFFF` over `BitVec 32`.

`mlkemDecompress10Form_eq_round` and `mlkemFrombytesC1Form_eq_decode` state each
form on its input domain without the mask.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.LeafForms

/-- The ML-KEM-768 `Decompress_10` per-coefficient body at `w = 64`:
    `((t & 0x3ff)·3329 + 512) >> 10`. -/
def mlkemDecompress10Form (t : BitVec 64) : BitVec 64 :=
  let m := t &&& 0x3ff
  let s := m * 3329 + 512
  s >>> (10 : Nat)

/-- **ML-KEM decompress form = FIPS-203 `Decompress_10`** on the codeword domain
    `t < 2^10`: the mask is the identity there and the body does not wrap the
    `BitVec 64`, so the result is the rounding decompression `(t·q + 512) >> 10`. -/
theorem mlkemDecompress10Form_eq_round (t : BitVec 64) (ht : t < 0x400#64) :
    mlkemDecompress10Form t = (t * 3329#64 + 512#64) >>> (10 : Nat) := by
  unfold mlkemDecompress10Form
  bv_decide

/-- The ML-KEM-768 `poly_frombytes` high-coefficient body at `w = 32`:
    `((b1 >> 4) | (b2 << 4)) & 0xFFF`. -/
def mlkemFrombytesC1Form (b1 b2 : BitVec 32) : BitVec 32 :=
  let hi := b1 >>> (4 : Nat)
  let lo := b2 <<< (4 : Nat)
  (hi ||| lo) &&& 0xFFF

/-- **ML-KEM `poly_frombytes` form = 12-bit high-coefficient decode** on the byte
    domain `b1, b2 < 2^8`: the two contributions occupy disjoint bit ranges and the
    `0xFFF` mask is exact. -/
theorem mlkemFrombytesC1Form_eq_decode (b1 b2 : BitVec 32)
    (hb1 : b1 < 0x100#32) (hb2 : b2 < 0x100#32) :
    mlkemFrombytesC1Form b1 b2 = (b1 >>> (4 : Nat)) ||| (b2 <<< (4 : Nat)) := by
  unfold mlkemFrombytesC1Form
  bv_decide

end CatCrypt.Crypto.MLKEM.LeafForms
