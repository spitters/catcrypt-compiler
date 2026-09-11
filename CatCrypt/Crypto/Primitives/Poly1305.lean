/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Poly1305 MAC (RFC 8439)

Constructive implementation of Poly1305 message authentication code.
Poly1305 evaluates a polynomial over GF(2^130 - 5) using a one-time key.

## Algorithm

Given key `(r, s)` where `r` is clamped and `s` is the nonce-derived pad:
1. Split message into 16-byte blocks
2. Append 0x01 to each block (to distinguish from zero blocks)
3. Evaluate: `acc = ((acc + block_i) * r) mod (2^130 - 5)`
4. Output: `(acc + s) mod 2^128`

All definitions are sealed with `@[irreducible]`.

## References

* RFC 8439, Section 2.5 — The Poly1305 Algorithm
* Bernstein — *The Poly1305-AES Message-Authentication Code*, FSE 2005
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.Poly1305

/-! ## GF(2^130 - 5) Arithmetic -/

/-- The prime `2^130 - 5` defining the Poly1305 field. -/
def poly1305_prime : Nat := 2^130 - 5

/-- Addition modulo `2^130 - 5`. -/
def addMod (a b : Nat) : Nat := (a + b) % poly1305_prime

/-- Multiplication modulo `2^130 - 5`. -/
def mulMod (a b : Nat) : Nat := (a * b) % poly1305_prime

/-! ## Key Clamping (RFC 8439, Section 2.5.2) -/

/-- Clamp the `r` portion of the Poly1305 key. -/
def clampR (r : Nat) : Nat :=
  r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-! ## Byte Encoding -/

/-- Decode a list of bytes as a little-endian natural number. -/
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldl (init := (0, 0)) (fun (acc : Nat × Nat) b =>
    (acc.1 + b.toNat * 2^acc.2, acc.2 + 8)) |>.1

/-- Convert a 16-byte block to a field element:
    decode as little-endian, then set bit `8 * len` (high bit marker). -/
def blockToNat (block : List UInt8) : Nat :=
  bytesToNat block + 2^(8 * block.length)

/-- Process one Poly1305 block: `acc = ((acc + block) * r) mod p`. -/
def processBlock (r : Nat) (acc : Nat) (block : List UInt8) : Nat :=
  mulMod (addMod acc (blockToNat block)) r

/-! ## Message Chunking -/

/-- Split a message into chunks of at most 16 bytes. -/
def chunkMessage (msg : List UInt8) : List (List UInt8) :=
  match h : msg with
  | [] => []
  | _ :: _ =>
    let chunk := msg.take 16
    let rest := msg.drop 16
    chunk :: chunkMessage rest
termination_by msg.length
decreasing_by
  simp_wf
  simp [List.length_drop, h]
  omega

/-! ## Full Poly1305 Computation -/

/-- Poly1305 MAC computation.

    Input:
    - `key`: 32 bytes (first 16 = `r`, last 16 = `s`)
    - `msg`: arbitrary-length message

    Output: 16-byte tag as `Nat` (to be serialized little-endian). -/
def poly1305 (key : List UInt8) (msg : List UInt8) : Nat :=
  let r := clampR (bytesToNat (key.take 16))
  let s := bytesToNat (key.drop 16 |>.take 16)
  let blocks := chunkMessage msg
  let acc := blocks.foldl (processBlock r) 0
  (acc + s) % 2^128

/-- Serialize a Poly1305 tag (Nat) to 16 little-endian bytes. -/
def tagToBytes (tag : Nat) : List UInt8 :=
  (List.range 16).map fun i => ((tag >>> (8 * i)) % 256).toUInt8

/-! ## Seal all definitions -/

attribute [irreducible] poly1305 processBlock blockToNat bytesToNat
attribute [irreducible] addMod mulMod clampR poly1305_prime tagToBytes

end CatCrypt.Crypto.Primitives.Poly1305
