/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Primitives.SHA256

/-!
# HMAC-SHA256 (RFC 2104)

Constructive implementation of HMAC using SHA-256.

HMAC(K, text) = SHA256((K ⊕ opad) || SHA256((K ⊕ ipad) || text))

Uses `sha256TwoBlock` for the inner/outer hashes since both
inputs are 64 + N bytes (two SHA-256 blocks).

All definitions are sealed with `@[irreducible]`.

## References

* RFC 2104 — HMAC: Keyed-Hashing for Message Authentication
* RFC 5869 — HMAC-based Extract-and-Expand Key Derivation Function (HKDF)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.HMAC

open CatCrypt.Crypto.Primitives.SHA256

/-! ## HMAC Constants -/

/-- HMAC ipad byte (0x36). -/
def ipadByte : UInt8 := 0x36

/-- HMAC opad byte (0x5c). -/
def opadByte : UInt8 := 0x5c

/-! ## Key Preparation -/

/-- Prepare HMAC key: if > 64 bytes, hash it; then pad to 64 bytes. -/
def prepareKey (key : List UInt8) : List UInt8 :=
  let k := if key.length > 64 then
    List.ofFn (sha256Short key)
  else key
  k ++ List.replicate (64 - k.length) 0

/-! ## HMAC-SHA256 -/

/-- XOR each byte with a constant. -/
def xorPad (key : List UInt8) (padByte : UInt8) : List UInt8 :=
  key.map (· ^^^ padByte)

/-- Convert a list to a `Fin 64 → UInt8` function (truncate/pad to 64 bytes). -/
def listToBlock64 (l : List UInt8) : Fin 64 → UInt8 :=
  fun i => l.getD i.val 0

/-- HMAC-SHA256: `HMAC(K, text) = SHA256((K ⊕ opad) || SHA256((K ⊕ ipad) || text))`.

    Uses `sha256TwoBlock` for both the inner and outer hashes,
    since `innerKey`/`outerKey` are always 64 bytes, making both
    inputs at least 64 bytes (requiring 2 SHA-256 blocks).

    Handles messages up to 55 bytes (so inner input ≤ 119 bytes = 2 blocks). -/
def hmacSha256 (key msg : List UInt8) : List UInt8 :=
  let k := prepareKey key
  let innerKey := xorPad k ipadByte
  let outerKey := xorPad k opadByte
  -- Inner hash: SHA256(innerKey || msg) — 2 blocks (innerKey = 64 bytes)
  let innerHash := List.ofFn (sha256TwoBlock (listToBlock64 innerKey) msg
    (innerKey.length + msg.length))
  -- Outer hash: SHA256(outerKey || innerHash) — 2 blocks (outerKey = 64 bytes)
  List.ofFn (sha256TwoBlock (listToBlock64 outerKey) innerHash
    (outerKey.length + innerHash.length))

/-! ## Properties (proved before sealing so native_decide can evaluate) -/

/-- HMAC-SHA256 output is always 32 bytes. -/
theorem hmacSha256_len (key msg : List UInt8) : (hmacSha256 key msg).length = 32 := by
  simp only [hmacSha256, List.length_ofFn]

/-- HMAC-SHA256 is non-trivial: RFC 4231 Test Case 1 key with different messages.
    Proved before `@[irreducible]` sealing so `native_decide` can evaluate. -/
theorem hmacSha256_nontrivial :
    hmacSha256 (List.replicate 20 0x0b)
      [0x48, 0x69, 0x20, 0x54, 0x68, 0x65, 0x72, 0x65] ≠
    hmacSha256 (List.replicate 20 0x0b)
      [0x77, 0x68, 0x61, 0x74, 0x20, 0x64, 0x6f] := by
  native_decide

/-! ## Seal all definitions -/

attribute [irreducible] hmacSha256 prepareKey xorPad listToBlock64

end CatCrypt.Crypto.Primitives.HMAC
