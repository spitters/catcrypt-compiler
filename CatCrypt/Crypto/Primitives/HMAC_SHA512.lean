/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Primitives.SHA512
public import CatCrypt.Crypto.Primitives.SHA512

/-!
# HMAC-SHA512 (RFC 2104)

Constructive implementation of HMAC using SHA-512.

```
HMAC(K, text) = SHA512((K ⊕ opad) || SHA512((K ⊕ ipad) || text))
```

Block size B = 128 bytes (SHA-512 block).  Output L = 64 bytes
(SHA-512 digest).  Uses `sha512TwoBlock` for the inner/outer hashes
since both inputs are 128 + N bytes (two SHA-512 blocks).

Mirrors the SHA-256 file `Primitives.HMAC` exactly with all sizes
doubled.

All definitions are sealed with `@[irreducible]`.

## References

* RFC 2104 — HMAC: Keyed-Hashing for Message Authentication
* RFC 4231 — Identifiers and Test Vectors for HMAC-SHA-256, HMAC-SHA-384, HMAC-SHA-512
* RFC 5869 — HMAC-based Extract-and-Expand Key Derivation Function (HKDF)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.HMAC_SHA512

open CatCrypt.Crypto.Primitives.SHA512

/-! ## HMAC Constants -/

/-- HMAC ipad byte (0x36). -/
def ipadByte : UInt8 := 0x36

/-- HMAC opad byte (0x5c). -/
def opadByte : UInt8 := 0x5c

/-! ## Key Preparation -/

/-- Prepare HMAC-SHA512 key: if > 128 bytes, hash it; then pad to 128 bytes. -/
def prepareKey (key : List UInt8) : List UInt8 :=
  let k := if key.length > 128 then
    List.ofFn (sha512Short key)
  else key
  k ++ List.replicate (128 - k.length) 0

/-! ## HMAC-SHA512 -/

/-- XOR each byte with a constant. -/
def xorPad (key : List UInt8) (padByte : UInt8) : List UInt8 :=
  key.map (· ^^^ padByte)

/-- Convert a list to a `Fin 128 → UInt8` function (truncate/pad to 128 bytes). -/
def listToBlock128 (l : List UInt8) : Fin 128 → UInt8 :=
  fun i => l.getD i.val 0

/-- HMAC-SHA512: `HMAC(K, text) = SHA512((K ⊕ opad) || SHA512((K ⊕ ipad) || text))`.

    Uses `sha512TwoBlock` for both the inner and outer hashes,
    since `innerKey`/`outerKey` are always 128 bytes, making both
    inputs at least 128 bytes (requiring 2 SHA-512 blocks).

    Handles messages up to 111 bytes (so inner input ≤ 239 bytes = 2 blocks). -/
def hmacSha512 (key msg : List UInt8) : List UInt8 :=
  let k := prepareKey key
  let innerKey := xorPad k ipadByte
  let outerKey := xorPad k opadByte
  -- Inner hash: SHA512(innerKey || msg) — 2 blocks (innerKey = 128 bytes)
  let innerHash := List.ofFn (sha512TwoBlock (listToBlock128 innerKey) msg
    (innerKey.length + msg.length))
  -- Outer hash: SHA512(outerKey || innerHash) — 2 blocks (outerKey = 128 bytes,
  -- innerHash = 64 bytes < 112 ⇒ second block fits its padding)
  List.ofFn (sha512TwoBlock (listToBlock128 outerKey) innerHash
    (outerKey.length + innerHash.length))

/-! ## Properties (proved before sealing so native_decide can evaluate) -/

/-- HMAC-SHA512 output is always 64 bytes. -/
theorem hmacSha512_len (key msg : List UInt8) : (hmacSha512 key msg).length = 64 := by
  simp only [hmacSha512, List.length_ofFn]

/-- HMAC-SHA512 is non-trivial: different messages with same key give
    different tags. -/
theorem hmacSha512_nontrivial :
    hmacSha512 (List.replicate 20 0x0b)
      [0x48, 0x69, 0x20, 0x54, 0x68, 0x65, 0x72, 0x65] ≠
    hmacSha512 (List.replicate 20 0x0b)
      [0x77, 0x68, 0x61, 0x74, 0x20, 0x64, 0x6f] := by
  native_decide

/-! ## Seal all definitions -/

attribute [irreducible] hmacSha512 prepareKey xorPad listToBlock128

end CatCrypt.Crypto.Primitives.HMAC_SHA512
