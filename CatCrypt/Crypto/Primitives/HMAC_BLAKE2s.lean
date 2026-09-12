/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.BLAKE2s

/-!
# HMAC-BLAKE2s and HKDF-BLAKE2s (RFC 2104, RFC 5869)

Constructive HMAC and HKDF built on BLAKE2s-256.

BLAKE2s has a 64-byte block size and 32-byte output, identical to SHA-256.
The HMAC and HKDF constructions follow the same structure as HMAC-SHA256.

All definitions are sealed with `@[irreducible]`.

## References

* RFC 2104 — HMAC: Keyed-Hashing for Message Authentication
* RFC 5869 — HMAC-based Extract-and-Expand Key Derivation Function (HKDF)
* RFC 7693 — BLAKE2
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.HMAC_BLAKE2s

open CatCrypt.Crypto.Primitives.BLAKE2s

/-! ## HMAC-BLAKE2s -/

def ipadByte : UInt8 := 0x36
def opadByte : UInt8 := 0x5c

/-- Prepare HMAC key: hash if >64 bytes, pad to 64 bytes. -/
@[irreducible] def prepareKey (key : List UInt8) : List UInt8 :=
  let k := if key.length > 64 then blake2s key else key
  k ++ List.replicate (64 - k.length) 0

/-- XOR each byte of a key with a pad byte. -/
@[irreducible] def xorPad (key : List UInt8) (padByte : UInt8) : List UInt8 :=
  key.map (· ^^^ padByte)

/-- HMAC-BLAKE2s(key, msg) = BLAKE2s(opad_key ++ BLAKE2s(ipad_key ++ msg)). -/
@[irreducible] def hmacBlake2s (key msg : List UInt8) : List UInt8 :=
  let k := prepareKey key
  let innerInput := xorPad k ipadByte ++ msg
  let innerHash := blake2s innerInput
  let outerInput := xorPad k opadByte ++ innerHash
  blake2s outerInput

/-! ## HKDF-BLAKE2s -/

/-- HKDF-Extract(salt, IKM) = HMAC-BLAKE2s(salt, IKM). -/
@[irreducible] def hkdfExtractBlake2s (salt ikm : List UInt8) : List UInt8 :=
  hmacBlake2s salt ikm

/-- HKDF-Expand(PRK, info, 32) = HMAC-BLAKE2s(PRK, info ++ [0x01]).
    Single-block expansion (L ≤ 32 bytes). -/
@[irreducible] def hkdfExpandBlake2s (prk info : List UInt8) : List UInt8 :=
  hmacBlake2s prk (info ++ [0x01])

end CatCrypt.Crypto.Primitives.HMAC_BLAKE2s
