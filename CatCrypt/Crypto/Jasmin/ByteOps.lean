/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCT


@[expose] public section
set_option autoImplicit false

/-!
# Phase K.1 — Byte-Op Leaf Whitelist for Symmetric Crypto Kernels

This module registers the byte-level leaf functions invoked by the
symmetric-crypto kernels (AES, ChaCha20, SHA-256, SHA-3 / Keccak) and
exposes thin builder helpers that produce the appropriate `LowCT`
nodes (`.RCall` / `.RCallN`) at each call site.

## Why a whitelist?

Phase K introduced `TowerType.TBytes (n : Nat)` so the symmetric
kernels can be authored against fixed-size byte arrays without
inventing new tower-type constructors per primitive.  Phase K.1
complements that by registering the *names* of the leaf functions
that operate on those byte arrays — every primitive-level operation
(SBox lookup, ChaCha20 quarter round, Keccak-f round, …) goes
through one of these whitelisted leaves rather than open-coding the
byte-level arithmetic in the DSL.

Downstream pipeline code (the borrow checker, the CT analyser, the
Jasmin emitter) consults `byteOpsLeafWhitelist` to decide whether a
given leaf name belongs to the symmetric-crypto family — important
for the CT analyser, which gives a tighter information-flow bound
on whitelisted leaves than on user-defined Rust calls.

## Convention notes

* For `bytes_rotl32` / `bytes_rotr32` / `bytes_rotl64` /
  `bytes_rotr64`, the rotation amount is a *static* parameter.  The
  builder takes it as a `Nat` and *currently* drops it from the call
  shape (the rotation amount is encoded into the leaf-spec lookup at
  the call site, not into the AST args).  If a kernel needs to vary
  the rotation amount at runtime, switch to the underlying
  `.RCall name dst [x, rotAmtSlot]` shape directly — but no current
  primitive does so.
* The ChaCha20 quarter round mutates four state words; we model it
  as a 4-destination `.RCallN` (the same shape used by the Phase G
  multi-output bignum carries).  Every other byte-op leaf is a
  single-destination `.RCall`.
-/

namespace CatCrypt.Crypto.Jasmin.LowCT.ByteOps

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1 The byte-op leaf whitelist -/

/-- Names of byte-level leaf functions invoked by AES / ChaCha20 /
    SHA-256 / SHA-3 kernels.  Downstream pipeline stages (borrow
    checker, CT analyser, Jasmin emitter) consult this list to
    decide whether a `.RCall name …` site dispatches to a
    symmetric-crypto byte-op or to a user-defined helper. -/
def byteOpsLeafWhitelist : List String := [
  -- AES round primitives
  "aes_sbox_lookup", "aes_round", "aes_inv_round", "aes_key_schedule_round",
  -- ChaCha20 round primitives
  "chacha_quarter_round", "chacha_block_round",
  -- SHA-256 round primitives
  "sha256_round", "sha256_compress",
  -- SHA-3 / Keccak round primitives
  "keccak_f_round", "keccak_p1600",
  -- Generic byte-level helpers used by all of the above
  "bytes_xor_blocks", "bytes_and", "bytes_or", "bytes_not",
  "bytes_rotl32", "bytes_rotr32", "bytes_rotl64", "bytes_rotr64",
  "bytes_load_u32_be", "bytes_load_u32_le",
  "bytes_load_u64_be", "bytes_load_u64_le",
  "bytes_store_u32_be", "bytes_store_u32_le",
  "bytes_store_u64_be", "bytes_store_u64_le",
]

/-- Membership test in the byte-op leaf whitelist.  The underlying
    `List.contains` for `String` is decidable (via `DecidableEq String`),
    so this is just a re-export with a stable name for the rest of the
    pipeline. -/
def isByteOpsLeaf (s : String) : Bool := byteOpsLeafWhitelist.contains s

/-- The `Decidable` instance follows from `Bool`-valued `contains` —
    Lean's `Decidable` for `b = true` is automatic.  This wrapper exists
    so downstream files can write `decide (isByteOpsLeaf "aes_round")` /
    `decide (byteOpsLeafWhitelist.contains "…")` without unfolding. -/
instance decidableContainsByteOpsLeaf (s : String) :
    Decidable (byteOpsLeafWhitelist.contains s = true) :=
  inferInstance

/-! ## §2 Per-primitive `LowCT` builder helpers -/

/-- AES forward round.  Lowers to `out := aes_round(state, roundKey)`. -/
def aesRound (out state roundKey : Located) : LowCT :=
  .RCall "aes_round" out [state, roundKey]

/-- AES inverse round (used in decryption). -/
def aesInvRound (out state roundKey : Located) : LowCT :=
  .RCall "aes_inv_round" out [state, roundKey]

/-- AES key-schedule round (one column of the expanded key). -/
def aesKeyScheduleRound (out prev rcon : Located) : LowCT :=
  .RCall "aes_key_schedule_round" out [prev, rcon]

/-- AES SBox table lookup on a single byte.  `byte` is a 1-byte
    `TBytes 1` (or `TU64` carrying the low byte). -/
def aesSboxLookup (out byte : Located) : LowCT :=
  .RCall "aes_sbox_lookup" out [byte]

/-- ChaCha20 quarter round.  Mutates four state words in place; modelled
    as a 4-destination `RCallN` (Phase G N-output shape).  The four
    destinations and the four (pre-state) reads are listed in the same
    order: `a`, `b`, `c`, `d`.  Borrow-check: the four destinations are
    distinct slots in the ChaCha state matrix. -/
def chachaQuarterRound (a b c d : Located) : LowCT :=
  .RCallN "chacha_quarter_round" [a, b, c, d] [a, b, c, d]

/-- ChaCha20 block round (8 quarter rounds: 4 column + 4 diagonal). -/
def chachaBlockRound (out state : Located) : LowCT :=
  .RCall "chacha_block_round" out [state]

/-- SHA-256 round (one of 64).  `state` is the 8-word working hash;
    `msgChunk` is the 64-byte message block expanded to the round's
    `K_t + W_t` input. -/
def sha256Round (out state msgChunk : Located) : LowCT :=
  .RCall "sha256_round" out [state, msgChunk]

/-- SHA-256 compression function (full 64 rounds + final add). -/
def sha256Compress (out state msgBlock : Located) : LowCT :=
  .RCall "sha256_compress" out [state, msgBlock]

/-- Keccak-f round (one of 24).  `state` is the 1600-bit (200-byte)
    Keccak state; output replaces it. -/
def keccakRound (out state : Located) : LowCT :=
  .RCall "keccak_f_round" out [state]

/-- Keccak-p1600 (full 24 rounds). -/
def keccakP1600 (out state : Located) : LowCT :=
  .RCall "keccak_p1600" out [state]

/-- Block-wise XOR of two equal-length byte arrays. -/
def bytesXorBlocks (out a b : Located) : LowCT :=
  .RCall "bytes_xor_blocks" out [a, b]

/-- Block-wise AND. -/
def bytesAnd (out a b : Located) : LowCT :=
  .RCall "bytes_and" out [a, b]

/-- Block-wise OR. -/
def bytesOr (out a b : Located) : LowCT :=
  .RCall "bytes_or" out [a, b]

/-- Block-wise bitwise NOT. -/
def bytesNot (out a : Located) : LowCT :=
  .RCall "bytes_not" out [a]

/-- 32-bit left rotation.  The rotation amount `n` is a static
    parameter consumed by the leaf spec, not an AST-level argument
    (no current symmetric-crypto kernel rotates by a runtime amount).
    See the module docstring for the convention. -/
def bytesRotl32 (out x : Located) (_n : Nat) : LowCT :=
  .RCall "bytes_rotl32" out [x]

/-- 32-bit right rotation. -/
def bytesRotr32 (out x : Located) (_n : Nat) : LowCT :=
  .RCall "bytes_rotr32" out [x]

/-- 64-bit left rotation. -/
def bytesRotl64 (out x : Located) (_n : Nat) : LowCT :=
  .RCall "bytes_rotl64" out [x]

/-- 64-bit right rotation. -/
def bytesRotr64 (out x : Located) (_n : Nat) : LowCT :=
  .RCall "bytes_rotr64" out [x]

/-! ## §3 Smoke tests

Each builder produces the documented `.RCall` / `.RCallN` shape
verifiable by `rfl`.  These examples double as a regression guard:
if the underlying `LowCT` constructors change, this file fails to
build and the pipeline catches the breakage immediately. -/

section SmokeTests

def s : Located := { locVar := "state",   locSrc := .TBytes 16 }
def k : Located := { locVar := "rk",      locSrc := .TBytes 16 }
def o : Located := { locVar := "out",     locSrc := .TBytes 16 }
def b : Located := { locVar := "byte",    locSrc := .TBytes 1  }
def a4 : Located := { locVar := "a", locSrc := .TBytes 4 }
def b4 : Located := { locVar := "b", locSrc := .TBytes 4 }
def c4 : Located := { locVar := "c", locSrc := .TBytes 4 }
def d4 : Located := { locVar := "d", locSrc := .TBytes 4 }

example : aesRound o s k = .RCall "aes_round" o [s, k] := rfl
example : aesInvRound o s k = .RCall "aes_inv_round" o [s, k] := rfl
example : aesKeyScheduleRound o s k = .RCall "aes_key_schedule_round" o [s, k] := rfl
example : aesSboxLookup o b = .RCall "aes_sbox_lookup" o [b] := rfl

example :
    chachaQuarterRound a4 b4 c4 d4
      = .RCallN "chacha_quarter_round" [a4, b4, c4, d4] [a4, b4, c4, d4] := rfl

example : chachaBlockRound o s = .RCall "chacha_block_round" o [s] := rfl

example : sha256Round o s k = .RCall "sha256_round" o [s, k] := rfl
example : sha256Compress o s k = .RCall "sha256_compress" o [s, k] := rfl

example : keccakRound o s = .RCall "keccak_f_round" o [s] := rfl
example : keccakP1600 o s = .RCall "keccak_p1600" o [s] := rfl

example : bytesXorBlocks o a4 b4 = .RCall "bytes_xor_blocks" o [a4, b4] := rfl
example : bytesAnd o a4 b4 = .RCall "bytes_and" o [a4, b4] := rfl
example : bytesOr  o a4 b4 = .RCall "bytes_or"  o [a4, b4] := rfl
example : bytesNot o a4    = .RCall "bytes_not" o [a4] := rfl

example : bytesRotl32 o a4 7  = .RCall "bytes_rotl32" o [a4] := rfl
example : bytesRotr32 o a4 12 = .RCall "bytes_rotr32" o [a4] := rfl
example : bytesRotl64 o a4 32 = .RCall "bytes_rotl64" o [a4] := rfl
example : bytesRotr64 o a4 16 = .RCall "bytes_rotr64" o [a4] := rfl

/-- Whitelist contains every leaf name the builders emit. -/
example : byteOpsLeafWhitelist.contains "aes_round" = true := by decide
example : byteOpsLeafWhitelist.contains "chacha_quarter_round" = true := by decide
example : byteOpsLeafWhitelist.contains "sha256_compress" = true := by decide
example : byteOpsLeafWhitelist.contains "keccak_p1600" = true := by decide
example : byteOpsLeafWhitelist.contains "bytes_xor_blocks" = true := by decide
example : byteOpsLeafWhitelist.contains "bytes_rotl32" = true := by decide

/-- Whitelist rejects user-defined names. -/
example : byteOpsLeafWhitelist.contains "my_user_helper" = false := by decide

/-- The `isByteOpsLeaf` wrapper agrees with `contains`. -/
example : isByteOpsLeaf "aes_round" = true := by decide
example : isByteOpsLeaf "not_a_leaf" = false := by decide

end SmokeTests

end CatCrypt.Crypto.Jasmin.LowCT.ByteOps
