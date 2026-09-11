/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminOps
public import CatCrypt.Deep.RawCode

/-!
# AES-128 Functional Specification

Pure functional specification of AES-128 encryption and decryption.
This is the reference spec against which the Jasmin implementation is proven
equivalent. Follows `aes_spec.v` from the CatCrypt jasmin branch.

## Main definitions

* `rcon` — AES round constants
* `keyExpand` — single round key expansion
* `keySchedule` — full 11-round key schedule
* `aes128` — AES-128 encryption
* `aes128Inv` — AES-128 decryption

## References

- FIPS 197: Advanced Encryption Standard (AES)
- `aes_spec.v` from CatCrypt jasmin branch
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.AES

noncomputable section

/-! ## Round Constants -/

/-- AES round constants (RCON). -/
def rcon : Nat → BitVec 8
  | 0 => 0x01
  | 1 => 0x02
  | 2 => 0x04
  | 3 => 0x08
  | 4 => 0x10
  | 5 => 0x20
  | 6 => 0x40
  | 7 => 0x80
  | 8 => 0x1B
  | 9 => 0x36
  | _ => 0x00

/-! ## Key Expansion -/

/-- Extract the i-th 32-bit word from a 128-bit key (little-endian). -/
def getKeyWord (key : BitVec 128) (i : Nat) : BitVec 32 :=
  getCol128 key i

/-- Reconstruct a 128-bit key from four 32-bit words. -/
def mkKey (w0 w1 w2 w3 : BitVec 32) : BitVec 128 :=
  setCol128 (setCol128 (setCol128 (setCol128 0 0 w0) 1 w1) 2 w2) 3 w3

/-- Single round of key expansion.
    `keyExpand prevKey rconVal` produces the next round key. -/
def keyExpand (prevKey : BitVec 128) (rconVal : BitVec 8) : BitVec 128 :=
  let w0 := getKeyWord prevKey 0
  let w1 := getKeyWord prevKey 1
  let w2 := getKeyWord prevKey 2
  let w3 := getKeyWord prevKey 3
  let tmp := subWord (rotWord w3) ^^^ (rconVal.zeroExtend 32)
  let w4 := w0 ^^^ tmp
  let w5 := w1 ^^^ w4
  let w6 := w2 ^^^ w5
  let w7 := w3 ^^^ w6
  mkKey w4 w5 w6 w7

/-- Round key at index `i` (0-indexed, 0 = original key). -/
def keySchedule (key : BitVec 128) : Nat → BitVec 128
  | 0 => key
  | i + 1 => keyExpand (keySchedule key i) (rcon i)

/-! ## AES-128 Encryption -/

/-- AES-128 encryption.
    `aes128 key msg` encrypts `msg` with `key`.
    10 rounds: 1 AddRoundKey + 9 (SubBytes, ShiftRows, MixColumns, AddRoundKey) + 1 final. -/
def aes128 (key msg : BitVec 128) : BitVec 128 :=
  -- Initial AddRoundKey
  let state := msg ^^^ keySchedule key 0
  -- 9 main rounds
  let state := (List.range 9).foldl (fun s i =>
    wAESENC s (keySchedule key (i + 1))
  ) state
  -- Final round (no MixColumns)
  wAESENCLAST state (keySchedule key 10)

/-! ## AES-128 Decryption -/

/-- AES-128 decryption.
    `aes128Inv key cipher` decrypts `cipher` with `key`. -/
def aes128Inv (key cipher : BitVec 128) : BitVec 128 :=
  let state := cipher ^^^ keySchedule key 10
  let state := (List.range 9).foldl (fun s i =>
    wAESDEC s (keySchedule key (10 - (i + 1)))
  ) state
  wAESDECLAST state (keySchedule key 0)

/-! ## CatCrypt Code Specification

These wrap the pure spec as `RawCode` for use in CatCrypt games. -/

open CatCrypt.Deep

/-- Key expansion as RawCode: stores round keys in an array. -/
def keyExpansionCode (key : BitVec 128) : RawCode (Fin 11 → BitVec 128) :=
  .ret (fun i => keySchedule key i.val)

/-- AES encryption as RawCode. -/
def aesCode (key msg : BitVec 128) : RawCode (BitVec 128) :=
  .ret (aes128 key msg)

/-- AES decryption as RawCode. -/
def aesInvCode (key cipher : BitVec 128) : RawCode (BitVec 128) :=
  .ret (aes128Inv key cipher)

/-! ## Basic Properties -/

/-- Key schedule at 0 is the original key. -/
@[simp] theorem keySchedule_zero (key : BitVec 128) :
    keySchedule key 0 = key := rfl

/-- AES encryption XORs with the key initially. -/
theorem aes128_initial (key msg : BitVec 128) :
    let state₀ := msg ^^^ key
    aes128 key msg =
      wAESENCLAST ((List.range 9).foldl (fun s i =>
        wAESENC s (keySchedule key (i + 1))) state₀) (keySchedule key 10) :=
  rfl

end

end CatCrypt.Crypto.Jasmin.AES
