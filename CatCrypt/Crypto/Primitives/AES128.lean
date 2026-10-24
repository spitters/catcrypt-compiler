/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

import all Init.Data.Repr
public import Mathlib.Logic.Function.Basic

/-!
# AES-128 Block Cipher (FIPS 197)

Constructive implementation of AES-128 encryption. The S-box is given as
a lookup table (derived from GF(2^8) inversion + affine transform).

All round-level and top-level functions are marked `@[irreducible]` to
prevent the kernel from evaluating them during proof checking.

## Structure

AES-128 uses:
- 128-bit key, 128-bit block (4×4 byte matrix, column-major)
- 10 rounds with SubBytes, ShiftRows, MixColumns, AddRoundKey
- Final round omits MixColumns
- Key expansion produces 11 round keys from the original key

## References

* FIPS 197 — Advanced Encryption Standard (AES)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.AES128

/-! ## AES S-box (FIPS 197, Section 5.1.1)

The S-box is the composition of:
1. Multiplicative inverse in GF(2^8) with irreducible polynomial
   `x^8 + x^4 + x^3 + x + 1` (mapping 0 to 0)
2. An affine transformation over GF(2)

We embed the standard lookup table directly. -/

def sboxData : List UInt8 := [
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
]

/-- AES S-box lookup: byte substitution (FIPS 197, Table 4). -/
def sbox (b : UInt8) : UInt8 :=
  sboxData.getD b.toNat 0

/-! ## Round constant (Rcon) for key expansion -/

def rconData : List UInt8 := [
  0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36
]

/-- Round constant for key expansion round `i` (0-indexed). -/
def rcon (i : Nat) : UInt8 := rconData.getD i 0

/-! ## State representation

AES state is a 4×4 byte matrix in column-major order.
We represent it as `Fin 16 → UInt8` where index `4*col + row`. -/

/-- AES state: 16 bytes in column-major order. -/
abbrev State := Fin 16 → UInt8

/-- AES-128 key: 16 bytes. -/
abbrev Key128 := Fin 16 → UInt8

/-- Access state byte at (row, col). Column-major: index = 4*col + row. -/
def stateGet (s : State) (row col : Fin 4) : UInt8 :=
  s ⟨4 * col.val + row.val, by omega⟩

/-- Set state byte at (row, col). -/
def stateSet (s : State) (row col : Fin 4) (v : UInt8) : State :=
  Function.update s ⟨4 * col.val + row.val, by omega⟩ v

/-! ## SubBytes (FIPS 197, Section 5.1.1) -/

/-- Apply the S-box to every byte of the state. -/
def subBytes (s : State) : State := fun i => sbox (s i)

/-! ## ShiftRows (FIPS 197, Section 5.1.2)

Row 0: no shift
Row 1: left shift by 1
Row 2: left shift by 2
Row 3: left shift by 3 -/

/-- Circular left shift of row indices. -/
def shiftRows (s : State) : State := fun i =>
  let row := i.val % 4
  let col := i.val / 4
  let newCol := (col + row) % 4
  stateGet s ⟨row, by omega⟩ ⟨newCol, by omega⟩

/-! ## MixColumns (FIPS 197, Section 5.1.3)

Each column is treated as a polynomial over GF(2^8) and multiplied
by the fixed polynomial `{03}x^3 + {01}x^2 + {01}x + {02}`. -/

/-- Multiply by 2 in GF(2^8) (xtime). -/
def xtime (b : UInt8) : UInt8 :=
  let shifted := b <<< 1
  if b &&& 0x80 != 0 then shifted ^^^ 0x1b else shifted

/-- Multiply by 3 in GF(2^8): `3·b = 2·b ⊕ b`. -/
def mul3 (b : UInt8) : UInt8 := xtime b ^^^ b

/-- Mix one column: multiply by the MDS matrix. -/
def mixColumn (b0 b1 b2 b3 : UInt8) : UInt8 × UInt8 × UInt8 × UInt8 :=
  ( xtime b0 ^^^ mul3 b1 ^^^ b2 ^^^ b3,
    b0 ^^^ xtime b1 ^^^ mul3 b2 ^^^ b3,
    b0 ^^^ b1 ^^^ xtime b2 ^^^ mul3 b3,
    mul3 b0 ^^^ b1 ^^^ b2 ^^^ xtime b3 )

/-- Apply MixColumns to all 4 columns. -/
def mixColumns (s : State) : State := fun i =>
  let col := i.val / 4
  let row := i.val % 4
  let c0 := stateGet s 0 ⟨col, by omega⟩
  let c1 := stateGet s 1 ⟨col, by omega⟩
  let c2 := stateGet s 2 ⟨col, by omega⟩
  let c3 := stateGet s 3 ⟨col, by omega⟩
  let (r0, r1, r2, r3) := mixColumn c0 c1 c2 c3
  match row with
  | 0 => r0 | 1 => r1 | 2 => r2 | _ => r3

/-! ## AddRoundKey (FIPS 197, Section 5.1.4) -/

/-- XOR the state with a round key. -/
def addRoundKey (s : State) (k : Key128) : State := fun i => s i ^^^ k i

/-! ## Key Expansion (FIPS 197, Section 5.2)

AES-128 expands the 16-byte key into 11 round keys (176 bytes total). -/

/-- Rotate a 4-byte word left by one byte. -/
def rotWord (w : Fin 4 → UInt8) : Fin 4 → UInt8 := fun i =>
  w ⟨(i.val + 1) % 4, by omega⟩

/-- Apply S-box to each byte of a 4-byte word. -/
def subWord (w : Fin 4 → UInt8) : Fin 4 → UInt8 := fun i => sbox (w i)

/-- Extract 4-byte word `j` from the expanded key array. -/
def getWord (expanded : Fin 176 → UInt8) (j : Fin 44) : Fin 4 → UInt8 := fun i =>
  expanded ⟨4 * j.val + i.val, by have := j.isLt; omega⟩

/-- AES-128 key expansion: produces 176 bytes (11 round keys). -/
def keyExpansion (key : Key128) : Fin 176 → UInt8 :=
  -- Start with the original key in positions 0..15
  let init : Fin 176 → UInt8 := fun i =>
    if h : i.val < 16 then key ⟨i.val, h⟩ else 0
  -- Expand words 4..43 (each word is 4 bytes)
  Fin.foldl 40 (fun (expanded : Fin 176 → UInt8) (wi : Fin 40) =>
    let j := wi.val + 4  -- word index (4..43)
    let prev := getWord expanded ⟨j - 1, by have := wi.isLt; omega⟩
    let prevNk := getWord expanded ⟨j - 4, by have := wi.isLt; omega⟩
    let temp :=
      if j % 4 == 0 then
        let rotated := rotWord prev
        let subbed := subWord rotated
        fun (i : Fin 4) =>
          if i.val == 0 then subbed i ^^^ rcon (j / 4 - 1) else subbed i
      else prev
    -- XOR with word from Nk positions back
    let newWord : Fin 4 → UInt8 := fun i => prevNk i ^^^ temp i
    -- Write the new word into the expanded key
    -- j = wi.val + 4, so j ∈ [4, 43], and 4*43 + 3 = 175 < 176
    Fin.foldl 4 (fun (exp : Fin 176 → UInt8) (bi : Fin 4) =>
      let idx : Fin 176 := ⟨4 * j + bi.val, by have := wi.isLt; omega⟩
      Function.update exp idx (newWord bi)) expanded) init

/-- Extract round key `r` (0..10) from the expanded key. -/
def roundKey (expanded : Fin 176 → UInt8) (r : Fin 11) : Key128 := fun i =>
  expanded ⟨16 * r.val + i.val, by omega⟩

/-! ## AES-128 Encryption (FIPS 197, Section 5.1) -/

/-- One AES round: SubBytes → ShiftRows → MixColumns → AddRoundKey. -/
def aesRound (s : State) (rk : Key128) : State :=
  addRoundKey (mixColumns (shiftRows (subBytes s))) rk

/-- Final AES round: SubBytes → ShiftRows → AddRoundKey (no MixColumns). -/
def aesFinalRound (s : State) (rk : Key128) : State :=
  addRoundKey (shiftRows (subBytes s)) rk

/-- AES-128 block encryption.

    Encrypts a 16-byte plaintext block with a 16-byte key.
    Performs initial AddRoundKey, 9 standard rounds, and 1 final round. -/
def aes128_encrypt (key : Key128) (block : State) : State :=
  let expanded := keyExpansion key
  let s0 := addRoundKey block (roundKey expanded ⟨0, by omega⟩)
  -- Rounds 1..9
  let s9 := Fin.foldl 9 (fun s (r : Fin 9) =>
    aesRound s (roundKey expanded ⟨r.val + 1, by omega⟩)) s0
  -- Final round 10
  aesFinalRound s9 (roundKey expanded ⟨10, by omega⟩)

/-! ## Seal all definitions

Prevents `simp`/`rfl`/`decide`/`norm_num` from unfolding these
definitions during proof checking. Use `unfold` or `delta` explicitly. -/

attribute [irreducible] sbox sboxData rcon rconData
attribute [irreducible] xtime mul3 mixColumn mixColumns
attribute [irreducible] subBytes shiftRows addRoundKey
attribute [irreducible] rotWord subWord keyExpansion roundKey getWord
attribute [irreducible] aesRound aesFinalRound aes128_encrypt

end CatCrypt.Crypto.Primitives.AES128
