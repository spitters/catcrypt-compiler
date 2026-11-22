/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.KeccakSponge
public import CatCrypt.Crypto.Primitives.KeccakArray -- shake: keep (`@[csimp]` theorems)
public meta import CatCrypt.Crypto.Primitives.KeccakArray -- shake: keep (evaluation by `#kat`)
public import CatCryptCore.Tactics.KatGuard

/-!
# cSHAKE, KMAC, TupleHash and ParallelHash on byte strings (NIST SP 800-185)

The functions of NIST SP 800-185 as executable functions over the sponge
`KeccakSponge.sponge` on Keccak-f[1600], restricted to byte strings and to outputs of whole
bytes, as §7.2 of the standard permits.

Every length argument of these functions (`outLen`, `blockLen`) is in bytes. The encodings
of the standard carry lengths in bits: a byte string `s` enters `encodeString` as the integer
`8 * s.length`, and an output of `outLen` bytes enters `rightEncode` as `8 * outLen`. The
block size of ParallelHash and the width of `bytepad` are encoded in bytes, as in the standard.

The standard bounds the encoded integers by `2 ^ 2040` (§2.3.1), requires a positive width of
`bytepad` (§2.3.3) and a positive block size of ParallelHash (§6.2). The functions are total
and do not check these validity conditions.

The functions are defined over the closure state of `KeccakSponge.sponge`, on which compiled
evaluation is exponential in the number of rounds. The module imports `KeccakArray`, whose
`@[csimp]` theorems make the compiled code use the equal sponge on an array state.

## Main definitions

* `leftEncode`, `rightEncode`, `encodeString`, `bytepad`: the encodings of §2.3.
* `cshake128`, `cshake256`: cSHAKE (§3).
* `kmac128`, `kmac256`, `kmacXof128`, `kmacXof256`: KMAC (§4).
* `tupleHash128`, `tupleHash256`, `tupleHashXof128`, `tupleHashXof256`: TupleHash (§5).
* `parallelHash128`, `parallelHash256`, `parallelHashXof128`, `parallelHashXof256`:
  ParallelHash (§6).

## Main results

* `encodeString_injective`: `encodeString` is injective on byte strings.
* `bytepad_length_dvd`: the length of `bytepad x w` is a multiple of `w`.
* `cshake128_nil`, `cshake256_nil`: cSHAKE with empty name and customization is SHAKE.
* `cshake128_length` and the corresponding theorem for each function: the output has
  `outLen` bytes.

## References

* NIST SP 800-185, *SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash*,
  <https://doi.org/10.6028/NIST.SP.800-185>
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.SP800185

open CatCrypt.Crypto.Primitives.KeccakSponge

/-! ## Encodings (SP 800-185 §2.3) -/

/-- The number `n` of base-256 digits of `x` in §2.3.1, with at least one digit and at most
`fuel + 1` digits counted. -/
def byteCount : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, x => if x < 256 then 1 else byteCount fuel (x / 256) + 1

/-- The `n` low base-256 digits `x₁ … xₙ` of `x`, most significant first (§2.3.1, steps 2
and 3). -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => beBytes n (x / 256) ++ [UInt8.ofNat (x % 256)]

/-- `left_encode(x)` (§2.3.1): the number of base-256 digits of `x` as one byte, then the
digits. The digit count stops at 255, the maximum under the validity condition
`x < 2 ^ 2040`. -/
def leftEncode (x : Nat) : List UInt8 :=
  let n := byteCount 254 x
  UInt8.ofNat n :: beBytes n x

/-- `right_encode(x)` (§2.3.1): the base-256 digits of `x`, then their number as one byte. The
digit count stops at 255, the maximum under the validity condition `x < 2 ^ 2040`. -/
def rightEncode (x : Nat) : List UInt8 :=
  let n := byteCount 254 x
  beBytes n x ++ [UInt8.ofNat n]

/-- `encode_string(S)` (§2.3.2) of a byte string: `left_encode` of its length in bits,
`8 * s.length`, then the string. -/
def encodeString (s : List UInt8) : List UInt8 :=
  leftEncode (8 * s.length) ++ s

/-- `bytepad(X, w)` (§2.3.3): `left_encode(w) ‖ X` followed by the fewest zero bytes that make
the length in bytes a multiple of `w`. -/
def bytepad (x : List UInt8) (w : Nat) : List UInt8 :=
  let z := leftEncode w ++ x
  z ++ List.replicate ((w - z.length % w) % w) 0

/-! ## cSHAKE (SP 800-185 §3) -/

/-- cSHAKE (§3.3) at a rate of `rate` bytes with function name `name` and customization
`custom`: SHAKE (suffix byte `0x1F`) if both are empty, and otherwise the sponge with suffix
byte `0x04` (the bits `00` and the first bit of pad10*1) on
`bytepad(encode_string(name) ‖ encode_string(custom), rate) ‖ x`. -/
def cshake (rate : Nat) (x : List UInt8) (outLen : Nat) (name custom : List UInt8) :
    List UInt8 :=
  if name.length = 0 ∧ custom.length = 0 then sponge rate 0x1F x outLen
  else sponge rate 0x04 (bytepad (encodeString name ++ encodeString custom) rate ++ x) outLen

/-- cSHAKE128 (§3.3): rate 168 bytes, `outLen` output bytes. -/
def cshake128 (x : List UInt8) (outLen : Nat) (name custom : List UInt8) : List UInt8 :=
  cshake 168 x outLen name custom

/-- cSHAKE256 (§3.3): rate 136 bytes, `outLen` output bytes. -/
def cshake256 (x : List UInt8) (outLen : Nat) (name custom : List UInt8) : List UInt8 :=
  cshake 136 x outLen name custom

/-! ## KMAC (SP 800-185 §4) -/

/-- The function name "KMAC" of §4.3 in ASCII. -/
def kmacName : List UInt8 := [0x4B, 0x4D, 0x41, 0x43]

/-- The string `newX` of §4.3, step 1: `bytepad(encode_string(key), rate) ‖ x ‖
right_encode(outBits)`. -/
def kmacInput (rate : Nat) (key x : List UInt8) (outBits : Nat) : List UInt8 :=
  bytepad (encodeString key) rate ++ x ++ rightEncode outBits

/-- KMAC128 (§4.3) with `outLen` output bytes. -/
def kmac128 (key x : List UInt8) (outLen : Nat) (custom : List UInt8) : List UInt8 :=
  cshake128 (kmacInput 168 key x (8 * outLen)) outLen kmacName custom

/-- KMAC256 (§4.3) with `outLen` output bytes. -/
def kmac256 (key x : List UInt8) (outLen : Nat) (custom : List UInt8) : List UInt8 :=
  cshake256 (kmacInput 136 key x (8 * outLen)) outLen kmacName custom

/-- KMACXOF128 (§4.3.1): the first `outLen` bytes, with encoded output length 0. -/
def kmacXof128 (key x : List UInt8) (outLen : Nat) (custom : List UInt8) : List UInt8 :=
  cshake128 (kmacInput 168 key x 0) outLen kmacName custom

/-- KMACXOF256 (§4.3.1): the first `outLen` bytes, with encoded output length 0. -/
def kmacXof256 (key x : List UInt8) (outLen : Nat) (custom : List UInt8) : List UInt8 :=
  cshake256 (kmacInput 136 key x 0) outLen kmacName custom

/-! ## TupleHash (SP 800-185 §5) -/

/-- The function name "TupleHash" of §5.3 in ASCII. -/
def tupleHashName : List UInt8 := [0x54, 0x75, 0x70, 0x6C, 0x65, 0x48, 0x61, 0x73, 0x68]

/-- The string `z` of §5.3, steps 1-3: the concatenated `encode_string` of the components of
a tuple. -/
def encodeStrings : List (List UInt8) → List UInt8
  | [] => []
  | s :: rest => encodeString s ++ encodeStrings rest

/-- The string `newX` of §5.3, step 4: the encoded tuple, then `right_encode(outBits)`. -/
def tupleHashInput (xs : List (List UInt8)) (outBits : Nat) : List UInt8 :=
  encodeStrings xs ++ rightEncode outBits

/-- TupleHash128 (§5.3) with `outLen` output bytes. -/
def tupleHash128 (xs : List (List UInt8)) (outLen : Nat) (custom : List UInt8) : List UInt8 :=
  cshake128 (tupleHashInput xs (8 * outLen)) outLen tupleHashName custom

/-- TupleHash256 (§5.3) with `outLen` output bytes. -/
def tupleHash256 (xs : List (List UInt8)) (outLen : Nat) (custom : List UInt8) : List UInt8 :=
  cshake256 (tupleHashInput xs (8 * outLen)) outLen tupleHashName custom

/-- TupleHashXOF128 (§5.3.1): the first `outLen` bytes, with encoded output length 0. -/
def tupleHashXof128 (xs : List (List UInt8)) (outLen : Nat) (custom : List UInt8) : List UInt8 :=
  cshake128 (tupleHashInput xs 0) outLen tupleHashName custom

/-- TupleHashXOF256 (§5.3.1): the first `outLen` bytes, with encoded output length 0. -/
def tupleHashXof256 (xs : List (List UInt8)) (outLen : Nat) (custom : List UInt8) : List UInt8 :=
  cshake256 (tupleHashInput xs 0) outLen tupleHashName custom

/-! ## ParallelHash (SP 800-185 §6) -/

/-- The function name "ParallelHash" of §6.3 in ASCII. -/
def parallelHashName : List UInt8 :=
  [0x50, 0x61, 0x72, 0x61, 0x6C, 0x6C, 0x65, 0x6C, 0x48, 0x61, 0x73, 0x68]

/-- The loop of §6.3, step 3: the concatenated cSHAKE values of `cvLen` bytes, with empty
name and customization, of the blocks. -/
def chainingValues (rate cvLen : Nat) : List (List UInt8) → List UInt8
  | [] => []
  | b :: rest => cshake rate b cvLen [] [] ++ chainingValues rate cvLen rest

/-- The string `newX` of §6.3, steps 1-5: with `n = ⌈x.length / blockLen⌉`, the string
`left_encode(blockLen)`, the chaining values of the `n` blocks of `x` (the last may be
shorter), `right_encode(n)` and `right_encode(outBits)`. -/
def parallelHashInput (rate cvLen : Nat) (x : List UInt8) (blockLen outBits : Nat) :
    List UInt8 :=
  let n := (x.length + blockLen - 1) / blockLen
  leftEncode blockLen ++ chainingValues rate cvLen (blocks blockLen n x) ++ rightEncode n ++
    rightEncode outBits

/-- ParallelHash128 (§6.3) with blocks of `blockLen` bytes, chaining values of 32 bytes and
`outLen` output bytes. -/
def parallelHash128 (x : List UInt8) (blockLen outLen : Nat) (custom : List UInt8) :
    List UInt8 :=
  cshake128 (parallelHashInput 168 32 x blockLen (8 * outLen)) outLen parallelHashName custom

/-- ParallelHash256 (§6.3) with blocks of `blockLen` bytes, chaining values of 64 bytes and
`outLen` output bytes. -/
def parallelHash256 (x : List UInt8) (blockLen outLen : Nat) (custom : List UInt8) :
    List UInt8 :=
  cshake256 (parallelHashInput 136 64 x blockLen (8 * outLen)) outLen parallelHashName custom

/-- ParallelHashXOF128 (§6.3.1): the first `outLen` bytes, with encoded output length 0. -/
def parallelHashXof128 (x : List UInt8) (blockLen outLen : Nat) (custom : List UInt8) :
    List UInt8 :=
  cshake128 (parallelHashInput 168 32 x blockLen 0) outLen parallelHashName custom

/-- ParallelHashXOF256 (§6.3.1): the first `outLen` bytes, with encoded output length 0. -/
def parallelHashXof256 (x : List UInt8) (blockLen outLen : Nat) (custom : List UInt8) :
    List UInt8 :=
  cshake256 (parallelHashInput 136 64 x blockLen 0) outLen parallelHashName custom

/-! ## Properties of the encodings -/

private theorem byteCount_le (fuel x : Nat) : byteCount fuel x ≤ fuel + 1 := by
  induction fuel generalizing x <;> grind [byteCount]

private theorem beBytes_length (n x : Nat) : (beBytes n x).length = n := by
  induction n generalizing x <;> grind [beBytes]

/-- `encode_string` (§2.3.2) is injective on all byte strings, in particular on those of fewer
than `2 ^ 2040` bits, which are its valid inputs. -/
theorem encodeString_injective : Function.Injective encodeString := by
  intro s t h
  simp only [encodeString, leftEncode, List.cons_append, List.cons.injEq] at h
  obtain ⟨hn, hb⟩ := h
  have hs := byteCount_le 254 (8 * s.length)
  have ht := byteCount_le 254 (8 * t.length)
  have hc : byteCount 254 (8 * s.length) = byteCount 254 (8 * t.length) := by
    grind
  exact (List.append_inj hb (by simp [beBytes_length, hc])).2

/-- The length of `bytepad x w` (§2.3.3) is a multiple of `w`. -/
theorem bytepad_length_dvd (x : List UInt8) (w : Nat) (hw : 0 < w) :
    w ∣ (bytepad x w).length := by
  simp only [bytepad, List.length_append, List.length_replicate]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod_mod, ← Nat.mod_add_mod,
    Nat.add_sub_cancel' (Nat.le_of_lt (Nat.mod_lt _ hw)), Nat.mod_self]

/-! ## cSHAKE with empty name and customization -/

/-- cSHAKE128 with empty name and customization is SHAKE128 (§3.3, step 1). -/
theorem cshake128_nil (x : List UInt8) (outLen : Nat) :
    cshake128 x outLen [] [] = shake128 x outLen := by
  simp [cshake128, cshake, shake128]

/-- cSHAKE256 with empty name and customization is SHAKE256 (§3.3, step 1). -/
theorem cshake256_nil (x : List UInt8) (outLen : Nat) :
    cshake256 x outLen [] [] = shake256 x outLen := by
  simp [cshake256, cshake, shake256]

/-! ## Output lengths -/

private theorem squeezeBlocks_length (rate : Nat) (hr : rate ≤ 200) (n : Nat)
    (s : Keccak.KState) : (squeezeBlocks rate s n).length = n * rate := by
  induction n generalizing s <;> grind [squeezeBlocks, stateToBytes_length]

private theorem sponge_length (rate : Nat) (suffix : UInt8) (msg : List UInt8) (outLen : Nat)
    (h0 : 0 < rate) (hr : rate ≤ 200) : (sponge rate suffix msg outLen).length = outLen := by
  have h := Nat.lt_mul_div_succ (outLen - 1) h0
  grind [sponge, squeezeBlocks_length, stateToBytes_length]

/-- cSHAKE128 (§3.3) returns `outLen` bytes. -/
theorem cshake128_length (x : List UInt8) (outLen : Nat) (name custom : List UInt8) :
    (cshake128 x outLen name custom).length = outLen := by
  grind [cshake128, cshake, sponge_length]

/-- cSHAKE256 (§3.3) returns `outLen` bytes. -/
theorem cshake256_length (x : List UInt8) (outLen : Nat) (name custom : List UInt8) :
    (cshake256 x outLen name custom).length = outLen := by
  grind [cshake256, cshake, sponge_length]

/-- KMAC128 (§4.3) returns `outLen` bytes. -/
theorem kmac128_length (key x : List UInt8) (outLen : Nat) (custom : List UInt8) :
    (kmac128 key x outLen custom).length = outLen :=
  cshake128_length _ _ _ _

/-- KMAC256 (§4.3) returns `outLen` bytes. -/
theorem kmac256_length (key x : List UInt8) (outLen : Nat) (custom : List UInt8) :
    (kmac256 key x outLen custom).length = outLen :=
  cshake256_length _ _ _ _

/-- KMACXOF128 (§4.3.1) returns `outLen` bytes. -/
theorem kmacXof128_length (key x : List UInt8) (outLen : Nat) (custom : List UInt8) :
    (kmacXof128 key x outLen custom).length = outLen :=
  cshake128_length _ _ _ _

/-- KMACXOF256 (§4.3.1) returns `outLen` bytes. -/
theorem kmacXof256_length (key x : List UInt8) (outLen : Nat) (custom : List UInt8) :
    (kmacXof256 key x outLen custom).length = outLen :=
  cshake256_length _ _ _ _

/-- TupleHash128 (§5.3) returns `outLen` bytes. -/
theorem tupleHash128_length (xs : List (List UInt8)) (outLen : Nat) (custom : List UInt8) :
    (tupleHash128 xs outLen custom).length = outLen :=
  cshake128_length _ _ _ _

/-- TupleHash256 (§5.3) returns `outLen` bytes. -/
theorem tupleHash256_length (xs : List (List UInt8)) (outLen : Nat) (custom : List UInt8) :
    (tupleHash256 xs outLen custom).length = outLen :=
  cshake256_length _ _ _ _

/-- TupleHashXOF128 (§5.3.1) returns `outLen` bytes. -/
theorem tupleHashXof128_length (xs : List (List UInt8)) (outLen : Nat) (custom : List UInt8) :
    (tupleHashXof128 xs outLen custom).length = outLen :=
  cshake128_length _ _ _ _

/-- TupleHashXOF256 (§5.3.1) returns `outLen` bytes. -/
theorem tupleHashXof256_length (xs : List (List UInt8)) (outLen : Nat) (custom : List UInt8) :
    (tupleHashXof256 xs outLen custom).length = outLen :=
  cshake256_length _ _ _ _

/-- ParallelHash128 (§6.3) returns `outLen` bytes. -/
theorem parallelHash128_length (x : List UInt8) (blockLen outLen : Nat) (custom : List UInt8) :
    (parallelHash128 x blockLen outLen custom).length = outLen :=
  cshake128_length _ _ _ _

/-- ParallelHash256 (§6.3) returns `outLen` bytes. -/
theorem parallelHash256_length (x : List UInt8) (blockLen outLen : Nat) (custom : List UInt8) :
    (parallelHash256 x blockLen outLen custom).length = outLen :=
  cshake256_length _ _ _ _

/-- ParallelHashXOF128 (§6.3.1) returns `outLen` bytes. -/
theorem parallelHashXof128_length (x : List UInt8) (blockLen outLen : Nat)
    (custom : List UInt8) : (parallelHashXof128 x blockLen outLen custom).length = outLen :=
  cshake128_length _ _ _ _

/-- ParallelHashXOF256 (§6.3.1) returns `outLen` bytes. -/
theorem parallelHashXof256_length (x : List UInt8) (blockLen outLen : Nat)
    (custom : List UInt8) : (parallelHashXof256 x blockLen outLen custom).length = outLen :=
  cshake256_length _ _ _ _

/-!
## Known-answer checks

The inputs and outputs are those of the sample documents that NIST publishes for SP 800-185,
under the directory
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/
in the file named at each check. A customization string printed there as "(null)" is the
empty string: its printed encoding is `01 00`.
-/

/-! `cSHAKE_samples.pdf`, Sample #1 (cSHAKE128, customization "Email Signature"). -/
set_option kat.ms 1000 in
#kat cshake128 [0x00, 0x01, 0x02, 0x03] 32 []
    [0x45, 0x6d, 0x61, 0x69, 0x6c, 0x20, 0x53, 0x69, 0x67, 0x6e, 0x61, 0x74, 0x75, 0x72, 0x65] ==
  [0xc1, 0xc3, 0x69, 0x25, 0xb6, 0x40, 0x9a, 0x04, 0xf1, 0xb5, 0x04, 0xfc, 0xbc, 0xa9, 0xd8, 0x2b,
   0x40, 0x17, 0x27, 0x7c, 0xb5, 0xed, 0x2b, 0x20, 0x65, 0xfc, 0x1d, 0x38, 0x14, 0xd5, 0xaa, 0xf5]

/-! `cSHAKE_samples.pdf`, Sample #3 (cSHAKE256, customization "Email Signature"). -/
set_option kat.ms 1000 in
#kat cshake256 [0x00, 0x01, 0x02, 0x03] 64 []
    [0x45, 0x6d, 0x61, 0x69, 0x6c, 0x20, 0x53, 0x69, 0x67, 0x6e, 0x61, 0x74, 0x75, 0x72, 0x65] ==
  [0xd0, 0x08, 0x82, 0x8e, 0x2b, 0x80, 0xac, 0x9d, 0x22, 0x18, 0xff, 0xee, 0x1d, 0x07, 0x0c, 0x48,
   0xb8, 0xe4, 0xc8, 0x7b, 0xff, 0x32, 0xc9, 0x69, 0x9d, 0x5b, 0x68, 0x96, 0xee, 0xe0, 0xed, 0xd1,
   0x64, 0x02, 0x0e, 0x2b, 0xe0, 0x56, 0x08, 0x58, 0xd9, 0xc0, 0x0c, 0x03, 0x7e, 0x34, 0xa9, 0x69,
   0x37, 0xc5, 0x61, 0xa7, 0x4c, 0x41, 0x2b, 0xb4, 0xc7, 0x46, 0x46, 0x95, 0x27, 0x28, 0x1c, 0x8c]

/-! `KMAC_samples.pdf`, Sample #1 (KMAC128, empty customization). -/
set_option kat.ms 1000 in
#kat kmac128
    [0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
     0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f]
    [0x00, 0x01, 0x02, 0x03] 32 [] ==
  [0xe5, 0x78, 0x0b, 0x0d, 0x3e, 0xa6, 0xf7, 0xd3, 0xa4, 0x29, 0xc5, 0x70, 0x6a, 0xa4, 0x3a, 0x00,
   0xfa, 0xdb, 0xd7, 0xd4, 0x96, 0x28, 0x83, 0x9e, 0x31, 0x87, 0x24, 0x3f, 0x45, 0x6e, 0xe1, 0x4e]

/-! `KMACXOF_samples.pdf`, Sample #4 (KMACXOF256, customization "My Tagged Application"). -/
set_option kat.ms 1000 in
#kat kmacXof256
    [0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
     0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f]
    [0x00, 0x01, 0x02, 0x03] 64
    [0x4d, 0x79, 0x20, 0x54, 0x61, 0x67, 0x67, 0x65, 0x64, 0x20, 0x41, 0x70, 0x70, 0x6c, 0x69, 0x63,
     0x61, 0x74, 0x69, 0x6f, 0x6e] ==
  [0x17, 0x55, 0x13, 0x3f, 0x15, 0x34, 0x75, 0x2a, 0xad, 0x07, 0x48, 0xf2, 0xc7, 0x06, 0xfb, 0x5c,
   0x78, 0x45, 0x12, 0xca, 0xb8, 0x35, 0xcd, 0x15, 0x67, 0x6b, 0x16, 0xc0, 0xc6, 0x64, 0x7f, 0xa9,
   0x6f, 0xaa, 0x7a, 0xf6, 0x34, 0xa0, 0xbf, 0x8f, 0xf6, 0xdf, 0x39, 0x37, 0x4f, 0xa0, 0x0f, 0xad,
   0x9a, 0x39, 0xe3, 0x22, 0xa7, 0xc9, 0x20, 0x65, 0xa6, 0x4e, 0xb1, 0xfb, 0x08, 0x01, 0xeb, 0x2b]

/-! `TupleHash_samples.pdf`, Sample #1 (TupleHash128, empty customization). -/
set_option kat.ms 1000 in
#kat tupleHash128 [[0x00, 0x01, 0x02], [0x10, 0x11, 0x12, 0x13, 0x14, 0x15]] 32 [] ==
  [0xc5, 0xd8, 0x78, 0x6c, 0x1a, 0xfb, 0x9b, 0x82, 0x11, 0x1a, 0xb3, 0x4b, 0x65, 0xb2, 0xc0, 0x04,
   0x8f, 0xa6, 0x4e, 0x6d, 0x48, 0xe2, 0x63, 0x26, 0x4c, 0xe1, 0x70, 0x7d, 0x3f, 0xfc, 0x8e, 0xd1]

/-! `TupleHashXOF_samples.pdf`, Sample #5 (TupleHashXOF256, customization "My Tuple App"). -/
set_option kat.ms 1000 in
#kat tupleHashXof256 [[0x00, 0x01, 0x02], [0x10, 0x11, 0x12, 0x13, 0x14, 0x15]] 64
    [0x4d, 0x79, 0x20, 0x54, 0x75, 0x70, 0x6c, 0x65, 0x20, 0x41, 0x70, 0x70] ==
  [0x64, 0x83, 0xcb, 0x3c, 0x99, 0x52, 0xeb, 0x20, 0xe8, 0x30, 0xaf, 0x47, 0x85, 0x85, 0x1f, 0xc5,
   0x97, 0xee, 0x3b, 0xf9, 0x3b, 0xb7, 0x60, 0x2c, 0x0e, 0xf6, 0xa6, 0x5d, 0x74, 0x1a, 0xec, 0xa7,
   0xe6, 0x3c, 0x3b, 0x12, 0x89, 0x81, 0xaa, 0x05, 0xc6, 0xd2, 0x74, 0x38, 0xc7, 0x9d, 0x27, 0x54,
   0xbb, 0x1b, 0x71, 0x91, 0xf1, 0x25, 0xd6, 0x62, 0x0f, 0xca, 0x12, 0xce, 0x65, 0x8b, 0x24, 0x42]

/-! `ParallelHash_samples.pdf`, 128-bit Sample #1 (ParallelHash128, empty customization). -/
set_option kat.ms 1000 in
#kat parallelHash128
    [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
     0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27] 8 32 [] ==
  [0xba, 0x8d, 0xc1, 0xd1, 0xd9, 0x79, 0x33, 0x1d, 0x3f, 0x81, 0x36, 0x03, 0xc6, 0x7f, 0x72, 0x60,
   0x9a, 0xb5, 0xe4, 0x4b, 0x94, 0xa0, 0xb8, 0xf9, 0xaf, 0x46, 0x51, 0x44, 0x54, 0xa2, 0xb4, 0xf5]

/-! `ParallelHashXOF_samples.pdf`, 256-bit Sample #2 (ParallelHashXOF256, customization
"Parallel Data"). -/
set_option kat.ms 1000 in
#kat parallelHashXof256
    [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
     0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27] 8 64
    [0x50, 0x61, 0x72, 0x61, 0x6c, 0x6c, 0x65, 0x6c, 0x20, 0x44, 0x61, 0x74, 0x61] ==
  [0x53, 0x8e, 0x10, 0x5f, 0x1a, 0x22, 0xf4, 0x4e, 0xd2, 0xf5, 0xcc, 0x16, 0x74, 0xfb, 0xd4, 0x0b,
   0xe8, 0x03, 0xd9, 0xc9, 0x9b, 0xf5, 0xf8, 0xd9, 0x0a, 0x2c, 0x81, 0x93, 0xf3, 0xfe, 0x6e, 0xa7,
   0x68, 0xe5, 0xc1, 0xa2, 0x09, 0x87, 0xe2, 0xc9, 0xc6, 0x5f, 0xeb, 0xed, 0x03, 0x88, 0x7a, 0x51,
   0xd3, 0x56, 0x24, 0xed, 0x12, 0x37, 0x75, 0x94, 0xb5, 0x58, 0x55, 0x41, 0xdc, 0x37, 0x7e, 0xfc]

end CatCrypt.Crypto.Primitives.SP800185
