/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-!
# Decode-verification for the rel32 control-flow forms (`jmp`/`call`/`jcc`)

`SailX86Decoder.lean` gives `decode (encode i) = some i` round-trips for the
register-direct GP forms (`encAluRR`/`encMovImm`/…): for those the encoder's
bytes are *proved* to decode back to the same operands, so `gas` is out of the
trusted path. The rel32 **control-flow** forms `LprogBytes` emits
(`encJmp32`/`encCall32`/`encJcc32`) had no such round-trip — they were
"gas-pinned by byte-diff" (trusted, like the differential anchor #438), the only
remaining residual in the byte path's trust edge.

This module closes that residual. It transcribes the same x86 decode discipline
to the control-flow opcode bytes:

* `0xE9 cd` (`jmp rel32`, 5 bytes), `0xE8 cd` (`call rel32`, 5 bytes),
* `0x0F 0x8x cd` (`jcc rel32`, 6 bytes), the `0F`-map condition tower
  (`0x80..0x8F`).

`decDisp32` inverts `ScalarEncoder.disp32LE` (the two's-complement little-endian
4-byte signed displacement): it reads the 4 bytes back into a `BitVec 32` and
takes `.toInt`. `disp32LE_roundtrip` proves the recovered displacement equals the
original for every in-range signed 32-bit `d` (`-2^31 ≤ d < 2^31`).

`decodeCF` dispatches on the first byte and reads the displacement via
`decDisp32`; `roundtrip_jmp32`/`roundtrip_call32`/`roundtrip_jcc32` are the
residual-closers: `decodeCF (encode i) = some i`.

## `jcc` opcode-vs-name honesty note

`LprogBytes.jccOpcode` is **many-to-one** — the condition synonyms collapse on
the same `0F 8x` byte (`Z` and `E` both `0x84`, `NZ` and `NE` both `0x85`,
`C`/`B` both `0x82`, `NC`/`AE` both `0x83`). The byte stream therefore carries
the *opcode*, not the source-level condition *name*: `decodeCF` cannot recover
which synonym was written, only the opcode. So `roundtrip_jcc32` is honestly
stated up to `jccOpcode cc` (the opcode the encoder emitted), which is the
faithful invertible target — the bytes decode to the same opcode, hence the same
condition the CPU tests.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86CFDecoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-! ## 1. The signed rel32 displacement decoder (inverse of `disp32LE`)

`ScalarEncoder.disp32LE o = imm32LE (BitVec.ofInt 32 o).toNat` is the 4 little-
endian bytes of the two's-complement 32-bit image of `o`. To invert: read the 4
bytes back into a `BitVec 32` (little-endian recomposition) and take `.toInt`
(the signed interpretation). -/

/-- Read 4 little-endian bytes back to the signed `Int` displacement — the
    inverse of `ScalarEncoder.disp32LE`. The 4 bytes form a `BitVec 32` (LE),
    whose `.toInt` is the two's-complement signed value. -/
def decDisp32 : List (BitVec 8) → Option Int
  | [b0, b1, b2, b3] =>
      let n : Nat := b0.toNat + b1.toNat * 0x100 + b2.toNat * 0x10000
                     + b3.toNat * 0x1000000
      some (BitVec.ofNat 32 n).toInt
  | _ => none

/-- The little-endian recomposition the `decDisp32` reader applies recovers the
    `BitVec 32`'s `.toNat` exactly: for `n = w.toNat` with `w : BitVec 32`, the
    four bytes `(n >>> 8i) &&& 0xff` recompose to `n`. (A `BitVec 32` analogue of
    `SailX86Decoder.imm32LE_recompose`, specialised to a `BitVec 32` source.) -/
theorem disp_recompose (n : Nat) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 8 (n &&& 0xff)).toNat
      + (BitVec.ofNat 8 ((n >>> 8) &&& 0xff)).toNat * 0x100
      + (BitVec.ofNat 8 ((n >>> 16) &&& 0xff)).toNat * 0x10000
      + (BitVec.ofNat 8 ((n >>> 24) &&& 0xff)).toNat * 0x1000000 = n := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- **The displacement round-trip.** For any in-range signed 32-bit displacement
    `d` (`-2^31 ≤ d < 2^31`), reading back the 4 LE bytes `disp32LE d` recovers
    `d` exactly. The bytes recompose to `(BitVec.ofInt 32 d).toNat`
    (`disp_recompose`), so `decDisp32` returns `(BitVec.ofInt 32 d).toInt`, which
    equals `d` in range (`BitVec.toInt_ofInt` / `BitVec.toInt_intCast`-style). -/
theorem disp32LE_roundtrip (d : Int) (hd : -2 ^ 31 ≤ d ∧ d < 2 ^ 31) :
    decDisp32 (disp32LE d) = some d := by
  obtain ⟨hlo, hhi⟩ := hd
  have hrec := disp_recompose (BitVec.ofInt 32 d).toNat (BitVec.isLt _)
  simp only [disp32LE, imm32LE, decDisp32, List.map_cons, List.map_nil]
  rw [hrec, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.toInt_ofInt]
  -- `(BitVec.ofInt 32 d).toInt = d.bmod 2^32 = d` for `d` in the signed 32-bit range.
  refine congrArg some ?_
  clear hrec
  norm_num [Int.bmod]
  omega

/-! ## 2. The decoded control-flow result + the dispatching decoder

`DecCF` is the result of a control-flow decode: `jmp d`, `call d`, or
`jcc opcode d`. The `jcc` arm carries the **opcode** byte (`0x80..0x8F`), not the
source condition name — `jccOpcode` is many-to-one, so the byte stream only
determines the opcode (see the module docstring's honesty note). -/

/-- A decoded rel32 control-flow instruction: the recovered signed displacement
    plus, for `jcc`, the `0F 8x` condition opcode byte. -/
inductive DecCF where
  | jmp (d : Int) : DecCF
  | call (d : Int) : DecCF
  | jcc (opcode : Nat) (d : Int) : DecCF
deriving DecidableEq, Repr

/-- Decode a rel32 control-flow byte stream, dispatching on the first byte:
    * `0xE9 cd` (5 bytes) → `jmp`,
    * `0xE8 cd` (5 bytes) → `call`,
    * `0x0F 0x8x cd` (6 bytes, `0x80 ≤ op ≤ 0x8F`) → `jcc op`,
    reading the 4-byte displacement via `decDisp32`. Any other shape ⇒ `none`. -/
def decodeCF : List (BitVec 8) → Option DecCF
  | op :: rest =>
      if op.toNat = 0xe9 then
        (decDisp32 rest).map DecCF.jmp
      else if op.toNat = 0xe8 then
        (decDisp32 rest).map DecCF.call
      else if op.toNat = 0x0f then
        match rest with
        | op2 :: disp =>
            if 0x80 ≤ op2.toNat ∧ op2.toNat ≤ 0x8f then
              (decDisp32 disp).map (DecCF.jcc op2.toNat)
            else none
        | [] => none
      else none
  | [] => none

/-! ## 3. The control-flow round-trips (the residual-closers)

`decodeCF (encode i) = some i` for the three rel32 control-flow forms. Each reduces
to a first-byte dispatch (`0xE9`/`0xE8`/`0x0F` are distinct so the `if`-tower picks
the right arm — `decide` on the byte equalities) followed by `disp32LE_roundtrip` on
the displacement tail. -/

/-- **Round-trip for `jmp rel32`** (`encJmp32`): decoding the `0xE9 cd` bytes
    recovers `jmp d` for any in-range signed 32-bit displacement. -/
theorem roundtrip_jmp32 (d : Int) (hd : -2 ^ 31 ≤ d ∧ d < 2 ^ 31) :
    decodeCF (encJmp32 d) = some (.jmp d) := by
  simp only [encJmp32, decodeCF, BitVec.toNat_ofNat, show (0xe9 : Nat) % 2 ^ 8 = 0xe9 from rfl,
    if_pos, disp32LE_roundtrip d hd, Option.map_some]

/-- **Round-trip for `call rel32`** (`encCall32`): decoding the `0xE8 cd` bytes
    recovers `call d`. The `0xE8 ≠ 0xE9` first-byte test routes to the `call` arm. -/
theorem roundtrip_call32 (d : Int) (hd : -2 ^ 31 ≤ d ∧ d < 2 ^ 31) :
    decodeCF (encCall32 d) = some (.call d) := by
  simp only [encCall32, decodeCF, BitVec.toNat_ofNat, show (0xe8 : Nat) % 2 ^ 8 = 0xe8 from rfl,
    if_true, if_neg (by decide : ¬(232 = 233)), disp32LE_roundtrip d hd, Option.map_some]

/-- **Round-trip for `jcc rel32`** (`encJcc32`): decoding the `0F 8x cd` bytes
    recovers `jcc (jccOpcode cc) d` — the **opcode** byte, not the condition name
    (`jccOpcode` is many-to-one; the byte stream determines only the opcode the CPU
    tests). `hcc` ranges `cc` over the known condition names, ensuring the emitted
    opcode lands in the `0x80..0x8F` `jcc` tower the decoder accepts. -/
theorem roundtrip_jcc32 (cc : String) (d : Int)
    (hcc : cc ∈ ["O","NO","B","C","AE","NC","E","Z","NE","NZ","BE","A","S","NS","L","GE","LE","G"])
    (hd : -2 ^ 31 ≤ d ∧ d < 2 ^ 31) :
    decodeCF (encJcc32 cc d) = some (.jcc (jccOpcode cc) d) := by
  -- the first byte `0x0F` is neither `0xE9` nor `0xE8`, so the `0F`-map arm fires;
  -- the second byte `jccOpcode cc` is in `0x80..0x8F` for every known `cc`.
  have hop : 0x80 ≤ jccOpcode cc % 2 ^ 8 ∧ jccOpcode cc % 2 ^ 8 ≤ 0x8f := by
    fin_cases hcc <;> simp only [jccOpcode] <;> decide
  have hopeq : jccOpcode cc % 2 ^ 8 = jccOpcode cc := by
    fin_cases hcc <;> simp only [jccOpcode] <;> decide
  rw [hopeq] at hop
  simp only [encJcc32, decodeCF, BitVec.toNat_ofNat, show (0x0f : Nat) % 2 ^ 8 = 0x0f from rfl,
    if_true, if_neg (by decide : ¬(15 = 233)), if_neg (by decide : ¬(15 = 232)),
    hopeq, if_pos hop, disp32LE_roundtrip d hd, Option.map_some]

/-! ## 4. Concrete examples (forward jump, loop back-edge, conditional back-edge) -/

/-- A forward `jmp +16`. -/
example : decodeCF (encJmp32 16) = some (.jmp 16) := by native_decide

/-- A backward `jmp -4` — the loop back-edge case (negative two's-complement
    displacement recovered exactly). -/
example : decodeCF (encJmp32 (-4)) = some (.jmp (-4)) := by native_decide

/-- A conditional back-edge `jne -9` (`0F 85 cd`): decodes to opcode `0x85`
    (`JNE`/`JNZ`) and displacement `-9`. -/
example : decodeCF (encJcc32 "NE" (-9)) = some (.jcc 0x85 (-9)) := by native_decide

/-- A `call +32`. -/
example : decodeCF (encCall32 32) = some (.call 32) := by native_decide
