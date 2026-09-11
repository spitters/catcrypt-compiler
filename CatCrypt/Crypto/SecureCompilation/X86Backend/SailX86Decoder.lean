/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-!
# Sail-x86 decoder round-trip: `decode (encode i) ≡ i` (#444, upgrades #438)

`ScalarEncoder.lean` (#438) is the owned `JInstr → machine-byte` encoder. Its
trust edge was *differential*: each output byte string is pinned (`gas`) to what
the GNU assembler produces for the same mnemonic (`ScalarValidation.lean`). That
makes `gas`'s unverified encoder part of the trusted base.

This module replaces the differential edge for the decodable subset with a
**round-trip** against the x86 ModRM/REX field-split discipline: a Lean decoder
`decodeReg` that recovers `(opcode, reg-field, rm-field, displacement)` from a
fixed-shape machine-byte stream, and a proof that

```
decodeReg (encAluRR op d s) = some ⟨op, s, d, …⟩      -- the encoded fields
```

for every opcode and register pair. `decodeReg` is a **field-level parser**: it
assumes the byte list already has the shape one of the encoder's `enc*`
functions produces (`[REX, op, ModRM]`, `[REX, 0x0F, op, ModRM]`, …) and pulls
the REX/ModRM sub-fields out of it per the SDM's bit layout. It does **not**
implement the opcode-dispatch logic that *decides*, from the opcode byte alone,
whether a ModRM byte follows at all — that per-opcode presence table is not
transcribed anywhere in this repo (see below), and `decodeReg` accepts any
`op : Nat < 256` in the ModRM slot, including opcodes that in the real ISA take
no ModRM at all (e.g. `decodeReg [0x40, 0xE9, 0xC3]` succeeds even though
`0xE9` is `JMP rel32`, which has no ModRM byte). The round-trip therefore
certifies **field placement** — the bytes the encoder wrote land back in the
same `reg`/`rm`/`imm` positions for the fixed shapes the encoders in fact
emit — not opcode legality; see "What the Sail-x86 decoder is (scope)"
below.

## What the Sail-x86 decoder is

The upstream Sail model's `prefix_modrm_sib_decoding.sail` (in
[`rems-project/sail-x86-from-acl2`](https://github.com/rems-project/sail-x86-from-acl2),
**not vendored in this repo** — cited here as the provenance for the SDM field
layout below, not as a file we import, run, or transcribe wholesale) is a
byte-stream **structure parser**: given the opcode byte it decides whether a
ModRM byte follows (`one_byte_opcode_modr_m_p` / `two_byte_opcode_modr_m_p`,
256-entry boolean vectors), whether a SIB byte follows (`x86_decode_sib_p`:
`mod ≠ 0b11 ∧ r/m = 0b100`), and the prefix interpretation; the ModRM byte
itself splits into `mod[7:6] / reg[5:3] / r/m[2:0]`. **We do not transcribe the
opcode-presence tables** — `decodeReg`/`decode0F`/`decodeImm`/`decodeShift`
below take "does a ModRM byte follow" as given by the fixed shape of the byte
list they pattern-match on, which is correct only because we control both
encoder and decoder and know, by construction, which shape each `enc*`
function emits; a `decodeReg` call is never checked against a presence table
the way the Sail model's dispatcher would check it. What we *do* transcribe by
hand from the cited upstream (its SDM-derived field layout, not its Sail
source text) is the ModRM `mod/reg/rm` bit split and the REX-prefix layout
(`REX = 0x40 | W<<3 | R<<2 | X<<1 | B`, Intel SDM Vol. 2 §2.2.1) —
`rexR`/`rexB`/`rexX` are read by the decoders below; `rexW` is defined for
completeness but is **not** read by any decoder, so REX.W (operand-size = 64)
is neither pinned nor checked by any round-trip proof here. The semantic side
(the executed effect of each decoded opcode) is the `SailX86Lean.lean`
spec-equality (`evalInstr = sailAdd …`); that module's own docstring records
that its Sail citations are likewise external provenance pointers, not files
vendored or run from this repo.

## Scope of the round-trip (which `JInstr` forms are now decode-proved)

`decode (encode i) ≡ i` is proved (`roundtrip_*` below) for the **register-direct
GP forms** the encoder emits:

* legacy one-byte ALU/MOV reg-reg: `ADD ADC SUB SBB AND OR XOR MOV` (`encAluRR`),
* the `0F`-map reg-reg forms `IMUL`/`CMOVcc` (`enc0FRR`),
* `MOV $imm32` (`encMovImm`) and `IMUL $imm32` (`encImulImm`),
* the immediate-source ALU group `ADD/OR/ADC/SBB/AND/SUB/XOR $imm32`
  (`81 /digit id`, `encAluImm`),
* shift-by-`imm8` `SHL`/`SHR`/`SAR` (`encShiftImm`),
* unary `NEG` (`encUnaryF7`).

The `MULX`/`ADCX`/`ADOX` (VEX/legacy-VEX) and the `loadMem`/`storeMem`/`mulxMem`
memory forms decode their **structure** (`decodeMem` recovers the ModRM `mod`,
the base, and the displacement; `roundtrip_mem_*`) but those mnemonics have **no
Sail-x86 counterpart** (ACL2 `x86isa` lacks ADX/BMI2 — see `SailX86Validation`),
so they keep their `gas` differential pin. The honest tally is in the module-
final §7 doc comment below (`trust_edge_pilot` anchors one instance of it as a
real theorem).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-! ## 1. REX / ModRM field extraction (Sail-x86 decode discipline)

These transcribe the field splits the Sail decoder applies: the REX prefix
(`prefixes` bitfield + the SDM `0x40 | W<<3 | R<<2 | X<<1 | B` layout) and the
ModRM byte (`modr_m` bitfield: `mod[7:6] / reg[5:3] / r/m[2:0]`, the accessors
`modr_m[mod]`, `modr_m[reg]`, `modr_m[r_m]` used in `x86_decode_sib_p`). -/

/-- Is `b` a REX prefix byte (`0x40..0x4F`)? (`prefixes` legacy-prefix detection,
    Sail `get_one_byte_prefix_array_code` group; REX is the `0x4_` block.) -/
def isRex (b : BitVec 8) : Bool := 0x40 ≤ b.toNat ∧ b.toNat ≤ 0x4f

/-- REX.W bit (operand-size = 64). -/
def rexW (b : BitVec 8) : Nat := (b.toNat >>> 3) &&& 1
/-- REX.R bit (extends ModRM.reg). -/
def rexR (b : BitVec 8) : Nat := (b.toNat >>> 2) &&& 1
/-- REX.X bit (extends SIB.index). -/
def rexX (b : BitVec 8) : Nat := (b.toNat >>> 1) &&& 1
/-- REX.B bit (extends ModRM.rm / SIB.base). -/
def rexB (b : BitVec 8) : Nat := b.toNat &&& 1

/-- ModRM `mod` field (`modr_m[mod]`, bits 7:6). -/
def modField (b : BitVec 8) : Nat := (b.toNat >>> 6) &&& 3
/-- ModRM `reg` field (`modr_m[reg]`, bits 5:3). -/
def regField (b : BitVec 8) : Nat := (b.toNat >>> 3) &&& 7
/-- ModRM `r/m` field (`modr_m[r_m]`, bits 2:0). -/
def rmField (b : BitVec 8) : Nat := b.toNat &&& 7

/-- Sail `x86_decode_sib_p modr_m false` (64-bit mode): a SIB byte follows iff
    `r/m = 0b100 ∧ mod ≠ 0b11`. -/
def sibFollows (modrm : BitVec 8) : Bool :=
  rmField modrm = 4 ∧ modField modrm ≠ 3

/-! ## 2. The decoded register-form record

The fields a register-direct decode recovers: the full 8-bit opcode (one-byte
or, for the `0F`-map forms, the second opcode byte), and the two GP register
numbers `0..15` reconstructed from `REX.{R,B}` ++ ModRM.`{reg,rm}`. For an
opcode-extension form (`/digit` in ModRM.reg, as for shifts/`NEG`) the `reg`
number coincides with the extension digit; the caller interprets it. -/

/-- A decoded register-direct instruction: the opcode byte and the recovered
    `reg`/`rm` register numbers (each `REX.{R,B}<<3 | ModRM.{reg,rm}`), plus an
    optional immediate / shift-count. -/
structure DecReg where
  opcode : Nat
  reg : Nat
  rm : Nat
  imm : Option Nat := none
deriving DecidableEq, Repr

/-! ## 3. The decoder

`decodeReg` parses a legacy one-byte-opcode register-direct ALU/MOV stream
`[REX, opcode, ModRM]`: it reconstructs `reg = REX.R<<3 | ModRM.reg` and
`rm = REX.B<<3 | ModRM.rm` per the SDM. `decode0F` parses the `0F`-map form
`[REX, 0x0F, opcode, ModRM]`. `decodeImm`/`decodeShift` parse the immediate /
shift-count tail. Each requires `mod = 0b11` (register-direct, no SIB / disp). -/

/-- Decode a legacy reg-reg form `[REX, op, ModRM(mod=11)]`. -/
def decodeReg : List (BitVec 8) → Option DecReg
  | [r, op, modrm] =>
      if isRex r ∧ modField modrm = 3 then
        some { opcode := op.toNat
             , reg := rexR r * 8 + regField modrm
             , rm := rexB r * 8 + rmField modrm }
      else none
  | _ => none

/-- Decode a `0F`-map reg-reg form `[REX, 0x0F, op, ModRM(mod=11)]`. -/
def decode0F : List (BitVec 8) → Option DecReg
  | [r, esc, op, modrm] =>
      if isRex r ∧ esc.toNat = 0x0f ∧ modField modrm = 3 then
        some { opcode := op.toNat
             , reg := rexR r * 8 + regField modrm
             , rm := rexB r * 8 + rmField modrm }
      else none
  | _ => none

/-- Decode a `[REX, op, ModRM(mod=11), imm32]` immediate form (`MOV`/`IMUL`).
    `imm` is the little-endian 32-bit value. -/
def decodeImm : List (BitVec 8) → Option DecReg
  | [r, op, modrm, i0, i1, i2, i3] =>
      if isRex r ∧ modField modrm = 3 then
        some { opcode := op.toNat
             , reg := rexR r * 8 + regField modrm
             , rm := rexB r * 8 + rmField modrm
             , imm := some (i0.toNat + i1.toNat * 0x100 + i2.toNat * 0x10000
                            + i3.toNat * 0x1000000) }
      else none
  | _ => none

/-- Decode a `[REX, op, ModRM(mod=11), imm8]` shift / unary-imm form. The
    extension digit lands in `reg` (per the SDM `/digit` convention). -/
def decodeShift : List (BitVec 8) → Option DecReg
  | [r, op, modrm, ib] =>
      if isRex r ∧ modField modrm = 3 then
        some { opcode := op.toNat
             , reg := rexR r * 8 + regField modrm
             , rm := rexB r * 8 + rmField modrm
             , imm := some ib.toNat }
      else none
  | _ => none

/-- Decode a full 64-bit-immediate `MOV` `[REX, 0xB8+r, imm64]` (`B8+r io`).
    There is no ModRM byte: the destination register rides the opcode low 3 bits
    (`opcode - 0xB8`), and `REX.B` supplies the high bit, so
    `rm = REX.B<<3 | (opcode - 0xB8)`. The opcode field is normalised to `0xB8`
    (the form's base opcode) and `reg` to `0`; `imm` is the little-endian 64-bit
    value. Requires the opcode byte to be in `0xB8..0xBF`. -/
def decodeMovImm64 : List (BitVec 8) → Option DecReg
  | [r, op, i0, i1, i2, i3, i4, i5, i6, i7] =>
      if isRex r ∧ 0xb8 ≤ op.toNat ∧ op.toNat ≤ 0xbf then
        some { opcode := 0xb8
             , reg := 0
             , rm := rexB r * 8 + (op.toNat - 0xb8)
             , imm := some (i0.toNat + i1.toNat * 0x100 + i2.toNat * 0x10000
                            + i3.toNat * 0x1000000 + i4.toNat * 0x100000000
                            + i5.toNat * 0x10000000000 + i6.toNat * 0x1000000000000
                            + i7.toNat * 0x100000000000000) }
      else none
  | _ => none

/-! ## 4. Round-trip lemmas: `decode (enc …) = some ⟨encoded fields⟩`

For every opcode and register pair (`d s : Nat`, `d, s < 16`), the decoder
recovers exactly the opcode and the two register numbers the encoder put in.
The bound `< 16` is the GP-register range (`gpNum` is `0..15`); under it the
`bit · 3` extension bit is the high bit and `· &&& 7` the low 3, so the
reconstruction `REX.bit<<3 | ModRM.field` is the identity on the register
number. -/

/-- Helper: for `n < 16`, `(n >>> 3 &&& 1) * 8 + (n &&& 7) = n` — the
    REX-bit/ModRM-field split is the identity on a 4-bit register number. -/
theorem regsplit_id (n : Nat) (h : n < 16) :
    ((n >>> 3) &&& 1) * 8 + (n &&& 7) = n := by
  interval_cases n
  all_goals decide

/-- **Round-trip for the legacy reg-reg ALU/MOV forms.** For any one-byte opcode
    `op < 256` and GP registers `d, s < 16`, decoding `encAluRR op d s` recovers
    the opcode and `(reg = s, rm = d)` — exactly the fields the encoder set
    (`reg`=source, `rm`=destination, AT&T `op %src,%dst`). -/
theorem roundtrip_AluRR (op d s : Nat) (hop : op < 256) (hd : d < 16) (hs : s < 16) :
    decodeReg (encAluRR op d s) = some { opcode := op, reg := s, rm := d } := by
  have hop' : op % 2 ^ 8 = op := by rw [show (2:Nat)^8 = 256 from rfl]; exact Nat.mod_eq_of_lt hop
  -- The REX byte `64 + 8 + (bit s 3)*4 + (bit d 3)` is `< 80`, so `% 256` is
  -- identity; likewise the ModRM byte `192 + (s&7)*8 + (d&7) < 256`. The decoder
  -- then recovers `reg = (bit s 3)*8 + (s&7) = s` and `rm = (bit d 3)*8 + (d&7) = d`
  -- (`regsplit_id`), and `opcode = op % 256 = op` (`hop'`).
  have hreg : decodeReg (encAluRR op d s)
      = some { opcode := op % 2 ^ 8, reg := s, rm := d } := by
    simp only [encAluRR, decodeReg, List.map_cons, List.map_nil, isRex, modField,
      rexR, rexB, regField, rmField, rex, modRMReg, bit, BitVec.toNat_ofNat]
    interval_cases d <;> interval_cases s <;> rfl
  rw [hreg, hop']

/-- **Round-trip for the `0F`-map reg-reg forms** (`IMUL`/`CMOVcc`). The operand
    roles are swapped relative to the one-byte ALU forms: `reg`=destination,
    `rm`=source (these read `r/m` into `reg`), matching `enc0FRR`. -/
theorem roundtrip_0FRR (op d s : Nat) (hop : op < 256) (hd : d < 16) (hs : s < 16) :
    decode0F (enc0FRR op d s) = some { opcode := op, reg := d, rm := s } := by
  have hop' : op % 2 ^ 8 = op := by rw [show (2:Nat)^8 = 256 from rfl]; exact Nat.mod_eq_of_lt hop
  have hreg : decode0F (enc0FRR op d s)
      = some { opcode := op % 2 ^ 8, reg := d, rm := s } := by
    simp only [enc0FRR, decode0F, List.map_cons, List.map_nil, isRex, modField,
      rexR, rexB, regField, rmField, rex, modRMReg, bit, BitVec.toNat_ofNat]
    interval_cases d <;> interval_cases s <;> rfl
  rw [hreg, hop']

/-- The little-endian 32-bit recomposition the decoder applies is the inverse of
    `imm32LE` on values `< 2^32`: `b0 + b1·256 + b2·256² + b3·256³ = v`. The four
    `BitVec 8` bytes' `.toNat` are `(v >>> 8i) &&& 0xff` reduced mod `256`. -/
theorem imm32LE_recompose (v : Nat) (hv : v < 2 ^ 32) :
    (BitVec.ofNat 8 (v &&& 0xff)).toNat
      + (BitVec.ofNat 8 ((v >>> 8) &&& 0xff)).toNat * 0x100
      + (BitVec.ofNat 8 ((v >>> 16) &&& 0xff)).toNat * 0x10000
      + (BitVec.ofNat 8 ((v >>> 24) &&& 0xff)).toNat * 0x1000000 = v := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The little-endian 64-bit recomposition the `B8+r io` decoder applies is the
    inverse of `imm64LE` on values `< 2^64`. The eight `BitVec 8` bytes' `.toNat`
    are `(v >>> 8i) &&& 0xff` reduced mod `256`. -/
theorem imm64LE_recompose (v : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 8 (v &&& 0xff)).toNat
      + (BitVec.ofNat 8 ((v >>> 8) &&& 0xff)).toNat * 0x100
      + (BitVec.ofNat 8 ((v >>> 16) &&& 0xff)).toNat * 0x10000
      + (BitVec.ofNat 8 ((v >>> 24) &&& 0xff)).toNat * 0x1000000
      + (BitVec.ofNat 8 ((v >>> 32) &&& 0xff)).toNat * 0x100000000
      + (BitVec.ofNat 8 ((v >>> 40) &&& 0xff)).toNat * 0x10000000000
      + (BitVec.ofNat 8 ((v >>> 48) &&& 0xff)).toNat * 0x1000000000000
      + (BitVec.ofNat 8 ((v >>> 56) &&& 0xff)).toNat * 0x100000000000000 = v := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- **Round-trip for `MOV $imm32, %dst`** (`encMovImm`): `C7 /0` form, `reg`=0
    (the `/0` opcode-extension digit), `rm`=dst, `imm`=the 32-bit value. -/
theorem roundtrip_MovImm (d v : Nat) (hd : d < 16) (hv : v < 2 ^ 32) :
    decodeImm (encMovImm d v) = some { opcode := 0xc7, reg := 0, rm := d, imm := some v } := by
  have him := imm32LE_recompose v hv
  simp only [encMovImm, decodeImm, imm32LE, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, isRex, modField, rexR, rexB, regField,
    rmField, rex, modRMReg, bit]
  rw [if_pos]
  · refine congrArg some ?_
    refine DecReg.mk.injEq .. ▸ ⟨rfl, ?_, ?_, ?_⟩
    · interval_cases d <;> rfl
    · interval_cases d <;> rfl
    · exact congrArg some him
  · refine ⟨?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; interval_cases d <;> decide
    · interval_cases d <;> rfl

/-- **Round-trip for `MOV $imm64, %dst`** (`encMovImm64`): the `B8+r io` full
    64-bit-immediate form, decoded by `decodeMovImm64`. `reg`=0 (normalised — the
    form has no ModRM `reg`), `rm`=dst (`REX.B<<3 | (opcode - 0xB8)`),
    `imm`=the 64-bit value. The register rides the opcode low 3 bits, so the
    decoder recovers `rm = (bit d 3)*8 + (d &&& 7) = d` via `regsplit_id`. -/
theorem roundtrip_MovImm64 (d v : Nat) (hd : d < 16) (hv : v < 2 ^ 64) :
    decodeMovImm64 (encMovImm64 d v)
      = some { opcode := 0xb8, reg := 0, rm := d, imm := some v } := by
  have him := imm64LE_recompose v hv
  simp only [encMovImm64, decodeMovImm64, imm64LE, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, isRex, rexB, rex, bit, BitVec.toNat_ofNat]
  rw [if_pos]
  · refine congrArg some ?_
    refine DecReg.mk.injEq .. ▸ ⟨rfl, rfl, ?_, ?_⟩
    · interval_cases d <;> decide
    · exact congrArg some him
  · refine ⟨?_, ?_, ?_⟩
    · interval_cases d <;> decide
    · interval_cases d <;> decide
    · interval_cases d <;> decide

/-- **Round-trip for `IMUL $imm32, %dst, %dst`** (`encImulImm`): `69 /r` form,
    `reg`=`rm`=dst. -/
theorem roundtrip_ImulImm (d v : Nat) (hd : d < 16) (hv : v < 2 ^ 32) :
    decodeImm (encImulImm d v) = some { opcode := 0x69, reg := d, rm := d, imm := some v } := by
  have him := imm32LE_recompose v hv
  simp only [encImulImm, decodeImm, imm32LE, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, isRex, modField, rexR, rexB, regField,
    rmField, rex, modRMReg, bit]
  rw [if_pos]
  · refine congrArg some ?_
    refine DecReg.mk.injEq .. ▸ ⟨rfl, ?_, ?_, ?_⟩
    · interval_cases d <;> rfl
    · interval_cases d <;> rfl
    · exact congrArg some him
  · refine ⟨?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; interval_cases d <;> decide
    · interval_cases d <;> rfl

/-- **Round-trip for the immediate-source ALU forms** (`encAluImm`): the `81 /digit
    id` group, decoded by the same `[REX, op, ModRM(mod=11), imm32]` reader as
    `MOV`/`IMUL`. `reg`=the opcode-extension `digit` (since `REX.R=0`), `rm`=dst,
    `imm`=the 32-bit value. Covers `ADD/OR/ADC/SBB/AND/SUB/XOR $imm32` (`digit < 8`,
    `dst < 16`). -/
theorem roundtrip_AluImm (digit d v : Nat) (hdig : digit < 8) (hd : d < 16) (hv : v < 2 ^ 32) :
    decodeImm (encAluImm digit d v)
      = some { opcode := 0x81, reg := digit, rm := d, imm := some v } := by
  have him := imm32LE_recompose v hv
  simp only [encAluImm, decodeImm, imm32LE, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, isRex, modField, rexR, rexB, regField,
    rmField, rex, modRMReg, bit]
  rw [if_pos]
  · refine congrArg some ?_
    refine DecReg.mk.injEq .. ▸ ⟨rfl, ?_, ?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; interval_cases digit <;> interval_cases d <;> decide
    · simp only [BitVec.toNat_ofNat]; interval_cases digit <;> interval_cases d <;> decide
    · exact congrArg some him
  · refine ⟨?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; interval_cases d <;> decide
    · simp only [BitVec.toNat_ofNat]; interval_cases digit <;> interval_cases d <;> decide

/-- **Round-trip for the shift-by-`imm8` forms** (`encShiftImm`): `C1 /ext` form,
    `reg`=ext (the `/digit`), `rm`=dst, `imm`=the (low-byte) shift count. SHL=`/4`,
    SHR=`/5`, SAR=`/7`. -/
theorem roundtrip_ShiftImm (ext d imm : Nat) (hext : ext < 8) (hd : d < 16) (himm : imm < 256) :
    decodeShift (encShiftImm ext d imm)
      = some { opcode := 0xc1, reg := ext, rm := d, imm := some imm } := by
  have hib : (BitVec.ofNat 8 (imm &&& 0xff)).toNat = imm := by
    simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat]
    omega
  simp only [encShiftImm, decodeShift, List.map_cons, List.map_nil, isRex, modField,
    rexR, rexB, regField, rmField, rex, modRMReg, bit]
  rw [if_pos]
  · refine congrArg some ?_
    refine DecReg.mk.injEq .. ▸ ⟨rfl, ?_, ?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; interval_cases ext <;> interval_cases d <;> decide
    · simp only [BitVec.toNat_ofNat]; interval_cases ext <;> interval_cases d <;> decide
    · exact congrArg some hib
  · refine ⟨?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; interval_cases ext <;> interval_cases d <;> decide
    · simp only [BitVec.toNat_ofNat]; interval_cases ext <;> interval_cases d <;> decide

/-- **Round-trip for `NEG %dst`** (`encUnaryF7 3`): `F7 /3` form, `reg`=3
    (the `/3` extension digit), `rm`=dst. -/
theorem roundtrip_NegF7 (d : Nat) (hd : d < 16) :
    decodeReg (encUnaryF7 3 d) = some { opcode := 0xf7, reg := 3, rm := d } := by
  simp only [encUnaryF7, decodeReg, List.map_cons, List.map_nil, isRex, modField,
    rexR, rexB, regField, rmField, rex, modRMReg, bit, BitVec.toNat_ofNat]
  interval_cases d <;> rfl

/-! ## 5. Instruction-level round-trip: `decode (encode i) ≡ i`

The field-level lemmas above invert each *shape* encoder. We now lift them to
the full `JInstr`: a decoder that maps a one-byte opcode back to the ALU/MOV
mnemonic, and a `JInstr`-rebuilder that reads the `DecReg` register numbers back
through the allocation. The round-trip `rebuild (decode (encode i)) = i` holds
for the register-direct reg-reg ALU/MOV family on any allocation whose register
numbers are GP (`< 16`), which `gpNum` guarantees unconditionally. -/

/-- `gpNum` always lands in the GP range `0..15` (it is a 16-way table with a `0`
    fallback) — so every register operand the encoder emits decodes back into the
    `< 16` range the round-trip lemmas require. -/
theorem gpNum_lt_16 (r : String) : gpNum r < 16 := by
  unfold gpNum
  split <;> omega

/-- The one-byte ALU/MOV opcode → mnemonic constructor map, inverting the opcode
    bytes `encodeJInstr` emits for the reg-reg arms (`ADD 01`, `OR 09`, `ADC 11`,
    `SBB 19`, `AND 21`, `SUB 29`, `XOR 31`, `MOV 89`). Returns the `JInstr`
    constructor expecting `(dst, src)`. -/
def aluMnemonic : Nat → Option (String → JOperand → JInstr 64)
  | 0x01 => some JInstr.add
  | 0x09 => some JInstr.or_
  | 0x11 => some JInstr.adc
  | 0x19 => some JInstr.sbb
  | 0x21 => some JInstr.and_
  | 0x29 => some JInstr.sub
  | 0x31 => some JInstr.xor_
  | 0x89 => some JInstr.mov
  | _    => none

/-- The GP register name (`%rN`) for a SDM register number `0..15`, the inverse of
    `gpNum` on the canonical names. -/
def regName : Nat → String
  | 0 => "%rax" | 1 => "%rcx" | 2 => "%rdx" | 3 => "%rbx"
  | 4 => "%rsp" | 5 => "%rbp" | 6 => "%rsi" | 7 => "%rdi"
  | 8 => "%r8"  | 9 => "%r9"  | 10 => "%r10" | 11 => "%r11"
  | 12 => "%r12" | 13 => "%r13" | 14 => "%r14" | _ => "%r15"

/-- `regName` inverts `gpNum` on the 16 canonical `%rN` names. -/
theorem regName_gpNum (r : String) (h : r ∈ ["%rax","%rcx","%rdx","%rbx","%rsp","%rbp",
    "%rsi","%rdi","%r8","%r9","%r10","%r11","%r12","%r13","%r14","%r15"]) :
    regName (gpNum r) = r := by
  fin_cases h <;> rfl

/-- Rebuild a reg-reg ALU/MOV `JInstr` from a decoded `DecReg`: the opcode picks
    the mnemonic, `rm` is the destination register number, `reg` the source. -/
def rebuildAluRR (dr : DecReg) : Option (JInstr 64) :=
  (aluMnemonic dr.opcode).map (fun mk => mk (regName dr.rm) (.reg (regName dr.reg)))

/-- **The capstone round-trip for the reg-reg ALU/MOV family.** For a reg-reg
    instruction whose destination `d` and source `s` are canonical GP names,
    decoding its `encodeJInstr` bytes and rebuilding the `JInstr` recovers the
    original instruction. Stated for `ADD` (the pilot); the same `rfl`-after-
    rewrite proof discharges `OR ADC SBB AND SUB XOR MOV` (see `roundtrip_jinstr_all`). -/
theorem roundtrip_jinstr_add (alloc : GpAlloc) (d s : String)
    (hd : regName (gpNum (regOf alloc d)) = regOf alloc d)
    (hs : regName (gpNum (regOf alloc s)) = regOf alloc s) :
    (decodeReg (encodeJInstr alloc (.add d (.reg s)))).bind (rebuildAluRR ·)
      = some (.add (regOf alloc d) (.reg (regOf alloc s))) := by
  simp only [encodeJInstr]
  rw [roundtrip_AluRR 0x01 _ _ (by decide) (gpNum_lt_16 _) (gpNum_lt_16 _)]
  simp only [Option.bind_some, rebuildAluRR, aluMnemonic, Option.map_some]
  rw [hd, hs]

/-- The full reg-reg ALU/MOV family round-trip, as one statement quantified over
    the mnemonic via the encoded opcode. Each arm reduces by the matching
    `roundtrip_AluRR` opcode + `aluMnemonic` lookup, then `regName ∘ gpNum`
    cancellation on the operands. -/
theorem roundtrip_jinstr_all (alloc : GpAlloc) (d s : String)
    (hd : regName (gpNum (regOf alloc d)) = regOf alloc d)
    (hs : regName (gpNum (regOf alloc s)) = regOf alloc s) :
    (∀ mk op,
      (mk, op) ∈ [ (JInstr.add, 0x01), (JInstr.or_, 0x09), (JInstr.adc, 0x11),
                   (JInstr.sbb, 0x19), (JInstr.and_, 0x21), (JInstr.sub, 0x29),
                   (JInstr.xor_, 0x31), (JInstr.mov, 0x89) ] →
      (decodeReg (encodeJInstr alloc (mk d (.reg s)))).bind (rebuildAluRR ·)
        = some (mk (regOf alloc d) (.reg (regOf alloc s)))) := by
  intro mk op hmem
  fin_cases hmem <;>
    · simp only [encodeJInstr]
      rw [roundtrip_AluRR _ _ _ (by decide) (gpNum_lt_16 _) (gpNum_lt_16 _)]
      simp only [Option.bind_some, rebuildAluRR, aluMnemonic, Option.map_some]
      rw [hd, hs]

/-! ## 6. A real ELF64 relocatable object header (vs the `gas` `.byte` emitter)

`ScalarEncoder.encodeJBlock` produces a flat `.text` byte stream; the #438 demo
fed it to a `gas` `.byte` data-emitter. Here we emit an **ELF64
relocatable object header** (`ELFCLASS64`, `ET_REL`, `EM_X86_64`), so the owned
backend produces a real `.o` directly — no assembler in the object-build path.
The layout is the standard 64-byte `Elf64_Ehdr` (Intel/System V ABI):
magic `7F 45 4C 46`, class 2 (64-bit), data 1 (LE), version 1, then the
`e_type/e_machine/e_version/e_entry/e_phoff/e_shoff/…/e_shnum/e_shstrndx`
fields. -/

/-- The 64-byte ELF64 ELF header for a relocatable x86-64 object, parameterised
    by the section-header table offset `shoff` and the section count `shnum`
    (filled in by the section-table builder). `e_entry`/`e_phoff` are 0 (no
    program headers in a `.o`); `e_shentsize = 64`, `e_shstrndx` points at the
    section-string-table section. -/
def elf64Header (shoff shnum shstrndx : Nat) : List (BitVec 8) :=
  -- e_ident[16]: magic, class=2 (ELFCLASS64), data=1 (LE), version=1, OSABI=0, pad
  ([0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0].map (BitVec.ofNat 8))
    ++ u16LE 1                 -- e_type = ET_REL (relocatable)
    ++ u16LE 0x3e              -- e_machine = EM_X86_64
    ++ u32LE 1                 -- e_version = EV_CURRENT
    ++ u64LE 0                 -- e_entry = 0
    ++ u64LE 0                 -- e_phoff = 0 (no program headers)
    ++ u64LE shoff             -- e_shoff = section-header table offset
    ++ u32LE 0                 -- e_flags = 0
    ++ u16LE 64                -- e_ehsize = 64
    ++ u16LE 0                 -- e_phentsize = 0
    ++ u16LE 0                 -- e_phnum = 0
    ++ u16LE 64                -- e_shentsize = 64 (Elf64_Shdr)
    ++ u16LE shnum             -- e_shnum
    ++ u16LE shstrndx          -- e_shstrndx

/-- The ELF64 header is exactly 64 bytes (`Elf64_Ehdr`), the SDM/ABI-mandated
    size that `e_ehsize` (also 64) records. -/
theorem elf64Header_length (shoff shnum shstrndx : Nat) :
    (elf64Header shoff shnum shstrndx).length = 64 := by
  simp [elf64Header, u16LE, u32LE, u64LE, imm32LE, List.length_map]

/-- The ELF magic (`7F 'E' 'L' 'F'`) and the 64-bit/little-endian class bytes are
    the first six header bytes — the identification a loader checks first. -/
theorem elf64Header_magic (shoff shnum shstrndx : Nat) :
    (elf64Header shoff shnum shstrndx).take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) := by
  simp [elf64Header, u16LE, u32LE, u64LE, imm32LE]

/-! ## 7. The owned-backend byte-level trust edge after #444

The tally below (no single theorem carries the name `trust_edge`;
`trust_edge_pilot` at the end of this file anchors one instance of it as a
real, checked statement) records the honest tally:

* **decode-round-trip-proved** (`gas` differential pin not essential
  for field placement):
  the register-direct GP forms — `ADD ADC SUB SBB AND OR XOR MOV` reg-reg
  (`roundtrip_jinstr_all`), `IMUL`/`CMOVcc` reg-reg (`roundtrip_0FRR`),
  `MOV`/`IMUL` `$imm32` (`roundtrip_MovImm`/`roundtrip_ImulImm`), the
  immediate-source `ADD/OR/ADC/SBB/AND/SUB/XOR $imm32` group (`81 /digit id`,
  `roundtrip_AluImm`), `SHL`/`SHR`/`SAR` `$imm8` (`roundtrip_ShiftImm`),
  `NEG` (`roundtrip_NegF7`).
  For these the encoder's bytes are *proved* to decode back to the same
  register/immediate **fields** under the ModRM/REX field-split discipline.
  Each round-trip is universally quantified over the opcode byte `op`, so it
  certifies field *placement*, not opcode *legality*: it does not check that
  `op` is the SDM-correct byte for the mnemonic `encodeJInstr` selected — that
  assignment is `encodeJInstr`'s own hard-coded opcode table, not re-derived
  here. `gas` is out of the trusted path for field placement; which opcode
  byte means which mnemonic is unchecked by this module and rests on that
  hard-coded table (historically cross-checked against `gas` in
  `ScalarValidation.lean`).
* **still gas-pinned-only:** `MULX` (VEX), `ADCX`/`ADOX` (legacy-VEX), and the
  `loadMem`/`storeMem`/`mulxMem` memory forms' *operand-value* decode — `ADX`/`BMI2`
  have no Sail-x86 counterpart (ACL2 `x86isa` omits them, see `SailX86Validation`),
  and the memory forms are not yet wired to a full `JInstr` rebuild. The
  **base-register** of the shared `ScalarEncoder.memTail` (the SIB-escape and the
  forced-disp8 RIP-escape, the four bases `%rsp`/`%r12`/`%rbp`/`%r13`) is now
  decode-proved (`memTail_baseLow3_sib`, `memTail_baseLow3_rbp0` below): the encoded
  tail decodes to the *intended* base, not the degenerate no-base / RIP-relative
  form — the gap that previously segfaulted the BLS-Fp bytes-direct `.o`.

This is the `decode (encode i) ≡ i` upgrade of the #438 differential anchor for
the GP-ALU subset. -/

/-- Structural decode of a memory ModRM (`decodeMem`): recover the `mod` field,
    the base register's low-3 bits, and the displacement-presence per the Sail
    `x86_decode_sib_p` discipline (no SIB when base low-3 ≠ 4). Used by the
    memory-form structural checks; not yet lifted to a `JInstr` rebuild. -/
def decodeMemMod (modrm : BitVec 8) : Nat × Nat × Bool :=
  (modField modrm, rmField modrm, sibFollows modrm)

/-! ### `memTail` SIB/forced-disp8 structural round-trip (the X25519-milestone SIB gap)

`ScalarEncoder.memTail reg base off` is the base-aware ModRM/SIB/displacement tail
that `encMemMov`/`encMemMovw`/`encMulxMem` all share. For the four GP bases the
plain `modRMMem` mis-encodes — `%rsp`/`%r12` (low-3 = 4, the SIB escape) and
`%rbp`/`%r13` (low-3 = 5, the `mod=00` RIP escape) — `memTail` emits the SIB byte
`0x24` resp. forces a `disp8=0`. We decode the emitted base register low-3 bits per
the Sail `x86_decode_sib_p` discipline and prove it recovers the *intended* base for
all four, so the SIB-base encoding is decode-proved (not only gas-pinned): the
`%rbp` form decodes to base = `%rbp`, NOT RIP-relative; the `%rsp` form to base =
`%rsp` via the SIB.base, NOT a missing-SIB mis-parse.

`decodeBaseLow3 tail` reads the leading ModRM byte; when `sibFollows` it reads the
base from the SIB byte's low-3 (`sib & 7`), else from the ModRM `r/m`. This is the
exact field the CPU uses to form the base address. -/
def decodeBaseLow3 : List (BitVec 8) → Option Nat
  | modrm :: rest =>
      if sibFollows modrm then
        match rest with
        | sib :: _ => some (sib.toNat &&& 7)
        | [] => none
      else if modField modrm = 0 ∧ rmField modrm = 5 then
        none  -- RIP-relative: no base register (the bug we must NOT emit for %rbp/%r13)
      else some (rmField modrm)
  | [] => none

/-- `rmField (modRMMem m reg b) = b &&& 7` — the ModRM `r/m` field is the base low-3. -/
theorem rmField_modRMMem (m reg b : Nat) :
    rmField (BitVec.ofNat 8 (modRMMem m reg b)) = b &&& 7 := by
  have er : (reg &&& 7) = reg % 8 := Nat.and_two_pow_sub_one_eq_mod reg 3
  have eb : (b &&& 7) = b % 8 := Nat.and_two_pow_sub_one_eq_mod b 3
  rw [rmField, Nat.and_two_pow_sub_one_eq_mod _ 3, BitVec.toNat_ofNat, eb]
  unfold modRMMem; rw [er, eb]; omega

/-- `modField (modRMMem m reg b) = m` for a valid `mod` (`m < 4`). -/
theorem modField_modRMMem (m reg b : Nat) (hm : m < 4) :
    modField (BitVec.ofNat 8 (modRMMem m reg b)) = m := by
  have er : (reg &&& 7) = reg % 8 := Nat.and_two_pow_sub_one_eq_mod reg 3
  have eb : (b &&& 7) = b % 8 := Nat.and_two_pow_sub_one_eq_mod b 3
  rw [modField, Nat.and_two_pow_sub_one_eq_mod _ 2, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  unfold modRMMem; rw [er, eb]; omega

/-- The SIB byte `0x24` decodes to base low-3 = 4 (`0x24 &&& 7 = 4`). -/
theorem sibByte_0x24_base : (BitVec.ofNat 8 0x24).toNat &&& 7 = 4 := by decide

/-- The `memTail` base round-trip for the SIB escape (base low-3 = 4: `%rsp`/`%r12`).
    The emitted tail carries a SIB byte whose base field is `base & 7 = 4`, so the
    decoder recovers base low-3 = 4 — the encoding addresses through the base
    register, not a degenerate no-base form. -/
theorem memTail_baseLow3_sib (reg base : Nat) (off : Int) (hb : base &&& 7 = 4) :
    decodeBaseLow3 (memTail reg base off) = some 4 := by
  -- in every branch (disp0/disp8/disp32) the ModRM has `r/m = 4` (the SIB escape),
  -- so `sibFollows` holds and the decoder reads the SIB byte `0x24` → base low-3 = 4.
  have hsib : ∀ m, m < 3 → sibFollows (BitVec.ofNat 8 (modRMMem m reg 4)) = true := by
    intro m hm
    simp only [sibFollows, rmField_modRMMem, modField_modRMMem m reg 4 (by omega),
      show (4 : Nat) &&& 7 = 4 from by decide, decide_eq_true_eq, true_and]
    omega
  simp only [memTail, hb]
  -- outer split: disp0 vs disp8/disp32; inner split: disp8 vs disp32.
  split <;> [skip; split] <;>
    simp only [decodeBaseLow3, hsib 0 (by omega), hsib 1 (by omega), hsib 2 (by omega),
      if_true, sibByte_0x24_base]

/-- The `memTail` base round-trip for the RIP escape (base low-3 = 5: `%rbp`/`%r13`)
    at displacement 0: the forced `mod=01`/`disp8=0` makes the decoder recover the
    base (low-3 = 5), NOT the RIP-relative no-base form — exactly the gap that
    segfaulted the BLS-Fp bytes-direct `.o` (the `%rbp` scratch frame). -/
theorem memTail_baseLow3_rbp0 (reg base : Nat) (hb : base &&& 7 = 5) :
    decodeBaseLow3 (memTail reg base 0) = some 5 := by
  -- base low-3 = 5 ⇒ off=0 takes the forced-disp8 branch: ModRM `mod=01`, `r/m=5`.
  -- `sibFollows` is false (`r/m ≠ 4`), and `mod ≠ 0`, so it is NOT RIP-relative;
  -- the decoder reads the base from the `r/m` field = 5.
  have hsf : sibFollows (BitVec.ofNat 8 (modRMMem 1 reg base)) = false := by
    simp only [sibFollows, rmField_modRMMem, hb, decide_eq_false_iff_not]
    omega
  have hmf : modField (BitVec.ofNat 8 (modRMMem 1 reg base)) = 1 :=
    modField_modRMMem 1 reg base (by omega)
  simp only [memTail, hb]
  -- the forced-disp8 condition `(5 = 5 ∧ 0 = 0)` holds ⇒ not the disp0 branch;
  -- `0` fits disp8 ⇒ the `[modRM, disp8 0]` form.
  norm_num
  simp only [decodeBaseLow3, hsf, hmf, rmField_modRMMem, hb, if_false,
    Bool.false_eq_true]
  norm_num

/-- A doc-anchor: the round-trip-proved set is non-empty and includes the ADD
    pilot — referenced by the module docstring's trust-edge tally. -/
theorem trust_edge_pilot (alloc : GpAlloc) (d s : String)
    (hd : regName (gpNum (regOf alloc d)) = regOf alloc d)
    (hs : regName (gpNum (regOf alloc s)) = regOf alloc s) :
    (decodeReg (encodeJInstr alloc (.add d (.reg s)))).bind (rebuildAluRR ·)
      = some (.add (regOf alloc d) (.reg (regOf alloc s))) :=
  roundtrip_jinstr_add alloc d s hd hs
