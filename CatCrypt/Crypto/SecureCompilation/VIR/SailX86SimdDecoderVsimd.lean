/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-!
# Sail-x86 VEX decoder round-trip for the unified `vsimd` byte path

This module proves `decode (encode i) = i` for the SIMD byte path against the
VEX prefix / ModRM field-split discipline, with the encode side taken from the
**unified** `VsimdByteEncoder.encodeVsimdInst` (and its `encVpshufdU` /
`encodeVsimdShift` siblings) over the unified `SimdOp` op set. The VEX prefix
decode fields below (`vex2_byte1`, `vex3_byte*` naming) are transcribed by
hand from the SDM's VEX bit layout (§2.3.5) — the same kind of field-level
transcription `SailX86Decoder.lean` does for the GP-ALU ModRM/REX layout, and
subject to the same honest-scope caveat that module states: this is a
structural field parser, not a re-implementation of the Sail-x86 opcode
dispatch tables. The only encoder dependency is the shared `X86Backend.CryptoExt`
prefix layer that `encodeVsimdInst` is built on.

**Provenance note:** nothing in this repository currently imports this file,
and this repository has no `SailX86SimdDecoder.lean` module and no
`X86Backend.Vec128Encoder` module. The scope below stands on its own terms: it
decode-round-trips `VsimdByteEncoder`'s unified encoder directly.

## Scope (the unified SIMD classes that are decode-round-trip-proved)

* **VEX-128 `0F`-map ALU set** — every `encAvx2Alu`-backed `SimdOp` arm
  (`bitwise .and/.or/.xor`, `packed .add/.sub/.mul`, `mulhi16`): `decodeVex2`
  inverts the 2-byte-VEX (`C5`) form, `roundtrip_vex2_alu` proves the field
  round-trip, and `roundtrip_encodeVsimdInst_alu` lifts it onto the `SimdOp`
  dispatcher (`roundtrip_encodeVsimdInst_vpxor` is the named pilot).
* **VEX-3 (`C4`) `0F38`-map `VPSHUFB`** — `encAvx2_0F38 0x00`: `decodeVex3`
  inverts the 3-byte form, `roundtrip_vex3` / `roundtrip_encodeVsimdInst_vpshufb`
  prove the round-trip.
* **VEX-2 `VPSHUFD` shuffle** — `encVpshufdU` (`0F 70 /r ib`):
  `decodeVpshufd` / `roundtrip_encodeVsimdInst_vpshufd`.
* **VEX-2 imm-shift NDD set** — `encodeVsimdShift` / `encVpslldqU`/`encVpsrldqU`
  (`0F 73 /7,/3 ib`): `decodeVex2Shift` / `roundtrip_encodeVsimdShift`.

## What the VEX-3 round-trip does *not* pin (`DecVex3` has no `pp`/`L` field)

`DecVex3` (§5 below) records only `opcode`/`mm`/`d`/`v`/`m`/`w` — it has **no
`pp` and no `L` field**. `decodeVex3` never reads VEX-3 byte-2's `pp` bits
(the mandatory-prefix selector, SDM §2.3.6) or the vector-length `L` bit, and
`roundtrip_vex3` proves nothing about either: `encVex3 mm pp w l op d v m imm`
round-trips for *every* `pp < 4` and `l < 2` the caller supplies, with the
conclusion silent on whether the decoded bytes actually carry that `pp`/`l`
back out. So the VEX-3 round-trip (`roundtrip_vex3`, `roundtrip_vpshufb`,
`roundtrip_encodeVsimdInst_vpshufb`) certifies the opcode, opcode map (`mm`),
the destination/source register fields, and `W` — it does **not** certify that
the mandatory-prefix or vector-length bits the encoder wrote are recoverably
present in the byte stream, even though a real decoder relies on `pp` to pick
the SIMD-prefix-selected opcode table and on `L` for 128- vs 256-bit width.

## Scope (the crypto-ext decode ceiling, gas-pinned)

The VAES (`vaesenc`/`vaesenclast`/`vaeskeygen`), PCLMUL (`clmul`) and GFNI
(`gf2p8mulb`/`affineqb`) `SimdOp` arms are 3-byte-VEX *encodable*, but their
**semantics** live in the ACL2/Sail-x86 model (`cryptoext_spec.sail`, in the
authors' external, not-vendored `sail-x86-from-acl2` checkout — see
`SailX86Validation.lean`) only as *execute* clauses, never a byte-decode
operand parse — so their byte forms stay gas-pinned, exactly as
`VsimdByteEncoder`'s per-arm gas pins and ceiling record. The proved
set here is the unified byte path's SIMD *body* off the gas pin (field
placement only — opcode legality is unchecked, as `SailX86Decoder.lean`
records for the GP-ALU decoder, and the VEX-3 forms additionally leave `pp`/`L`
unpinned per the note above).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SailX86SimdDecoderVsimd

open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (SimdOp JasminBinOp)

/-! ## 1. VEX prefix field extraction (Sail `vex2_byte1`/`vex3_byte*` bitfields)

These transcribe the Sail-x86 `structures.sail` VEX bitfields — the same field
splits `SailX86SimdDecoder.lean` uses, re-homed here `Vec128`-free. A `BitVec 8`
prefix byte is split into its named fields; the inverted `R̄`/`B̄`/`vvvv` fields
(SDM §2.3.5) are un-inverted by the register-recovery accessors. -/

/-- VEX byte-1 (2-byte `C5` form) `R̄` bit (bit 7). The logical `R = 1 - R̄`. -/
def vex2R (b : BitVec 8) : Nat := 1 - ((b.toNat >>> 7) &&& 1)
/-- VEX byte-1 (2-byte `C5` form) `vvvv` field (bits 6..3), as the SDM source
    register `v = 15 - field`. -/
def vex2Vvvv (b : BitVec 8) : Nat := 15 - ((b.toNat >>> 3) &&& 15)
/-- VEX byte-1 (2-byte `C5` form) `L` bit (bit 2). -/
def vex2L (b : BitVec 8) : Nat := (b.toNat >>> 2) &&& 1
/-- VEX byte-1 (2-byte `C5` form) `pp` field (bits 1..0). -/
def vex2Pp (b : BitVec 8) : Nat := b.toNat &&& 3

/-- ModRM `mod` field (bits 7..6). -/
def modField (b : BitVec 8) : Nat := (b.toNat >>> 6) &&& 3
/-- ModRM `reg` field (bits 5..3). -/
def regField (b : BitVec 8) : Nat := (b.toNat >>> 3) &&& 7
/-- ModRM `r/m` field (bits 2..0). -/
def rmField (b : BitVec 8) : Nat := b.toNat &&& 7

/-! ## 2. The decoded VEX-2 register-form record -/

/-- A decoded VEX 3-register op: opcode, dst (`d`), src1 (`v` = vvvv), src2 (`m`),
    plus the `L`/`pp` prefix selectors. -/
structure DecVex where
  opcode : Nat
  d : Nat
  v : Nat
  m : Nat
  l : Nat
  pp : Nat
deriving DecidableEq, Repr

/-- Decode a 2-byte-VEX (`C5`) `0F`-map three-register form
    `[0xC5, P1, op, ModRM(mod=11)]`. Requires `mod = 0b11` (register-direct). -/
def decodeVex2 : List (BitVec 8) → Option DecVex
  | [v0, p1, op, modrm] =>
      if v0.toNat = 0xc5 ∧ modField modrm = 3 then
        some { opcode := op.toNat
             , d := vex2R p1 * 8 + regField modrm
             , v := vex2Vvvv p1
             , m := rmField modrm
             , l := vex2L p1
             , pp := vex2Pp p1 }
      else none
  | _ => none

/-! ## 3. Round-trip for the VEX-128 `0F`-map ALU set

`encAvx2Alu op 0 d v m` takes the 2-byte `C5` form exactly when `bit m 3 = 0`
(low src2). Under the low-XMM register range (`d, v, m < 8`) the form is always
2-byte and `decodeVex2` recovers the encoder's exact operands. -/

/-- **Round-trip for the VEX-128 `0F`-map ALU set.** For `d, v, m < 8` and any
    opcode `op < 256`, decoding `encAvx2Alu op 0 d v m` recovers exactly
    `(opcode=op, d, v, m, l=0, pp=01)`. -/
theorem roundtrip_vex2_alu (op d v m : Nat) (hop : op < 256)
    (hd : d < 8) (hv : v < 8) (hm : m < 8) :
    decodeVex2 (encAvx2Alu op 0 d v m)
      = some { opcode := op, d := d, v := v, m := m, l := 0, pp := 1 } := by
  have hop' : op % 2 ^ 8 = op := by
    rw [show (2:Nat)^8 = 256 from rfl]; exact Nat.mod_eq_of_lt hop
  have hbm : bit m 3 = 0 := by
    simp only [bit]; interval_cases m <;> decide
  have hdec : decodeVex2 (encAvx2Alu op 0 d v m)
      = some { opcode := op % 2 ^ 8, d := d, v := v, m := m, l := 0, pp := 1 } := by
    simp only [encAvx2Alu, encVexAuto, encVex2, vex2p1,
      decodeVex2, List.map_cons, List.map_nil, vex2R, vex2Vvvv, vex2L, vex2Pp,
      modField, regField, rmField, modRMReg, bit, cbit]
    interval_cases d <;> interval_cases v <;> interval_cases m <;> rfl
  rw [hdec, hop']

/-! ## 4. Lifting the VEX-128 ALU round-trip onto `encodeVsimdInst`

The `encAvx2Alu`-backed `SimdOp` arms (`bitwise`, `packed`, `mulhi16`) all reduce
to `encAvx2Alu opcode 0 d a b`, so the field round-trip lifts directly. We give a
named pilot (`.bitwise .xor`, opcode `0xEF`) plus the general statement over the
opcode the dispatcher selects. -/

/-- **The unified-encoder VEX-128 `VPXOR` round-trip pilot.** Decoding the bytes
    `encodeVsimdInst (.bitwise .xor) d a b` produces (off the gas pin, under the
    Sail-x86 VEX parse) the operands the instruction names, for low XMM
    `d, a, b < 8`. -/
theorem roundtrip_encodeVsimdInst_vpxor (d a b : Nat)
    (hd : d < 8) (ha : a < 8) (hb : b < 8) :
    decodeVex2 (encodeVsimdInst (.bitwise .xor) d a b)
      = some { opcode := 0xef, d := d, v := a, m := b, l := 0, pp := 1 } := by
  simpa [encodeVsimdInst] using roundtrip_vex2_alu 0xef d a b (by decide) hd ha hb

/-- **The unified `encAvx2Alu`-arm round-trip, general in the opcode.** Every
    `encAvx2Alu`-backed `SimdOp` byte sequence (i.e. one equal to
    `encAvx2Alu op 0 d a b` for the opcode the dispatcher picks) decodes back to
    `(op, d, a, b)` for low XMM registers — covering `bitwise .and/.or/.xor`,
    `packed .add/.sub/.mul`, and `mulhi16`. -/
theorem roundtrip_encodeVsimdInst_alu (op d a b : Nat) (sop : SimdOp)
    (hop : op < 256) (hd : d < 8) (ha : a < 8) (hb : b < 8)
    (henc : encodeVsimdInst sop d a b = encAvx2Alu op 0 d a b) :
    decodeVex2 (encodeVsimdInst sop d a b)
      = some { opcode := op, d := d, v := a, m := b, l := 0, pp := 1 } := by
  rw [henc]; exact roundtrip_vex2_alu op d a b hop hd ha hb

/-! ## 5. VEX-3 (`C4`) prefix decode and the `0F38`-map `VPSHUFB` round-trip -/

/-- VEX-3 byte-1 (`C4` form, `vex3_byte1`) `R̄` bit (bit 7); logical `R = 1−R̄`. -/
def vex3R (b : BitVec 8) : Nat := 1 - ((b.toNat >>> 7) &&& 1)
/-- VEX-3 byte-1 `B̄` bit (bit 5); logical `B = 1−B̄`. -/
def vex3B (b : BitVec 8) : Nat := 1 - ((b.toNat >>> 5) &&& 1)
/-- VEX-3 byte-1 `mmmmm` opcode-map field (bits 4..0). -/
def vex3Mm (b : BitVec 8) : Nat := b.toNat &&& 31
/-- VEX-3 byte-2 (`vex3_byte2`) `W` bit (bit 7). -/
def vex3W (b : BitVec 8) : Nat := (b.toNat >>> 7) &&& 1
/-- VEX-3 byte-2 `vvvv` field (bits 6..3), as the SDM source `v = 15 − field`. -/
def vex3Vvvv (b : BitVec 8) : Nat := 15 - ((b.toNat >>> 3) &&& 15)
/-- VEX-3 byte-2 `pp` field (bits 1..0). -/
def vex3Pp (b : BitVec 8) : Nat := b.toNat &&& 3

/-- A decoded VEX-3 register-form op: opcode + map (`mm`), dst (`d`), src1 (`v`),
    src2 (`m`), and the `W`/`pp` selectors. -/
structure DecVex3 where
  opcode : Nat
  mm : Nat
  d : Nat
  v : Nat
  m : Nat
  w : Nat
deriving DecidableEq, Repr

/-- Decode a 3-byte-VEX register form `[0xC4, P1, P2, op, ModRM(mod=11)]` (a
    trailing `imm8` is not part of the operand recovery). Requires `mod = 0b11`. -/
def decodeVex3 : List (BitVec 8) → Option DecVex3
  | v0 :: p1 :: p2 :: op :: modrm :: _ =>
      if v0.toNat = 0xc4 ∧ modField modrm = 3 then
        some { opcode := op.toNat
             , mm := vex3Mm p1
             , d := vex3R p1 * 8 + regField modrm
             , v := vex3Vvvv p2
             , m := vex3B p1 * 8 + rmField modrm
             , w := vex3W p2 }
      else none
  | _ => none

/-- **Round-trip for the VEX-3 three-register set.** For `d, v, m < 16`, opcode
    `op < 256`, map `mm < 32`, prefix `pp < 4`, width `w < 2`, length bit `l < 2`,
    decoding `encVex3 mm pp w l op d v m imm` recovers `(opcode=op, mm, d, v, m, w)`. -/
theorem roundtrip_vex3 (mm pp w l op d v m : Nat) (imm : Option Nat)
    (hop : op < 256) (hmm : mm < 32) (hpp : pp < 4) (hw : w < 2) (hl : l < 2)
    (hd : d < 16) (hv : v < 16) (hm : m < 16) :
    decodeVex3 (encVex3 mm pp w l op d v m imm)
      = some { opcode := op, mm := mm, d := d, v := v, m := m, w := w } := by
  have hbd : d >>> 3 &&& 1 < 2 := by interval_cases d <;> decide
  have hbm : m >>> 3 &&& 1 < 2 := by interval_cases m <;> decide
  have hop' : op % 2 ^ 8 = op := by
    rw [show (2:Nat)^8 = 256 from rfl]; exact Nat.mod_eq_of_lt hop
  have hmod : (((192 + (d &&& 7) * 8 + (m &&& 7)) % 2 ^ 8) >>> 6) &&& 3 = 3 := by
    interval_cases d <;> interval_cases m <;> decide
  have hmm_g : ∀ r b : Nat, r < 2 → b < 2 →
      (((1 - r) * 128 + 64 + (1 - b) * 32 + mm) % 2 ^ 8) &&& 31 = mm := by
    intro r b hr hbb; interval_cases r <;> interval_cases b <;> interval_cases mm <;> decide
  have hr_g : ∀ r b : Nat, r < 2 → b < 2 →
      1 - ((((1 - r) * 128 + 64 + (1 - b) * 32 + mm) % 2 ^ 8) >>> 7 &&& 1) = r := by
    intro r b hr hbb; interval_cases r <;> interval_cases b <;> interval_cases mm <;> decide
  have hb_g : ∀ r b : Nat, r < 2 → b < 2 →
      1 - ((((1 - r) * 128 + 64 + (1 - b) * 32 + mm) % 2 ^ 8) >>> 5 &&& 1) = b := by
    intro r b hr hbb; interval_cases r <;> interval_cases b <;> interval_cases mm <;> decide
  have hreg : ((192 + (d &&& 7) * 8 + (m &&& 7)) % 2 ^ 8) >>> 3 &&& 7 = d &&& 7 := by
    interval_cases d <;> interval_cases m <;> decide
  have hrm : ((192 + (d &&& 7) * 8 + (m &&& 7)) % 2 ^ 8) &&& 7 = m &&& 7 := by
    interval_cases d <;> interval_cases m <;> decide
  have hdsplit : (d >>> 3 &&& 1) * 8 + (d &&& 7) = d := by interval_cases d <;> decide
  have hmsplit : (m >>> 3 &&& 1) * 8 + (m &&& 7) = m := by interval_cases m <;> decide
  have hv_id : 15 - (((w * 128 + (15 - (v &&& 15)) * 8 + l * 4 + pp) % 2 ^ 8) >>> 3 &&& 15) = v := by
    interval_cases w <;> interval_cases v <;> interval_cases pp <;> interval_cases l <;> decide
  have hw_id : ((w * 128 + (15 - (v &&& 15)) * 8 + l * 4 + pp) % 2 ^ 8) >>> 7 &&& 1 = w := by
    interval_cases w <;> interval_cases v <;> interval_cases pp <;> interval_cases l <;> decide
  have hd_id : (1 - ((((1 - (d >>> 3 &&& 1)) * 128 + 64 + (1 - (m >>> 3 &&& 1)) * 32 + mm)
      % 2 ^ 8) >>> 7 &&& 1)) * 8 + (((192 + (d &&& 7) * 8 + (m &&& 7)) % 2 ^ 8) >>> 3 &&& 7) = d := by
    rw [hr_g _ _ hbd hbm, hreg, hdsplit]
  have hm_id : (1 - ((((1 - (d >>> 3 &&& 1)) * 128 + 64 + (1 - (m >>> 3 &&& 1)) * 32 + mm)
      % 2 ^ 8) >>> 5 &&& 1)) * 8 + (((192 + (d &&& 7) * 8 + (m &&& 7)) % 2 ^ 8) &&& 7) = m := by
    rw [hb_g _ _ hbd hbm, hrm, hmsplit]
  have hmm_id : (((1 - (d >>> 3 &&& 1)) * 128 + 64 + (1 - (m >>> 3 &&& 1)) * 32 + mm)
      % 2 ^ 8) &&& 31 = mm := hmm_g _ _ hbd hbm
  have hdec : decodeVex3 (encVex3 mm pp w l op d v m imm)
      = some { opcode := op % 2 ^ 8, mm := mm, d := d, v := v, m := m, w := w } := by
    cases imm <;>
    · simp only [encVex3, vex3p1, vex3p2, modRMReg,
        bit, cbit, decodeVex3, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append,
        modField, regField, rmField, vex3Mm, vex3R, vex3B, vex3Vvvv, vex3W,
        BitVec.toNat_ofNat]
      rw [if_pos ⟨trivial, hmod⟩]
      refine congrArg some ?_
      refine DecVex3.mk.injEq .. ▸ ⟨rfl, hmm_id, hd_id, hv_id, hm_id, hw_id⟩
  rw [hdec, hop']

/-- **`VPSHUFB` round-trip** (the byte-rotate + lane shuffle), an instance of
    `roundtrip_vex3` on `encAvx2_0F38 0x00`. -/
theorem roundtrip_vpshufb (d v m : Nat) (hd : d < 16) (hv : v < 16) (hm : m < 16) :
    decodeVex3 (encAvx2_0F38 0x00 0 d v m)
      = some { opcode := 0x00, mm := 0b00010, d := d, v := v, m := m, w := 0 } := by
  simpa [encAvx2_0F38] using
    roundtrip_vex3 0b00010 0b01 0 0 0x00 d v m none (by decide) (by decide)
      (by decide) (by decide) (by decide) hd hv hm

/-- **The unified-encoder `VPSHUFB` round-trip.** Decoding
    `encodeVsimdInst .vpshufb d a b` recovers the named operands under the Sail-x86
    VEX-3 parse, for `d, a, b < 16`. -/
theorem roundtrip_encodeVsimdInst_vpshufb (d a b : Nat)
    (hd : d < 16) (ha : a < 16) (hb : b < 16) :
    decodeVex3 (encodeVsimdInst .vpshufb d a b)
      = some { opcode := 0x00, mm := 0b00010, d := d, v := a, m := b, w := 0 } := by
  simpa [encodeVsimdInst] using roundtrip_vpshufb d a b hd ha hb

/-! ## 6. VEX-2 `VPSHUFD` shuffle round-trip (unified `encVpshufdU`) -/

/-- Decode a 2-byte-VEX 2-operand-imm form `[0xC5, P1, 0x70, ModRM(mod=11), ib]`
    (`VPSHUFD`): `d = R̄inv<<3 | ModRM.reg`, `m = ModRM.rm`, `imm = ib`. -/
def decodeVpshufd : List (BitVec 8) → Option (Nat × Nat × Nat × Nat)
  | [v0, p1, op, modrm, ib] =>
      if v0.toNat = 0xc5 ∧ modField modrm = 3 then
        some (op.toNat, vex2R p1 * 8 + regField modrm, rmField modrm, ib.toNat)
      else none
  | _ => none

/-- **Round-trip for the unified `VPSHUFD` shuffle.** For destination `d < 8`, low
    source `src < 8`, immediate `imm < 256`, decoding `encVpshufdU 0 d src imm`
    recovers `(0x70, d, src, imm)` — the `0F 70 /r ib` packed-dword shuffle. -/
theorem roundtrip_encVpshufdU (d src imm : Nat)
    (hd : d < 8) (hsrc : src < 8) (himm : imm < 256) :
    decodeVpshufd (encVpshufdU 0 d src imm)
      = some (0x70, d, src, imm) := by
  have hbm : src >>> 3 &&& 1 = 0 := by interval_cases src <;> decide
  have hand : ∀ k : Nat, k &&& 255 = k % 2 ^ 8 := fun k => by
    rw [show (255:Nat) = 2 ^ 8 - 1 from rfl]; exact Nat.and_two_pow_sub_one_eq_mod k 8
  have himm' : imm % 2 ^ 8 = imm := by
    rw [show (2:Nat)^8 = 256 from rfl]; exact Nat.mod_eq_of_lt himm
  have hmod : ((192 + (d &&& 7) * 8 + (src &&& 7)) % 2 ^ 8) >>> 6 &&& 3 = 3 := by
    interval_cases d <;> interval_cases src <;> decide
  have hd_id : (1 - ((((1 - (d >>> 3 &&& 1)) * 128 + (15 - (0 &&& 15)) * 8 + 0 * 4 + 1)
      % 2 ^ 8) >>> 7 &&& 1)) * 8 + (((192 + (d &&& 7) * 8 + (src &&& 7)) % 2 ^ 8) >>> 3 &&& 7) = d := by
    interval_cases d <;> interval_cases src <;> decide
  have hsrc_id : ((192 + (d &&& 7) * 8 + (src &&& 7)) % 2 ^ 8) &&& 7 = src := by
    interval_cases d <;> interval_cases src <;> decide
  have hdec : decodeVpshufd (encVpshufdU 0 d src imm)
      = some (0x70, d, src, imm % 2 ^ 8) := by
    simp only [encVpshufdU, bit, hbm, if_true, vex2p1,
      modRMReg, cbit, decodeVpshufd, List.map_cons, List.map_nil,
      modField, regField, rmField, vex2R, BitVec.toNat_ofNat, hand]
    rw [if_pos ⟨trivial, hmod⟩]
    refine congrArg some ?_
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext hsrc_id ?_))
    · exact hd_id
    · exact Nat.mod_mod_of_dvd _ dvd_rfl
  rw [hdec, himm']

/-- **The unified-encoder `VPSHUFD` round-trip.** Decoding
    `encodeVsimdInst (.vpshufd imm) d a b` recovers `(0x70, d, a, imm)` for low XMM
    `d, a < 8`, `imm < 256` (the `b` operand is unused for this unary shuffle). -/
theorem roundtrip_encodeVsimdInst_vpshufd (d a b imm : Nat)
    (hd : d < 8) (ha : a < 8) (himm : imm < 256) :
    decodeVpshufd (encodeVsimdInst (.vpshufd imm) d a b)
      = some (0x70, d, a, imm) := by
  simpa [encodeVsimdInst] using roundtrip_encVpshufdU d a imm hd ha himm

/-! ## 7. VEX-2 imm-shift NDD round-trip (unified `encodeVsimdShift`)

`encodeVsimdShift ext 0 dst src imm` (2-byte `C5` form, low `src`) emits the NDD
layout `[0xc5, vex2p1 (bit ext 3) dst 0 0b01, 0x73, modRMReg ext src, imm]`: the
written register lives in `vvvv`, `ModRM.reg` carries the `/digit` group extension
(`/7` SLL = `encVpslldqU`, `/3` SRL = `encVpsrldqU`), and `ModRM.rm` is the
source. -/

/-- A decoded VEX-2 imm-shift NDD op: opcode (group byte), the `/digit` extension
    `ext` (in `ModRM.reg`), the NDD destination `d` (in `vvvv`), the source `m`
    (in `ModRM.rm`), and the immediate count `imm`. -/
structure DecVexShift where
  opcode : Nat
  ext : Nat
  d : Nat
  m : Nat
  imm : Nat
deriving DecidableEq, Repr

/-- Decode a 2-byte-VEX imm-shift NDD form `[0xC5, P1, op, ModRM(mod=11), ib]`:
    `d = 15 - vvvv-field`, `ext = ModRM.reg`, `m = ModRM.rm`, `imm = ib`. -/
def decodeVex2Shift : List (BitVec 8) → Option DecVexShift
  | [v0, p1, op, modrm, ib] =>
      if v0.toNat = 0xc5 ∧ modField modrm = 3 then
        some { opcode := op.toNat
             , ext := regField modrm
             , d := vex2Vvvv p1
             , m := rmField modrm
             , imm := ib.toNat }
      else none
  | _ => none

/-- **Round-trip for the unified VEX-2 imm-shift NDD set.** For an `ext < 8`
    opcode-group digit, NDD destination `d < 16`, low source `m < 8`, immediate
    `imm < 256`, decoding `encodeVsimdShift ext 0 d m imm` recovers
    `(opcode=0x73, ext, d, m, imm)`. Covers `encVpslldqU` (`/7`) and `encVpsrldqU`
    (`/3`). -/
theorem roundtrip_encodeVsimdShift (ext d m imm : Nat)
    (hext : ext < 8) (hd : d < 16) (hm : m < 8) (himm : imm < 256) :
    decodeVex2Shift (encodeVsimdShift ext 0 d m imm)
      = some { opcode := 0x73, ext := ext, d := d, m := m, imm := imm } := by
  have hbm : m >>> 3 &&& 1 = 0 := by interval_cases m <;> decide
  have hand : ∀ k : Nat, k &&& 255 = k % 2 ^ 8 := fun k => by
    rw [show (255:Nat) = 2 ^ 8 - 1 from rfl]; exact Nat.and_two_pow_sub_one_eq_mod k 8
  have himm' : imm % 2 ^ 8 = imm := by
    rw [show (2:Nat)^8 = 256 from rfl]; exact Nat.mod_eq_of_lt himm
  have hmod : ((192 + (ext &&& 7) * 8 + (m &&& 7)) % 2 ^ 8) >>> 6 &&& 3 = 3 := by
    interval_cases ext <;> interval_cases m <;> decide
  have hext_id : ((192 + (ext &&& 7) * 8 + (m &&& 7)) % 2 ^ 8) >>> 3 &&& 7 = ext := by
    interval_cases ext <;> interval_cases m <;> decide
  have hm_id : (192 + (ext &&& 7) * 8 + (m &&& 7)) % 2 ^ 8 &&& 7 = m := by
    interval_cases ext <;> interval_cases m <;> decide
  have hd_id : 15 - ((((1 - (ext >>> 3 &&& 1)) * 128 + (15 - (d &&& 15)) * 8 + 0 * 4 + 1)
      % 2 ^ 8) >>> 3 &&& 15) = d := by
    interval_cases ext <;> interval_cases d <;> decide
  have hdec : decodeVex2Shift (encodeVsimdShift ext 0 d m imm)
      = some { opcode := (0x73 : Nat) % 2 ^ 8, ext := ext, d := d, m := m, imm := imm % 2 ^ 8 } := by
    simp only [encodeVsimdShift, encodeVsimdShiftImm, bit, hbm, if_true, vex2p1,
      modRMReg, cbit, decodeVex2Shift, List.map_cons, List.map_nil,
      modField, regField, rmField, vex2Vvvv, BitVec.toNat_ofNat, hand]
    rw [if_pos ⟨trivial, hmod⟩]
    refine congrArg some ?_
    refine DecVexShift.mk.injEq .. ▸
      ⟨rfl, hext_id, hd_id, hm_id, Nat.mod_mod_of_dvd _ dvd_rfl⟩
  rw [hdec, himm', show (0x73 : Nat) % 2 ^ 8 = 0x73 from rfl]

/-- **`VPSLLDQ` round-trip** (`0F 73 /7`), an instance of `roundtrip_encodeVsimdShift`
    at `ext = 7`. -/
theorem roundtrip_encVpslldqU (d m imm : Nat)
    (hd : d < 16) (hm : m < 8) (himm : imm < 256) :
    decodeVex2Shift (encVpslldqU 0 d m imm)
      = some { opcode := 0x73, ext := 7, d := d, m := m, imm := imm } :=
  roundtrip_encodeVsimdShift 7 d m imm (by decide) hd hm himm

/-- **`VPSRLDQ` round-trip** (`0F 73 /3`), an instance of `roundtrip_encodeVsimdShift`
    at `ext = 3`. -/
theorem roundtrip_encVpsrldqU (d m imm : Nat)
    (hd : d < 16) (hm : m < 8) (himm : imm < 256) :
    decodeVex2Shift (encVpsrldqU 0 d m imm)
      = some { opcode := 0x73, ext := 3, d := d, m := m, imm := imm } :=
  roundtrip_encodeVsimdShift 3 d m imm (by decide) hd hm himm

/-! ## 8. The unified SIMD byte-level trust edge

`trust_edge_vsimd_pilot` records that the round-trip-proved unified SIMD set is
non-empty and rides the `VsimdByteEncoder.encodeVsimdInst` path directly — no
bespoke per-family encoder sits in the trusted decode path. -/

/-- A doc-anchor: the unified round-trip-proved SIMD set is non-empty and includes
    the VEX-128 `VPXOR` pilot off `encodeVsimdInst`. -/
theorem trust_edge_vsimd_pilot (d a b : Nat) (hd : d < 8) (ha : a < 8) (hb : b < 8) :
    decodeVex2 (encodeVsimdInst (.bitwise .xor) d a b)
      = some { opcode := 0xef, d := d, v := a, m := b, l := 0, pp := 1 } :=
  roundtrip_encodeVsimdInst_vpxor d a b hd ha hb

end CatCrypt.Crypto.SecureCompilation.VIR.SailX86SimdDecoderVsimd
