/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonEncoder
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonEncoder
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-!
# Sail-arm NEON decoder round-trip: `decode (encode i) = i` (#548)

`NeonEncoder.lean` is the owned `NInst → machine-byte` encoder. Its bench trust
edge is *differential*: each emitted 32-bit word is pinned to what
`aarch64-linux-gnu-as` produces (an untracked local comparison checkout, not
vendored in this repo, plus the qemu KAT). That makes `as`'s unverified encoder
part of the trusted base.

This module replaces the differential edge, for the instruction classes in
scope below, with a **round-trip** against an AArch64 ASIMD *decoder*
discipline: a Lean decoder `decodeNeon` that recovers the instruction-class
fields `(opcode-class, Rd, Rn, Rm/sh)` from a 32-bit instruction word,
following the field-split structure of the
[`rems-project/sail-arm`](https://github.com/rems-project/sail-arm) `decode64`
ASIMD clauses (`vector_arithmetic_binary_uniform_add_*`, `…_logical_andorr_*`,
`…_logical_bsleor_*`, `vector_shift_left_simd_*`, `vector_shift_right_simd_*`)
as transcribed by hand from the public sail-arm sources — this repo does not
vendor a sail-arm checkout, so the clause structure below is the authors'
transcription and is not machine-checked against the upstream model — and a
proof that `decodeNeon (encode i) = some ⟨class, Rd, Rn, …⟩` for every
instruction in the proved subset (§6 below).

Because the decoder applies the Arm ARM C7 fixed-width field splits the way
sail-arm's `decode64` is believed to read them (`op_code[hi..lo]`, per the
transcription above), `decode (encode i)` recovering exactly the operands `i`
named means the encoder produces words a decoder built to that discipline maps
back to the same instruction — the encoder's bytes are *proved* to round-trip
under that discipline, and not only matched to `as`.

## The decode discriminants (from `aarch_decode.sail`, ASIMD `decode64`)

A64 ASIMD is **fixed-width**. The "three-same" group (`grp = op_code[28:24] =
0b01110`) holds ADD/SUB/MUL/AND/ORR/EOR, discriminated by `(U[29], size[23:22],
opcode[15:11])`; the "shift-by-immediate" group (`grp = 0b01111`) holds SHL/USHR,
discriminated by `(U[29], opcode[15:11])` with the shift in the `immh:immb`
field `op_code[22:16]`. (`Q[30]=1` throughout: 128-bit `v` registers.) The
register fields are at the same `Rd[4:0] Rn[9:5] Rm[20:16]` positions as the
scalar GP forms, so we reuse `SailArmDecoder.{fldRd,fldRn,fldRm,leWord_wordLE}`.

## Scope of the round-trip (which `NInst` forms are decode-proved)

`decode (encode i) = i` is proved (`roundtrip_ninst_*` below) for exactly:
`ADD`/`SUB`/`MUL` (`.4S`), `AND`/`ORR`/`EOR` (`.16B`, including `MOV` as the
`ORR Vd,Vn,Vn` alias), and `SHL`/`USHR` (`.4S`, by immediate) — the forms
`NeonEncoder.encodeNInst` emits. Two other NEON emitters are **not** covered by
`decodeNeon`: `encodeNInst8x16`'s `SQDMULH.8H` (the ML-KEM NTT high-mul,
`.mulhs`) and `encLdrQ`/`encStrQ`'s `LDR Q`/`STR Q` 128-bit loads and stores —
`decodeWord` has no dispatch case for either group, so those words stay on the
gas-differential/qemu-KAT trust edge (§6 below) rather than this round-trip.

`decodeWord` also never reads `Q[30]` (nor bit[21] or bit[10] of the ASIMD
`opcode` field): the three-same and shift-by-immediate group dispatch uses only
`grp[28:24]`, `U[29]`, `size[23:22]`/`opcode[15:11]` (and `immh:immb` for the
shift amount), so a 64-bit-arrangement word and its 128-bit counterpart that
agree on those bits decode identically — e.g. `0x0ea08400` and `0x4ea08400`
(which differ only in `Q[30]`) both decode as ADD. The round-trip therefore
does not itself certify the `Q=1`/128-bit arrangement of the decoded word, only
that `encodeNInst` happens to always set it.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8000

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.SailNeonDecoder

open CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon
open CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.NeonEncoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder (wordLE)
open CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
  (leWord leWord_wordLE fldRd fldRn fldRm grp)

/-! ## 1. ASIMD-specific field slices

Reuse `Rd[4:0]`, `Rn[9:5]`, `Rm[20:16]`, `grp[28:24]` from `SailArmDecoder`; add
the ASIMD discriminant slices `U[29]`, `size[23:22]`, `opcode[15:11]`, and the
`immh:immb` shift field `op_code[22:16]`. -/

/-- `op_code[29]` — the `U` bit (signed/unsigned, op-family discriminant). -/
def fldU (w : Nat) : Nat := (w / 0x20000000) % 2
/-- `op_code[23:22]` — the `size` field (element size, three-same discriminant). -/
def fldSize (w : Nat) : Nat := (w / 0x400000) % 4
/-- `op_code[15:11]` — the 5-bit ASIMD `opcode` field. -/
def fldOpcode (w : Nat) : Nat := (w / 0x800) % 32
/-- `op_code[22:16]` — the 7-bit `immh:immb` shift field (shift-by-immediate). -/
def fldImmhb (w : Nat) : Nat := (w / 0x10000) % 128

/-! ## 2. The decoded ASIMD instruction-class record -/

/-- The decoded NEON/ASIMD instruction class the round-trip distinguishes. -/
inductive NeonClass where
  /-- ADD (vector, `.4S`). -/
  | add
  /-- SUB (vector, `.4S`). -/
  | sub
  /-- MUL (vector, `.4S`). -/
  | mul
  /-- AND (vector, `.16B`). -/
  | and
  /-- ORR (vector, `.16B`) — also the `MOV` alias when `Rm=Rn`. -/
  | orr
  /-- EOR (vector, `.16B`). -/
  | eor
  /-- SHL (vector, by immediate, `.4S`). -/
  | shl
  /-- USHR (vector, by immediate, `.4S`). -/
  | ushr
  deriving DecidableEq, Repr

/-- A decoded ASIMD instruction: its class plus the recovered operand fields
    (`Rd`, `Rn`, and either `Rm` for the three-register ops or `sh` for the
    shift-by-immediate ops). -/
structure DecNeon where
  cls : NeonClass
  rd : Nat
  rn : Nat
  rm : Nat := 0
  sh : Nat := 0
  deriving DecidableEq, Repr

/-! ## 3. The decoder

`decodeNeon` recovers the 4-byte word (`leWord`), dispatches on the fixed ASIMD
group bits the sail-arm `decode64` clauses match (`grp[28:24]` plus the
discriminating `U`/`size`/`opcode`), and slices the operand fields exactly as the
matched clause does. -/

/-- Decode a 32-bit ASIMD word to its class + operand fields, following the
    sail-arm `decode64` ASIMD clause dispatch and field slices. The three-same
    group (`grp=0x0e`) is split by `(U, size, opcode)`; the shift-by-immediate
    group (`grp=0x0f`) by `(U, opcode)` with the shift recovered from
    `immh:immb`. -/
def decodeWord (w : Nat) : Option DecNeon :=
  if grp w = 0x0e then
    -- three-same group: ADD/SUB/MUL (opcode 0x10/0x13) + AND/ORR/EOR (opcode 0x03)
    if fldU w = 0 ∧ fldSize w = 2 ∧ fldOpcode w = 0x10 then
      some { cls := .add, rd := fldRd w, rn := fldRn w, rm := fldRm w }
    else if fldU w = 1 ∧ fldSize w = 2 ∧ fldOpcode w = 0x10 then
      some { cls := .sub, rd := fldRd w, rn := fldRn w, rm := fldRm w }
    else if fldU w = 0 ∧ fldSize w = 2 ∧ fldOpcode w = 0x13 then
      some { cls := .mul, rd := fldRd w, rn := fldRn w, rm := fldRm w }
    else if fldU w = 0 ∧ fldSize w = 0 ∧ fldOpcode w = 0x03 then
      some { cls := .and, rd := fldRd w, rn := fldRn w, rm := fldRm w }
    else if fldU w = 0 ∧ fldSize w = 2 ∧ fldOpcode w = 0x03 then
      some { cls := .orr, rd := fldRd w, rn := fldRn w, rm := fldRm w }
    else if fldU w = 1 ∧ fldSize w = 0 ∧ fldOpcode w = 0x03 then
      some { cls := .eor, rd := fldRd w, rn := fldRn w, rm := fldRm w }
    else none
  else if grp w = 0x0f then
    -- shift-by-immediate group: SHL (U=0,opcode=0x0a, sh = immhb-32),
    -- USHR (U=1,opcode=0x00, sh = 64-immhb)
    if fldU w = 0 ∧ fldOpcode w = 0x0a then
      some { cls := .shl, rd := fldRd w, rn := fldRn w, sh := fldImmhb w - 32 }
    else if fldU w = 1 ∧ fldOpcode w = 0x00 then
      some { cls := .ushr, rd := fldRd w, rn := fldRn w, sh := 64 - fldImmhb w }
    else none
  else none

/-- Decode a 4-byte little-endian ASIMD instruction stream. -/
def decodeNeon (bs : List (BitVec 8)) : Option DecNeon :=
  (leWord bs).bind decodeWord

/-! ## 4. Field-recovery round-trips on the encoded words

For each encoder family, the decoder recovers exactly the class and operand
fields the encoder put in. The operand bounds (`Rd,Rn,Rm < 32`, the shift in
the canonical range) make the field slices exact: the bit windows do not overlap,
so each slice reads back the planted value. We prove the word value is `< 2^32`
(so `leWord` round-trips), rewrite the class selectors to their literal value,
then the field slices recover the operands. -/

/-! ### Three-same group (ADD/SUB/MUL/AND/ORR/EOR)

Each proof: the encoded word is `base + Rm·0x10000 + Rn·0x20 + Rd` with the base
carrying the group bits (`grp=0x0e`) and the `(U,size,opcode)` discriminants; the
register fields land in the clear low/Rm slots, so the slices read back. -/

/-- **Round-trip for ADD.4S.** -/
theorem roundtrip_add (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeNeon (encVecRRR baseAdd d n m)
      = some { cls := .add, rd := d, rn := n, rm := m } := by
  have hw : baseAdd + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseAdd]; omega
  rw [encVecRRR, decodeNeon, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseAdd + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0e := by simp only [grp, hW, baseAdd]; omega
  have hu : fldU W = 0 := by simp only [fldU, hW, baseAdd]; omega
  have hsz : fldSize W = 2 := by simp only [fldSize, hW, baseAdd]; omega
  have hoc : fldOpcode W = 0x10 := by simp only [fldOpcode, hW, baseAdd]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseAdd]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseAdd]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW, baseAdd]; omega
  rw [decodeWord, hg, hrd, hrn, hrm]; simp [hu, hsz, hoc]

/-- **Round-trip for SUB.4S.** -/
theorem roundtrip_sub (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeNeon (encVecRRR baseSub d n m)
      = some { cls := .sub, rd := d, rn := n, rm := m } := by
  have hw : baseSub + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseSub]; omega
  rw [encVecRRR, decodeNeon, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseSub + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0e := by simp only [grp, hW, baseSub]; omega
  have hu : fldU W = 1 := by simp only [fldU, hW, baseSub]; omega
  have hsz : fldSize W = 2 := by simp only [fldSize, hW, baseSub]; omega
  have hoc : fldOpcode W = 0x10 := by simp only [fldOpcode, hW, baseSub]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseSub]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseSub]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW, baseSub]; omega
  rw [decodeWord, hg, hrd, hrn, hrm]; simp [hu, hsz, hoc]

/-- **Round-trip for MUL.4S.** -/
theorem roundtrip_mul (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeNeon (encVecRRR baseMul d n m)
      = some { cls := .mul, rd := d, rn := n, rm := m } := by
  have hw : baseMul + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseMul]; omega
  rw [encVecRRR, decodeNeon, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseMul + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0e := by simp only [grp, hW, baseMul]; omega
  have hu : fldU W = 0 := by simp only [fldU, hW, baseMul]; omega
  have hsz : fldSize W = 2 := by simp only [fldSize, hW, baseMul]; omega
  have hoc : fldOpcode W = 0x13 := by simp only [fldOpcode, hW, baseMul]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseMul]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseMul]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW, baseMul]; omega
  rw [decodeWord, hg, hrd, hrn, hrm]; simp [hu, hsz, hoc]

/-- **Round-trip for AND.16B.** -/
theorem roundtrip_and (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeNeon (encVecRRR baseAnd d n m)
      = some { cls := .and, rd := d, rn := n, rm := m } := by
  have hw : baseAnd + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseAnd]; omega
  rw [encVecRRR, decodeNeon, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseAnd + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0e := by simp only [grp, hW, baseAnd]; omega
  have hu : fldU W = 0 := by simp only [fldU, hW, baseAnd]; omega
  have hsz : fldSize W = 0 := by simp only [fldSize, hW, baseAnd]; omega
  have hoc : fldOpcode W = 0x03 := by simp only [fldOpcode, hW, baseAnd]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseAnd]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseAnd]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW, baseAnd]; omega
  rw [decodeWord, hg, hrd, hrn, hrm]; simp [hu, hsz, hoc]

/-- **Round-trip for ORR.16B** (also the `MOV Vd,Vn,Vn` alias when `m=n`). -/
theorem roundtrip_orr (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeNeon (encVecRRR baseOrr d n m)
      = some { cls := .orr, rd := d, rn := n, rm := m } := by
  have hw : baseOrr + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseOrr]; omega
  rw [encVecRRR, decodeNeon, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseOrr + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0e := by simp only [grp, hW, baseOrr]; omega
  have hu : fldU W = 0 := by simp only [fldU, hW, baseOrr]; omega
  have hsz : fldSize W = 2 := by simp only [fldSize, hW, baseOrr]; omega
  have hoc : fldOpcode W = 0x03 := by simp only [fldOpcode, hW, baseOrr]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseOrr]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseOrr]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW, baseOrr]; omega
  rw [decodeWord, hg, hrd, hrn, hrm]; simp [hu, hsz, hoc]

/-- **Round-trip for EOR.16B.** -/
theorem roundtrip_eor (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeNeon (encVecRRR baseEor d n m)
      = some { cls := .eor, rd := d, rn := n, rm := m } := by
  have hw : baseEor + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseEor]; omega
  rw [encVecRRR, decodeNeon, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseEor + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0e := by simp only [grp, hW, baseEor]; omega
  have hu : fldU W = 1 := by simp only [fldU, hW, baseEor]; omega
  have hsz : fldSize W = 0 := by simp only [fldSize, hW, baseEor]; omega
  have hoc : fldOpcode W = 0x03 := by simp only [fldOpcode, hW, baseEor]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseEor]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseEor]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW, baseEor]; omega
  rw [decodeWord, hg, hrd, hrn, hrm]; simp [hu, hsz, hoc]

/-! ### Shift-by-immediate group (SHL/USHR)

The shift is in the `immh:immb` field `[22:16]`: for `SHL.4S` it is `32+sh`, for
`USHR.4S` it is `64-sh`; the decoder inverts each (`sh = immhb-32` / `64-immhb`).
We require `sh < 32` (the canonical `.4S` shift range; the ChaCha rotates use
`#7..#25`). -/

/-- **Round-trip for SHL.4S, #sh** (`0 < sh < 32`). -/
theorem roundtrip_shl (d n sh : Nat) (hd : d < 32) (hn : n < 32)
    (hsh0 : 0 < sh) (hsh : sh < 32) :
    decodeNeon (encShl d n sh)
      = some { cls := .shl, rd := d, rn := n, sh := sh } := by
  have hsm : sh % 32 = sh := Nat.mod_eq_of_lt hsh
  have hf : (32 + sh % 32) % 128 = 32 + sh := by rw [hsm]; omega
  have hw : 0x4f005400 + ((32 + sh % 32) % 128) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [hf, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encShl, decodeNeon, leWord_wordLE _ hw, Option.bind_some, hf,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x4f005400 + (32 + sh) * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0f := by simp only [grp, hW]; omega
  have hgn : grp W ≠ 0x0e := by rw [hg]; decide
  have hu : fldU W = 0 := by simp only [fldU, hW]; omega
  have hoc : fldOpcode W = 0x0a := by simp only [fldOpcode, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hib : fldImmhb W = 32 + sh := by simp only [fldImmhb, hW]; omega
  rw [decodeWord, if_neg hgn, hg, hrd, hrn, hib, if_pos rfl, if_pos ⟨hu, hoc⟩,
    show 32 + sh - 32 = sh from by omega]

/-- **Round-trip for USHR.4S, #sh** (`0 < sh < 32`). -/
theorem roundtrip_ushr (d n sh : Nat) (hd : d < 32) (hn : n < 32)
    (hsh0 : 0 < sh) (hsh : sh < 32) :
    decodeNeon (encUshr d n sh)
      = some { cls := .ushr, rd := d, rn := n, sh := sh } := by
  have hsm : sh % 32 = sh := Nat.mod_eq_of_lt hsh
  have hf : (64 - sh % 32) % 128 = 64 - sh := by rw [hsm]; omega
  have hw : 0x6f000400 + ((64 - sh % 32) % 128) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [hf, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encUshr, decodeNeon, leWord_wordLE _ hw, Option.bind_some, hf,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x6f000400 + (64 - sh) * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0f := by simp only [grp, hW]; omega
  have hgn : grp W ≠ 0x0e := by rw [hg]; decide
  have hu : fldU W = 1 := by simp only [fldU, hW]; omega
  have hun : fldU W ≠ 0 := by rw [hu]; decide
  have hoc : fldOpcode W = 0x00 := by simp only [fldOpcode, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hib : fldImmhb W = 64 - sh := by simp only [fldImmhb, hW]; omega
  rw [decodeWord, if_neg hgn, hg, hrd, hrn, hib]
  have hne : ¬ (fldU W = 0 ∧ fldOpcode W = 0x0a) := fun ⟨h, _⟩ => hun h
  rw [if_pos rfl, if_neg hne, if_pos ⟨hu, hoc⟩,
    show 64 - (64 - sh) = sh from by omega]

/-! ## 5. Instruction-level round-trip: `decode (encode i) = i`

Lift the field-level lemmas to the full `NInst`: a `rebuild` reading the
`DecNeon` class + register numbers back into an `NInst` over the *allocated*
register names, and the capstone theorems `roundtrip_ninst_*` proving
`rebuild (decode (encode i)) = i` (on the allocated names) for every arm of the
emitted subset. The register numbers are `< 32` (which `vNum` guarantees), so no
side condition leaks. -/

/-- `vNum` always lands in `0..31` (a 32-entry table with a `0` fallback). -/
theorem vNum_lt_32 (r : String) : vNum r < 32 := by
  unfold vNum
  cases h : (List.range 32).findIdx? (fun i => r = "v" ++ toString i) with
  | none => simp only [Option.getD]; omega
  | some k =>
      have hk : k < (List.range 32).length :=
        (List.findIdx?_eq_some_iff_getElem.mp h).1
      simp only [List.length_range] at hk
      simp only [Option.getD]; omega

/-- The register name (`vN`) for an ASIMD register number `0..31`, the inverse of
    `vNum` on the canonical names. -/
def regName (n : Nat) : String := "v" ++ toString n

/-- Rebuild an `NInst` from a decoded `DecNeon`, mapping register numbers back to
    `vN` names. The `MOV` alias decodes as `orr` with `Rm=Rn`, which `rebuild`
    recognises as a `mov`. -/
def rebuild (dr : DecNeon) : Option NInst :=
  match dr.cls with
  | .add => some (.add (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .sub => some (.sub (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .mul => some (.mul (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .and => some (.and (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .orr =>
      if dr.rm = dr.rn then some (.mov (regName dr.rd) (regName dr.rn))
      else some (.orr (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .eor => some (.eor (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .shl => some (.shl (regName dr.rd) (regName dr.rn) dr.sh)
  | .ushr => some (.ushr (regName dr.rd) (regName dr.rn) dr.sh)

/-- `regName` inverts `vNum` on every name the allocator assigns (the V pool
    `v0 … v31`). Proved by enumerating the finite pool. -/
theorem regName_vNum (r : String) (h : r ∈ vPool) : regName (vNum r) = r := by
  fin_cases h <;> native_decide

/-- **Capstone round-trip for ADD.4S.** -/
theorem roundtrip_ninst_add (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b) :
    (decodeNeon (encodeNInst alloc (.add d a b))).bind rebuild
      = some (.add (vOf alloc d) (vOf alloc a) (vOf alloc b)) := by
  simp only [encodeNInst]
  rw [roundtrip_add _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for SUB.4S. -/
theorem roundtrip_ninst_sub (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b) :
    (decodeNeon (encodeNInst alloc (.sub d a b))).bind rebuild
      = some (.sub (vOf alloc d) (vOf alloc a) (vOf alloc b)) := by
  simp only [encodeNInst]
  rw [roundtrip_sub _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for MUL.4S. -/
theorem roundtrip_ninst_mul (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b) :
    (decodeNeon (encodeNInst alloc (.mul d a b))).bind rebuild
      = some (.mul (vOf alloc d) (vOf alloc a) (vOf alloc b)) := by
  simp only [encodeNInst]
  rw [roundtrip_mul _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for AND.16B. -/
theorem roundtrip_ninst_and (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b) :
    (decodeNeon (encodeNInst alloc (.and d a b))).bind rebuild
      = some (.and (vOf alloc d) (vOf alloc a) (vOf alloc b)) := by
  simp only [encodeNInst]
  rw [roundtrip_and _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for ORR.16B (`b ≠ a`, so it is an `orr` not the `mov` alias). -/
theorem roundtrip_ninst_orr (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b)
    (hne : vNum (vOf alloc b) ≠ vNum (vOf alloc a)) :
    (decodeNeon (encodeNInst alloc (.orr d a b))).bind rebuild
      = some (.orr (vOf alloc d) (vOf alloc a) (vOf alloc b)) := by
  simp only [encodeNInst]
  rw [roundtrip_orr _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuild, if_neg hne]
  rw [hd, ha, hb]

/-- Round-trip for EOR.16B. -/
theorem roundtrip_ninst_eor (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b) :
    (decodeNeon (encodeNInst alloc (.eor d a b))).bind rebuild
      = some (.eor (vOf alloc d) (vOf alloc a) (vOf alloc b)) := by
  simp only [encodeNInst]
  rw [roundtrip_eor _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for MOV.16B (the `ORR Vd, Vn, Vn` alias): decoded with `Rm=Rn`,
    `rebuild` recovers the `mov`. -/
theorem roundtrip_ninst_mov (alloc : VAlloc) (d s : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (hs : regName (vNum (vOf alloc s)) = vOf alloc s) :
    (decodeNeon (encodeNInst alloc (.mov d s))).bind rebuild
      = some (.mov (vOf alloc d) (vOf alloc s)) := by
  simp only [encodeNInst]
  rw [roundtrip_orr _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuild, if_true]
  rw [hd, hs]

/-- Round-trip for SHL.4S, #imm (`0 < imm < 32`; the ChaCha rotates `#7/#8/#12/#16`
    all satisfy this). -/
theorem roundtrip_ninst_shl (alloc : VAlloc) (d a : String) (imm : Nat)
    (himm0 : 0 < imm) (himm : imm < 32)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a) :
    (decodeNeon (encodeNInst alloc (.shl d a imm))).bind rebuild
      = some (.shl (vOf alloc d) (vOf alloc a) imm) := by
  simp only [encodeNInst]
  rw [roundtrip_shl _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) himm0 himm]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha]

/-- Round-trip for USHR.4S, #imm (`0 < imm < 32`). -/
theorem roundtrip_ninst_ushr (alloc : VAlloc) (d a : String) (imm : Nat)
    (himm0 : 0 < imm) (himm : imm < 32)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a) :
    (decodeNeon (encodeNInst alloc (.ushr d a imm))).bind rebuild
      = some (.ushr (vOf alloc d) (vOf alloc a) imm) := by
  simp only [encodeNInst]
  rw [roundtrip_ushr _ _ _ (vNum_lt_32 _) (vNum_lt_32 _) himm0 himm]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha]

/-! ## 6. The owned NEON byte-level trust edge

The proved subset — `ADD`/`SUB`/`MUL` (`.4S`), `AND`/`ORR`/`EOR` (`.16B`, with
`MOV` as the `ORR Vd,Vn,Vn` alias), and `SHL`/`USHR` (`.4S`, by immediate) — is
decode-round-trip-proved against the (hand-transcribed) sail-arm ASIMD
`decode64` field-split discipline, so `aarch64-linux-gnu-as` is out of the
trusted path for exactly those instructions. `SQDMULH.8H` (`encodeNInst8x16`)
and `LDR Q`/`STR Q` (`encLdrQ`/`encStrQ`) are **not** decode-round-trip-proved —
`decodeWord` has no case for either — so they remain on the differential/KAT
trust edge below, same as `as`'s output for the round-trip-proved forms would
be absent this module. The bench differential (an untracked local checkout,
`qr-neon-bytes-diff`, not vendored in this repo) additionally pins the
verified-encoder words byte-identical to `as` on the ChaCha 4-way quarter-round,
and the qemu KAT (`qr-neon-kat`) runs the assembled object on real AArch64. -/

/-- A doc-anchor: the round-trip-proved set is non-empty and includes the ADD
    pilot. -/
theorem trust_edge_pilot (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b) :
    (decodeNeon (encodeNInst alloc (.add d a b))).bind rebuild
      = some (.add (vOf alloc d) (vOf alloc a) (vOf alloc b)) :=
  roundtrip_ninst_add alloc d a b hd ha hb

end CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.SailNeonDecoder
