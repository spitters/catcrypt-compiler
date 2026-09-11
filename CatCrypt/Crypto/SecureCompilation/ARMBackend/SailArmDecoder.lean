/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-!
# Sail-arm decoder round-trip: `decode (encode i) = i` (#533 sub-2)

`ArmEncoder.lean` is the owned `AInst → machine-byte` encoder. Its bench trust
edge is *differential*: each emitted 32-bit word is pinned to what
`aarch64-linux-gnu-as` produces for the same mnemonic (an untracked local
checkout/harness, not vendored in this repo, plus the qemu KAT). That makes
`as`'s unverified encoder part of the trusted base.

This module replaces the differential edge with a **round-trip** against the
AArch64 *decoder* discipline: a Lean decoder `decodeA64` that recovers the
instruction-class fields `(opcode-class, Rd, Rn, Rm/imm)` from a 32-bit
instruction word, and a proof that

```
decodeA64 (encode i) = some ⟨class, Rd, Rn, …⟩      -- the encoded fields
```

for every instruction in the emitted GP-ALU subset. Because the decoder applies
the Arm ARM C4.1 fixed-width field splits the way sail-arm's `decode64` is
believed to read them (`op_code[hi..lo]`, per the transcription below),
`decode (encode i)` recovering exactly the operands `i` named means the encoder
produces words that this transcribed decode discipline maps back to the same
instruction — the encoder's bytes are *proved* to round-trip under that
discipline, and not only matched to `as`.

## Provenance of the transcribed clauses (read this before trusting the edge)

The field splits below are the authors' **hand transcription** of the
[`rems-project/sail-arm`](https://github.com/rems-project/sail-arm) `decode64`
clauses (`arm-v8.5-a/model/aarch_decode.sail`) and the matching Arm ARM C4.1
encoding tables. **This repo vendors no sail-arm checkout**: `bench/` is
untracked, so any local `bench/reference_install/…` path is outside the package
and outside CI. Nothing here is machine-checked against upstream sail-arm — the
transcription is itself a trusted step, auditable by eye against the public
model and the Arm ARM.

## What the sail-arm `decode64` clause is

A64 is **fixed-width**: `decode64 : bits(32) -> …` matches a single 32-bit word
against a fixed-position bit pattern, then slices the operand fields with
`op_code[hi..lo]` (the exact field positions are quoted in `ArmEncoder.lean` and
reproduced field-for-field in `recompose…` below) and dispatches to the
per-instruction execute clause. For the **round-trip** we need only the *parse*
(which bits are operands, and what they mean), and that parse is exactly the
field-slicing the `decode64` clause performs. The execute side (the effect of
each decoded instruction) is the model's `evalAInst` differential KAT
(`ArmLowering.qr_rfc_kat`, RFC 8439 §2.1.1) — so the two together close both
halves: the bytes decode to the right operands (here), and the instruction's
effect is the model semantics (validated against the RFC vector and qemu).

The transcribed field positions (from `aarch_decode.sail`, `decode64`):

| class                | leading bits (`op_code[31..]`) | fields read                  |
|----------------------|--------------------------------|------------------------------|
| ADD/SUB shifted reg  | `_ ?001011 ?? 0 …`             | Rd[4:0] Rn[9:5] imm6[15:10] Rm[20:16] shift[23:22] S[29] op[30] sf[31] |
| AND/ORR/EOR sh. reg  | `_ ??01010 ?? ? …`             | Rd[4:0] Rn[9:5] imm6[15:10] Rm[20:16] N[21] shift[23:22] opc[30:29] sf[31] |
| EXTR (ROR alias)     | `_ 00100111 ? 0 …`             | Rd[4:0] Rn[9:5] imms[15:10] Rm[20:16] o0[21] N[22] op21[30:29] sf[31] |
| UBFM (LSL/LSR alias) | `_ ??100110 …`                 | Rd[4:0] Rn[9:5] imms[15:10] immr[21:16] N[22] opc[30:29] sf[31] |

## Which real-A64 discriminants the decoders do *not* read

The decoders below are *partial*: they classify the words this backend emits,
not all of A64. They read the group selector `[28:24]`, `opc[30:29]`/`op[30]`,
`S[29]`, `[23:21]`, `[21]` (shifted vs extended register, and the logical `N`),
`[22]` (the bitfield/extract `N`) and `[23]` (bitfield vs extract, and move-wide
vs logical-immediate). They do **not** read:

* **`sf[31]`** — the 32/64-bit operand-size bit. `decodeA64` is applied only to
  `encodeAInst` (`W`, `sf=0`) output and `decodeB64` only to `encodeBInst` (`X`,
  `sf=1`) output; a word of the other width would be classified as if it were
  this one. The two decoders are *not* a single A64 decode table.
* **the `SBFM`/`BFM` neighbours of `UBFM`** — `opc=10` is tested, so `SBFM`
  (`00`) and `BFM` (`01`) fall through to `none` rather than being decoded; and
  the 64-bit bitfield `N[22]` (which must be `1` when `sf=1`) is unread there.
* **`MADD`'s `Ra[14:10]` and `o0[15]`** — `MUL` is `MADD …, XZR`; the decoder
  classifies on `[28:24]` + `[23:21]` and drops `Ra`, so `MSUB` (`o0=1`) and a
  `MADD` with `Ra ≠ XZR` would both decode as `madd`/rebuild as `MUL`.
* **`CSEL`'s neighbours** — `[23:21]=100` in `grp=0x1a` also holds `CSINC`/
  `CSINV`/`CSNEG`, split by `op[30]`/`o2[10]`, which the decoder does not read.
* **`UBFM`'s `immr`/`imms` pair, on the rebuild side** — `rebuildB`'s `.ubfmX`
  arm applies the A64 alias rule as a two-way split: `imms = 63` ⇒ `LSR #immr`,
  and *every other* `imms` ⇒ `LSL #((64−immr) mod 64)`. But `LSL #sh` is only
  the `imms = 63 − sh` sub-family; a `UBFX`/bitfield-extract word (any
  `immr`/`imms` with `imms ≠ 63` and `imms ≠ 63 − ((64−immr) mod 64)`) is
  therefore rebuilt as a **bogus `LSL`** rather than rejected. Like the entries
  above this is soundness-preserving for `decode (encode i) = i` (the encoder
  only ever emits the `LSL`/`LSR` alias words), but it is another way the
  rebuild is not a faithful A64 disassembler.

Each of these is a *soundness-preserving* gap for the round-trip theorems (they
only ever claim `decode (encode i) = i` for words the encoder actually built),
but it means the decoder is **not** a faithful full `decode64`.

## Scope of the round-trip (which `AInst` forms are decode-proved)

`decode (encode i) = i` is proved (`roundtrip_ainst_*` below) for **every arm of
`encodeAInst`**: `ADD`/`SUB` (shifted-register), `AND`/`ORR`/`EOR`
(shifted-register), `MOV` (the `ORR Wd, WZR, Ws` alias), `ROR` (the `EXTR`
alias), and `LSR`/`LSL` (the `UBFM` alias). Side conditions: `ORR` needs
`Rn ≠ WZR` (otherwise the word *is* the `MOV` alias, and `roundtrip_ainst_mov`
covers it) and `LSL` needs `0 < sh` (`LSL #0` and `LSR #0` are the same word).
Unlike the x86 capstone — where `MULX`/`ADCX`/`ADOX` had **no** Sail counterpart
(ACL2 `x86isa` omits ADX/BMI2) and stayed `gas`-pinned — the authors believe
**every** instruction the owned ARM backend emits has a sail-arm `decode64`
clause, so there is **no Sail-coverage ceiling** for this subset. That is an
unverified claim about upstream: no sail-arm checkout is vendored here, so
nothing in this tree enumerates upstream's clause set. (The NEON/SVE SIMD A64
forms — the `Vec128` analogue — are out of scope for the scalar backend, the same
way x86's SIMD lives in a separate `Avx512`/`Vec128` module; sail-arm is believed
to model them too, so they are expected to carry no ceiling either.)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8000

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder

/-! ## 1. Field extraction from a 32-bit word (sail-arm `op_code[hi..lo]` slices)

These transcribe the bit slices the `decode64` clauses apply. A field
`op_code[hi .. lo]` of a `BitVec 32` is `(word >>> lo) &&& (2^(hi-lo+1) - 1)`. -/

/-- Reassemble the little-endian 4-byte word into its `Nat` value (the inverse of
    `wordLE`): byte 0 is bits `[7:0]`, byte 3 is `[31:24]`. -/
def leWord (bs : List (BitVec 8)) : Option Nat :=
  match bs with
  | [b0, b1, b2, b3] =>
      some (b0.toNat + b1.toNat * 0x100 + b2.toNat * 0x10000 + b3.toNat * 0x1000000)
  | _ => none

/-! A field `op_code[hi .. lo]` of width `k = hi - lo + 1` is the `Nat` slice
`(w / 2^lo) % 2^k` — `>>> lo` is `/ 2^lo` and `&&& (2^k - 1)` is `% 2^k`. We
write the slices directly in that `div`/`mod` form (equal to the `BitVec` slice
the sail-arm clause computes) so the round-trip arithmetic is omega-friendly. -/

/-- `op_code[4:0]` — the destination register `Rd`. -/
def fldRd (w : Nat) : Nat := w % 32
/-- `op_code[9:5]` — the first source register `Rn`. -/
def fldRn (w : Nat) : Nat := (w / 32) % 32
/-- `op_code[20:16]` — the second source register `Rm`. -/
def fldRm (w : Nat) : Nat := (w / 0x10000) % 32
/-- `op_code[15:10]` — the `imm6`/`imms` 6-bit field. -/
def fldImms (w : Nat) : Nat := (w / 0x400) % 64
/-- `op_code[21:16]` — the `immr` 6-bit field (UBFM). -/
def fldImmr (w : Nat) : Nat := (w / 0x10000) % 64
/-- `op_code[30:29]` — the `opc` 2-bit field (logical / movewide / bitfield). -/
def fldOpc (w : Nat) : Nat := (w / 0x20000000) % 4
/-- `op_code[30]` — the `op` bit (ADD=0/SUB=1 in addsub-shiftedreg). -/
def fldOp30 (w : Nat) : Nat := (w / 0x40000000) % 2
/-- `op_code[21]` — the `N` bit of the logical shifted-register form, the `o0`
    bit of `EXTR`, and the shifted/extended-register split of addsub (`0` =
    shifted). Zero in every form these encoders emit. -/
def fldBit21 (w : Nat) : Nat := (w / 0x200000) % 2
/-- `op_code[22]` — the `N` bit of the bitfield/extract forms (`N = sf`). -/
def fldBit22 (w : Nat) : Nat := (w / 0x400000) % 2
/-- `op_code[23]` — the bitfield(`0`)/extract(`1`) split inside the
    `op_code[28:24] = 10011` group. -/
def fldBit23 (w : Nat) : Nat := (w / 0x800000) % 2

/-! ## 2. The decoded instruction-class record

The fields a fixed-width A64 decode recovers: a class tag, the recovered register
numbers, and (for the bitfield/extract forms) the immediate fields. -/

/-- The decoded A64 instruction class the round-trip distinguishes. -/
inductive A64Class where
  /-- ADD/SUB shifted-register: `op=0` ADD, `op=1` SUB. -/
  | addsub (op : Nat)
  /-- Logical shifted-register: `opc=00` AND, `01` ORR, `10` EOR. -/
  | logical (opc : Nat)
  /-- EXTR (the ROR alias). -/
  | extr
  /-- UBFM (the LSL/LSR alias). -/
  | ubfm
deriving DecidableEq, Repr

/-- A decoded A64 GP-ALU instruction: its class plus the recovered operand
    fields (`Rd`, `Rn`, `Rm`, and the two 6-bit immediates `imms`/`immr`). -/
structure DecA64 where
  cls : A64Class
  rd : Nat
  rn : Nat
  rm : Nat := 0
  imms : Nat := 0
  immr : Nat := 0
deriving DecidableEq, Repr

/-! ## 3. The decoder

`decodeA64` recovers the 4-byte word, dispatches on the fixed leading bits the
sail-arm `decode64` clauses match (`[31:24]` opcode group + the discriminating
`[30:29]`/`op` bits), and slices the operand fields exactly as the matched clause
does. The leading-bit dispatch mirrors the `decode64` pattern constants quoted in
the module docstring. -/

/-- The fixed opcode group `op_code[28:24]` (the 5-bit class selector after `sf`,
    `op`, `S`/`opc`). -/
def grp (w : Nat) : Nat := (w / 0x1000000) % 32

/-- Decode a 32-bit A64 GP-ALU word to its class + operand fields, following the
    sail-arm `decode64` clause dispatch and field slices. -/
def decodeWord (w : Nat) : Option DecA64 :=
  -- ADD/SUB shifted register: [28:24]=01011 (0x0b), [21]=0 (shifted, not extended)
  -- — discriminated by op[30]
  if grp w = 0x0b ∧ fldBit21 w = 0 then
    some { cls := .addsub (fldOp30 w), rd := fldRd w, rn := fldRn w, rm := fldRm w }
  -- Logical shifted register: [28:24]=01010 (0x0a), [21]=0 (N)
  else if grp w = 0x0a ∧ fldBit21 w = 0 then
    some { cls := .logical (fldOpc w), rd := fldRd w, rn := fldRn w, rm := fldRm w }
  -- EXTR: [28:24]=10011 (0x13), [23]=1 (extract), [22]=0 (N), opc[30:29]=00
  else if grp w = 0x13 ∧ fldBit23 w = 1 ∧ fldBit22 w = 0 ∧ fldOpc w = 0 then
    some { cls := .extr, rd := fldRd w, rn := fldRn w, rm := fldRm w, imms := fldImms w }
  -- UBFM: [28:24]=10011 (0x13), [23]=0 (bitfield), [22]=0 (N), opc[30:29]=10 (=2)
  else if grp w = 0x13 ∧ fldBit23 w = 0 ∧ fldBit22 w = 0 ∧ fldOpc w = 2 then
    some { cls := .ubfm, rd := fldRd w, rn := fldRn w, imms := fldImms w, immr := fldImmr w }
  else none

/-- Decode a 4-byte little-endian instruction stream. -/
def decodeA64 (bs : List (BitVec 8)) : Option DecA64 :=
  (leWord bs).bind decodeWord

/-! ## 4. `leWord ∘ wordLE = id` on 32-bit values

The little-endian byte split/recompose round-trips on any `w < 2^32`. -/

/-- `leWord (wordLE w) = some w` for `w < 2^32`: the four `BitVec 8` bytes
    `(w >>> 8i) &&& 0xff` recompose to `w`. -/
theorem leWord_wordLE (w : Nat) (hw : w < 2 ^ 32) : leWord (wordLE w) = some w := by
  simp only [wordLE, List.map_cons, List.map_nil, leWord]
  refine congrArg some ?_
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## 5. Field-recovery on the encoded words

For each encoder family, the decoder recovers exactly the class and operand
fields the encoder put in. The bound on each operand (`Rd,Rn,Rm < 32`,
`imms < 64`) makes the field slices exact: the bit windows do not overlap, so
each `(w / 2^lo) % 2^k` reads back the planted value. We prove the word value is
`< 2^32` (so `leWord` round-trips), rewrite the class selectors `grp`/`fldOpc`
to their literal value (so the `decodeWord` dispatch reduces to the matched
branch without the kernel re-reducing the full word), then the field slices
recover the operands. -/

/-- **Round-trip for ADD/SUB (shifted register).** Decoding `encAddSub op d n m`
    recovers `(addsub op, Rd=d, Rn=n, Rm=m)` for `op<2`, registers `< 32`. -/
theorem roundtrip_addsub (op d n m : Nat) (hop : op < 2) (hd : d < 32) (hn : n < 32)
    (hm : m < 32) :
    decodeA64 (encAddSub op d n m)
      = some { cls := .addsub op, rd := d, rn := n, rm := m } := by
  have hw : (op % 2) * 0x40000000 + 0x0b000000 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
      < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
    omega
  rw [encAddSub, decodeA64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := op * 0x40000000 + 0x0b000000 + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0b := by simp only [grp, hW]; omega
  have hb21 : fldBit21 W = 0 := by simp only [fldBit21, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hop30 : fldOp30 W = op := by simp only [fldOp30, hW]; omega
  rw [decodeWord, hg, hb21, hrd, hrn, hrm, hop30]; simp

/-- **Round-trip for AND/ORR/EOR (shifted register).** Decoding `encLogical opc d n m`
    recovers `(logical opc, Rd=d, Rn=n, Rm=m)` for `opc<4`, registers `< 32`. -/
theorem roundtrip_logical (opc d n m : Nat) (hopc : opc < 4) (hd : d < 32) (hn : n < 32)
    (hm : m < 32) :
    decodeA64 (encLogical opc d n m)
      = some { cls := .logical opc, rd := d, rn := n, rm := m } := by
  have hw : (opc % 4) * 0x20000000 + 0x0a000000 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
      < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hopc, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
    omega
  rw [encLogical, decodeA64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hopc, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := opc * 0x20000000 + 0x0a000000 + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0a := by simp only [grp, hW]; omega
  have hb21 : fldBit21 W = 0 := by simp only [fldBit21, hW]; omega
  have hgn : ¬ (grp W = 0x0b ∧ fldBit21 W = 0) := by
    rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hopc' : fldOpc W = opc := by simp only [fldOpc, hW]; omega
  rw [decodeWord, if_neg hgn, hg, hb21, hrd, hrn, hrm, hopc']; simp

/-- **Round-trip for EXTR (the ROR alias).** Decoding `encExtr d n m imms` recovers
    `(extr, Rd=d, Rn=n, Rm=m, imms=imms)` for registers `< 32`, `imms < 64`. -/
theorem roundtrip_extr (d n m imms : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32)
    (himms : imms < 64) :
    decodeA64 (encExtr d n m imms)
      = some { cls := .extr, rd := d, rn := n, rm := m, imms := imms } := by
  have hw : 0x13800000 + (m % 32) * 0x10000 + (imms % 64) * 0x400 + (n % 32) * 0x20 + (d % 32)
      < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt himms, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
    omega
  rw [encExtr, decodeA64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt himms, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x13800000 + m * 0x10000 + imms * 0x400 + n * 0x20 + d with hW
  have hg : grp W = 0x13 := by simp only [grp, hW]; omega
  have hgc : fldOpc W = 0 := by simp only [fldOpc, hW]; omega
  have hb23 : fldBit23 W = 1 := by simp only [fldBit23, hW]; omega
  have hb22 : fldBit22 W = 0 := by simp only [fldBit22, hW]; omega
  have hgn1 : ¬ (grp W = 0x0b ∧ fldBit21 W = 0) := by
    rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn2 : ¬ (grp W = 0x0a ∧ fldBit21 W = 0) := by
    rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hi : fldImms W = imms := by simp only [fldImms, hW]; omega
  rw [decodeWord, if_neg hgn1, if_neg hgn2, if_pos ⟨hg, hb23, hb22, hgc⟩, hrd, hrn, hrm, hi]

/-- **Round-trip for UBFM (the LSL/LSR alias).** Decoding `encUbfm d n immr imms`
    recovers `(ubfm, Rd=d, Rn=n, imms=imms, immr=immr)` for registers `< 32`,
    `imms, immr < 64`. -/
theorem roundtrip_ubfm (d n immr imms : Nat) (hd : d < 32) (hn : n < 32)
    (himmr : immr < 64) (himms : imms < 64) :
    decodeA64 (encUbfm d n immr imms)
      = some { cls := .ubfm, rd := d, rn := n, imms := imms, immr := immr } := by
  have hw : 0x53000000 + (immr % 64) * 0x10000 + (imms % 64) * 0x400 + (n % 32) * 0x20 + (d % 32)
      < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt himmr, Nat.mod_eq_of_lt himms, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
    omega
  rw [encUbfm, decodeA64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt himmr, Nat.mod_eq_of_lt himms, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x53000000 + immr * 0x10000 + imms * 0x400 + n * 0x20 + d with hW
  have hg : grp W = 0x13 := by simp only [grp, hW]; omega
  have hgc : fldOpc W = 2 := by simp only [fldOpc, hW]; omega
  have hb23 : fldBit23 W = 0 := by simp only [fldBit23, hW]; omega
  have hb22 : fldBit22 W = 0 := by simp only [fldBit22, hW]; omega
  have hgn1 : ¬ (grp W = 0x0b ∧ fldBit21 W = 0) := by
    rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn2 : ¬ (grp W = 0x0a ∧ fldBit21 W = 0) := by
    rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn3 : ¬ (grp W = 0x13 ∧ fldBit23 W = 1 ∧ fldBit22 W = 0 ∧ fldOpc W = 0) := by
    rw [hb23]; rintro ⟨_, h, _⟩; exact absurd h (by decide)
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hi : fldImms W = imms := by simp only [fldImms, hW]; omega
  have hr : fldImmr W = immr := by simp only [fldImmr, hW]; omega
  rw [decodeWord, if_neg hgn1, if_neg hgn2, if_neg hgn3, if_pos ⟨hg, hb23, hb22, hgc⟩,
    hrd, hrn, hi, hr]

/-! ## 6. Instruction-level round-trip: `decode (encode i) = i`

The field-level lemmas above invert each *shape* encoder. We now lift them to the
full `AInst`: a `rebuild` that reads the `DecA64` class + register numbers back
into an `AInst` over the *allocated* register names, and the capstone theorem
`roundtrip_ainst` proving `rebuild (decode (encode i)) = i` (on the allocated
names) for every arm of the emitted subset. The register numbers are GP (`< 32`),
which `wNum` guarantees, so no side condition leaks. -/

/-- `wNum` always lands in the register range `0..31` (`wzr=31`, else a 31-entry
    table with a `0` fallback). Every operand the encoder emits decodes back into
    the `< 32` range the round-trip lemmas require. -/
theorem wNum_lt_32 (r : String) : wNum r < 32 := by
  unfold wNum
  split
  · omega
  · cases h : (List.range 31).findIdx? (fun i => r = "w" ++ toString i) with
    | none => simp only [Option.getD]; omega
    | some k =>
        have hk : k < (List.range 31).length :=
          (List.findIdx?_eq_some_iff_getElem.mp h).1
        simp only [List.length_range] at hk
        simp only [Option.getD]; omega

/-- The register name (`wN`) for an A64 register number `0..31`, the inverse of
    `wNum` on the canonical names (`31 = wzr`). -/
def regName (n : Nat) : String :=
  if n = 31 then "wzr" else "w" ++ toString n

/-- Rebuild an `AInst` from a decoded `DecA64`, mapping register numbers back to
    `wN` names. The `MOV Wd, Ws = ORR Wd, WZR, Ws` alias decodes as
    `logical 1` with `Rn=31`, which `rebuild` recognises as a `mov`. -/
def rebuild (dr : DecA64) : Option AInst :=
  match dr.cls with
  | .addsub 0 => some (.add (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .addsub 1 => some (.sub (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .addsub _ => none
  | .logical 0 => some (.and (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .logical 1 =>
      if dr.rn = 31 then some (.mov (regName dr.rd) (regName dr.rm))
      else some (.orr (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .logical 2 => some (.eor (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .logical _ => none
  | .extr => some (.ror (regName dr.rd) (regName dr.rn) dr.imms)
  | .ubfm =>
      -- imms=31 ⇒ LSR #immr ; else LSL #(32-immr mod 32)
      if dr.imms = 31 then some (.lsr (regName dr.rd) (regName dr.rn) dr.immr)
      else some (.lsl (regName dr.rd) (regName dr.rn) ((32 - dr.immr) % 32))

/-- `regName` inverts `wNum` on every name the allocator assigns: the GP pool
    `gpPool` (`w0 … w17`) plus the zero register `wzr`. (`allocGp` only ever
    emits a `gpPool` name or `wzr`; the `<UNALLOCATED:_>` sentinel is a build-
    rejecting non-name, never a decoded operand.) Proved by enumerating the
    finite pool. -/
theorem regName_wNum (r : String) (h : r ∈ gpPool ++ ["wzr"]) :
    regName (wNum r) = r := by
  fin_cases h <;> native_decide

/-- **The capstone round-trip for the emitted GP-ALU subset.** For every `AOp`
    in the emitted alphabet, encoding it through the allocation and decoding +
    rebuilding recovers the lowered `AInst` over the allocated register names —
    i.e. the encoder's bytes decode back to the same instruction under the
    sail-arm decode discipline, for the full emitted subset. -/
theorem roundtrip_ainst_add (alloc : GpAlloc) (d a b : String)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a)
    (hb : regName (wNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeA64 (encodeAInst alloc (.add d a b))).bind rebuild
      = some (.add (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeAInst]
  rw [roundtrip_addsub 0 _ _ _ (by decide) (wNum_lt_32 _) (wNum_lt_32 _) (wNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for `SUB Wd, Wa, Wb`. -/
theorem roundtrip_ainst_sub (alloc : GpAlloc) (d a b : String)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a)
    (hb : regName (wNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeA64 (encodeAInst alloc (.sub d a b))).bind rebuild
      = some (.sub (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeAInst]
  rw [roundtrip_addsub 1 _ _ _ (by decide) (wNum_lt_32 _) (wNum_lt_32 _) (wNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for `AND Wd, Wa, Wb`. -/
theorem roundtrip_ainst_and (alloc : GpAlloc) (d a b : String)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a)
    (hb : regName (wNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeA64 (encodeAInst alloc (.and d a b))).bind rebuild
      = some (.and (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeAInst]
  rw [roundtrip_logical 0 _ _ _ (by decide) (wNum_lt_32 _) (wNum_lt_32 _) (wNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for `ORR Wd, Wa, Wb` (`a` not `wzr`, so it is an `orr` not the
    `mov` alias). -/
theorem roundtrip_ainst_orr (alloc : GpAlloc) (d a b : String)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a)
    (hb : regName (wNum (gpOf alloc b)) = gpOf alloc b)
    (hane : wNum (gpOf alloc a) ≠ 31) :
    (decodeA64 (encodeAInst alloc (.orr d a b))).bind rebuild
      = some (.orr (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeAInst]
  rw [roundtrip_logical 1 _ _ _ (by decide) (wNum_lt_32 _) (wNum_lt_32 _) (wNum_lt_32 _)]
  simp only [Option.bind_some, rebuild, if_neg hane]
  rw [hd, ha, hb]

/-- Round-trip for `EOR Wd, Wa, Wb`. -/
theorem roundtrip_ainst_eor (alloc : GpAlloc) (d a b : String)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a)
    (hb : regName (wNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeA64 (encodeAInst alloc (.eor d a b))).bind rebuild
      = some (.eor (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeAInst]
  rw [roundtrip_logical 2 _ _ _ (by decide) (wNum_lt_32 _) (wNum_lt_32 _) (wNum_lt_32 _)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha, hb]

/-- Round-trip for `MOV Wd, Ws` (the `ORR Wd, WZR, Ws` alias): decoded with
    `Rn = WZR (31)`, `rebuild` recovers the `mov`. -/
theorem roundtrip_ainst_mov (alloc : GpAlloc) (d s : String)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (hs : regName (wNum (gpOf alloc s)) = gpOf alloc s) :
    (decodeA64 (encodeAInst alloc (.mov d s))).bind rebuild
      = some (.mov (gpOf alloc d) (gpOf alloc s)) := by
  simp only [encodeAInst]
  rw [roundtrip_logical 1 _ _ _ (by decide) (wNum_lt_32 _) (by decide) (wNum_lt_32 _)]
  simp only [Option.bind_some, rebuild, if_true]
  rw [hd, hs]

/-- Round-trip for `ROR Wd, Wa, #imm` (the `EXTR Wd, Wa, Wa, #imm` alias), for a
    shift amount `imm < 32` (the canonical A64 32-bit rotate range; the ChaCha
    rotates `#16/#20/#24/#25` all satisfy this). -/
theorem roundtrip_ainst_ror (alloc : GpAlloc) (d a : String) (imm : Nat) (himm : imm < 32)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a) :
    (decodeA64 (encodeAInst alloc (.ror d a imm))).bind rebuild
      = some (.ror (gpOf alloc d) (gpOf alloc a) imm) := by
  simp only [encodeAInst]
  rw [Nat.mod_eq_of_lt himm,
    roundtrip_extr _ _ _ _ (wNum_lt_32 _) (wNum_lt_32 _) (wNum_lt_32 _) (by omega)]
  simp only [Option.bind_some, rebuild]
  rw [hd, ha]

/-- Round-trip for `LSR Wd, Wa, #imm` (the `UBFM Wd, Wa, #imm, #31` alias), for a
    shift amount `imm < 32`. -/
theorem roundtrip_ainst_lsr (alloc : GpAlloc) (d a : String) (imm : Nat) (himm : imm < 32)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a) :
    (decodeA64 (encodeAInst alloc (.lsr d a imm))).bind rebuild
      = some (.lsr (gpOf alloc d) (gpOf alloc a) imm) := by
  simp only [encodeAInst]
  rw [Nat.mod_eq_of_lt himm,
    roundtrip_ubfm _ _ _ _ (wNum_lt_32 _) (wNum_lt_32 _) (by omega) (by decide)]
  simp only [Option.bind_some, rebuild, if_true]
  rw [hd, ha]

/-- Round-trip for `LSL Wd, Wa, #imm` (the `UBFM Wd, Wa, #((32−imm) mod 32),
    #(31−imm)` alias), for `0 < imm < 32`.

    `imm = 0` is excluded because `LSL #0` and `LSR #0` are the *same* word
    (`UBFM Wd, Wa, #0, #31`), which the A64 preferred-disassembly rule reads as
    `LSR`; `roundtrip_ainst_lsr` covers it. -/
theorem roundtrip_ainst_lsl (alloc : GpAlloc) (d a : String) (imm : Nat)
    (himm0 : 0 < imm) (himm : imm < 32)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a) :
    (decodeA64 (encodeAInst alloc (.lsl d a imm))).bind rebuild
      = some (.lsl (gpOf alloc d) (gpOf alloc a) imm) := by
  simp only [encodeAInst, Nat.mod_eq_of_lt himm]
  rw [Nat.mod_eq_of_lt (show 32 - imm < 32 by omega),
    roundtrip_ubfm _ _ _ _ (wNum_lt_32 _) (wNum_lt_32 _) (by omega) (by omega)]
  simp only [Option.bind_some, rebuild]
  rw [if_neg (show ¬ (31 - imm = 31) by omega), show (32 - (32 - imm)) % 32 = imm by omega,
    hd, ha]

/-! ## 7. The owned-ARM-backend byte-level trust edge after sub-2

`trust_edge` (a doc-only theorem) records the honest tally — and, unlike the x86
capstone, there is **no Sail-coverage ceiling** for the emitted scalar subset:

* **decode-round-trip-proved** (the `as`/gas differential pin is not
  essential): **every arm of `encodeAInst`** — `ADD`/`SUB` (shifted-register,
  `roundtrip_ainst_add`/`_sub`), `AND`/`ORR`/`EOR` (shifted-register,
  `_and`/`_orr`/`_eor`), `MOV` (the `ORR Wd, WZR, Ws` alias, `_mov`), `ROR` (the
  `EXTR` alias, `_ror`), and `LSR`/`LSL` (the `UBFM` alias, `_lsr`/`_lsl`). For
  each, the encoder's 32-bit word is *proved* to decode back to the same
  instruction under the transcribed `decode64` field-split discipline, so `as` is
  out of the trusted path. Two side conditions are inherent to the A64 aliases,
  not gaps: `_orr` assumes `Rn ≠ WZR` (else the word *is* `MOV`, covered by
  `_mov`), and `_lsl` assumes `0 < sh` (`LSL #0` and `LSR #0` are one word,
  covered by `_lsr`).
* **Sail-coverage ceiling: none for this subset — an unverified claim about
  upstream.** The authors believe every instruction the owned ARM backend emits
  has a sail-arm `decode64` clause (A64 is a fixed-width ISA with a uniform
  decode table — there is no ADX/BMI2-style gap the way x86's `MULX`/`ADCX`/
  `ADOX` lacked an ACL2 `x86isa` counterpart), and likewise that sail-arm models
  the NEON/SVE SIMD forms that are out of scope for the *scalar* backend (the
  `Vec128` analogue lives in a separate module). Neither belief is checked here:
  no sail-arm checkout is vendored in this repo, so nothing in this tree
  enumerates upstream's clause set.
* **What this does *not* say.** The decode discipline is a hand transcription
  (no vendored sail-arm; see the provenance section above), and `decodeA64` is a
  partial decoder that leaves `sf[31]`, the `SBFM`/`BFM` neighbours and the
  `MADD`/`CSEL` neighbour fields unread — see "Which real-A64 discriminants the
  decoders do not read". The round-trip is therefore *encoder-side sound*
  (encoded words decode back to themselves), not a claim that these decoders
  classify arbitrary A64 words correctly.

The bench differential (`qr-a64-bytes-diff`) additionally pins the
verified-encoder words byte-identical to `aarch64-linux-gnu-as` on the ChaCha
quarter-round, and the qemu KAT (`qr-a64-kat`) runs the assembled object on real
AArch64 — both in an untracked local checkout/harness, not vendored in this
repo. -/

/-- A doc-anchor: the round-trip-proved set is non-empty and includes the ADD
    pilot — referenced by the module docstring's trust-edge tally. -/
theorem trust_edge_pilot (alloc : GpAlloc) (d a b : String)
    (hd : regName (wNum (gpOf alloc d)) = gpOf alloc d)
    (ha : regName (wNum (gpOf alloc a)) = gpOf alloc a)
    (hb : regName (wNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeA64 (encodeAInst alloc (.add d a b))).bind rebuild
      = some (.add (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) :=
  roundtrip_ainst_add alloc d a b hd ha hb

/-! ## 8. The 64-bit bignum/field decode round-trip (#547)

The same `decode (encode i) = i` discipline for the bignum/field `BInst` subset,
against the matching sail-arm `decode64` clauses (`integer_arithmetic_addsub_*`,
`integer_arithmetic_mul_*`, `integer_conditional_select_*`, `integer_logical_*`,
`MoveWide`, `Bitfield`). Every emitted class has a sail-arm clause (A64 is
uniform-decode), so — as with the scalar subset — there is **no Sail-coverage
ceiling**, and `decode (encode i) = i` is proved for **every arm of
`encodeBInst`** (`roundtrip_binst_*`), axiom-clean. The class-discriminating
fields are at the positions the `decode64` clauses read (the encoder side is
quoted in `ArmEncoder.lean §6`):

| class                  | leading bits           | discriminant            |
|------------------------|------------------------|-------------------------|
| ADD/SUB/ADDS/SUBS (sh) | `1 op S 01011 …`       | `grp=0x0b`, op[30], S[29] |
| ADC/SBC/ADCS/SBCS      | `1 op S 11010000 …`    | `grp=0x1a`, `[23:21]=000`, op[30], S[29] |
| CSEL                   | `1 0 0 11010100 …`     | `grp=0x1a`, `[23:21]=100`, cond[15:12] |
| MADD (MUL)             | `1 0011011 000 …`      | `grp=0x1b`, `[23:21]=000` |
| UMULH                  | `1 0011011 110 …`      | `grp=0x1b`, `[23:21]=110` |
| MOVZ/MOVK              | `1 opc 100101 hw …`    | `grp=0x12`, `[23]=1`, opc[30:29] |
| AND/ORR/EOR (sh. reg)  | `1 opc 01010 00 0 …`   | `grp=0x0a`, `[21]=0`, **opc[30:29]** |
| UBFM (LSR/LSL alias)   | `1 10 100110 1 …`      | `grp=0x13`, `[23]=0`, opc[30:29]=10 |

Three of these groups share a `grp` value with a neighbour, so `grp` alone never
suffices:

* ADC/SBC and CSEL both sit in `grp=0x1a` (`[28:24]=11010`), split by `[23:21]`
  (`000` ⇒ addsub-carry, `100` ⇒ conditional-select) — read via `fldOp23`;
* the bitfield (`UBFM`, `[23]=0`) and extract (`EXTR`, `[23]=1`) groups both sit
  in `grp=0x13`, and move-wide (`[23]=1`) shares `grp=0x12` with logical
  immediate (`[23]=0`) — both split by `fldBit23`;
* AND/ORR/EOR/ANDS all sit in `grp=0x0a` and are split *only* by `opc[30:29]` —
  read via `fldOpc`.

That last split is the one `decodeBignumWide` used to skip: it classified every
`grp=0x0a` word as `ORR`, so `encAndX` and `encEorX` output rebuilt as `MOV`; and
it read `grp=0x13` bitfield words as move-wide, so `encUbfmX` output rebuilt as
`MOVZ`. `roundtrip_andX`/`_orrX`/`_eorX`/`_ubfmX` now pin all four apart.

Two side conditions on the capstones are inherent to the A64 alias rules, not
gaps: `roundtrip_binst_orr` assumes `Rn ≠ XZR` (else the word *is* the `MOV`
alias, covered by `roundtrip_binst_mov`), and `roundtrip_binst_lsl` assumes
`0 < sh` (`LSL #0` and `LSR #0` are the same word, covered by
`roundtrip_binst_lsr`). `decodeB64` does not read `sf[31]` or the bitfield
`N[22]`, and drops `MADD`'s `Ra`/`o0` and `CSEL`'s `op`/`o2` — see the module
docstring's list of unread discriminants. -/

/-- `op_code[29]` — the `S` (flag-setting) bit. -/
def fldS29 (w : Nat) : Nat := (w / 0x20000000) % 2
/-- `op_code[23:21]` — the sub-class selector inside `grp=0x1a` (`000` addsub-carry,
    `100` conditional-select) and `grp=0x1b` (`000` MADD, `110` UMULH). -/
def fldOp23 (w : Nat) : Nat := (w / 0x200000) % 8
/-- `op_code[15:12]` — the 4-bit `cond` field (conditional select). -/
def fldCond (w : Nat) : Nat := (w / 0x1000) % 16

/-- The decoded bignum/field instruction class. -/
inductive B64Class where
  /-- ADD/SUB shifted-register, `X` form: `op` (0 ADD/1 SUB), `S` (flag-setting). -/
  | addsubX (op s : Nat)
  /-- ADC/SBC with carry: `op` (0 ADC/1 SBC), `S`. -/
  | addsubCarry (op s : Nat)
  /-- MADD (the MUL form, `Ra=31`). -/
  | madd
  /-- UMULH. -/
  | umulh
  /-- CSEL: the 4-bit `cond`. -/
  | csel (cond : Nat)
  /-- MOVZ/MOVK wide-immediate: `opc` (2 MOVZ/3 MOVK), `hw`. -/
  | movewide (opc hw : Nat)
  /-- Logical shifted-register, `X` form: `opc=00` AND, `01` ORR (the MOV alias
      when `Rn=XZR`), `10` EOR, `11` ANDS. The `opc[30:29]` field is what splits
      the three ops apart, so it is carried here rather than collapsed. -/
  | logicalX (opc : Nat)
  /-- UBFM, `X` form — the `LSR`/`LSL` alias basis; `immr`/`imms` are read from
      the `DecB64` immediate fields. -/
  | ubfmX
  deriving DecidableEq, Repr

/-- A decoded bignum instruction: class + the recovered operand fields
    (`imms`/`immr` are the two 6-bit bitfield immediates of the UBFM form). -/
structure DecB64 where
  cls : B64Class
  rd : Nat
  rn : Nat := 0
  rm : Nat := 0
  imm16 : Nat := 0
  imms : Nat := 0
  immr : Nat := 0
deriving DecidableEq, Repr

/-- `op_code[20:5]` — the 16-bit `imm16` of MOVZ/MOVK. -/
def fldImm16 (w : Nat) : Nat := (w / 32) % 0x10000
/-- `op_code[22:21]` — the 2-bit `hw` shift selector of MOVZ/MOVK. -/
def fldHw (w : Nat) : Nat := (w / 0x200000) % 4

/-- Decode a 64-bit bignum/field word to its class + operand fields, following
    the sail-arm `decode64` clause dispatch and field slices. -/
def decodeBignumWord (w : Nat) : Option DecB64 :=
  if grp w = 0x0b then
    some { cls := .addsubX (fldOp30 w) (fldS29 w), rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else if grp w = 0x1a ∧ fldOp23 w = 0 then
    some { cls := .addsubCarry (fldOp30 w) (fldS29 w), rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else if grp w = 0x1a ∧ fldOp23 w = 4 then
    some { cls := .csel (fldCond w), rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else if grp w = 0x1b ∧ fldOp23 w = 0 then
    some { cls := .madd, rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else if grp w = 0x1b ∧ fldOp23 w = 6 then
    some { cls := .umulh, rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else none

/-- The three groups `decodeBignumWord` does not cover, in a second decoder.
Both data-processing-immediate groups here have `grp = [28:24]` shared with a
neighbour and are split by the `[23]` bit, which `fldBit23` reads:

* **move-wide immediate** — `[28:23] = 100101`, i.e. `grp = 0x12` with
  `[23] = 1`; `grp = 0x12` with `[23] = 0` is *logical immediate*, a different
  instruction. `MOVZ` is `opc = 10`, `MOVK` `opc = 11`;
* **UBFM (bitfield)** — `[28:23] = 100110`, i.e. `grp = 0x13` with `[23] = 0`
  and `opc[30:29] = 10`; `grp = 0x13` with `[23] = 1` is `EXTR`;
* **logical shifted-register** — `grp = [28:24] = 01010 = 0x0a`, `[21] = 0` (`N`),
  split into AND/ORR/EOR/ANDS by `opc[30:29]` (`00`/`01`/`10`/`11`). The `MOV
  Xd, Xs` alias is `ORR Xd, XZR, Xs`, i.e. `opc = 01` with `Rn = 31`.

`sf[31]` is *not* read here (the `X` forms are what `encodeBInst` emits, and the
`W` forms differ only in `sf`), nor is the bitfield `N[22]`. -/
def decodeBignumWide (w : Nat) : Option DecB64 :=
  if grp w = 0x12 ∧ fldBit23 w = 1 then  -- [28:23]=100101 : move-wide — opc via [30:29]
    some { cls := .movewide (fldOpc w) (fldHw w), rd := fldRd w, imm16 := fldImm16 w }
  else if grp w = 0x13 ∧ fldBit23 w = 0 ∧ fldOpc w = 2 then  -- [28:23]=100110, opc=10 : UBFM
    some { cls := .ubfmX, rd := fldRd w, rn := fldRn w, imms := fldImms w, immr := fldImmr w }
  else if grp w = 0x0a ∧ fldBit21 w = 0 then  -- 64-bit logical shifted-register
    some { cls := .logicalX (fldOpc w), rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else none

/-- The unified bignum decoder: arithmetic/select first, then the
    wide-immediate / bitfield / logical-shifted-register groups. -/
def decodeB64 (bs : List (BitVec 8)) : Option DecB64 :=
  (leWord bs).bind (fun w => (decodeBignumWord w).orElse (fun _ => decodeBignumWide w))

/-! ### Field-recovery round-trips for the bignum encoders

For each `enc*X` family, the decoder recovers exactly the class and operands the
encoder planted. Same arithmetic posture as the scalar lemmas: prove the word is
`< 2^32`, rewrite the discriminating selectors to their literal value, then the
operand slices read back. -/

/-- **Round-trip for ADD/SUB/ADDS/SUBS (shifted register, X form).** -/
theorem roundtrip_addsubX (op s d n m : Nat) (hop : op < 2) (hs : s < 2)
    (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeB64 (encAddSubX op s d n m)
      = some { cls := .addsubX op s, rd := d, rn := n, rm := m } := by
  have hw : 0x80000000 + (op % 2) * 0x40000000 + (s % 2) * 0x20000000 + 0x0b000000
      + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hm,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encAddSubX, decodeB64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x80000000 + op * 0x40000000 + s * 0x20000000 + 0x0b000000
    + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0b := by simp only [grp, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have ho : fldOp30 W = op := by simp only [fldOp30, hW]; omega
  have hss : fldS29 W = s := by simp only [fldS29, hW]; omega
  unfold decodeBignumWord
  rw [hg, hrd, hrn, hrm, ho, hss]
  simp

/-- **Round-trip for ADC/SBC/ADCS/SBCS (add/subtract with carry).** -/
theorem roundtrip_addsubCarry (op s d n m : Nat) (hop : op < 2) (hs : s < 2)
    (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeB64 (encAddSubCarry op s d n m)
      = some { cls := .addsubCarry op s, rd := d, rn := n, rm := m } := by
  have hw : 0x80000000 + (op % 2) * 0x40000000 + (s % 2) * 0x20000000 + 0x1a000000
      + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hm,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encAddSubCarry, decodeB64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x80000000 + op * 0x40000000 + s * 0x20000000 + 0x1a000000
    + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x1a := by simp only [grp, hW]; omega
  have hgn : grp W ≠ 0x0b := by rw [hg]; decide
  have ho23 : fldOp23 W = 0 := by simp only [fldOp23, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have ho : fldOp30 W = op := by simp only [fldOp30, hW]; omega
  have hss : fldS29 W = s := by simp only [fldS29, hW]; omega
  unfold decodeBignumWord
  rw [hg, ho23, hrd, hrn, hrm, ho, hss]
  simp

/-- **Round-trip for CSEL.** -/
theorem roundtrip_csel (d n m cond : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32)
    (hc : cond < 16) :
    decodeB64 (encCsel d n m cond)
      = some { cls := .csel cond, rd := d, rn := n, rm := m } := by
  have hw : 0x9a800000 + (m % 32) * 0x10000 + (cond % 16) * 0x1000
      + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encCsel, decodeB64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x9a800000 + m * 0x10000 + cond * 0x1000 + n * 0x20 + d with hW
  have hg : grp W = 0x1a := by simp only [grp, hW]; omega
  have hgn : grp W ≠ 0x0b := by rw [hg]; decide
  have ho23 : fldOp23 W = 4 := by simp only [fldOp23, hW]; omega
  have ho23n : ¬ (grp W = 0x1a ∧ fldOp23 W = 0) := by rw [ho23]; rintro ⟨_, h⟩; exact absurd h (by decide)
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hcd : fldCond W = cond := by simp only [fldCond, hW]; omega
  unfold decodeBignumWord
  rw [hg, ho23, hrd, hrn, hrm, hcd]
  simp

/-- **Round-trip for MADD (the MUL form).** -/
theorem roundtrip_madd (d n m a : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32)
    (ha : a < 32) :
    decodeB64 (encMadd d n m a)
      = some { cls := .madd, rd := d, rn := n, rm := m } := by
  have hw : 0x9b000000 + (m % 32) * 0x10000 + (a % 32) * 0x400
      + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encMadd, decodeB64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x9b000000 + m * 0x10000 + a * 0x400 + n * 0x20 + d with hW
  have hg : grp W = 0x1b := by simp only [grp, hW]; omega
  have hgn1 : grp W ≠ 0x0b := by rw [hg]; decide
  have hgn2 : ¬ (grp W = 0x1a ∧ fldOp23 W = 0) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn3 : ¬ (grp W = 0x1a ∧ fldOp23 W = 4) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have ho23 : fldOp23 W = 0 := by simp only [fldOp23, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  unfold decodeBignumWord
  rw [hg, ho23, hrd, hrn, hrm]
  simp

/-- **Round-trip for UMULH.** -/
theorem roundtrip_umulh (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeB64 (encUmulh d n m)
      = some { cls := .umulh, rd := d, rn := n, rm := m } := by
  have hw : 0x9bc00000 + (m % 32) * 0x10000 + 31 * 0x400 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encUmulh, decodeB64, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x9bc00000 + m * 0x10000 + 31 * 0x400 + n * 0x20 + d with hW
  have hg : grp W = 0x1b := by simp only [grp, hW]; omega
  have hgn1 : grp W ≠ 0x0b := by rw [hg]; decide
  have hgn2 : ¬ (grp W = 0x1a ∧ fldOp23 W = 0) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn3 : ¬ (grp W = 0x1a ∧ fldOp23 W = 4) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have ho23 : fldOp23 W = 6 := by simp only [fldOp23, hW]; omega
  have ho23n : ¬ (grp W = 0x1b ∧ fldOp23 W = 0) := by rw [ho23]; rintro ⟨_, h⟩; exact absurd h (by decide)
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  unfold decodeBignumWord
  rw [hg, ho23, hrd, hrn, hrm]
  simp

/-- **Round-trip for MOVZ/MOVK (wide immediate, X form).** -/
theorem roundtrip_movWideX (opc d imm16 hw : Nat) (hopc2 : opc = 2 ∨ opc = 3)
    (hd : d < 32) (himm : imm16 < 0x10000) (hhw : hw < 4) :
    decodeB64 (encMovWideX opc d imm16 hw)
      = some { cls := .movewide opc hw, rd := d, imm16 := imm16 } := by
  have hopc : opc < 4 := by omega
  have hw32 : 0x80000000 + (opc % 4) * 0x20000000 + 0x12800000 + (hw % 4) * 0x200000
      + (imm16 % 0x10000) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hopc, Nat.mod_eq_of_lt hhw, Nat.mod_eq_of_lt himm, Nat.mod_eq_of_lt hd]; omega
  rw [encMovWideX, decodeB64, leWord_wordLE _ hw32, Option.bind_some,
    Nat.mod_eq_of_lt hopc, Nat.mod_eq_of_lt hhw, Nat.mod_eq_of_lt himm, Nat.mod_eq_of_lt hd]
  set W := 0x80000000 + opc * 0x20000000 + 0x12800000 + hw * 0x200000
    + imm16 * 0x20 + d with hW
  -- MOVZ/MOVK word: [28:23]=100101 with [23]=1 set by +0x12800000, so
  -- grp[28:24]=10010 = 0x12. `decodeBignumWord` returns none (0x12 ∉ {0x0b,0x1a,0x1b});
  -- `decodeBignumWide` matches the grp=0x12 branch.
  have hg : grp W = 0x12 := by simp only [grp, hW]; rcases hopc2 with h | h <;> subst h <;> omega
  have hb23 : fldBit23 W = 1 := by
    simp only [fldBit23, hW]; rcases hopc2 with h | h <;> subst h <;> omega
  have hgn1 : grp W ≠ 0x0b := by rw [hg]; decide
  have hgn2 : ¬ (grp W = 0x1a ∧ fldOp23 W = 0) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn3 : ¬ (grp W = 0x1a ∧ fldOp23 W = 4) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn5 : ¬ (grp W = 0x1b ∧ fldOp23 W = 0) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn6 : ¬ (grp W = 0x1b ∧ fldOp23 W = 6) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hopcF : fldOpc W = opc := by simp only [fldOpc, hW]; rcases hopc2 with h | h <;> subst h <;> omega
  have hhwF : fldHw W = hw := by simp only [fldHw, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have himmF : fldImm16 W = imm16 := by simp only [fldImm16, hW]; omega
  have hdecW : decodeBignumWord W = none := by
    unfold decodeBignumWord
    rw [if_neg hgn1, if_neg hgn2, if_neg hgn3, if_neg hgn5, if_neg hgn6]
  have hdecWide : decodeBignumWide W
      = some { cls := .movewide opc hw, rd := d, imm16 := imm16 } := by
    unfold decodeBignumWide
    rw [hg, hb23, hopcF, hhwF, hrd, himmF]
    simp
  rw [hdecW, hdecWide]
  rfl

/-- **Round-trip for AND (shifted register, X form).** `opc[30:29] = 00`. -/
theorem roundtrip_andX (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeB64 (encAndX d n m)
      = some { cls := .logicalX 0, rd := d, rn := n, rm := m } := by
  have hw32 : 0x8a000000 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encAndX, decodeB64, leWord_wordLE _ hw32, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0x8a000000 + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0a := by simp only [grp, hW]; omega
  have hb21 : fldBit21 W = 0 := by simp only [fldBit21, hW]; omega
  have hopcF : fldOpc W = 0 := by simp only [fldOpc, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hdecW : decodeBignumWord W = none := by unfold decodeBignumWord; rw [hg]; simp
  have hdecWide : decodeBignumWide W
      = some { cls := .logicalX 0, rd := d, rn := n, rm := m } := by
    unfold decodeBignumWide; rw [hg, hb21, hopcF, hrd, hrn, hrm]; simp
  rw [hdecW, hdecWide]
  rfl

/-- **Round-trip for ORR (shifted register, X form).** `opc[30:29] = 01`. -/
theorem roundtrip_orrX (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeB64 (encOrrX d n m)
      = some { cls := .logicalX 1, rd := d, rn := n, rm := m } := by
  have hw32 : 0xaa000000 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encOrrX, decodeB64, leWord_wordLE _ hw32, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0xaa000000 + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0a := by simp only [grp, hW]; omega
  have hb21 : fldBit21 W = 0 := by simp only [fldBit21, hW]; omega
  have hopcF : fldOpc W = 1 := by simp only [fldOpc, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hdecW : decodeBignumWord W = none := by unfold decodeBignumWord; rw [hg]; simp
  have hdecWide : decodeBignumWide W
      = some { cls := .logicalX 1, rd := d, rn := n, rm := m } := by
    unfold decodeBignumWide; rw [hg, hb21, hopcF, hrd, hrn, hrm]; simp
  rw [hdecW, hdecWide]
  rfl

/-- **Round-trip for EOR (shifted register, X form).** `opc[30:29] = 10`. -/
theorem roundtrip_eorX (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeB64 (encEorX d n m)
      = some { cls := .logicalX 2, rd := d, rn := n, rm := m } := by
  have hw32 : 0xca000000 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]; omega
  rw [encEorX, decodeB64, leWord_wordLE _ hw32, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0xca000000 + m * 0x10000 + n * 0x20 + d with hW
  have hg : grp W = 0x0a := by simp only [grp, hW]; omega
  have hb21 : fldBit21 W = 0 := by simp only [fldBit21, hW]; omega
  have hopcF : fldOpc W = 2 := by simp only [fldOpc, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hdecW : decodeBignumWord W = none := by unfold decodeBignumWord; rw [hg]; simp
  have hdecWide : decodeBignumWide W
      = some { cls := .logicalX 2, rd := d, rn := n, rm := m } := by
    unfold decodeBignumWide; rw [hg, hb21, hopcF, hrd, hrn, hrm]; simp
  rw [hdecW, hdecWide]
  rfl

/-- **Round-trip for UBFM (the LSR/LSL alias basis, X form).** Decoding
    `encUbfmX immr imms n d` recovers `(ubfmX, Rd=d, Rn=n, imms, immr)` for
    registers `< 32` and both 6-bit immediates `< 64`. -/
theorem roundtrip_ubfmX (immr imms n d : Nat) (himmr : immr < 64) (himms : imms < 64)
    (hn : n < 32) (hd : d < 32) :
    decodeB64 (encUbfmX immr imms n d)
      = some { cls := .ubfmX, rd := d, rn := n, imms := imms, immr := immr } := by
  have hw32 : 0xd3400000 + (immr % 64) * 0x10000 + (imms % 64) * 0x400
      + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt himmr, Nat.mod_eq_of_lt himms, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt hd]; omega
  rw [encUbfmX, decodeB64, leWord_wordLE _ hw32, Option.bind_some,
    Nat.mod_eq_of_lt himmr, Nat.mod_eq_of_lt himms, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := 0xd3400000 + immr * 0x10000 + imms * 0x400 + n * 0x20 + d with hW
  have hg : grp W = 0x13 := by simp only [grp, hW]; omega
  have hb23 : fldBit23 W = 0 := by simp only [fldBit23, hW]; omega
  have hopcF : fldOpc W = 2 := by simp only [fldOpc, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hi : fldImms W = imms := by simp only [fldImms, hW]; omega
  have hr : fldImmr W = immr := by simp only [fldImmr, hW]; omega
  have hdecW : decodeBignumWord W = none := by unfold decodeBignumWord; rw [hg]; simp
  have hdecWide : decodeBignumWide W
      = some { cls := .ubfmX, rd := d, rn := n, imms := imms, immr := immr } := by
    unfold decodeBignumWide; rw [hg, hb23, hopcF, hrd, hrn, hi, hr]; simp
  rw [hdecW, hdecWide]
  rfl

/-! ### The capstone: every emitted `BInst` decode-round-trips

`roundtrip_binst` rebuilds the decoded class + register numbers back into the
source `BInst` over the allocated `xN` names. The register numbers are GP
(`< 32`, by `xNum_lt_32`), so no side condition leaks. -/

/-- `xNum` always lands in `0..31`. -/
theorem xNum_lt_32 (r : String) : xNum r < 32 := by
  unfold xNum
  split
  · omega
  · cases h : (List.range 31).findIdx? (fun i => r = "x" ++ toString i) with
    | none => simp only [Option.getD]; omega
    | some k =>
        have hk : k < (List.range 31).length := (List.findIdx?_eq_some_iff_getElem.mp h).1
        simp only [List.length_range] at hk
        simp only [Option.getD]; omega

/-- The `xN` register name for a number `0..31` (`31 = xzr`). -/
def xRegName (n : Nat) : String :=
  if n = 31 then "xzr" else "x" ++ toString n

/-- Rebuild a `BInst` from a decoded `DecB64`, mapping register numbers to `xN`. -/
def rebuildB (dr : DecB64) : Option BInst :=
  match dr.cls with
  | .addsubX 0 0 => some (.add (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .addsubX 1 0 => some (.sub (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .addsubX 0 1 => some (.adds (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .addsubX 1 1 => some (.subs (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .addsubX _ _ => none
  | .addsubCarry 0 0 => some (.adc (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .addsubCarry 1 0 => some (.sbc (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .addsubCarry 0 1 => some (.adcs (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .addsubCarry 1 1 => some (.sbcs (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .addsubCarry _ _ => none
  | .madd => some (.mul (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .umulh => some (.umulh (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .csel 3 => some (.csel (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm) .cc)
  | .csel 2 => some (.csel (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm) .cs)
  | .csel _ => none
  | .movewide 2 _hw => some (.movz (xRegName dr.rd) dr.imm16)  -- hw=0 for movz here
  | .movewide 3 hw => some (.movk (xRegName dr.rd) dr.imm16 hw)
  | .movewide _ _ => none
  | .logicalX 0 => some (.and (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .logicalX 1 =>
      -- `ORR Xd, XZR, Xs` is the `MOV Xd, Xs` alias; any other `Rn` is a real ORR.
      if dr.rn = 31 then some (.mov (xRegName dr.rd) (xRegName dr.rm))
      else some (.orr (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .logicalX 2 => some (.eor (xRegName dr.rd) (xRegName dr.rn) (xRegName dr.rm))
  | .logicalX _ => none  -- `opc=11` is ANDS, outside the emitted alphabet
  | .ubfmX =>
      -- A64 alias rule: `imms=63` ⇒ `LSR #immr`; otherwise `LSL #((64−immr) mod 64)`
      -- (`LSL #sh = UBFM #((64−sh) mod 64), #(63−sh)`).
      if dr.imms = 63 then some (.lsr (xRegName dr.rd) (xRegName dr.rn) dr.immr)
      else some (.lsl (xRegName dr.rd) (xRegName dr.rn) ((64 - dr.immr) % 64))

/-- `xRegName` inverts `xNum` on the bignum register pool (`x0..x17` + `xzr`). -/
theorem xRegName_xNum (r : String)
    (h : r ∈ (List.range 18).map (fun i => "x" ++ toString i) ++ ["xzr"]) :
    xRegName (xNum r) = r := by
  fin_cases h <;> native_decide

/-- **Capstone round-trip for `ADDS`.** -/
theorem roundtrip_binst_adds (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.adds d a b))).bind rebuildB
      = some (.adds (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_addsubX 0 1 _ _ _ (by decide) (by decide)
    (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `ADCS`.** -/
theorem roundtrip_binst_adcs (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.adcs d a b))).bind rebuildB
      = some (.adcs (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_addsubCarry 0 1 _ _ _ (by decide) (by decide)
    (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `SUBS`.** -/
theorem roundtrip_binst_subs (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.subs d a b))).bind rebuildB
      = some (.subs (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_addsubX 1 1 _ _ _ (by decide) (by decide)
    (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `SBCS`.** -/
theorem roundtrip_binst_sbcs (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.sbcs d a b))).bind rebuildB
      = some (.sbcs (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_addsubCarry 1 1 _ _ _ (by decide) (by decide)
    (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `CSEL …, cc`.** -/
theorem roundtrip_binst_csel_cc (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.csel d a b .cc))).bind rebuildB
      = some (.csel (gpOf alloc d) (gpOf alloc a) (gpOf alloc b) .cc) := by
  simp only [encodeBInst, acondNum]
  rw [roundtrip_csel _ _ _ _ (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _) (by decide)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `MUL`.** -/
theorem roundtrip_binst_mul (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.mul d a b))).bind rebuildB
      = some (.mul (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_madd _ _ _ _ (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _) (by decide)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `UMULH`.** -/
theorem roundtrip_binst_umulh (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.umulh d a b))).bind rebuildB
      = some (.umulh (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_umulh _ _ _ (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `MOVZ`.** -/
theorem roundtrip_binst_movz (alloc : GpAlloc) (d : String) (imm16 : Nat)
    (himm : imm16 < 0x10000)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d) :
    (decodeB64 (encodeBInst alloc (.movz d imm16))).bind rebuildB
      = some (.movz (gpOf alloc d) imm16) := by
  simp only [encodeBInst, Nat.mod_eq_of_lt himm]
  rw [roundtrip_movWideX 2 _ _ _ (Or.inl rfl) (xNum_lt_32 _) himm (by decide)]
  simp only [Option.bind_some, rebuildB]; rw [hd]

/-- **Capstone round-trip for `MOVK`.** -/
theorem roundtrip_binst_movk (alloc : GpAlloc) (d : String) (imm16 hw : Nat)
    (himm : imm16 < 0x10000) (hhw : hw < 4)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d) :
    (decodeB64 (encodeBInst alloc (.movk d imm16 hw))).bind rebuildB
      = some (.movk (gpOf alloc d) imm16 hw) := by
  simp only [encodeBInst, Nat.mod_eq_of_lt himm]
  rw [roundtrip_movWideX 3 _ _ _ (Or.inr rfl) (xNum_lt_32 _) himm hhw]
  simp only [Option.bind_some, rebuildB]; rw [hd]

/-- **Capstone round-trip for `ADD`** (the no-flags `S=0` form). -/
theorem roundtrip_binst_add (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.add d a b))).bind rebuildB
      = some (.add (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_addsubX 0 0 _ _ _ (by decide) (by decide)
    (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `SUB`** (the no-flags `S=0` form). -/
theorem roundtrip_binst_sub (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.sub d a b))).bind rebuildB
      = some (.sub (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_addsubX 1 0 _ _ _ (by decide) (by decide)
    (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `ADC`** (carry-in, no flags out). -/
theorem roundtrip_binst_adc (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.adc d a b))).bind rebuildB
      = some (.adc (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_addsubCarry 0 0 _ _ _ (by decide) (by decide)
    (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `SBC`** (borrow-in, no flags out). -/
theorem roundtrip_binst_sbc (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.sbc d a b))).bind rebuildB
      = some (.sbc (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_addsubCarry 1 0 _ _ _ (by decide) (by decide)
    (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `CSEL …, cs`** (the other emitted condition). -/
theorem roundtrip_binst_csel_cs (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.csel d a b .cs))).bind rebuildB
      = some (.csel (gpOf alloc d) (gpOf alloc a) (gpOf alloc b) .cs) := by
  simp only [encodeBInst, acondNum]
  rw [roundtrip_csel _ _ _ _ (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _) (by decide)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `AND`** (`opc=00`, so no `MOV`-alias collision). -/
theorem roundtrip_binst_and (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.and d a b))).bind rebuildB
      = some (.and (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_andX _ _ _ (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `ORR`** (`a` not `xzr`, so it is an `orr` and not
    the `MOV Xd, Xs = ORR Xd, XZR, Xs` alias). -/
theorem roundtrip_binst_orr (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b)
    (hane : xNum (gpOf alloc a) ≠ 31) :
    (decodeB64 (encodeBInst alloc (.orr d a b))).bind rebuildB
      = some (.orr (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_orrX _ _ _ (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB, if_neg hane]; rw [hd, ha, hb]

/-- **Capstone round-trip for `EOR`.** -/
theorem roundtrip_binst_eor (alloc : GpAlloc) (d a b : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a)
    (hb : xRegName (xNum (gpOf alloc b)) = gpOf alloc b) :
    (decodeB64 (encodeBInst alloc (.eor d a b))).bind rebuildB
      = some (.eor (gpOf alloc d) (gpOf alloc a) (gpOf alloc b)) := by
  simp only [encodeBInst]
  rw [roundtrip_eorX _ _ _ (xNum_lt_32 _) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]; rw [hd, ha, hb]

/-- **Capstone round-trip for `MOV`** (the `ORR Xd, XZR, Xs` alias): decoded with
    `Rn = XZR (31)`, which `rebuildB` reads back as the `mov`. -/
theorem roundtrip_binst_mov (alloc : GpAlloc) (d s : String)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (hs : xRegName (xNum (gpOf alloc s)) = gpOf alloc s) :
    (decodeB64 (encodeBInst alloc (.mov d s))).bind rebuildB
      = some (.mov (gpOf alloc d) (gpOf alloc s)) := by
  simp only [encodeBInst]
  rw [roundtrip_orrX _ _ _ (xNum_lt_32 _) (by decide) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB, if_true]; rw [hd, hs]

/-- **Capstone round-trip for `LSR`** (the `UBFM Xd, Xn, #sh, #63` alias), for a
    shift amount `sh < 64` (the 64-bit range). -/
theorem roundtrip_binst_lsr (alloc : GpAlloc) (d a : String) (sh : Nat) (hsh : sh < 64)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a) :
    (decodeB64 (encodeBInst alloc (.lsr d a sh))).bind rebuildB
      = some (.lsr (gpOf alloc d) (gpOf alloc a) sh) := by
  simp only [encodeBInst, Nat.mod_eq_of_lt hsh]
  rw [roundtrip_ubfmX _ _ _ _ hsh (by decide) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB, if_true]; rw [hd, ha]

/-- **Capstone round-trip for `LSL`** (the `UBFM Xd, Xn, #((64−sh) mod 64),
    #(63−sh)` alias), for `0 < sh < 64`.

    `sh = 0` is excluded, not an artefact: `LSL #0` and `LSR #0` encode
    to the *same* word `UBFM Xd, Xn, #0, #63`, and the A64 preferred-disassembly
    rule reads `imms = 63` as `LSR`. At `sh = 0` the two are the same instruction
    (a plain move of `Xn` into `Xd`), so the decoder cannot — and need not —
    recover which mnemonic the source used; `roundtrip_binst_lsr` covers that
    word. -/
theorem roundtrip_binst_lsl (alloc : GpAlloc) (d a : String) (sh : Nat)
    (hsh0 : 0 < sh) (hsh : sh < 64)
    (hd : xRegName (xNum (gpOf alloc d)) = gpOf alloc d)
    (ha : xRegName (xNum (gpOf alloc a)) = gpOf alloc a) :
    (decodeB64 (encodeBInst alloc (.lsl d a sh))).bind rebuildB
      = some (.lsl (gpOf alloc d) (gpOf alloc a) sh) := by
  simp only [encodeBInst, Nat.mod_eq_of_lt hsh]
  rw [Nat.mod_eq_of_lt (show 64 - sh < 64 by omega),
    roundtrip_ubfmX _ _ _ _ (by omega) (by omega) (xNum_lt_32 _) (xNum_lt_32 _)]
  simp only [Option.bind_some, rebuildB]
  rw [if_neg (show ¬ (63 - sh = 63) by omega), show (64 - (64 - sh)) % 64 = sh by omega,
    hd, ha]

/-! ## 9. The branch / control-flow decode round-trip (the looped-emission edge, #551)

The same `decode (encode i) = i` discipline for the three branch forms the looped
emission uses (`encB`/`encBcond`/`encCmpBranch`), against the sail-arm `decode64`
branch clauses (`Branch_uncond`, `Branch_cond`, `CompareAndBranch`). These are
fixed-position immediate forms read from the top opcode bits:

| class            | leading bits        | fields                                  |
|------------------|---------------------|-----------------------------------------|
| B (uncond imm)   | `000101 …` (`0x14`) | `imm26[25:0]`                           |
| B.cond (cond imm)| `01010100 …` (`0x54`)| `imm19[23:5] cond[3:0]`                |
| CBNZ/CBZ (W)     | `0 011010 op …` (`0x34/0x35`) | `op[24] imm19[23:5] Rt[4:0]` |

Every emitted branch has a sail-arm `decode64` clause (A64 is uniform-decode), so
— as with the GP-ALU and bignum subsets — there is **no Sail-coverage ceiling**:
the looped-emission branch alphabet is decode-round-trip-proved, axiom-clean. The
`imm19`/`imm26` field recovers the *signed-masked* PC offset the encoder planted
(the assembler's `(target − here)/4`); we round-trip the planted field bits. -/

/-- `op_code[31:26]` — the 6-bit top opcode (the branch-group selector). -/
def fldTop6 (w : Nat) : Nat := w / 0x4000000
/-- `op_code[25:0]` — the 26-bit `imm26` of the unconditional `B`. -/
def fldImm26 (w : Nat) : Nat := w % 0x4000000
/-- `op_code[23:5]` — the 19-bit `imm19` of `B.cond`/`CBNZ`/`CBZ`. -/
def fldImm19 (w : Nat) : Nat := (w / 0x20) % 0x80000
/-- `op_code[3:0]` — the 4-bit `cond` of `B.cond`. -/
def fldCond4 (w : Nat) : Nat := w % 16
/-- `op_code[24]` — the `op` bit of `CBNZ`(1)/`CBZ`(0). -/
def fldCbOp (w : Nat) : Nat := (w / 0x1000000) % 2
/-- `op_code[30:25]` — the compare-and-branch group selector (`0b011010 = 0x1a`). -/
def fldCbGrp (w : Nat) : Nat := (w / 0x2000000) % 64

/-- The decoded branch instruction class. -/
inductive BranchClass where
  /-- Unconditional `B`, with the recovered `imm26`. -/
  | b (imm26 : Nat)
  /-- Conditional `B.cond`, with `cond` and `imm19`. -/
  | bcond (cond imm19 : Nat)
  /-- `CBNZ`(op=1)/`CBZ`(op=0), with `Rt` and `imm19`. -/
  | cmpbr (op rt imm19 : Nat)
  deriving DecidableEq, Repr

/-- Decode a 32-bit branch word to its class + immediate/register fields,
    following the sail-arm `decode64` branch-clause dispatch. -/
def decodeBranchWord (w : Nat) : Option BranchClass :=
  if fldTop6 w = 0x05 then               -- 000101 ⇒ unconditional B
    some (.b (fldImm26 w))
  else if w / 0x1000000 = 0x54 then      -- 01010100 ⇒ B.cond
    some (.bcond (fldCond4 w) (fldImm19 w))
  else if fldCbGrp w = 0x1a then         -- 0 011010 ⇒ compare-and-branch (W form, sf=0)
    some (.cmpbr (fldCbOp w) (w % 32) (fldImm19 w))
  else none

/-- Decode a 4-byte little-endian branch stream. -/
def decodeBranch (bs : List (BitVec 8)) : Option BranchClass :=
  (leWord bs).bind decodeBranchWord

/-- **Round-trip for `B`.** Decoding `encB imm26` recovers `(b imm26)` for
    `imm26 < 2^26`. -/
theorem roundtrip_b (imm26 : Nat) (h : imm26 < 0x4000000) :
    decodeBranch (encB imm26) = some (.b imm26) := by
  have hw : 0x14000000 + (imm26 % 0x4000000) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt h]; omega
  rw [encB, decodeBranch, leWord_wordLE _ hw, Option.bind_some, Nat.mod_eq_of_lt h]
  set W := 0x14000000 + imm26 with hW
  have ht : fldTop6 W = 0x05 := by simp only [fldTop6, hW]; omega
  have hi : fldImm26 W = imm26 := by simp only [fldImm26, hW]; omega
  rw [decodeBranchWord, if_pos ht, hi]

/-- **Round-trip for `B.cond`.** Decoding `encBcond cond imm19` recovers
    `(bcond cond imm19)` for `cond < 16`, `imm19 < 2^19`. -/
theorem roundtrip_bcond (cond imm19 : Nat) (hc : cond < 16) (hi : imm19 < 0x80000) :
    decodeBranch (encBcond cond imm19) = some (.bcond cond imm19) := by
  have hw : 0x54000000 + (imm19 % 0x80000) * 0x20 + (cond % 16) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hi]; omega
  rw [encBcond, decodeBranch, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hi]
  set W := 0x54000000 + imm19 * 0x20 + cond with hW
  have htn : fldTop6 W ≠ 0x05 := by simp only [fldTop6, hW]; omega
  have ht : W / 0x1000000 = 0x54 := by simp only [hW]; omega
  have hcd : fldCond4 W = cond := by simp only [fldCond4, hW]; omega
  have him : fldImm19 W = imm19 := by simp only [fldImm19, hW]; omega
  rw [decodeBranchWord, if_neg htn, if_pos ht, hcd, him]

/-- **Round-trip for `CBNZ`/`CBZ`.** Decoding `encCmpBranch op t imm19` recovers
    `(cmpbr op t imm19)` for `op < 2`, `t < 32`, `imm19 < 2^19`. -/
theorem roundtrip_cmpbr (op t imm19 : Nat) (hop : op < 2) (ht : t < 32)
    (hi : imm19 < 0x80000) :
    decodeBranch (encCmpBranch op t imm19) = some (.cmpbr op t imm19) := by
  have hw : 0x34000000 + (op % 2) * 0x1000000 + (imm19 % 0x80000) * 0x20 + (t % 32)
      < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt ht]; omega
  rw [encCmpBranch, decodeBranch, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hop, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt ht]
  set W := 0x34000000 + op * 0x1000000 + imm19 * 0x20 + t with hW
  have htn : fldTop6 W ≠ 0x05 := by simp only [fldTop6, hW]; omega
  have ht54 : W / 0x1000000 ≠ 0x54 := by simp only [hW]; omega
  have hgrp : fldCbGrp W = 0x1a := by simp only [fldCbGrp, hW]; omega
  have hop' : fldCbOp W = op := by simp only [fldCbOp, hW]; omega
  have hrt : W % 32 = t := by simp only [hW]; omega
  have him : fldImm19 W = imm19 := by simp only [fldImm19, hW]; omega
  rw [decodeBranchWord, if_neg htn, if_neg ht54, if_pos hgrp, hop', hrt, him]

/-! ### Instruction-level branch round-trip: `decode (encode i) = i`

`rebuildBranch` reads a `BranchClass` back into an `ABranch` over the target label
`l` (the label is the assembler symbol the encoder's `resolve` mapped to the
recovered offset; the round-trip recovers the *form* and operands — the branch
kind, the condition, and the counter register — for a fixed resolved offset). The
register the `CBNZ` tests is recovered through `regName ∘ wNum`, the same
inversion the GP-ALU capstone uses. -/

/-- Rebuild an `ABranch` from a decoded `BranchClass`, over the target label `l`.
    `CBNZ`/`CBZ` map their `op` bit back to the kind and `regName` the counter. -/
def rebuildBranch (l : ALabel) (bc : BranchClass) : Option ABranch :=
  match bc with
  | .b _ => some (.b l)
  | .bcond cond _ =>
      match cond with
      | 0 => some (.bcond .eq l)
      | 1 => some (.bcond .ne l)
      | 2 => some (.bcond .cs l)
      | 3 => some (.bcond .cc l)
      | _ => none
  | .cmpbr 1 rt _ => some (.cbnz (regName rt) l)
  | .cmpbr 0 rt _ => some (.cbz (regName rt) l)
  | .cmpbr _ _ _ => none

/-- **Capstone round-trip for the `CBNZ` counter back-edge.** Decoding +
    rebuilding the encoded `CBNZ Wt, l` recovers the `cbnz` over the allocated
    counter register — the looped-emission back-edge's bytes decode back to the
    same instruction under the sail-arm branch-decode discipline. -/
theorem roundtrip_abranch_cbnz (alloc : GpAlloc) (t l : String) (resolve : ALabel → Nat)
    (hres : resolve l < 0x80000)
    (ht : regName (wNum (gpOf alloc t)) = gpOf alloc t) :
    (decodeBranch (encodeABranch alloc resolve (.cbnz t l))).bind (rebuildBranch l)
      = some (.cbnz (gpOf alloc t) l) := by
  simp only [encodeABranch]
  rw [roundtrip_cmpbr 1 _ _ (by decide) (wNum_lt_32 _) hres]
  simp only [Option.bind_some, rebuildBranch]; rw [ht]

/-- **Capstone round-trip for the unconditional `B`.** -/
theorem roundtrip_abranch_b (alloc : GpAlloc) (l : String) (resolve : ALabel → Nat)
    (hres : resolve l < 0x4000000) :
    (decodeBranch (encodeABranch alloc resolve (.b l))).bind (rebuildBranch l)
      = some (.b l) := by
  simp only [encodeABranch]
  rw [roundtrip_b _ hres]; simp [rebuildBranch]

/-- **Capstone round-trip for the conditional back-edge `B.ne`.** -/
theorem roundtrip_abranch_bne (alloc : GpAlloc) (l : String) (resolve : ALabel → Nat)
    (hres : resolve l < 0x80000) :
    (decodeBranch (encodeABranch alloc resolve (.bcond .ne l))).bind (rebuildBranch l)
      = some (.bcond .ne l) := by
  simp only [encodeABranch, BCond.num]
  rw [roundtrip_bcond 1 _ (by decide) hres]; simp [rebuildBranch]

end CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
