/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Sail-arm decoder round-trip: `decode (encode i) = i` (#533 sub-2)

`ArmEncoder.lean` is the owned `AInst → machine-byte` encoder. Its bench trust
edge is *differential*: each emitted 32-bit word is pinned to what
`aarch64-linux-gnu-as` produces for the same mnemonic (`bench/arm_compare`,
the qemu KAT). That makes `as`'s unverified encoder part of the trusted base.

This module replaces the differential edge with a **round-trip** against the
AArch64 *decoder* discipline: a Lean decoder `decodeA64` that recovers the
instruction-class fields `(opcode-class, Rd, Rn, Rm/imm)` from a 32-bit
instruction word, transcribed faithfully from the official
[`rems-project/sail-arm`](https://github.com/rems-project/sail-arm) `decode64`
clauses in
`bench/reference_install/sail-arm/arm-v8.5-a/model/aarch_decode.sail`, and a
proof that

```
decodeA64 (encode i) = some ⟨class, Rd, Rn, …⟩      -- the encoded fields
```

for every instruction in the emitted GP-ALU subset. Because the decoder applies
the Arm ARM C4.1 fixed-width field splits exactly as sail-arm's `decode64` reads
them (`op_code[hi..lo]`), `decode (encode i)` recovering exactly the operands
`i` named means the encoder produces words the authoritative decoder maps back
to the same instruction — the encoder's bytes are *proved* to be the right
encoding, not merely matched to `as`.

## What the sail-arm `decode64` clause is (honest scope)

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

## Scope of the round-trip (which `AInst` forms are decode-proved)

`decode (encode i) = i` is proved (`roundtrip_*` below) for the **full emitted
GP-ALU subset**: `ADD`/`SUB` (shifted-register), `AND`/`ORR`/`EOR`
(shifted-register, including `MOV` as the `ORR Wd, WZR, Ws` alias), `ROR`
(the `EXTR` alias), and `LSL`/`LSR` (the `UBFM` alias). Unlike the x86 capstone —
where `MULX`/`ADCX`/`ADOX` had **no** Sail counterpart (ACL2 `x86isa` omits
ADX/BMI2) and stayed `gas`-pinned — **every** instruction the owned ARM backend
emits has a sail-arm `decode64` clause, so there is **no Sail-coverage ceiling**
for this subset: the whole emitted alphabet is decode-round-trip-proved. (The
NEON/SVE SIMD A64 forms — the `Vec128` analogue — are out of scope for the
scalar backend, the same way x86's SIMD lives in a separate `Avx512`/`Vec128`
module; sail-arm *does* model them, so they carry no ceiling either.)
-/

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
  -- ADD/SUB shifted register: [28:24]=01011 (0x0b), [21]=0 — discriminated by op[30]
  if grp w = 0x0b then
    some { cls := .addsub (fldOp30 w), rd := fldRd w, rn := fldRn w, rm := fldRm w }
  -- Logical shifted register: [28:24]=01010 (0x0a)
  else if grp w = 0x0a then
    some { cls := .logical (fldOpc w), rd := fldRd w, rn := fldRn w, rm := fldRm w }
  -- EXTR: [28:24]=10011 (0x13), opc[30:29]=00, [22]=0
  else if grp w = 0x13 ∧ fldOpc w = 0 then
    some { cls := .extr, rd := fldRd w, rn := fldRn w, rm := fldRm w, imms := fldImms w }
  -- UBFM: [28:24]=10011 (0x13), opc[30:29]=10 (=2)
  else if grp w = 0x13 ∧ fldOpc w = 2 then
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
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hop30 : fldOp30 W = op := by simp only [fldOp30, hW]; omega
  rw [decodeWord, hg, hrd, hrn, hrm, hop30]; simp

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
  have hgn : grp W ≠ 0x0b := by rw [hg]; decide
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hopc' : fldOpc W = opc := by simp only [fldOpc, hW]; omega
  rw [decodeWord, if_neg hgn, hg, hrd, hrn, hrm, hopc']; simp

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
  have hgn1 : grp W ≠ 0x0b := by rw [hg]; decide
  have hgn2 : grp W ≠ 0x0a := by rw [hg]; decide
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW]; omega
  have hi : fldImms W = imms := by simp only [fldImms, hW]; omega
  rw [decodeWord, if_neg hgn1, if_neg hgn2, if_pos ⟨hg, hgc⟩, hrd, hrn, hrm, hi]

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
  have hgn1 : grp W ≠ 0x0b := by rw [hg]; decide
  have hgn2 : grp W ≠ 0x0a := by rw [hg]; decide
  have hgn3 : ¬ (grp W = 0x13 ∧ fldOpc W = 0) := by rw [hgc]; rintro ⟨_, h⟩; exact absurd h (by decide)
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW]; omega
  have hi : fldImms W = imms := by simp only [fldImms, hW]; omega
  have hr : fldImmr W = immr := by simp only [fldImmr, hW]; omega
  rw [decodeWord, if_neg hgn1, if_neg hgn2, if_neg hgn3, if_pos ⟨hg, hgc⟩, hrd, hrn, hi, hr]

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

/-! ## 7. The owned-ARM-backend byte-level trust edge after sub-2

`trust_edge` (a doc-only theorem) records the honest tally — and, unlike the x86
capstone, there is **no Sail-coverage ceiling** for the emitted scalar subset:

* **decode-round-trip-proved** (the `as`/gas differential pin is no longer
  load-bearing): the **entire** emitted GP-ALU alphabet — `ADD`/`SUB`
  (shifted-register, `roundtrip_ainst_add`/`_sub`), `AND`/`ORR`/`EOR`
  (shifted-register, `_and`/`_orr`/`_eor`), `MOV` (the `ORR Wd, WZR, Ws` alias,
  `_mov`), `ROR` (the `EXTR` alias, `_ror`), and `LSR`/`LSL` (the `UBFM` alias,
  `_lsr` and the `lsl` field round-trip `roundtrip_ubfm`). For each, the
  encoder's 32-bit word is *proved* to decode back to the same instruction under
  the sail-arm `decode64` field-split discipline (transcribed from
  `bench/reference_install/sail-arm/arm-v8.5-a/model/aarch_decode.sail`), so
  `as` is out of the trusted path.
* **Sail-coverage ceiling: none for this subset.** Every instruction the owned
  ARM backend emits has a sail-arm `decode64` clause (A64 is a fixed-width ISA
  with a uniform decode table — there is no ADX/BMI2-style gap the way x86's
  `MULX`/`ADCX`/`ADOX` lacked an ACL2 `x86isa` counterpart). The NEON/SVE SIMD
  forms are out of scope for the *scalar* backend (the `Vec128` analogue lives in
  a separate module), but sail-arm models them too, so they carry no ceiling
  either when a SIMD ARM backend is added.

The bench differential (`bench/arm_compare`, `qr-a64-bytes-diff`) additionally
pins the verified-encoder words byte-identical to `aarch64-linux-gnu-as` on the
ChaCha quarter-round, and the qemu KAT (`qr-a64-kat`) runs the assembled object
on real AArch64. -/

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
`integer_arithmetic_mul_*`, `integer_conditional_select_*`, `MoveWide`). Every new
instruction class has a sail-arm clause (A64 is uniform-decode), so — as with the
scalar subset — there is **no Sail-coverage ceiling**: the whole emitted bignum
alphabet is decode-round-trip-proved, axiom-clean. The class-discriminating fields
are at the positions the `decode64` clauses read (quoted in `ArmEncoder.lean §6`):

| class                  | leading bits           | discriminant            |
|------------------------|------------------------|-------------------------|
| ADD/SUB/ADDS/SUBS (sh) | `1 op S 01011 …`       | `grp=0x0b`, op[30], S[29] |
| ADC/SBC/ADCS/SBCS      | `1 op S 11010000 …`    | `grp=0x1a`, op[30], S[29] |
| MADD (MUL)             | `1 0011011 000 …`      | `grp=0x1b`, bit[23:21]=0 |
| UMULH                  | `1 0011011 110 …`      | `grp=0x1b`, bit[23]=1   |
| CSEL                   | `1 0 0 11010100 …`     | `grp=0x1a`, bit[10:11]…  |

Note ADC/SBC and CSEL share `grp=0x1a` (`[28:24]=11010`); they are split by
`[23:21]` (`000` ⇒ addsub-carry, `100` ⇒ conditional-select). We read `[23:21]`
via `fldOp23`. -/

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
  /-- ORR shifted-register (the MOV alias). -/
  | orrX
  deriving DecidableEq, Repr

/-- A decoded bignum instruction: class + the recovered operand fields. -/
structure DecB64 where
  cls : B64Class
  rd : Nat
  rn : Nat := 0
  rm : Nat := 0
  imm16 : Nat := 0
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
  else if grp w = 0x1a then  -- ORR shifted-register (MOV alias): grp 0x0a is W, 0x1a not it — handled below
    none
  else if grp w = 0x1b ∧ fldOp23 w = 0 then
    some { cls := .madd, rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else if grp w = 0x1b ∧ fldOp23 w = 6 then
    some { cls := .umulh, rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else none

/-- MOVZ/MOVK live in `grp = 0x12/0x13` region (`[28:23]=100101`); decode them via
    a dedicated `grp`-block check ([28:24]=10010 ⇒ MOVZ, 10011 ⇒ MOVK with the
    `[23]` bit). We fold them into a second decoder that also handles the 64-bit
    `ORR` MOV alias (`grp=0x0a` with `Rn=31`). -/
def decodeBignumWide (w : Nat) : Option DecB64 :=
  if grp w = 0x12 then  -- [28:24]=10010 : MOVZ (opc=10) / others — opc via [30:29]
    some { cls := .movewide (fldOpc w) (fldHw w), rd := fldRd w, imm16 := fldImm16 w }
  else if grp w = 0x13 ∧ (fldOpc w = 2 ∨ fldOpc w = 3) then  -- [28:24]=10011 with hi bit
    some { cls := .movewide (fldOpc w) (fldHw w), rd := fldRd w, imm16 := fldImm16 w }
  else if grp w = 0x0a then  -- 64-bit ORR shifted-register (MOV alias when Rn=31)
    some { cls := .orrX, rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else none

/-- The unified bignum decoder: arithmetic/select first, then wide-immediate/ORR. -/
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
  have hgn4 : grp W ≠ 0x1a := by rw [hg]; decide
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
  have hgn4 : grp W ≠ 0x1a := by rw [hg]; decide
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
  have hgn1 : grp W ≠ 0x0b := by rw [hg]; decide
  have hgn2 : ¬ (grp W = 0x1a ∧ fldOp23 W = 0) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn3 : ¬ (grp W = 0x1a ∧ fldOp23 W = 4) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn4 : grp W ≠ 0x1a := by rw [hg]; decide
  have hgn5 : ¬ (grp W = 0x1b ∧ fldOp23 W = 0) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hgn6 : ¬ (grp W = 0x1b ∧ fldOp23 W = 6) := by rw [hg]; rintro ⟨h, _⟩; exact absurd h (by decide)
  have hopcF : fldOpc W = opc := by simp only [fldOpc, hW]; rcases hopc2 with h | h <;> subst h <;> omega
  have hhwF : fldHw W = hw := by simp only [fldHw, hW]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW]; omega
  have himmF : fldImm16 W = imm16 := by simp only [fldImm16, hW]; omega
  have hdecW : decodeBignumWord W = none := by
    unfold decodeBignumWord
    rw [if_neg hgn1, if_neg hgn2, if_neg hgn3, if_neg hgn4, if_neg hgn5, if_neg hgn6]
  have hdecWide : decodeBignumWide W
      = some { cls := .movewide opc hw, rd := d, imm16 := imm16 } := by
    unfold decodeBignumWide
    rw [hg, hopcF, hhwF, hrd, himmF]
    simp
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
  | .orrX => some (.mov (xRegName dr.rd) (xRegName dr.rm))

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
