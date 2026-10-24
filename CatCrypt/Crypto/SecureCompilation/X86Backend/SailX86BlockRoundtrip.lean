/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86ByteFields
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86ByteFields
public import CatCryptCore.Tactics.KatGuard

/-!
# Byte-stream round-trip: `decode (encodeJBlock alloc block) = block`

A decoder that reads a `.text` byte stream back into a `List (JInstr 64)`, and
the theorem that it recovers any block built from the covered instruction forms.

`SailX86Decoder` inverts the encoder one *shape* at a time and only for the
register-direct GP forms. This module inverts whole instructions, including the
`MULX`/`ADCX`/`ADOX` and the `[base + disp]` memory forms, and then whole
blocks: the bytes an emitted leaf ships are parsed back, instruction by
instruction, with nothing left over.

## The covered set

`decodableJ` is the decidable predicate naming the forms `decodeJ1` inverts:

* reg-reg `ADD SUB ADC SBB AND OR XOR MOV`, and the `0F`-map `IMUL`/`CMOVcc`,
* the `imm32`-source group (`81 /digit id`), `MOV $imm32` (`C7 /0`),
  `MOV $imm64` (`B8+r io`), `IMUL $imm32` (`69 /r`),
* `SHL`/`SHR`/`SAR $imm8` and `NEG`,
* `ADCX`/`ADOX` (`66`/`F3 0F38 F6`) with a register or a `[base + disp]` source,
* `MULX` in both the register and the memory-source form,
* `loadMem`/`storeMem` (`8B`/`89` against `[base + disp]`), and the
  store-immediate `storeMem` (`C7 /0 id` against `[base + disp]`),
* `loadMemIdx`/`storeMemIdx` (`8B`/`89` against `[base + index * scale]`, the
  SIB form with `REX.X` extending the index field); these are inverted by
  `decodeJ1` (`roundtrip_loadMemIdx`, `roundtrip_storeMemIdx`) but sit outside
  `blockCovered`, because their side condition — the index register is not
  `%rsp` — is a fact of the allocation, which `blockCovered` does not see;
  `EncodeJBlock6Roundtrip.blockCovered6` carries it,
* the index-free `LEA` (`8D` against `[base + disp]`), written
  `lea dst base base 0 off`: at scale `0` the index contributes nothing to the
  address, and the decoder returns the base in the index position,
* `MOVZX` from an 8- or 16-bit source (`0F B6`/`0F B7 /r`),
* reg-reg `TEST` (`85 /r`) and `BT $imm8` (`0F BA /4 ib`),
* `setc`, the `SETB`/`MOVZBQ` pair `encSetcMovzx` emits, read as one
  instruction; its `SETB` carries `REX.B`, a bare `REX` or no prefix,

under the side conditions the encoding needs: an `imm32` immediate is a 64-bit
value that sign-extends from 32 bits (`fitsImm32S`; the decoder reads the field
through `imm32S`, the sign extension the CPU applies under `REX.W`), an `imm8`
fits a byte, and a displacement fits a signed 32-bit value (the encoder
picks the `disp0`, `disp8` or `disp32` form, and the decoder reads all three).
`blockCovered` is that
same set, in the form `roundtrip_block` places as a hypothesis on each
instruction of a block.

Outside the covered set: the indexed moves (above), `loadSym`,
`movzx` from a 32-bit source (its `MOV` encoding carries no `REX.W`, which
`decodeRex`'s opcode table does not distinguish from the 64-bit `MOV` it already
decodes — including this shape would make the two ambiguous), `movsx`,
the indexed `lea` (nonzero scale, the SIB form `encLeaSib`),
the register-count shift forms, the immediate-source `test` (`F7 /0 id`), the
register-source `bt` (`0F A3 /r`), and the immediate-source arms of `cmov`/`adcx`/
`adox`/`mulx`, for which the encoder substitutes a `0` operand rather
than encoding the instruction it was given. The instructions the encoder declines
(`ScalarEncoder.encodableJInstr` false: `inc`, `dec`, `clc`, `stc`, `xchg`,
`imulri`, `mul`, `imulWide`, `shld`, `shrd`, `rcl`, `rcr`, `testN`, `btr`,
`bts`) are outside the covered set as well: `encodeJInstr` emits no bytes at all
for these shapes (`ScalarEncoder.lean`'s `encodeJInstr`, final match arm), so a
`decodeJ1` case for one of them would have nothing to invert — closing this part
of the gap needs the encoder extended first, not the decoder. The
general-condition `cmovcc` and `setcc` are encoded (`encSetccByte`, the
`0x40 + condCode` `cmovcc` arm) and are outside the covered set for the other
reason: `decodableJ` returns false for both, so the decoder, not the encoder, is
what a `decodeJ1` case for them waits on.

## What the round-trip says

The decoder is written against the Sail-x86 parse discipline
(`SailX86ByteFields`): the REX/VEX prefix layout, the ModRM `mod/reg/rm` split,
the SIB escape with `REX.X` extending the index field (`decodeMemTail`), and the
displacement forms. Recovering the instruction from the
bytes says the encoder's output is the encoding of the instruction it was given,
rather than a byte string that agrees with `gas`.

Register names round-trip up to the allocation: the bytes carry SDM register
*numbers*, so the decoder returns the canonical `%rN` name. `renameJ` applies
the same resolution to the source instruction, and the two sides are compared
after it.

`MULX`'s first source is architecturally `%rdx` and is not encoded, so the bytes
can only recover it as `%rdx`. `renameJ` resolves that operand through the
allocation like any other, which puts "the allocation pins the multiplier to
`%rdx`" (`mulxRdxOk`) inside the covered set instead of leaving it unstated.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-! ## 1. Displacements and the memory-operand tail -/

/-- The signed value of a one-byte displacement. -/
def sdisp8 (b : BitVec 8) : Int := b.toInt

/-- The signed value of a four-byte little-endian displacement. -/
def sdisp32 (b0 b1 b2 b3 : BitVec 8) : Int :=
  (BitVec.ofNat 32 (b0.toNat + b1.toNat * 0x100 + b2.toNat * 0x10000
    + b3.toNat * 0x1000000)).toInt

/-- Read the displacement a ModRM `mod` field announces: none at `mod = 00`, one
    signed byte at `mod = 01`, four at `mod = 10`. -/
def decodeDisp : Nat → List (BitVec 8) → Option (Int × List (BitVec 8))
  | 0, bs => some (0, bs)
  | 1, d :: r => some (sdisp8 d, r)
  | 2, d0 :: d1 :: d2 :: d3 :: r => some (sdisp32 d0 d1 d2 d3, r)
  | _, _ => none

/-- The 64-bit value a 32-bit immediate field `u < 2 ^ 32` denotes under the sign
    extension every `REX.W` `imm32` form (`81 /digit id`, `C7 /0 id`, `69 /r id`)
    applies: `u` below `2 ^ 31`, else `u + (2 ^ 64 - 2 ^ 32)`. -/
def sext32 (u : Nat) : Nat := if u < 2 ^ 31 then u else u + (2 ^ 64 - 2 ^ 32)

/-- The sign-extended 64-bit value of the little-endian `imm32` bytes
    `j0 j1 j2 j3`. -/
def imm32S (j0 j1 j2 j3 : BitVec 8) : Nat :=
  sext32 (j0.toNat + j1.toNat * 0x100 + j2.toNat * 0x10000 + j3.toNat * 0x1000000)

/-- Parse a memory operand under the prefix's `X` bit `x` (`REX.X`, or the
    inverted `X̄` of a VEX prefix): the ModRM byte, the SIB byte when the `r/m`
    field is the SIB escape `100`, and the displacement. Returns the ModRM `reg`
    field, the base register's low three bits (the SIB `base` field in the SIB
    form), the index register with its stride when the SIB byte names one, the
    displacement, and the bytes left. The SIB byte has the ModRM bit layout: its
    `mod` position is the scale exponent, its `reg` position the index field, its
    `r/m` position the base field. An index field `100` under `x = 0` names no
    index register; otherwise the index is `x * 8 + field` and the stride
    `2 ^ exponent`. `mod = 11` is register-direct, `mod = 00, r/m = 101` is
    RIP-relative and `mod = 00` with SIB base field `101` has no base; all three
    name no base register and are rejected. -/
def decodeMemTail (x : Nat) :
    List (BitVec 8) → Option (Nat × Nat × Option (Nat × Nat) × Int × List (BitVec 8))
  | modrm :: rest =>
      if modField modrm = 3 then none
      else if rmField modrm = 4 then
        match rest with
        | sib :: rest1 =>
            if modField modrm = 0 ∧ rmField sib = 5 then none
            else
              let idx : Option (Nat × Nat) :=
                if x = 0 ∧ regField sib = 4 then none
                else some (x * 8 + regField sib, 2 ^ modField sib)
              (decodeDisp (modField modrm) rest1).map
                fun p => (regField modrm, rmField sib, idx, p.1, p.2)
        | [] => none
      else if modField modrm = 0 ∧ rmField modrm = 5 then none
      else
        (decodeDisp (modField modrm) rest).map
          fun p => (regField modrm, rmField modrm, none, p.1, p.2)
  | [] => none

/-! ## 2. The instruction decoder -/

/-- `ADCX`/`ADOX` after their mandatory prefix byte: `REX 0F 38 F6 ModRM`, with a
    register source at `mod = 11` and a `[base + disp]` source otherwise.
    `isAdcx` records which prefix was seen (`66` for `ADCX`, `F3` for `ADOX`). -/
def decodeAdx (isAdcx : Bool) : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | r :: e1 :: e2 :: e3 :: modrm :: rest =>
      if isRex r ∧ e1.toNat = 0x0f ∧ e2.toNat = 0x38 ∧ e3.toNat = 0xf6 then
        if modField modrm = 3 then
          let d := regName (rexR r * 8 + regField modrm)
          let s : JOperand := .reg (regName (rexB r * 8 + rmField modrm))
          some (if isAdcx then .adcx d s else .adox d s, rest)
        else
          match decodeMemTail (rexX r) (modrm :: rest) with
          | some (rf, bLow, none, off, rest2) =>
              let d := regName (rexR r * 8 + rf)
              let b := regName (rexB r * 8 + bLow)
              some (if isAdcx then .adcxMem d b off else .adoxMem d b off, rest2)
          | _ => none
      else none
  | _ => none

/-- The `MOVZBQ %d8, %d` bytes (`REX.W 0F B6 ModRM(11, d, d)`) that follow the
    `SETB` of the fused `setc` encoding `encSetcMovzx`. -/
def movzbqBytes (n : Nat) : List (BitVec 8) :=
  [ rex 1 (bit n 3) 0 (bit n 3), 0x0f, 0xb6, modRMReg n n ].map (BitVec.ofNat 8)

/-- The second half of a `setc`: after `SETB` into register `n`, the next four
    bytes must be `movzbqBytes n`, and the pair is `setc` of the `%rN` name. -/
def decodeMovzbq (n : Nat) : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | m0 :: m1 :: m2 :: m3 :: rest =>
      if [m0, m1, m2, m3] = movzbqBytes n then some (.setc (regName n), rest) else none
  | _ => none

/-- The condition of a `SETcc` second opcode byte the decoders read alone: `94` (`SETE`)
    and `95` (`SETNE`). -/
def setccCond? (e : Nat) : Option Condt :=
  if e = 0x94 then some .e else if e = 0x95 then some .ne else none

/-- A `setc` whose `SETB` carries no `REX` prefix (`0F 92 ModRM(11, /0, d)`), and a
    `SETE`/`SETNE` of a low byte (`0F 94`/`95 ModRM(11, /0, d)`, read as
    `setcc`, which writes the low byte and keeps the rest of the register): the
    ModRM `r/m` field names `%al`, `%cl`, `%dl` or `%bl`, since without a prefix the
    values `100..111` name `%ah`..`%bh`. -/
def decodeSetcBare : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | e :: modrm :: rest =>
      if e.toNat = 0x92 ∧ modField modrm = 3 ∧ regField modrm = 0 ∧ rmField modrm < 4 then
        decodeMovzbq (rmField modrm) rest
      else if modField modrm = 3 ∧ regField modrm = 0 ∧ rmField modrm < 4 then
        (setccCond? e.toNat).map fun c => (.setcc c (regName (rmField modrm)), rest)
      else none
  | _ => none

/-- `MULX` after the leading `C4` of its three-byte VEX prefix. The VEX bytes
    carry `R̄`/`B̄` (the inverted REX extension bits), `vvvv` (the inverted
    low destination), `W = 1`, `L = 0` and `pp = 11`; the ModRM `mod` field then
    selects the register form from the `[base + disp]` memory form. -/
def decodeMulx : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | v1 :: v2 :: op :: modrm :: rest =>
      if op.toNat = 0xf6 ∧ (v1.toNat >>> 6) &&& 1 = 1 ∧ v1.toNat &&& 31 = 2
          ∧ (v2.toNat >>> 7) &&& 1 = 1 ∧ v2.toNat &&& 7 = 3 then
        let rBit := 1 - ((v1.toNat >>> 7) &&& 1)
        let bBit := 1 - ((v1.toNat >>> 5) &&& 1)
        let dstLo := regName (15 - ((v2.toNat >>> 3) &&& 15))
        if modField modrm = 3 then
          some (.mulx (regName (rBit * 8 + regField modrm)) dstLo (.reg "%rdx")
                  (.reg (regName (bBit * 8 + rmField modrm))), rest)
        else
          match decodeMemTail 0 (modrm :: rest) with
          | some (rf, bLow, none, off, rest2) =>
              some (.mulxMem (regName (rBit * 8 + rf)) dstLo (.reg "%rdx")
                      (regName (bBit * 8 + bLow)) off, rest2)
          | _ => none
      else none
  | _ => none

/-- The REX-prefixed forms: `r` is the REX byte already read, the list starts at
    the opcode byte. -/
def decodeRex (r : BitVec 8) : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | op :: rest =>
      if op.toNat = 0x0f then
        match rest with
        | e :: modrm :: rest1 =>
            if modField modrm = 3 then
              let d := regName (rexR r * 8 + regField modrm)
              let s : JOperand := .reg (regName (rexB r * 8 + rmField modrm))
              if e.toNat = 0xaf then some (.imul d s, rest1)
              else if e.toNat = 0x44 then some (.cmove d s, rest1)
              else if e.toNat = 0x45 then some (.cmovne d s, rest1)
              else if e.toNat = 0x42 then some (.cmovb d s, rest1)
              else if e.toNat = 0xb6 then
                some (.movzx d 8 (regName (rexB r * 8 + rmField modrm)), rest1)
              else if e.toNat = 0xb7 then
                some (.movzx d 16 (regName (rexB r * 8 + rmField modrm)), rest1)
              else if e.toNat = 0x92 then
                if regField modrm = 0 then decodeMovzbq (rexB r * 8 + rmField modrm) rest1
                else none
              else if e.toNat = 0xba then
                match rest1 with
                | ib :: rest2 =>
                    if regField modrm = 4 then
                      some (.bt (regName (rexB r * 8 + rmField modrm)) (.imm ib.toNat), rest2)
                    else none
                | [] => none
              else none
            else none
        | _ => none
      else if 0xb8 ≤ op.toNat ∧ op.toNat ≤ 0xbf then
        match rest with
        | i0 :: i1 :: i2 :: i3 :: i4 :: i5 :: i6 :: i7 :: rest1 =>
            some (.mov (regName (rexB r * 8 + (op.toNat - 0xb8)))
                    (.imm (i0.toNat + i1.toNat * 0x100 + i2.toNat * 0x10000
                      + i3.toNat * 0x1000000 + i4.toNat * 0x100000000
                      + i5.toNat * 0x10000000000 + i6.toNat * 0x1000000000000
                      + i7.toNat * 0x100000000000000)), rest1)
        | _ => none
      else if op.toNat = 0x8b then
        match decodeMemTail (rexX r) rest with
        | some (rf, bLow, none, off, rest1) =>
            some (.loadMem (regName (rexR r * 8 + rf))
                    (regName (rexB r * 8 + bLow)) off, rest1)
        | some (rf, bLow, some (idx, scale), off, rest1) =>
            if off = 0 then
              some (.loadMemIdx (regName (rexR r * 8 + rf))
                      (regName (rexB r * 8 + bLow)) (regName idx) scale, rest1)
            else none
        | none => none
      else
        match rest with
        | modrm :: rest1 =>
            let dst := regName (rexB r * 8 + rmField modrm)
            let src : JOperand := .reg (regName (rexR r * 8 + regField modrm))
            if op.toNat = 0x89 then
              if modField modrm = 3 then some (.mov dst src, rest1)
              else
                match decodeMemTail (rexX r) (modrm :: rest1) with
                | some (rf, bLow, none, off, rest2) =>
                    some (.storeMem (regName (rexB r * 8 + bLow)) off
                            (.reg (regName (rexR r * 8 + rf))), rest2)
                | some (rf, bLow, some (idx, scale), off, rest2) =>
                    if off = 0 then
                      some (.storeMemIdx (regName (rexB r * 8 + bLow)) (regName idx) scale
                              (.reg (regName (rexR r * 8 + rf))), rest2)
                    else none
                | none => none
            else if modField modrm ≠ 3 then
              if op.toNat = 0x8d then
                match decodeMemTail (rexX r) (modrm :: rest1) with
                | some (rf, bLow, none, off, rest2) =>
                    let b := regName (rexB r * 8 + bLow)
                    some (.lea (regName (rexR r * 8 + rf)) b b 0 off, rest2)
                | _ => none
              else if op.toNat = 0xc7 then
                match decodeMemTail (rexX r) (modrm :: rest1) with
                | some (rf, bLow, none, off, j0 :: j1 :: j2 :: j3 :: rest2) =>
                    if rf = 0 then
                      some (.storeMem (regName (rexB r * 8 + bLow)) off
                        (.imm (imm32S j0 j1 j2 j3)), rest2)
                    else none
                | _ => none
              else none
            else if op.toNat = 0x81 then
              match rest1 with
              | j0 :: j1 :: j2 :: j3 :: rest2 =>
                  match aluImmMnemonic (regField modrm) with
                  | some mk => some (mk dst (.imm (imm32S j0 j1 j2 j3)), rest2)
                  | none => none
              | _ => none
            else if op.toNat = 0xc7 then
              match rest1 with
              | j0 :: j1 :: j2 :: j3 :: rest2 =>
                  if regField modrm = 0 then
                    some (.mov dst (.imm (imm32S j0 j1 j2 j3)), rest2)
                  else none
              | _ => none
            else if op.toNat = 0x69 then
              match rest1 with
              | j0 :: j1 :: j2 :: j3 :: rest2 =>
                  if regField modrm = rmField modrm then
                    some (.imul dst (.imm (imm32S j0 j1 j2 j3)), rest2)
                  else none
              | _ => none
            else if op.toNat = 0xc1 then
              match rest1 with
              | ib :: rest2 =>
                  if regField modrm = 4 then some (.shl dst (.imm ib.toNat), rest2)
                  else if regField modrm = 5 then some (.shr dst (.imm ib.toNat), rest2)
                  else if regField modrm = 7 then some (.sar dst (.imm ib.toNat), rest2)
                  else none
              | [] => none
            else if op.toNat = 0xf7 then
              if regField modrm = 3 then some (.neg dst, rest1) else none
            else
              match aluMnemonic op.toNat with
              | some mk => some (mk dst src, rest1)
              | none => if op.toNat = 0x85 then some (.test dst src, rest1) else none
        | [] => none
  | [] => none

/-- The `REX`-prefixed forms at `REX.W = 0` whose 32-bit operation has the effect of
    a `JInstr 64`: `MOVZX` from a byte or a word register (`0F B6 /r`, `0F B7 /r`),
    which zero the upper bits at either operand size; `SETB` followed by its `MOVZX`
    (`0F 92 /0`); `SETE`/`SETNE` of a byte register (`0F 94`/`95 /0`), a byte
    operation at any width; and `MOV $imm32, %r32` (`B8+rd id`), whose 32-bit write zero-extends
    into the register. Every other `REX.W = 0` form is a 32-bit operation that no
    `JInstr 64` denotes, and is rejected. -/
def decodeRexW0 (r : BitVec 8) : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | op :: rest =>
      if op.toNat = 0x0f then
        match rest with
        | e :: modrm :: rest1 =>
            if modField modrm = 3 then
              let d := regName (rexR r * 8 + regField modrm)
              if e.toNat = 0xb6 then
                some (.movzx d 8 (regName (rexB r * 8 + rmField modrm)), rest1)
              else if e.toNat = 0xb7 then
                some (.movzx d 16 (regName (rexB r * 8 + rmField modrm)), rest1)
              else if e.toNat = 0x92 then
                if regField modrm = 0 then decodeMovzbq (rexB r * 8 + rmField modrm) rest1
                else none
              else if regField modrm = 0 then
                (setccCond? e.toNat).map fun c =>
                  (.setcc c (regName (rexB r * 8 + rmField modrm)), rest1)
              else none
            else none
        | _ => none
      else if 0xb8 ≤ op.toNat ∧ op.toNat ≤ 0xbf then
        match rest with
        | i0 :: i1 :: i2 :: i3 :: rest1 =>
            some (.mov (regName (rexB r * 8 + (op.toNat - 0xb8)))
              (.imm (i0.toNat + i1.toNat * 0x100 + i2.toNat * 0x10000
                + i3.toNat * 0x1000000)), rest1)
        | _ => none
      else none
  | [] => none

/-- Decode one instruction off the front of a byte stream, returning it and the
    bytes that follow. The leading byte selects the family: the `66`/`F3`
    mandatory prefixes introduce `ADCX`/`ADOX`, `C4` the three-byte VEX `MULX`
    forms, a `0x40..0x4F` byte the REX-prefixed GP forms (`decodeRex` at
    `REX.W = 1`, `decodeRexW0` at `REX.W = 0`), and a bare `0F` the prefix-free
    `SETB` of a `setc`. -/
def decodeJ1 : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | [] => none
  | b0 :: rest =>
      if b0.toNat = 0x66 then decodeAdx true rest
      else if b0.toNat = 0xf3 then decodeAdx false rest
      else if b0.toNat = 0xc4 then decodeMulx rest
      else if isRex b0 then
        if rexW b0 = 1 then decodeRex b0 rest else decodeRexW0 b0 rest
      else if b0.toNat = 0x0f then decodeSetcBare rest
      else none

/-- Decode a byte stream into `n` instructions, requiring the stream to be
    consumed exactly: `n` successful single-instruction decodes and no bytes
    left. -/
def decodeJStream : Nat → List (BitVec 8) → Option (List (JInstr 64))
  | 0, bs => if bs.isEmpty then some [] else none
  | n + 1, bs =>
      match decodeJ1 bs with
      | some (i, rest) => (decodeJStream n rest).map (i :: ·)
      | none => none

/-- The `REX.W D1 /4` (`shl $1`), `REX.W D1 /5` (`shr $1`) and `REX.W D1 /7`
    (`sar $1`) register-direct shift-by-one forms. -/
def decodeShift1 : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | r :: op :: modrm :: rest =>
      if isRex r ∧ rexW r = 1 ∧ op.toNat = 0xd1 ∧ modField modrm = 3 then
        let dst := regName (rexB r * 8 + rmField modrm)
        if regField modrm = 4 then some (.shl dst (.imm 1), rest)
        else if regField modrm = 5 then some (.shr dst (.imm 1), rest)
        else if regField modrm = 7 then some (.sar dst (.imm 1), rest)
        else none
      else none
  | _ => none

/-- The register-direct compares `REX.W 39 /r` (`cmp %reg, %rm`, computing
    `rm - reg`) and `REX.W 81 /7 id` (`cmp $imm32, %rm`, the immediate
    sign-extended to 64 bits). -/
def decodeCmp : List (BitVec 8) → Option (JInstr 64 × List (BitVec 8))
  | r :: op :: modrm :: rest =>
      if isRex r ∧ rexW r = 1 ∧ modField modrm = 3 then
        let a := regName (rexB r * 8 + rmField modrm)
        if op.toNat = 0x39 then
          some (.cmp a (.reg (regName (rexR r * 8 + regField modrm))), rest)
        else if op.toNat = 0x81 ∧ regField modrm = 7 then
          match rest with
          | j0 :: j1 :: j2 :: j3 :: rest1 =>
              some (.cmp a (.imm (sext32 (j0.toNat + j1.toNat * 0x100
                + j2.toNat * 0x10000 + j3.toNat * 0x1000000))), rest1)
          | _ => none
        else none
      else none
  | _ => none

/-- Decode one instruction off the front of a byte stream: `decodeJ1`, and on the
    streams `decodeJ1` rejects, the `D1` shift-by-one forms and then the
    compares. -/
def decodeJ1_6 (bs : List (BitVec 8)) : Option (JInstr 64 × List (BitVec 8)) :=
  match decodeJ1 bs with
  | some r => some r
  | none => (decodeShift1 bs).or (decodeCmp bs)

/-- Wherever `decodeJ1` succeeds, `decodeJ1_6` returns the same result. -/
theorem decodeJ1_6_of_decodeJ1 (bs rest : List (BitVec 8)) (i : JInstr 64)
    (h : decodeJ1 bs = some (i, rest)) :
    decodeJ1_6 bs = some (i, rest) := by
  simp only [decodeJ1_6, h]

/-- On a stream `decodeJ1` rejects, `decodeJ1_6` is `decodeShift1`, then
    `decodeCmp`. -/
theorem decodeJ1_6_of_none (bs : List (BitVec 8)) (h : decodeJ1 bs = none) :
    decodeJ1_6 bs = (decodeShift1 bs).or (decodeCmp bs) := by
  simp only [decodeJ1_6, h]

/-! ## 3. Resolving register names through the allocation -/

/-- The canonical `%rN` name the encoder resolves a block-level register name to:
    the allocation lookup, then the SDM register number, then back. -/
def nameOf (alloc : GpAlloc) (n : String) : String := regName (gpNum (regOf alloc n))

/-- `nameOf` on an operand; an immediate is unchanged. -/
def operandOf (alloc : GpAlloc) : JOperand → JOperand
  | .reg r => .reg (nameOf alloc r)
  | .imm v => .imm v

/-- Resolve every register name of an instruction through the allocation. This is
    the normal form the decoder returns: the bytes carry register numbers, so a
    round-trip recovers the canonical name, not the block-level one. -/
def renameJ (alloc : GpAlloc) : JInstr 64 → JInstr 64
  | .mov d s => .mov (nameOf alloc d) (operandOf alloc s)
  | .add d s => .add (nameOf alloc d) (operandOf alloc s)
  | .sub d s => .sub (nameOf alloc d) (operandOf alloc s)
  | .adc d s => .adc (nameOf alloc d) (operandOf alloc s)
  | .sbb d s => .sbb (nameOf alloc d) (operandOf alloc s)
  | .imul d s => .imul (nameOf alloc d) (operandOf alloc s)
  | .neg d => .neg (nameOf alloc d)
  | .setc d => .setc (nameOf alloc d)
  | .and_ d s => .and_ (nameOf alloc d) (operandOf alloc s)
  | .test a b => .test (nameOf alloc a) (operandOf alloc b)
  | .or_ d s => .or_ (nameOf alloc d) (operandOf alloc s)
  | .xor_ d s => .xor_ (nameOf alloc d) (operandOf alloc s)
  | .shl d s => .shl (nameOf alloc d) (operandOf alloc s)
  | .shr d s => .shr (nameOf alloc d) (operandOf alloc s)
  | .sar d s => .sar (nameOf alloc d) (operandOf alloc s)
  | .cmove d s => .cmove (nameOf alloc d) (operandOf alloc s)
  | .cmovne d s => .cmovne (nameOf alloc d) (operandOf alloc s)
  | .cmovb d s => .cmovb (nameOf alloc d) (operandOf alloc s)
  | .adcx d s => .adcx (nameOf alloc d) (operandOf alloc s)
  | .adox d s => .adox (nameOf alloc d) (operandOf alloc s)
  | .mulx dh dl a b =>
      .mulx (nameOf alloc dh) (nameOf alloc dl) (operandOf alloc a) (operandOf alloc b)
  | .mulxMem dh dl a base off =>
      .mulxMem (nameOf alloc dh) (nameOf alloc dl) (operandOf alloc a)
        (nameOf alloc base) off
  | .loadMem d base off => .loadMem (nameOf alloc d) (nameOf alloc base) off
  | .storeMem base off s => .storeMem (nameOf alloc base) off (operandOf alloc s)
  | .loadMemIdx d base idx scale =>
      .loadMemIdx (nameOf alloc d) (nameOf alloc base) (nameOf alloc idx) scale
  | .storeMemIdx base idx scale s =>
      .storeMemIdx (nameOf alloc base) (nameOf alloc idx) scale (operandOf alloc s)
  | .cmp a b => .cmp (nameOf alloc a) (operandOf alloc b)
  | .not_ d => .not_ (nameOf alloc d)
  | .andn d a b => .andn (nameOf alloc d) (nameOf alloc a) (nameOf alloc b)
  | .rol d amt => .rol (nameOf alloc d) (operandOf alloc amt)
  | .ror d amt => .ror (nameOf alloc d) (operandOf alloc amt)
  | .rorx d src amt => .rorx (nameOf alloc d) (nameOf alloc src) (operandOf alloc amt)
  | .shlx d src cnt => .shlx (nameOf alloc d) (nameOf alloc src) (nameOf alloc cnt)
  | .shrx d src cnt => .shrx (nameOf alloc d) (nameOf alloc src) (nameOf alloc cnt)
  | .sarx d src cnt => .sarx (nameOf alloc d) (nameOf alloc src) (nameOf alloc cnt)
  | .movzx d sw src => .movzx (nameOf alloc d) sw (nameOf alloc src)
  | .movsx d sw src => .movsx (nameOf alloc d) sw (nameOf alloc src)
  | .lea d base idx scale off =>
      .lea (nameOf alloc d) (nameOf alloc base) (nameOf alloc idx) scale off
  | .loadSym d sym => .loadSym (nameOf alloc d) sym
  | .inc d => .inc (nameOf alloc d)
  | .dec d => .dec (nameOf alloc d)
  | .clc => .clc
  | .stc => .stc
  | .xchg a b => .xchg (nameOf alloc a) (nameOf alloc b)
  | .imulri d src imm => .imulri (nameOf alloc d) (nameOf alloc src) imm
  | .mul dh dl src => .mul (nameOf alloc dh) (nameOf alloc dl) (nameOf alloc src)
  | .imulWide dh dl src =>
      .imulWide (nameOf alloc dh) (nameOf alloc dl) (nameOf alloc src)
  | .shld d src amt => .shld (nameOf alloc d) (nameOf alloc src) (operandOf alloc amt)
  | .shrd d src amt => .shrd (nameOf alloc d) (nameOf alloc src) (operandOf alloc amt)
  | .rcl d amt => .rcl (nameOf alloc d) (operandOf alloc amt)
  | .rcr d amt => .rcr (nameOf alloc d) (operandOf alloc amt)
  | .cmovcc c d s => .cmovcc c (nameOf alloc d) (operandOf alloc s)
  | .setcc c d => .setcc c (nameOf alloc d)
  | .testN sz a b => .testN sz (nameOf alloc a) (operandOf alloc b)
  | .bt a b => .bt (nameOf alloc a) (operandOf alloc b)
  | .btr d b => .btr (nameOf alloc d) (operandOf alloc b)
  | .bts d b => .bts (nameOf alloc d) (operandOf alloc b)
  | .addMem d base off => .addMem (nameOf alloc d) (nameOf alloc base) off
  | .addToMem base off s => .addToMem (nameOf alloc base) off (operandOf alloc s)
  | .adcxMem d base off => .adcxMem (nameOf alloc d) (nameOf alloc base) off
  | .adoxMem d base off => .adoxMem (nameOf alloc d) (nameOf alloc base) off
  | .imulMem d base off => .imulMem (nameOf alloc d) (nameOf alloc base) off
  | .imulriMem d base off imm => .imulriMem (nameOf alloc d) (nameOf alloc base) off imm
  | .cmpMem a base off => .cmpMem (nameOf alloc a) (nameOf alloc base) off
  | .cmovccMem c d base off => .cmovccMem c (nameOf alloc d) (nameOf alloc base) off
  | .bzhi d src idx => .bzhi (nameOf alloc d) (nameOf alloc src) (nameOf alloc idx)

/-! ## 4. The covered set -/

/-- A displacement the `[base + disp8]` form encodes exactly. -/
def dispOk (off : Int) : Bool := -128 ≤ off ∧ off ≤ 127

/-- A displacement the `[base + disp32]` form encodes exactly: a signed 32-bit
    value. `memTail` emits the shortest of the `disp0`/`disp8`/`disp32` forms
    that holds it. -/
def dispOk32 (off : Int) : Bool := -2 ^ 31 ≤ off ∧ off < 2 ^ 31

/-- A signed-byte displacement is a signed 32-bit displacement. -/
theorem dispOk32_of_dispOk (off : Int) (h : dispOk off = true) : dispOk32 off = true := by
  simp only [dispOk, dispOk32, decide_eq_true_eq] at h ⊢
  omega

/-- The instruction forms `decodeJ1` inverts, with the width side conditions each
    encoding needs: an `imm32` immediate is a 64-bit value that sign-extends from
    32 bits (`fitsImm32S`), an `imm8` fits a byte, a displacement fits a signed
    32-bit value. -/
def decodableJ : JInstr 64 → Bool
  | .mov _ (.reg _) => true
  | .mov _ (.imm v) => v < 2 ^ 64
  | .add _ (.reg _) => true
  | .add _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | .sub _ (.reg _) => true
  | .sub _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | .adc _ (.reg _) => true
  | .adc _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | .sbb _ (.reg _) => true
  | .sbb _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | .and_ _ (.reg _) => true
  | .and_ _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | .or_ _ (.reg _) => true
  | .or_ _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | .xor_ _ (.reg _) => true
  | .xor_ _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | .imul _ (.reg _) => true
  | .imul _ (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v
  | .neg _ => true
  | .shl _ (.imm v) => v < 256
  | .shr _ (.imm v) => v < 256
  | .sar _ (.imm v) => v < 256
  | .cmove _ (.reg _) => true
  | .cmovne _ (.reg _) => true
  | .cmovb _ (.reg _) => true
  | .adcx _ (.reg _) => true
  | .adox _ (.reg _) => true
  | .mulx _ _ (.reg _) (.reg _) => true
  | .mulxMem _ _ (.reg _) _ off => dispOk32 off
  | .loadMem _ _ off => dispOk32 off
  | .storeMem _ off (.reg _) => dispOk32 off
  | .storeMem _ off (.imm v) => decide (v < 2 ^ 64) && fitsImm32S v && dispOk32 off
  | .lea _ base idx scale off => scale == 0 && base == idx && dispOk32 off
  | .movzx _ 8 _ => true
  | .movzx _ 16 _ => true
  | .setc _ => true
  | .test _ (.reg _) => true
  | .bt _ (.imm v) => v < 256
  | .adcxMem _ _ off => dispOk32 off
  | .adoxMem _ _ off => dispOk32 off
  | _ => false

/-- `MULX` reads its first source from `%rdx` and does not encode it, so the
    bytes recover that operand only when the allocation pins it there. -/
def mulxRdxOk (alloc : GpAlloc) : JInstr 64 → Bool
  | .mulx _ _ (.reg a) _ => gpNum (regOf alloc a) == 2
  | .mulxMem _ _ (.reg a) _ _ => gpNum (regOf alloc a) == 2
  | _ => true

/-- The instruction forms a block may contain for the whole-block round-trip
    `roundtrip_block`: the forms `decodeJ1` inverts, with the immediate-width and
    displacement side conditions their encodings need. -/
def blockCovered : JInstr 64 → Bool := decodableJ

-- The boundary of the covered set: the forms it admits, and the forms and
-- out-of-range operands it rejects. These are static checks pinning the
-- decidable predicate against silent change; each reduces a small closed term.
-- They precede the round-trip theorems so that the first kernel check does not
-- wait on the module's asynchronous proof tasks.
#kat_kernel blockCovered (.mov "a" (.reg "b"))
#kat_kernel ! blockCovered (.loadMemIdx "a" "b" "c" 8)
#kat_kernel ! blockCovered (.storeMemIdx "a" "c" 8 (.reg "b"))
#kat_kernel blockCovered (.shl "a" (.imm 13))
#kat_kernel blockCovered (.loadMem "a" "b" (-8))
#kat_kernel blockCovered (.setc "a")
#kat_kernel blockCovered (.test "a" (.reg "b"))
#kat_kernel ! blockCovered (.test "a" (.imm 1))
#kat_kernel blockCovered (.bt "a" (.imm 0))
#kat_kernel ! blockCovered (.bt "a" (.imm 256))
#kat_kernel ! blockCovered (.bt "a" (.reg "b"))
#kat_kernel blockCovered (.adcxMem "a" "b" 152)
#kat_kernel blockCovered (.storeMem "a" 392 (.imm 0))
#kat_kernel ! blockCovered (.storeMem "a" 0 (.imm (2 ^ 32)))
-- An `imm32` immediate is the 64-bit value the sign-extended field denotes: the
-- range `[2 ^ 31, 2 ^ 64 - 2 ^ 31)` has no `imm32` encoding.
#kat_kernel blockCovered (.add "a" (.imm (2 ^ 31 - 1)))
#kat_kernel ! blockCovered (.add "a" (.imm (2 ^ 31)))
#kat_kernel ! blockCovered (.add "a" (.imm (2 ^ 32 - 1)))
#kat_kernel blockCovered (.sub "a" (.imm (2 ^ 64 - 1)))
#kat_kernel blockCovered (.storeMem "a" 0 (.imm (2 ^ 64 - 2 ^ 31)))
#kat_kernel ! blockCovered (.imul "a" (.imm (2 ^ 64 - 2 ^ 31 - 1)))
#kat_kernel ! blockCovered (.setcc .b "a")
#kat_kernel ! blockCovered (.shl "a" (.reg "b"))
-- The flag-only, BMI1/BMI2 and extension-move forms, and the indexed `lea`, have
-- no `decodeJ1` arm, so they sit outside the covered set.
#kat_kernel ! blockCovered (.cmp "a" (.reg "b"))
#kat_kernel ! blockCovered (.not_ "a")
#kat_kernel ! blockCovered (.andn "a" "b" "c")
#kat_kernel ! blockCovered (.rol "a" (.imm 3))
#kat_kernel ! blockCovered (.ror "a" (.imm 3))
#kat_kernel ! blockCovered (.rorx "a" "b" (.imm 3))
#kat_kernel ! blockCovered (.shlx "a" "b" "c")
#kat_kernel ! blockCovered (.shrx "a" "b" "c")
#kat_kernel ! blockCovered (.sarx "a" "b" "c")
#kat_kernel blockCovered (.movzx "a" 8 "b")
#kat_kernel blockCovered (.movzx "a" 16 "b")
#kat_kernel ! blockCovered (.movzx "a" 32 "b")
#kat_kernel ! blockCovered (.movsx "a" 8 "b")
#kat_kernel ! blockCovered (.lea "a" "b" "c" 8 0)
#kat_kernel ! blockCovered (.lea "a" "b" "b" 1 0)
#kat_kernel ! blockCovered (.lea "a" "b" "c" 0 0)
#kat_kernel blockCovered (.lea "a" "b" "b" 0 32)
#kat_kernel ! blockCovered (.lea "a" "b" "b" 0 (2 ^ 31))
#kat_kernel ! blockCovered (.mov "a" (.imm (2 ^ 64)))
#kat_kernel blockCovered (.loadMem "a" "b" 4096)
#kat_kernel blockCovered (.storeMem "a" (-2 ^ 31) (.reg "b"))
#kat_kernel ! blockCovered (.loadMem "a" "b" (2 ^ 31))
#kat_kernel ! blockCovered (.storeMem "a" (-2 ^ 31 - 1) (.reg "b"))

/-! ## 5. Round-trip for the register-direct forms -/

/-- The REX-bit/ModRM-field split recovers the register name the allocation
    resolves a block-level name to. -/
theorem regName_split (alloc : GpAlloc) (r : String) :
    regName (bit (gpNum (regOf alloc r)) 3 * 8 + (gpNum (regOf alloc r) &&& 7))
      = nameOf alloc r := by
  rw [bit, regsplit_id _ (gpNum_lt_16 _), nameOf]

/-- `ADCX %src, %dst` (`66 REX.W 0F 38 F6 /r`) decodes back to itself, consuming
    exactly its own six bytes. -/
theorem roundtrip_adcx (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.adcx d (.reg s)) ++ rest)
      = some (renameJ alloc (.adcx d (.reg s)), rest) := by
  simp only [encodeJInstr, encAdxCarry, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, decodeJ1, BitVec.toNat_ofNat, decodeAdx,
    isRex_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), modField_modRMReg, regField_modRMReg,
    rmField_modRMReg, regName_split, renameJ, operandOf, ite_true, and_true]

/-- `ADOX %src, %dst` (`F3 REX.W 0F 38 F6 /r`) decodes back to itself, consuming
    exactly its own six bytes. -/
theorem roundtrip_adox (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.adox d (.reg s)) ++ rest)
      = some (renameJ alloc (.adox d (.reg s)), rest) := by
  simp only [encodeJInstr, encAdxCarry, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, decodeJ1,
    BitVec.toNat_ofNat, ite_eq_right (show ¬((0xf3 : Nat) % 2 ^ 8 = 0x66) by decide),
    decodeAdx, isRex_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), modField_modRMReg, regField_modRMReg,
    rmField_modRMReg, regName_split, renameJ, operandOf, ite_true, and_true,
    ite_eq_right (show ¬(false = true) by decide)]

/-! ## 6. The VEX prefix bytes of `MULX`

The field lemmas are stated on the byte's numeric value modulo `2 ^ 8`, the form
`BitVec.toNat_ofNat` puts the encoder's `BitVec.ofNat 8` bytes into. -/

/-- Bit 6 of the first VEX byte is `X̄ = 1` (no SIB index). -/
theorem vex1_bit6 (r b : Nat) :
    ((((1 - r) * 128 + 1 * 64 + (1 - b) * 32 + 2) % 2 ^ 8) >>> 6) &&& 1 = 1 := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow]
  omega

/-- The low five bits of the first VEX byte are the `mmmmm = 00010` map selector
    (`0F38`). -/
theorem vex1_map (r b : Nat) :
    (((1 - r) * 128 + 1 * 64 + (1 - b) * 32 + 2) % 2 ^ 8) &&& 31 = 2 := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 5]
  omega

/-- Bit 7 of the first VEX byte is `R̄`, the inverted REX.R extension. -/
theorem vex1_rbar (r b : Nat) (hr : r ≤ 1) (hb : b ≤ 1) :
    ((((1 - r) * 128 + 1 * 64 + (1 - b) * 32 + 2) % 2 ^ 8) >>> 7) &&& 1 = 1 - r := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow]
  omega

/-- Bit 5 of the first VEX byte is `B̄`, the inverted REX.B extension. -/
theorem vex1_bbar (r b : Nat) (hr : r ≤ 1) (hb : b ≤ 1) :
    ((((1 - r) * 128 + 1 * 64 + (1 - b) * 32 + 2) % 2 ^ 8) >>> 5) &&& 1 = 1 - b := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow]
  omega

/-- Bit 7 of the second VEX byte is `W = 1` (64-bit operand size). -/
theorem vex2_w (v : Nat) :
    (((128 + (15 - (v &&& 15)) * 8 + 3) % 2 ^ 8) >>> 7) &&& 1 = 1 := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 4, Nat.and_two_pow_sub_one_eq_mod _ 1,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The low three bits of the second VEX byte are `L = 0` and `pp = 11` (the `F2`
    mandatory prefix). -/
theorem vex2_pp (v : Nat) :
    ((128 + (15 - (v &&& 15)) * 8 + 3) % 2 ^ 8) &&& 7 = 3 := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 4, Nat.and_two_pow_sub_one_eq_mod _ 3]
  omega

/-- The `vvvv` field of the second VEX byte is the inverted low destination, so
    `15 - vvvv` recovers it. -/
theorem vex2_vvvv (v : Nat) (hv : v < 16) :
    15 - ((((128 + (15 - (v &&& 15)) * 8 + 3) % 2 ^ 8) >>> 3) &&& 15) = v := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 4, Nat.and_two_pow_sub_one_eq_mod _ 4,
    Nat.shiftRight_eq_div_pow]
  omega

/-- `1 - (1 - bit n i)` is `bit n i`: the decoder's un-inversion of the VEX
    extension bits. -/
theorem one_sub_one_sub_bit (n i : Nat) : 1 - (1 - bit n i) = bit n i := by
  have := bit_le_one n i
  omega

/-! ## 7. Round-trip for `MULX` -/

/-- `MULX %src2, %dstLo, %dstHi` (`VEX.LZ.F2.0F38.W1 F6 /r`) decodes back to
    itself when the allocation pins the implicit multiplier operand to `%rdx`,
    which is the operand the VEX encoding does not carry. -/
theorem roundtrip_mulx (alloc : GpAlloc) (dh dl a b : String) (rest : List (BitVec 8))
    (ha : mulxRdxOk alloc (.mulx dh dl (.reg a) (.reg b)) = true) :
    decodeJ1 (encodeJInstr alloc (.mulx dh dl (.reg a) (.reg b)) ++ rest)
      = some (renameJ alloc (.mulx dh dl (.reg a) (.reg b)), rest) := by
  have hrdx : regName (gpNum (regOf alloc a)) = "%rdx" := by
    simp only [mulxRdxOk, beq_iff_eq] at ha
    rw [ha]; rfl
  simp only [encodeJInstr, encMulxRR, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, decodeJ1,
    BitVec.toNat_ofNat, ite_eq_right (show ¬((0xc4 : Nat) % 2 ^ 8 = 0x66) by decide),
    ite_eq_right (show ¬((0xc4 : Nat) % 2 ^ 8 = 0xf3) by decide), decodeMulx,
    vex1_bit6, vex1_map,
    vex1_rbar _ _ (bit_le_one _ _) (bit_le_one _ _),
    vex1_bbar _ _ (bit_le_one _ _) (bit_le_one _ _),
    vex2_w, vex2_pp, vex2_vvvv _ (gpNum_lt_16 _), one_sub_one_sub_bit,
    modField_modRMReg, regField_modRMReg, rmField_modRMReg, regName_split,
    renameJ, operandOf, nameOf, hrdx, ite_true, and_true]

/-! ## 8. The memory-operand tail -/

/-- A displacement in signed-byte range is recovered from its `disp8` byte. -/
theorem sdisp8_disp8 (off : Int) (h : dispOk off = true) : sdisp8 (disp8 off) = off := by
  simp only [dispOk, decide_eq_true_eq] at h
  simp only [sdisp8, disp8, BitVec.toInt_ofInt, Int.bmod_def]
  split <;> omega

/-- The four little-endian `disp32LE` bytes of a signed 32-bit displacement
    decode, at `mod = 10`, back to the displacement: the bytes recompose to the
    two's-complement value and `sdisp32` sign-extends it. -/
theorem decodeDisp_disp32LE (off : Int) (rest : List (BitVec 8))
    (h : dispOk32 off = true) :
    decodeDisp 2 (disp32LE off ++ rest) = some (off, rest) := by
  simp only [dispOk32, decide_eq_true_eq] at h
  have hrec : ∀ v : Nat, v < 2 ^ 32 →
      (v &&& 0xff) % 2 ^ 8 + ((v >>> 8) &&& 0xff) % 2 ^ 8 * 0x100
        + ((v >>> 16) &&& 0xff) % 2 ^ 8 * 0x10000
        + ((v >>> 24) &&& 0xff) % 2 ^ 8 * 0x1000000 = v := by
    intro v hv
    simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow]
    omega
  simp only [disp32LE, imm32LE, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, decodeDisp, sdisp32, BitVec.toNat_ofNat,
    hrec _ (BitVec.isLt (BitVec.ofInt 32 off)), BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.toInt_ofInt, Option.some.injEq, Prod.mk.injEq, and_true]
  rw [Int.bmod_def]
  split <;> omega

/-- `REX.X` of a `REX.W` prefix byte is the bit the encoder put there. -/
theorem rexX_rex (r x b : Nat) (hx : x ≤ 1) (hb : b ≤ 1) :
    rexX (BitVec.ofNat 8 (rex 1 r x b)) = x := by
  rw [rexX, Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  unfold rex; omega

/-- `decodeMemTail` under a clear `X` bit inverts `memTail` on a signed 32-bit
    displacement: it recovers the ModRM `reg` field, the base register's low
    three bits, no index, and the displacement, leaving no bytes. This covers the
    `disp0`, `disp8` and `disp32` forms `memTail` selects between, and all four
    special bases — the SIB escape at base low-3 = 4 and the forced `disp8` at
    base low-3 = 5. -/
theorem decodeMemTail_memTail32 (reg base : Nat) (off : Int) (rest : List (BitVec 8))
    (h : dispOk32 off = true) :
    decodeMemTail 0 (memTail reg base off ++ rest)
      = some (reg &&& 7, base &&& 7, none, off, rest) := by
  have hrm : rmField (BitVec.ofNat 8 0x24) = 4 := by decide
  have hrg : regField (BitVec.ofNat 8 0x24) = 4 := by decide
  rcases Decidable.em (dispOk off = true) with h8 | h8
  · have hd := sdisp8_disp8 off h8
    simp only [dispOk, decide_eq_true_eq] at h8
    rcases eq_or_ne off 0 with rfl | h0
    · rcases Decidable.em (base &&& 7 = 4) with hs | hs
      · simp [memTail, decodeMemTail, decodeDisp, modField_modRMMem, rmField_modRMMem,
          regField_modRMMem, hs, hrm, hrg]
      · rcases Decidable.em (base &&& 7 = 5) with h5 | h5 <;>
          simp [memTail, decodeMemTail, decodeDisp, modField_modRMMem, rmField_modRMMem,
            regField_modRMMem, hs, h5, hd]
    · rcases Decidable.em (base &&& 7 = 4) with hs | hs <;>
        simp [memTail, decodeMemTail, decodeDisp, modField_modRMMem, rmField_modRMMem,
          regField_modRMMem, hs, h0, hd, h8, hrm, hrg]
  · have hd := decodeDisp_disp32LE off rest h
    simp only [dispOk, decide_eq_true_eq] at h8
    have h0 : off ≠ 0 := by omega
    rcases Decidable.em (base &&& 7 = 4) with hs | hs <;>
      simp [memTail, decodeMemTail, modField_modRMMem, rmField_modRMMem,
        regField_modRMMem, hs, h0, h8, hd, hrm, hrg]

/-- `decodeMemTail` under a clear `X` bit inverts `memTail` on a signed-byte
    displacement: it recovers the ModRM `reg` field, the base register's low
    three bits, no index, and the displacement, leaving no bytes. -/
theorem decodeMemTail_memTail (reg base : Nat) (off : Int) (rest : List (BitVec 8))
    (h : dispOk off = true) :
    decodeMemTail 0 (memTail reg base off ++ rest)
      = some (reg &&& 7, base &&& 7, none, off, rest) :=
  decodeMemTail_memTail32 reg base off rest (dispOk32_of_dispOk off h)

/-- The SIB-escape ModRM byte `encMemMovSib` emits is `modRMMem md r 4`. -/
theorem sibModRM_eq_modRMMem (md r : Nat) : md * 64 + (r &&& 7) * 8 + 4 = modRMMem md r 4 :=
  rfl

/-- `decodeMemTail` under the index's bit `3` inverts the ModRM/SIB tail of
    `encMemMovSib` for an index register other than `%rsp` and an encodable
    stride: it recovers the ModRM `reg` field, the base's low three bits, the
    index register and its stride, a zero displacement, and the bytes after the
    tail. `md = 0` is the `disp0` form, available when the base's low three bits
    are not `101`; `md = 1` carries the zero `disp8` byte. -/
theorem decodeMemTail_sibTail (r base index scale md : Nat) (rest : List (BitVec 8))
    (hx : index < 16) (hx4 : index ≠ 4) (hs : scaleOk scale = true)
    (hmd : (md = 0 ∧ base &&& 7 ≠ 5) ∨ md = 1) :
    decodeMemTail (bit index 3)
        (BitVec.ofNat 8 (modRMMem md r 4) :: BitVec.ofNat 8 (sibByte scale index base)
          :: (if md = 1 then [disp8 0] else []) ++ rest)
      = some (r &&& 7, base &&& 7, some (index, scale), 0, rest) := by
  have hsc := two_pow_sibScale scale hs
  have hid : index >>> 3 % 2 * 8 + (index &&& 7) = index := by
    have := regsplit_id index hx
    rwa [Nat.and_one_is_mod] at this
  have hnx : index >>> 3 % 2 = 0 → ¬ index &&& 7 = 4 := by
    intro h1 h2; omega
  rw [sibByte_eq_modRMMem]
  rcases hmd with ⟨rfl, h5⟩ | rfl
  · simp [decodeMemTail, decodeDisp, modField_modRMMem, regField_modRMMem, rmField_modRMMem,
      sibScale_lt_four, hsc, h5]
    exact ⟨hnx, hid⟩
  · simp [decodeMemTail, decodeDisp, modField_modRMMem, regField_modRMMem, rmField_modRMMem,
      sibScale_lt_four, hsc, sdisp8_disp8 0 (by decide)]
    exact ⟨hnx, hid⟩

/-- A `memTail` byte string starts with a memory `ModRM` byte, whose `mod` field
    is `00`, `01` or `10` — never the register-direct `11`. -/
theorem memTail_head (reg base : Nat) (off : Int) :
    ∃ m ts, memTail reg base off = m :: ts ∧ modField m ≠ 3 := by
  simp only [memTail]
  split_ifs <;> exact ⟨_, _, rfl, by simp [modField_modRMMem]⟩

/-! ## 9. Round-trip for the `[base + disp]` memory forms -/

/-- A `REX.W`-prefixed byte stream is none of the `66`/`F3`/`C4` mandatory-prefix
    families, so `decodeJ1` routes it to `decodeRex`. -/
theorem decodeJ1_rex (r x b : Nat) (hr : r ≤ 1) (hx : x ≤ 1) (hb : b ≤ 1)
    (rest : List (BitVec 8)) :
    decodeJ1 (BitVec.ofNat 8 (rex 1 r x b) :: rest)
      = decodeRex (BitVec.ofNat 8 (rex 1 r x b)) rest := by
  have h66 : ¬ ((BitVec.ofNat 8 (rex 1 r x b)).toNat = 0x66) := by
    rw [BitVec.toNat_ofNat]; unfold rex; omega
  have hf3 : ¬ ((BitVec.ofNat 8 (rex 1 r x b)).toNat = 0xf3) := by
    rw [BitVec.toNat_ofNat]; unfold rex; omega
  have hc4 : ¬ ((BitVec.ofNat 8 (rex 1 r x b)).toNat = 0xc4) := by
    rw [BitVec.toNat_ofNat]; unfold rex; omega
  simp only [decodeJ1, ite_eq_right h66, ite_eq_right hf3, ite_eq_right hc4,
    isRex_rex _ _ _ hr hx hb, rexW_rex _ _ _ hr hx hb, ite_true]

/-- `MOV off(%base), %dst` (`REX.W 8B /r`) decodes back to itself for a
    signed 32-bit displacement. -/
theorem roundtrip_loadMem32 (alloc : GpAlloc) (d base : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk32 off = true) :
    decodeJ1 (encodeJInstr alloc (.loadMem d base off) ++ rest)
      = some (renameJ alloc (.loadMem d base off), rest) := by
  simp only [encodeJInstr, encMemMov, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0x8b : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0x8b : Nat) % 2 ^ 8 ∧ (0x8b : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    rexX_rex _ _ _ (Nat.zero_le 1) (bit_le_one _ _),
    decodeMemTail_memTail32 _ _ _ _ h,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, ite_true]

/-- `MOV %src, off(%base)` (`REX.W 89 /r`) decodes back to itself for a
    signed 32-bit displacement. -/
theorem roundtrip_storeMem32 (alloc : GpAlloc) (base s : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk32 off = true) :
    decodeJ1 (encodeJInstr alloc (.storeMem base off (.reg s)) ++ rest)
      = some (renameJ alloc (.storeMem base off (.reg s)), rest) := by
  obtain ⟨m, ts, hm, hmod⟩ :=
    memTail_head (gpNum (regOf alloc s)) (gpNum (regOf alloc base)) off
  have hdec :=
    decodeMemTail_memTail32 (gpNum (regOf alloc s)) (gpNum (regOf alloc base)) off rest h
  rw [hm, List.cons_append] at hdec
  simp only [encodeJInstr, encMemMov, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, hm,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0x89 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0x89 : Nat) % 2 ^ 8 ∧ (0x89 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0x89 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right hmod, rexX_rex _ _ _ (Nat.zero_le 1) (bit_le_one _ _), hdec,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf, ite_true]

/-- `MULX off(%base), %dstLo, %dstHi` (`VEX.LZ.F2.0F38.W1 F6 /r` against
    `[base + disp]`, signed 32-bit displacement) decodes back to itself when the
    allocation pins the implicit multiplier operand to `%rdx`. -/
theorem roundtrip_mulxMem32 (alloc : GpAlloc) (dh dl a base : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk32 off = true)
    (ha : mulxRdxOk alloc (.mulxMem dh dl (.reg a) base off) = true) :
    decodeJ1 (encodeJInstr alloc (.mulxMem dh dl (.reg a) base off) ++ rest)
      = some (renameJ alloc (.mulxMem dh dl (.reg a) base off), rest) := by
  have hrdx : regName (gpNum (regOf alloc a)) = "%rdx" := by
    simp only [mulxRdxOk, beq_iff_eq] at ha
    rw [ha]; rfl
  obtain ⟨m, ts, hm, hmod⟩ :=
    memTail_head (gpNum (regOf alloc dh)) (gpNum (regOf alloc base)) off
  have hdec :=
    decodeMemTail_memTail32 (gpNum (regOf alloc dh)) (gpNum (regOf alloc base)) off rest h
  rw [hm, List.cons_append] at hdec
  simp only [encodeJInstr, encMulxMem, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, hm, decodeJ1, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0xc4 : Nat) % 2 ^ 8 = 0x66) by decide),
    ite_eq_right (show ¬((0xc4 : Nat) % 2 ^ 8 = 0xf3) by decide), decodeMulx,
    vex1_bit6, vex1_map,
    vex1_rbar _ _ (bit_le_one _ _) (bit_le_one _ _),
    vex1_bbar _ _ (bit_le_one _ _) (bit_le_one _ _),
    vex2_w, vex2_pp, vex2_vvvv _ (gpNum_lt_16 _), one_sub_one_sub_bit,
    ite_eq_right hmod, hdec, regName_split, renameJ, operandOf, nameOf, hrdx,
    ite_true, and_true]

/-- The index-free `LEA off(%base), %dst` (`REX.W 8D /r` against `[base + disp]`,
    signed 32-bit displacement), written `lea dst base base 0 off`, decodes back to
    itself. -/
theorem roundtrip_lea32 (alloc : GpAlloc) (d base : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk32 off = true) :
    decodeJ1 (encodeJInstr alloc (.lea d base base 0 off) ++ rest)
      = some (renameJ alloc (.lea d base base 0 off), rest) := by
  obtain ⟨m, ts, hm, hmod⟩ :=
    memTail_head (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off
  have hdec :=
    decodeMemTail_memTail32 (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off rest h
  rw [hm, List.cons_append] at hdec
  simp only [encodeJInstr, encMemMov, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, hm,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0x8d : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0x8d : Nat) % 2 ^ 8 ∧ (0x8d : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0x8d : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0x8d : Nat) % 2 ^ 8 = 0x89) by decide),
    ne_eq, hmod, not_false_eq_true, ite_eq_left,
    rexX_rex _ _ _ (Nat.zero_le 1) (bit_le_one _ _), hdec,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ]

/-- `MOV (%base,%idx,scale), %dst` (`REX.W 8B /r` with a SIB byte) decodes back
    to itself when the index register is not `%rsp` and the stride is `1`, `2`,
    `4` or `8`. -/
theorem roundtrip_loadMemIdx (alloc : GpAlloc) (d base idx : String) (scale : Nat)
    (rest : List (BitVec 8)) (hx4 : gpNum (regOf alloc idx) ≠ 4)
    (hs : scaleOk scale = true) :
    decodeJ1 (encodeJInstr alloc (.loadMemIdx d base idx scale) ++ rest)
      = some (renameJ alloc (.loadMemIdx d base idx scale), rest) := by
  have hdec := fun md hmd => decodeMemTail_sibTail (gpNum (regOf alloc d))
    (gpNum (regOf alloc base)) (gpNum (regOf alloc idx)) scale md rest (gpNum_lt_16 _) hx4 hs hmd
  by_cases h5 : gpNum (regOf alloc base) &&& 7 = 5
  · have hd := hdec 1 (Or.inr rfl)
    simp only [ite_true, List.cons_append, List.nil_append] at hd
    simp only [encodeJInstr, encMemMovSib, ite_eq_left h5, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, sibModRM_eq_modRMMem,
      decodeJ1_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
      decodeRex, BitVec.toNat_ofNat,
      ite_eq_right (show ¬((0x8b : Nat) % 2 ^ 8 = 0x0f) by decide),
      ite_eq_right (show ¬(0xb8 ≤ (0x8b : Nat) % 2 ^ 8 ∧ (0x8b : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
      rexX_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _), hd,
      rexR_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
      rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, nameOf, ite_true]
  · have hd := hdec 0 (Or.inl ⟨rfl, h5⟩)
    simp only [ite_eq_right (show ¬((0 : Nat) = 1) by decide), List.cons_append,
      List.nil_append] at hd
    simp only [encodeJInstr, encMemMovSib, ite_eq_right h5, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, sibModRM_eq_modRMMem,
      decodeJ1_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
      decodeRex, BitVec.toNat_ofNat,
      ite_eq_right (show ¬((0x8b : Nat) % 2 ^ 8 = 0x0f) by decide),
      ite_eq_right (show ¬(0xb8 ≤ (0x8b : Nat) % 2 ^ 8 ∧ (0x8b : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
      rexX_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _), hd,
      rexR_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
      rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, nameOf, ite_true]

/-- `MOV %src, (%base,%idx,scale)` (`REX.W 89 /r` with a SIB byte) decodes back
    to itself when the index register is not `%rsp` and the stride is `1`, `2`,
    `4` or `8`. -/
theorem roundtrip_storeMemIdx (alloc : GpAlloc) (base idx : String) (scale : Nat)
    (s : String) (rest : List (BitVec 8)) (hx4 : gpNum (regOf alloc idx) ≠ 4)
    (hs : scaleOk scale = true) :
    decodeJ1 (encodeJInstr alloc (.storeMemIdx base idx scale (.reg s)) ++ rest)
      = some (renameJ alloc (.storeMemIdx base idx scale (.reg s)), rest) := by
  have hdec := fun md hmd => decodeMemTail_sibTail (gpNum (regOf alloc s))
    (gpNum (regOf alloc base)) (gpNum (regOf alloc idx)) scale md rest (gpNum_lt_16 _) hx4 hs hmd
  have hmod : ∀ md, md < 4 →
      modField (BitVec.ofNat 8 (modRMMem md (gpNum (regOf alloc s)) 4)) = md :=
    fun md hmd => modField_modRMMem _ _ _ hmd
  by_cases h5 : gpNum (regOf alloc base) &&& 7 = 5
  · have hd := hdec 1 (Or.inr rfl)
    simp only [ite_true, List.cons_append, List.nil_append] at hd
    simp only [encodeJInstr, encMemMovSib, ite_eq_left h5, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, sibModRM_eq_modRMMem,
      decodeJ1_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
      decodeRex, BitVec.toNat_ofNat,
      ite_eq_right (show ¬((0x89 : Nat) % 2 ^ 8 = 0x0f) by decide),
      ite_eq_right (show ¬(0xb8 ≤ (0x89 : Nat) % 2 ^ 8 ∧ (0x89 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
      ite_eq_right (show ¬((0x89 : Nat) % 2 ^ 8 = 0x8b) by decide),
      hmod 1 (by decide), ite_eq_right (show ¬((1 : Nat) = 3) by decide),
      rexX_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _), hd,
      rexR_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
      rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf, nameOf, ite_true]
  · have hd := hdec 0 (Or.inl ⟨rfl, h5⟩)
    simp only [ite_eq_right (show ¬((0 : Nat) = 1) by decide), List.cons_append,
      List.nil_append] at hd
    simp only [encodeJInstr, encMemMovSib, ite_eq_right h5, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, sibModRM_eq_modRMMem,
      decodeJ1_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
      decodeRex, BitVec.toNat_ofNat,
      ite_eq_right (show ¬((0x89 : Nat) % 2 ^ 8 = 0x0f) by decide),
      ite_eq_right (show ¬(0xb8 ≤ (0x89 : Nat) % 2 ^ 8 ∧ (0x89 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
      ite_eq_right (show ¬((0x89 : Nat) % 2 ^ 8 = 0x8b) by decide),
      hmod 0 (by decide), ite_eq_right (show ¬((0 : Nat) = 3) by decide),
      rexX_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _), hd,
      rexR_rex _ _ _ (bit_le_one _ _) (bit_le_one _ _) (bit_le_one _ _),
      rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf, nameOf, ite_true]

/-- The index-free `LEA off(%base), %dst` (`REX.W 8D /r`) decodes back to itself
    for a displacement the `disp8` form encodes. -/
theorem roundtrip_lea (alloc : GpAlloc) (d base : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk off = true) :
    decodeJ1 (encodeJInstr alloc (.lea d base base 0 off) ++ rest)
      = some (renameJ alloc (.lea d base base 0 off), rest) :=
  roundtrip_lea32 alloc d base off rest (dispOk32_of_dispOk off h)

/-- `MOV off(%base), %dst` (`REX.W 8B /r`) decodes back to itself for a
    displacement the `disp8` form encodes. -/
theorem roundtrip_loadMem (alloc : GpAlloc) (d base : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk off = true) :
    decodeJ1 (encodeJInstr alloc (.loadMem d base off) ++ rest)
      = some (renameJ alloc (.loadMem d base off), rest) :=
  roundtrip_loadMem32 alloc d base off rest (dispOk32_of_dispOk off h)

/-- `MOV %src, off(%base)` (`REX.W 89 /r`) decodes back to itself for a
    displacement the `disp8` form encodes. -/
theorem roundtrip_storeMem (alloc : GpAlloc) (base s : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk off = true) :
    decodeJ1 (encodeJInstr alloc (.storeMem base off (.reg s)) ++ rest)
      = some (renameJ alloc (.storeMem base off (.reg s)), rest) :=
  roundtrip_storeMem32 alloc base s off rest (dispOk32_of_dispOk off h)

/-- `MULX off(%base), %dstLo, %dstHi` (`VEX.LZ.F2.0F38.W1 F6 /r` against
    `[base + disp8]`) decodes back to itself when the allocation pins the
    implicit multiplier operand to `%rdx`. -/
theorem roundtrip_mulxMem (alloc : GpAlloc) (dh dl a base : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk off = true)
    (ha : mulxRdxOk alloc (.mulxMem dh dl (.reg a) base off) = true) :
    decodeJ1 (encodeJInstr alloc (.mulxMem dh dl (.reg a) base off) ++ rest)
      = some (renameJ alloc (.mulxMem dh dl (.reg a) base off), rest) :=
  roundtrip_mulxMem32 alloc dh dl a base off rest (dispOk32_of_dispOk off h) ha

/-! ## 10. Round-trip for the legacy REX-prefixed GP forms

The one-byte-opcode ALU/MOV forms, the `0F`-map `IMUL`/`CMOVcc`, the
immediate-source groups (`81 /digit id`, `C7 /0 id`, `B8+r io`, `69 /r id`),
the `C1 /ext ib` shifts and `F7 /3 NEG`. Each decodes off the front of its own
bytes and leaves the rest of the stream untouched. -/

/-- The one-byte opcodes `decodeRex` routes to the `aluMnemonic` table: a byte
    that is neither the `0F` escape, nor in the `B8+r` immediate-`MOV` block,
    nor one of the ModRM-extension or memory opcodes `decodeRex` dispatches
    before reaching the table. -/
def aluTableOp (op : Nat) : Bool :=
  op < 256 ∧ op ≠ 0x0f ∧ ¬ (0xb8 ≤ op ∧ op ≤ 0xbf) ∧ op ≠ 0x8b ∧ op ≠ 0x89 ∧
    op ≠ 0x81 ∧ op ≠ 0xc7 ∧ op ≠ 0x69 ∧ op ≠ 0xc1 ∧ op ≠ 0xf7

/-- A reg-reg legacy ALU form (`REX.W op /r`) decodes back to the mnemonic its
    opcode names in `aluMnemonic`, with `reg` the source and `rm` the
    destination. -/
theorem roundtrip_aluRR (alloc : GpAlloc) (op : Nat)
    (mk : String → JOperand → JInstr 64) (d s : String) (rest : List (BitVec 8))
    (hop : aluTableOp op = true) (halu : aluMnemonic op = some mk) :
    decodeJ1 (encAluRR op (gpNum (regOf alloc d)) (gpNum (regOf alloc s)) ++ rest)
      = some (mk (nameOf alloc d) (.reg (nameOf alloc s)), rest) := by
  simp only [aluTableOp, decide_eq_true_eq] at hop
  obtain ⟨hlt, h0f, hb8, h8b, h89, h81, hc7, h69, hc1, hf7⟩ := hop
  have hm : op % 2 ^ 8 = op := Nat.mod_eq_of_lt hlt
  simp only [encAluRR, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat, hm, ite_eq_right h0f, ite_eq_right hb8, ite_eq_right h8b, ite_eq_right h89,
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    ite_false, ite_eq_right h81, ite_eq_right hc7, ite_eq_right h69, ite_eq_right hc1, ite_eq_right hf7, halu]

/-- `MOV %src, %dst` (`REX.W 89 /r`) decodes back to itself. -/
theorem roundtrip_movRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.mov d (.reg s)) ++ rest)
      = some (renameJ alloc (.mov d (.reg s)), rest) := by
  simp only [encodeJInstr, encAluRR, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0x89 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0x89 : Nat) % 2 ^ 8 ∧ (0x89 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0x89 : Nat) % 2 ^ 8 = 0x8b) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf, ite_true]

/-- `ADD %src, %dst` (`REX.W 01 /r`) decodes back to itself. -/
theorem roundtrip_addRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.add d (.reg s)) ++ rest)
      = some (renameJ alloc (.add d (.reg s)), rest) :=
  roundtrip_aluRR alloc 0x01 JInstr.add d s rest (by decide) rfl

/-- `OR %src, %dst` (`REX.W 09 /r`) decodes back to itself. -/
theorem roundtrip_orRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.or_ d (.reg s)) ++ rest)
      = some (renameJ alloc (.or_ d (.reg s)), rest) :=
  roundtrip_aluRR alloc 0x09 JInstr.or_ d s rest (by decide) rfl

/-- `ADC %src, %dst` (`REX.W 11 /r`) decodes back to itself. -/
theorem roundtrip_adcRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.adc d (.reg s)) ++ rest)
      = some (renameJ alloc (.adc d (.reg s)), rest) :=
  roundtrip_aluRR alloc 0x11 JInstr.adc d s rest (by decide) rfl

/-- `SBB %src, %dst` (`REX.W 19 /r`) decodes back to itself. -/
theorem roundtrip_sbbRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.sbb d (.reg s)) ++ rest)
      = some (renameJ alloc (.sbb d (.reg s)), rest) :=
  roundtrip_aluRR alloc 0x19 JInstr.sbb d s rest (by decide) rfl

/-- `AND %src, %dst` (`REX.W 21 /r`) decodes back to itself. -/
theorem roundtrip_andRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.and_ d (.reg s)) ++ rest)
      = some (renameJ alloc (.and_ d (.reg s)), rest) :=
  roundtrip_aluRR alloc 0x21 JInstr.and_ d s rest (by decide) rfl

/-- `SUB %src, %dst` (`REX.W 29 /r`) decodes back to itself. -/
theorem roundtrip_subRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.sub d (.reg s)) ++ rest)
      = some (renameJ alloc (.sub d (.reg s)), rest) :=
  roundtrip_aluRR alloc 0x29 JInstr.sub d s rest (by decide) rfl

/-- `XOR %src, %dst` (`REX.W 31 /r`) decodes back to itself. -/
theorem roundtrip_xorRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.xor_ d (.reg s)) ++ rest)
      = some (renameJ alloc (.xor_ d (.reg s)), rest) :=
  roundtrip_aluRR alloc 0x31 JInstr.xor_ d s rest (by decide) rfl

/-- `IMUL %src, %dst` (`REX.W 0F AF /r`) decodes back to itself. The `0F`-map
    operand roles are `reg`=destination, `rm`=source. -/
theorem roundtrip_imulRR (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.imul d (.reg s)) ++ rest)
      = some (renameJ alloc (.imul d (.reg s)), rest) := by
  simp only [encodeJInstr, enc0FRR, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat, modField_modRMReg, regField_modRMReg,
    rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf, ite_true]

/-- `CMOVE %src, %dst` (`REX.W 0F 44 /r`) decodes back to itself. -/
theorem roundtrip_cmove (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.cmove d (.reg s)) ++ rest)
      = some (renameJ alloc (.cmove d (.reg s)), rest) := by
  simp only [encodeJInstr, enc0FRR, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat, modField_modRMReg, regField_modRMReg,
    rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf, ite_true,
    ite_eq_right (show ¬((0x44 : Nat) % 2 ^ 8 = 0xaf) by decide)]

/-- `CMOVNE %src, %dst` (`REX.W 0F 45 /r`) decodes back to itself. -/
theorem roundtrip_cmovne (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.cmovne d (.reg s)) ++ rest)
      = some (renameJ alloc (.cmovne d (.reg s)), rest) := by
  simp only [encodeJInstr, enc0FRR, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat, modField_modRMReg, regField_modRMReg,
    rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf, ite_true,
    ite_eq_right (show ¬((0x45 : Nat) % 2 ^ 8 = 0xaf) by decide),
    ite_eq_right (show ¬((0x45 : Nat) % 2 ^ 8 = 0x44) by decide)]

/-- `CMOVB %src, %dst` (`REX.W 0F 42 /r`) decodes back to itself. -/
theorem roundtrip_cmovb (alloc : GpAlloc) (d s : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.cmovb d (.reg s)) ++ rest)
      = some (renameJ alloc (.cmovb d (.reg s)), rest) := by
  simp only [encodeJInstr, enc0FRR, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat, modField_modRMReg, regField_modRMReg,
    rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf, ite_true,
    ite_eq_right (show ¬((0x42 : Nat) % 2 ^ 8 = 0xaf) by decide),
    ite_eq_right (show ¬((0x42 : Nat) % 2 ^ 8 = 0x44) by decide),
    ite_eq_right (show ¬((0x42 : Nat) % 2 ^ 8 = 0x45) by decide)]

/-- `MOVZX %src8, %dst` (`REX.W 0F B6 /r`, zero-extending an 8-bit source into a
    64-bit register) decodes back to itself. -/
theorem roundtrip_movzx8 (alloc : GpAlloc) (d src : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.movzx d 8 src) ++ rest)
      = some (renameJ alloc (.movzx d 8 src), rest) := by
  simp only [encodeJInstr, enc0FRR,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat, modField_modRMReg, regField_modRMReg,
    rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, nameOf, ite_true,
    ite_eq_right (show ¬((0xb6 : Nat) = 0xaf) by decide),
    ite_eq_right (show ¬((0xb6 : Nat) = 0x44) by decide),
    ite_eq_right (show ¬((0xb6 : Nat) = 0x45) by decide),
    ite_eq_right (show ¬((0xb6 : Nat) = 0x42) by decide)]

/-- `MOVZX %src16, %dst` (`REX.W 0F B7 /r`, zero-extending a 16-bit source into a
    64-bit register) decodes back to itself. -/
theorem roundtrip_movzx16 (alloc : GpAlloc) (d src : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.movzx d 16 src) ++ rest)
      = some (renameJ alloc (.movzx d 16 src), rest) := by
  simp only [encodeJInstr, ite_eq_right (show ¬((16 : Nat) = 8) by decide), enc0FRR,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat, modField_modRMReg, regField_modRMReg,
    rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, nameOf, ite_true,
    ite_eq_right (show ¬((0xb7 : Nat) = 0xaf) by decide),
    ite_eq_right (show ¬((0xb7 : Nat) = 0x44) by decide),
    ite_eq_right (show ¬((0xb7 : Nat) = 0x45) by decide),
    ite_eq_right (show ¬((0xb7 : Nat) = 0x42) by decide),
    ite_eq_right (show ¬((0xb7 : Nat) = 0xb6) by decide)]

/-- The little-endian 32-bit recomposition, on the `% 2 ^ 8` byte values the
    decoder reads out of `BitVec.ofNat 8` bytes. -/
theorem imm32_recompose_mod (v : Nat) (hv : v < 2 ^ 32) :
    (v &&& 0xff) % 2 ^ 8 + ((v >>> 8) &&& 0xff) % 2 ^ 8 * 0x100
      + ((v >>> 16) &&& 0xff) % 2 ^ 8 * 0x10000
      + ((v >>> 24) &&& 0xff) % 2 ^ 8 * 0x1000000 = v := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The little-endian 32-bit recomposition of the `imm32LE` bytes of any `v` is
    `v % 2 ^ 32`. -/
theorem imm32_recompose_mod_any (v : Nat) :
    (v &&& 0xff) % 2 ^ 8 + ((v >>> 8) &&& 0xff) % 2 ^ 8 * 0x100
      + ((v >>> 16) &&& 0xff) % 2 ^ 8 * 0x10000
      + ((v >>> 24) &&& 0xff) % 2 ^ 8 * 0x1000000 = v % 2 ^ 32 := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  omega

/-- Below `2 ^ 31` the sign extension is the identity. -/
theorem sext32_of_lt (u : Nat) (h : u < 2 ^ 31) : sext32 u = u := ite_eq_left h

/-- `fitsImm32S` as the arithmetic condition it decides. -/
@[simp] theorem fitsImm32S_eq_true (v : Nat) :
    fitsImm32S v = true ↔ v < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ v := by
  simp only [fitsImm32S, Bool.or_eq_true, decide_eq_true_eq]

/-- Sign-extending the low 32 bits of a 64-bit value that fits a signed 32-bit
    immediate recovers the value: below `2 ^ 31` the low bits are the value, and
    for `2 ^ 64 - 2 ^ 31 ≤ v < 2 ^ 64` they are `v - (2 ^ 64 - 2 ^ 32)`, which is at
    least `2 ^ 31`. -/
theorem sext32_imm32 (v : Nat) (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    sext32 (v % 2 ^ 32) = v := by
  simp only [fitsImm32S, Bool.or_eq_true, decide_eq_true_eq] at hf
  unfold sext32
  split <;> omega

/-- The decoder's sign-extended reading of the `imm32LE` bytes of a 64-bit value
    that sign-extends from 32 bits is the value. -/
theorem imm32S_imm32LE (v : Nat) (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    imm32S (BitVec.ofNat 8 (v &&& 0xff)) (BitVec.ofNat 8 ((v >>> 8) &&& 0xff))
      (BitVec.ofNat 8 ((v >>> 16) &&& 0xff)) (BitVec.ofNat 8 ((v >>> 24) &&& 0xff)) = v := by
  simp only [imm32S, BitVec.toNat_ofNat, imm32_recompose_mod_any, sext32_imm32 v hv hf]

/-- The little-endian 64-bit recomposition, on the `% 2 ^ 8` byte values the
    decoder reads out of `BitVec.ofNat 8` bytes. -/
theorem imm64_recompose_mod (v : Nat) (hv : v < 2 ^ 64) :
    (v &&& 0xff) % 2 ^ 8 + ((v >>> 8) &&& 0xff) % 2 ^ 8 * 0x100
      + ((v >>> 16) &&& 0xff) % 2 ^ 8 * 0x10000
      + ((v >>> 24) &&& 0xff) % 2 ^ 8 * 0x1000000
      + ((v >>> 32) &&& 0xff) % 2 ^ 8 * 0x100000000
      + ((v >>> 40) &&& 0xff) % 2 ^ 8 * 0x10000000000
      + ((v >>> 48) &&& 0xff) % 2 ^ 8 * 0x1000000000000
      + ((v >>> 56) &&& 0xff) % 2 ^ 8 * 0x100000000000000 = v := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  omega

/-- A one-byte `imm8` value is recovered from its byte when it fits one. -/
theorem imm8_recompose_mod (v : Nat) (hv : v < 256) : (v &&& 0xff) % 2 ^ 8 = v := by
  simp only [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- An immediate-source ALU form (`REX.W 81 /digit id`) decodes back to the
    mnemonic its opcode-extension digit names in `aluImmMnemonic`, for a 64-bit
    immediate that sign-extends from 32 bits. -/
theorem roundtrip_aluImm (alloc : GpAlloc) (digit : Nat)
    (mk : String → JOperand → JInstr 64) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hdig : digit < 8) (hv : v < 2 ^ 64) (hf : fitsImm32S v = true)
    (halu : aluImmMnemonic digit = some mk) :
    decodeJ1 (encAluImm digit (gpNum (regOf alloc d)) v ++ rest)
      = some (mk (nameOf alloc d) (.imm v), rest) := by
  have hd7 : digit &&& 7 = digit := by
    rw [Nat.and_two_pow_sub_one_eq_mod digit 3]; omega
  simp only [encAluImm, imm32LE, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0x81 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0x81 : Nat) % 2 ^ 8 ∧ (0x81 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0x81 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0x81 : Nat) % 2 ^ 8 = 0x89) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg, hd7,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    ite_false, ite_true, halu, imm32S_imm32LE v hv hf]

/-- `ADD $imm32, %dst` (`REX.W 81 /0 id`) decodes back to itself. -/
theorem roundtrip_addImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1 (encodeJInstr alloc (.add d (.imm v)) ++ rest)
      = some (renameJ alloc (.add d (.imm v)), rest) :=
  roundtrip_aluImm alloc 0 JInstr.add d v rest (by decide) hv hf rfl

/-- `OR $imm32, %dst` (`REX.W 81 /1 id`) decodes back to itself. -/
theorem roundtrip_orImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1 (encodeJInstr alloc (.or_ d (.imm v)) ++ rest)
      = some (renameJ alloc (.or_ d (.imm v)), rest) :=
  roundtrip_aluImm alloc 1 JInstr.or_ d v rest (by decide) hv hf rfl

/-- `ADC $imm32, %dst` (`REX.W 81 /2 id`) decodes back to itself. -/
theorem roundtrip_adcImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1 (encodeJInstr alloc (.adc d (.imm v)) ++ rest)
      = some (renameJ alloc (.adc d (.imm v)), rest) :=
  roundtrip_aluImm alloc 2 JInstr.adc d v rest (by decide) hv hf rfl

/-- `SBB $imm32, %dst` (`REX.W 81 /3 id`) decodes back to itself. -/
theorem roundtrip_sbbImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1 (encodeJInstr alloc (.sbb d (.imm v)) ++ rest)
      = some (renameJ alloc (.sbb d (.imm v)), rest) :=
  roundtrip_aluImm alloc 3 JInstr.sbb d v rest (by decide) hv hf rfl

/-- `AND $imm32, %dst` (`REX.W 81 /4 id`) decodes back to itself. -/
theorem roundtrip_andImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1 (encodeJInstr alloc (.and_ d (.imm v)) ++ rest)
      = some (renameJ alloc (.and_ d (.imm v)), rest) :=
  roundtrip_aluImm alloc 4 JInstr.and_ d v rest (by decide) hv hf rfl

/-- `SUB $imm32, %dst` (`REX.W 81 /5 id`) decodes back to itself. -/
theorem roundtrip_subImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1 (encodeJInstr alloc (.sub d (.imm v)) ++ rest)
      = some (renameJ alloc (.sub d (.imm v)), rest) :=
  roundtrip_aluImm alloc 5 JInstr.sub d v rest (by decide) hv hf rfl

/-- `XOR $imm32, %dst` (`REX.W 81 /6 id`) decodes back to itself. -/
theorem roundtrip_xorImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1 (encodeJInstr alloc (.xor_ d (.imm v)) ++ rest)
      = some (renameJ alloc (.xor_ d (.imm v)), rest) :=
  roundtrip_aluImm alloc 6 JInstr.xor_ d v rest (by decide) hv hf rfl

/-- `IMUL $imm32, %dst, %dst` (`REX.W 69 /r id`) decodes back to itself. -/
theorem roundtrip_imulImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) (hf : fitsImm32S v = true) :
    decodeJ1 (encodeJInstr alloc (.imul d (.imm v)) ++ rest)
      = some (renameJ alloc (.imul d (.imm v)), rest) := by
  simp only [encodeJInstr, encImulImm, imm32LE, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0x69 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0x69 : Nat) % 2 ^ 8 ∧ (0x69 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0x69 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0x69 : Nat) % 2 ^ 8 = 0x89) by decide),
    ite_eq_right (show ¬((0x69 : Nat) % 2 ^ 8 = 0x81) by decide),
    ite_eq_right (show ¬((0x69 : Nat) % 2 ^ 8 = 0xc7) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    ite_false, ite_true, renameJ, operandOf, imm32S_imm32LE v hv hf]

/-- `MOV $imm, %dst` decodes back to itself for any immediate a 64-bit register
    can hold. The encoder picks the sign-extending `C7 /0 id` form below `2 ^ 31`
    and the full-width `B8+r io` form above it; both are inverted. -/
theorem roundtrip_movImm (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 2 ^ 64) :
    decodeJ1 (encodeJInstr alloc (.mov d (.imm v)) ++ rest)
      = some (renameJ alloc (.mov d (.imm v)), rest) := by
  by_cases h31 : v < 2 ^ 31
  · have hf : fitsImm32S v = true := by
      simp only [fitsImm32S, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl h31
    simp only [encodeJInstr, ite_eq_left h31, encMovImm, imm32LE, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append,
      decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
      decodeRex, BitVec.toNat_ofNat,
      ite_eq_right (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x0f) by decide),
      ite_eq_right (show ¬(0xb8 ≤ (0xc7 : Nat) % 2 ^ 8 ∧ (0xc7 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
      ite_eq_right (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x8b) by decide),
      ite_eq_right (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x89) by decide),
      ite_eq_right (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x81) by decide),
      modField_modRMReg, regField_modRMReg, rmField_modRMReg,
      rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
      ite_false, ite_true, show (0 : Nat) &&& 7 = 0 by decide, renameJ, operandOf,
      imm32S_imm32LE v hv hf]
  · have hlow : gpNum (regOf alloc d) &&& 7 = gpNum (regOf alloc d) % 8 :=
      Nat.and_two_pow_sub_one_eq_mod _ 3
    have h0f : ¬ ((0xb8 + (gpNum (regOf alloc d) &&& 7)) % 2 ^ 8 = 0x0f) := by
      rw [hlow]; omega
    have hrange : 0xb8 ≤ (0xb8 + (gpNum (regOf alloc d) &&& 7)) % 2 ^ 8
        ∧ (0xb8 + (gpNum (regOf alloc d) &&& 7)) % 2 ^ 8 ≤ 0xbf := by
      rw [hlow]; omega
    have hsub : (0xb8 + (gpNum (regOf alloc d) &&& 7)) % 2 ^ 8 - 0xb8
        = gpNum (regOf alloc d) &&& 7 := by
      rw [hlow]; omega
    simp only [encodeJInstr, ite_eq_right h31, encMovImm64, imm64LE, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append,
      decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
      decodeRex, BitVec.toNat_ofNat, ite_eq_right h0f, ite_eq_left hrange, hsub,
      rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf,
      imm64_recompose_mod v hv]

/-- `SHL $imm8, %dst` (`REX.W C1 /4 ib`) decodes back to itself. -/
theorem roundtrip_shl (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 256) :
    decodeJ1 (encodeJInstr alloc (.shl d (.imm v)) ++ rest)
      = some (renameJ alloc (.shl d (.imm v)), rest) := by
  simp only [encodeJInstr, encShiftImm, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0xc1 : Nat) % 2 ^ 8 ∧ (0xc1 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x89) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x81) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0xc7) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x69) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    ite_false, ite_true, show (4 : Nat) &&& 7 = 4 by decide, renameJ, operandOf,
    imm8_recompose_mod v hv]

/-- `SHR $imm8, %dst` (`REX.W C1 /5 ib`) decodes back to itself. -/
theorem roundtrip_shr (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 256) :
    decodeJ1 (encodeJInstr alloc (.shr d (.imm v)) ++ rest)
      = some (renameJ alloc (.shr d (.imm v)), rest) := by
  simp only [encodeJInstr, encShiftImm, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0xc1 : Nat) % 2 ^ 8 ∧ (0xc1 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x89) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x81) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0xc7) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x69) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    ite_false, ite_true, show (5 : Nat) &&& 7 = 5 by decide,
    ite_eq_right (show ¬((5 : Nat) = 4) by decide), renameJ, operandOf,
    imm8_recompose_mod v hv]

/-- `SAR $imm8, %dst` (`REX.W C1 /7 ib`) decodes back to itself. -/
theorem roundtrip_sar (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 256) :
    decodeJ1 (encodeJInstr alloc (.sar d (.imm v)) ++ rest)
      = some (renameJ alloc (.sar d (.imm v)), rest) := by
  simp only [encodeJInstr, encShiftImm, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0xc1 : Nat) % 2 ^ 8 ∧ (0xc1 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x89) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x81) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0xc7) by decide),
    ite_eq_right (show ¬((0xc1 : Nat) % 2 ^ 8 = 0x69) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    ite_false, ite_true, show (7 : Nat) &&& 7 = 7 by decide,
    ite_eq_right (show ¬((7 : Nat) = 4) by decide), ite_eq_right (show ¬((7 : Nat) = 5) by decide),
    renameJ, operandOf, imm8_recompose_mod v hv]

/-- `NEG %dst` (`REX.W F7 /3`) decodes back to itself. -/
theorem roundtrip_neg (alloc : GpAlloc) (d : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.neg d) ++ rest)
      = some (renameJ alloc (.neg d), rest) := by
  simp only [encodeJInstr, encUnaryF7, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0xf7 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0xf7 : Nat) % 2 ^ 8 ∧ (0xf7 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0xf7 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0xf7 : Nat) % 2 ^ 8 = 0x89) by decide),
    ite_eq_right (show ¬((0xf7 : Nat) % 2 ^ 8 = 0x81) by decide),
    ite_eq_right (show ¬((0xf7 : Nat) % 2 ^ 8 = 0xc7) by decide),
    ite_eq_right (show ¬((0xf7 : Nat) % 2 ^ 8 = 0x69) by decide),
    ite_eq_right (show ¬((0xf7 : Nat) % 2 ^ 8 = 0xc1) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    ite_false, ite_true, show (3 : Nat) &&& 7 = 3 by decide, renameJ]

/-! ## 11. Round-trip for `TEST`, `BT`, `setc`, the memory-source `ADCX`/`ADOX` and
the store-immediate -/

/-- `TEST %src, %a` (`REX.W 85 /r`) decodes back to itself. -/
theorem roundtrip_test (alloc : GpAlloc) (a b : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.test a (.reg b)) ++ rest)
      = some (renameJ alloc (.test a (.reg b)), rest) := by
  simp only [encodeJInstr, encAluRR, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0x85 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0x85 : Nat) % 2 ^ 8 ∧ (0x85 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0x85 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0x85 : Nat) % 2 ^ 8 = 0x89) by decide),
    ite_eq_right (show ¬((0x85 : Nat) % 2 ^ 8 = 0x81) by decide),
    ite_eq_right (show ¬((0x85 : Nat) % 2 ^ 8 = 0xc7) by decide),
    ite_eq_right (show ¬((0x85 : Nat) % 2 ^ 8 = 0x69) by decide),
    ite_eq_right (show ¬((0x85 : Nat) % 2 ^ 8 = 0xc1) by decide),
    ite_eq_right (show ¬((0x85 : Nat) % 2 ^ 8 = 0xf7) by decide),
    show aluMnemonic ((0x85 : Nat) % 2 ^ 8) = none from rfl,
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ne_eq, not_true_eq_false,
    ite_false, ite_true, renameJ, operandOf]

/-- `BT $imm8, %d` (`REX.W 0F BA /4 ib`) decodes back to itself. -/
theorem roundtrip_bt (alloc : GpAlloc) (d : String) (v : Nat) (rest : List (BitVec 8))
    (hv : v < 256) :
    decodeJ1 (encodeJInstr alloc (.bt d (.imm v)) ++ rest)
      = some (renameJ alloc (.bt d (.imm v)), rest) := by
  simp only [encodeJInstr, encBtImm8, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0xba : Nat) % 2 ^ 8 = 0xaf) by decide),
    ite_eq_right (show ¬((0xba : Nat) % 2 ^ 8 = 0x44) by decide),
    ite_eq_right (show ¬((0xba : Nat) % 2 ^ 8 = 0x45) by decide),
    ite_eq_right (show ¬((0xba : Nat) % 2 ^ 8 = 0x42) by decide),
    ite_eq_right (show ¬((0xba : Nat) % 2 ^ 8 = 0xb6) by decide),
    ite_eq_right (show ¬((0xba : Nat) % 2 ^ 8 = 0xb7) by decide),
    ite_eq_right (show ¬((0xba : Nat) % 2 ^ 8 = 0x92) by decide),
    modField_modRMReg, regField_modRMReg, rmField_modRMReg,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, ite_true,
    show (4 : Nat) &&& 7 = 4 by decide, renameJ, operandOf, imm8_recompose_mod v hv]

/-- The fused `setc` bytes `encSetcMovzx n` (`SETB %n8` then `MOVZBQ %n8, %n`)
    decode to `setc` of the `%rN` name of `n`, for each of the sixteen GP
    registers and all three `REX` bands of the `SETB`. -/
theorem decodeJ1_encSetcMovzx (n : Nat) (hn : n < 16) (rest : List (BitVec 8)) :
    decodeJ1 (encSetcMovzx n ++ rest) = some (.setc (regName n), rest) := by
  interval_cases n <;> rfl

/-- `setc %d` (`SETB %d8; MOVZBQ %d8, %d`) decodes back to itself. -/
theorem roundtrip_setc (alloc : GpAlloc) (d : String) (rest : List (BitVec 8)) :
    decodeJ1 (encodeJInstr alloc (.setc d) ++ rest)
      = some (renameJ alloc (.setc d), rest) :=
  decodeJ1_encSetcMovzx _ (gpNum_lt_16 _) rest

/-- `ADCX off(%base), %dst` (`66 REX.W 0F 38 F6 /r` against `[base + disp]`) decodes
    back to itself for a signed 32-bit displacement. -/
theorem roundtrip_adcxMem32 (alloc : GpAlloc) (d base : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk32 off = true) :
    decodeJ1 (encodeJInstr alloc (.adcxMem d base off) ++ rest)
      = some (renameJ alloc (.adcxMem d base off), rest) := by
  obtain ⟨m, ts, hm, hmod⟩ :=
    memTail_head (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off
  have hdec :=
    decodeMemTail_memTail32 (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off rest h
  rw [hm, List.cons_append] at hdec
  simp only [encodeJInstr, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, hm, decodeJ1, BitVec.toNat_ofNat, decodeAdx,
    isRex_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), ite_eq_right hmod,
    rexX_rex _ _ _ (Nat.zero_le 1) (bit_le_one _ _), hdec, regName_split, renameJ,
    ite_true, and_true]

/-- `ADOX off(%base), %dst` (`F3 REX.W 0F 38 F6 /r` against `[base + disp]`) decodes
    back to itself for a signed 32-bit displacement. -/
theorem roundtrip_adoxMem32 (alloc : GpAlloc) (d base : String) (off : Int)
    (rest : List (BitVec 8)) (h : dispOk32 off = true) :
    decodeJ1 (encodeJInstr alloc (.adoxMem d base off) ++ rest)
      = some (renameJ alloc (.adoxMem d base off), rest) := by
  obtain ⟨m, ts, hm, hmod⟩ :=
    memTail_head (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off
  have hdec :=
    decodeMemTail_memTail32 (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off rest h
  rw [hm, List.cons_append] at hdec
  simp only [encodeJInstr, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, hm, decodeJ1, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0xf3 : Nat) % 2 ^ 8 = 0x66) by decide), decodeAdx,
    isRex_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexR_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), ite_eq_right hmod,
    rexX_rex _ _ _ (Nat.zero_le 1) (bit_le_one _ _), hdec, regName_split, renameJ,
    ite_true, and_true, ite_eq_right (show ¬(false = true) by decide)]

/-- `MOV $imm32, off(%base)` (`REX.W C7 /0 id` against `[base + disp]`) decodes back
    to itself for a 64-bit immediate that sign-extends from 32 bits and a signed
    32-bit displacement. -/
theorem roundtrip_storeMemImm32 (alloc : GpAlloc) (base : String) (off : Int) (v : Nat)
    (rest : List (BitVec 8)) (hv : v < 2 ^ 64) (hf : fitsImm32S v = true)
    (h : dispOk32 off = true) :
    decodeJ1 (encodeJInstr alloc (.storeMem base off (.imm v)) ++ rest)
      = some (renameJ alloc (.storeMem base off (.imm v)), rest) := by
  obtain ⟨m, ts, hm, hmod⟩ := memTail_head 0 (gpNum (regOf alloc base)) off
  have hdec :=
    decodeMemTail_memTail32 0 (gpNum (regOf alloc base)) off (imm32LE v ++ rest) h
  rw [hm, List.cons_append] at hdec
  simp only [encodeJInstr, encMemMovImm, encMemMov, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_assoc, hm,
    decodeJ1_rex _ _ _ (bit_le_one _ _) (Nat.zero_le 1) (bit_le_one _ _),
    decodeRex, BitVec.toNat_ofNat,
    ite_eq_right (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x0f) by decide),
    ite_eq_right (show ¬(0xb8 ≤ (0xc7 : Nat) % 2 ^ 8 ∧ (0xc7 : Nat) % 2 ^ 8 ≤ 0xbf) by decide),
    ite_eq_right (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x8b) by decide),
    ite_eq_right (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x89) by decide),
    ite_eq_right (show ¬((0xc7 : Nat) % 2 ^ 8 = 0x8d) by decide),
    ne_eq, hmod, not_false_eq_true, ite_eq_left,
    rexX_rex _ _ _ (Nat.zero_le 1) (bit_le_one _ _), hdec]
  simp only [imm32LE, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    BitVec.toNat_ofNat, show (0 : Nat) &&& 7 = 0 by decide, ite_true,
    rexB_rex _ _ _ (bit_le_one _ _), regName_split, renameJ, operandOf,
    imm32S_imm32LE v hv hf]

/-! ## 12. Whole-block round-trip -/

/-- The two conjuncts of the `imm32` side condition of `decodableJ`. -/
theorem decodableJ_imm32 {v : Nat} (h : (decide (v < 2 ^ 64) && fitsImm32S v) = true) :
    v < 2 ^ 64 ∧ fitsImm32S v = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h

/-- One instruction of the covered set decodes off the front of its own bytes,
    leaving whatever follows untouched. -/
theorem roundtrip_decodeJ1 (alloc : GpAlloc) (i : JInstr 64) (rest : List (BitVec 8))
    (hc : blockCovered i = true) (hr : mulxRdxOk alloc i = true) :
    decodeJ1 (encodeJInstr alloc i ++ rest) = some (renameJ alloc i, rest) := by
  have hd : decodableJ i = true := hc
  clear hc
  cases i with
  | mov d s =>
      cases s with
      | reg r => exact roundtrip_movRR _ _ _ _
      | imm v => exact roundtrip_movImm _ _ _ _ (of_decide_eq_true hd)
  | add d s =>
      cases s with
      | reg r => exact roundtrip_addRR _ _ _ _
      | imm v => exact roundtrip_addImm _ _ _ _ (decodableJ_imm32 hd).1 (decodableJ_imm32 hd).2
  | sub d s =>
      cases s with
      | reg r => exact roundtrip_subRR _ _ _ _
      | imm v => exact roundtrip_subImm _ _ _ _ (decodableJ_imm32 hd).1 (decodableJ_imm32 hd).2
  | adc d s =>
      cases s with
      | reg r => exact roundtrip_adcRR _ _ _ _
      | imm v => exact roundtrip_adcImm _ _ _ _ (decodableJ_imm32 hd).1 (decodableJ_imm32 hd).2
  | sbb d s =>
      cases s with
      | reg r => exact roundtrip_sbbRR _ _ _ _
      | imm v => exact roundtrip_sbbImm _ _ _ _ (decodableJ_imm32 hd).1 (decodableJ_imm32 hd).2
  | imul d s =>
      cases s with
      | reg r => exact roundtrip_imulRR _ _ _ _
      | imm v => exact roundtrip_imulImm _ _ _ _ (decodableJ_imm32 hd).1 (decodableJ_imm32 hd).2
  | neg d => exact roundtrip_neg _ _ _
  | setc d => exact roundtrip_setc _ _ _
  | and_ d s =>
      cases s with
      | reg r => exact roundtrip_andRR _ _ _ _
      | imm v => exact roundtrip_andImm _ _ _ _ (decodableJ_imm32 hd).1 (decodableJ_imm32 hd).2
  | test a b =>
      cases b with
      | reg r => exact roundtrip_test _ _ _ _
      | imm v => simp [decodableJ] at hd
  | or_ d s =>
      cases s with
      | reg r => exact roundtrip_orRR _ _ _ _
      | imm v => exact roundtrip_orImm _ _ _ _ (decodableJ_imm32 hd).1 (decodableJ_imm32 hd).2
  | xor_ d s =>
      cases s with
      | reg r => exact roundtrip_xorRR _ _ _ _
      | imm v => exact roundtrip_xorImm _ _ _ _ (decodableJ_imm32 hd).1 (decodableJ_imm32 hd).2
  | shl d s =>
      cases s with
      | reg r => simp [decodableJ] at hd
      | imm v => exact roundtrip_shl _ _ _ _ (of_decide_eq_true hd)
  | shr d s =>
      cases s with
      | reg r => simp [decodableJ] at hd
      | imm v => exact roundtrip_shr _ _ _ _ (of_decide_eq_true hd)
  | sar d s =>
      cases s with
      | reg r => simp [decodableJ] at hd
      | imm v => exact roundtrip_sar _ _ _ _ (of_decide_eq_true hd)
  | cmove d s =>
      cases s with
      | reg r => exact roundtrip_cmove _ _ _ _
      | imm v => simp [decodableJ] at hd
  | cmovne d s =>
      cases s with
      | reg r => exact roundtrip_cmovne _ _ _ _
      | imm v => simp [decodableJ] at hd
  | cmovb d s =>
      cases s with
      | reg r => exact roundtrip_cmovb _ _ _ _
      | imm v => simp [decodableJ] at hd
  | mulx dh dl a b =>
      cases a with
      | imm v => simp [decodableJ] at hd
      | reg ra =>
          cases b with
          | imm v => simp [decodableJ] at hd
          | reg rb => exact roundtrip_mulx _ _ _ _ _ _ hr
  | mulxMem dh dl a base off =>
      cases a with
      | imm v => simp [decodableJ] at hd
      | reg ra => exact roundtrip_mulxMem32 _ _ _ _ _ _ _ hd hr
  | adcx d s =>
      cases s with
      | reg r => exact roundtrip_adcx _ _ _ _
      | imm v => simp [decodableJ] at hd
  | adox d s =>
      cases s with
      | reg r => exact roundtrip_adox _ _ _ _
      | imm v => simp [decodableJ] at hd
  | loadMem d base off => exact roundtrip_loadMem32 _ _ _ _ _ hd
  | storeMem base off s =>
      cases s with
      | reg r => exact roundtrip_storeMem32 _ _ _ _ _ hd
      | imm v =>
          simp only [decodableJ, Bool.and_eq_true, decide_eq_true_eq] at hd
          exact roundtrip_storeMemImm32 _ _ _ _ _ hd.1.1 hd.1.2 hd.2
  | loadMemIdx d base idx scale => simp [decodableJ] at hd
  | storeMemIdx base idx scale s => simp [decodableJ] at hd
  | loadSym d sym => simp [decodableJ] at hd
  | cmp a b => simp [decodableJ] at hd
  | not_ d => simp [decodableJ] at hd
  | andn d a b => simp [decodableJ] at hd
  | rol d amt => simp [decodableJ] at hd
  | ror d amt => simp [decodableJ] at hd
  | rorx d src amt => simp [decodableJ] at hd
  | shlx d src cnt => simp [decodableJ] at hd
  | shrx d src cnt => simp [decodableJ] at hd
  | sarx d src cnt => simp [decodableJ] at hd
  | movzx d sw src =>
      rcases eq_or_ne sw 8 with rfl | h8
      · exact roundtrip_movzx8 _ _ _ _
      · rcases eq_or_ne sw 16 with rfl | h16
        · exact roundtrip_movzx16 _ _ _ _
        · simp [decodableJ, h8, h16] at hd
  | movsx d sw src => simp [decodableJ] at hd
  | lea d base idx scale off =>
      simp only [decodableJ, Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨⟨rfl, rfl⟩, hoff⟩ := hd
      exact roundtrip_lea32 _ _ _ _ _ hoff
  | bt d s =>
      cases s with
      | reg r => simp [decodableJ] at hd
      | imm v => exact roundtrip_bt _ _ _ _ (of_decide_eq_true hd)
  | adcxMem d base off => exact roundtrip_adcxMem32 _ _ _ _ _ hd
  | adoxMem d base off => exact roundtrip_adoxMem32 _ _ _ _ _ hd
  | inc _ | dec _ | clc | stc | xchg _ _ | imulri _ _ _ | mul _ _ _ | imulWide _ _ _
  | shld _ _ _ | shrd _ _ _ | rcl _ _ | rcr _ _ | cmovcc _ _ _ | setcc _ _
  | testN _ _ _ | btr _ _ | bts _ _
  | addMem _ _ _ | addToMem _ _ _ | imulMem _ _ _
  | imulriMem _ _ _ _ | cmpMem _ _ _ | cmovccMem _ _ _ _ | bzhi _ _ _ =>
      simp [decodableJ] at hd

/-- A block built from the covered forms decodes back, instruction by
    instruction, with no bytes left over. -/
theorem roundtrip_block (alloc : GpAlloc) (block : List (JInstr 64))
    (hc : ∀ i ∈ block, blockCovered i = true)
    (hr : ∀ i ∈ block, mulxRdxOk alloc i = true) :
    decodeJStream block.length (encodeJBlock alloc block)
      = some (block.map (renameJ alloc)) := by
  induction block with
  | nil => rfl
  | cons i is ih =>
      have hrest := ih (fun j hj => hc j (by simp [hj])) (fun j hj => hr j (by simp [hj]))
      simp only [encodeJBlock] at hrest ⊢
      simp only [List.length_cons, List.flatMap_cons, decodeJStream,
        roundtrip_decodeJ1 alloc i _ (hc i (by simp)) (hr i (by simp)),
        hrest, Option.map_some, List.map_cons]

end CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
