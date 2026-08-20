/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAsmPrinter

/-!
# A verified machine-code byte encoder for the scalar A64 `AInst` instructions (#533 sub-2)

`ArmAsmPrinter.lean` prints an `AInst` block to GAS AArch64 assembly *text*, which
is then handed to `as`/`clang` to be encoded into machine bytes — that last step
trusts the assembler's instruction encoder. This module is the **AArch64 analogue
of `X86Backend/ScalarEncoder.lean`**: it encodes each `AInst` directly to its
AArch64 fixed-width 32-bit machine-code word in Lean, so the kernel body is emitted
as bytes by a function whose output we audit against the Arm ARM and round-trip
against the official `rems-project/sail-arm` decode tables (`SailArmDecoder.lean`).

A64 is a **fixed-width** ISA: every instruction is exactly one little-endian
32-bit word (4 bytes). This is dramatically simpler than the x86 variable-length
REX/ModRM/SIB stream — there are no prefixes, no operand-size byte, no ModRM
addressing modes for the GP-ALU subset; each mnemonic is a fixed field layout
over the 32-bit word, with the register numbers and immediate sitting in fixed
bit positions. We compute the word arithmetically and split it little-endian.

## The narrowed trust boundary (same posture as the x86 encoder)

`ArmAsmPrinter` → `as` trusts (printer is correct GAS syntax) ∧ (`as` encodes each
mnemonic per the Arm ARM). This encoder replaces both with a *Lean* function whose
every output word is determined by the fixed A64 field construction below —
auditable field by field against the Arm Architecture Reference Manual (the C4.1
"A64 instruction set encoding" tables). The remaining trusted edge shrinks to
*this encoder matches the ARM*, discharged two ways:

* **structurally** — `encodeAInst` always emits a well-formed 4-byte word
  (`encode_length` below), proved unconditionally for all inputs;
* **round-trip** — `SailArmDecoder.lean` proves `decode (encode i) = i` against the
  official sail-arm `decode64` field splits (transcribed from
  `bench/reference_install/sail-arm/arm-v8.5-a/model/aarch_decode.sail`), so the
  encoder's bytes are *proved* to decode back to the same instruction under the
  authoritative Arm decode discipline, not just matched to `as`.

The bench differential pin (`bench/arm_compare`) cross-checks the emitted words
against `aarch64-linux-gnu-as` output for the same quarter-round (the qemu KAT).

## Encoding layout (the C4.1 A64 forms this transcribes, W-registers, `sf=0`)

All fields are at the bit positions the sail-arm `decode64` clauses read
(`op_code[hi..lo]`); `sf=0` selects the 32-bit `W` operand size.

* **ADD/SUB (shifted register)** — `sf op S 01011 shift(2) 0 Rm(5) imm6(6) Rn(5) Rd(5)`:
  `op=0` ADD / `op=1` SUB, `S=0` (no flags), `shift=00` (LSL), `imm6=0` (no shift).
  Decode clause: `_ 0001011 …` (ADD), `_ 1001011 …` (SUB).
* **AND/ORR/EOR (shifted register)** — `sf opc(2) 01010 shift(2) N Rm(5) imm6(6) Rn(5) Rd(5)`:
  `opc=00` AND / `opc=01` ORR / `opc=10` EOR, `N=0`, `shift=00`, `imm6=0`.
  Decode clause: `_ ??01010 …`.
* **EXTR (the ROR basis)** — `sf 00100111 N 0 Rm(5) imms(6) Rn(5) Rd(5)` with
  `N=sf`. `ROR Wd, Wn, #sh` is the alias `EXTR Wd, Wn, Wn, #sh` (`Rm=Rn`,
  `imms=sh`). Decode clause: `_ 00100111 _ 0 …`.
* **LSL/LSR (immediate)** — bitfield (UBFM) `sf 10 100110 N immr(6) imms(6) Rn(5) Rd(5)`,
  `opc=10` (UBFM), `N=sf`. `LSR Wd, Wn, #sh` = `UBFM Wd, Wn, #sh, #31`
  (`immr=sh`, `imms=31`); `LSL Wd, Wn, #sh` = `UBFM Wd, Wn, #(-sh mod 32), #(31-sh)`.
* **MOV (register)** — the alias `ORR Wd, WZR, Wm` (`Rn=31` = WZR).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder

open CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. Register-name → number, and the little-endian word splitter -/

/-- The numeric index `0..31` of a `wN` register name, in the A64 register
    encoding (`w0=0 … w30=30`, `wzr=31`). A name not in the pool reads as `0`
    (never produced by `allocGp` on a fitting block; an overflow yields the
    `<UNALLOCATED:_>` sentinel, encoded as `0`). The zero register `wzr` is `31`. -/
def wNum (r : String) : Nat :=
  if r = "wzr" then 31
  else (List.range 31).findIdx? (fun i => r = "w" ++ toString i) |>.getD 0

/-- Split a 32-bit instruction word into its four little-endian bytes (A64 is a
    little-endian fixed-width ISA: byte 0 is `word[7:0]`). -/
def wordLE (w : Nat) : List (BitVec 8) :=
  [ w &&& 0xff, (w >>> 8) &&& 0xff, (w >>> 16) &&& 0xff, (w >>> 24) &&& 0xff ].map
    (BitVec.ofNat 8)

/-! ## 2. The fixed-field A64 word builders

Each builder places the register numbers / immediate at the exact bit positions
the sail-arm `decode64` clause reads them from. `sf=0` (the leading `0` in each
constant) selects the 32-bit `W` operand size. -/

/-- ADD/SUB (shifted register), `W` form, `shift=LSL #0`. `op=0` ADD, `op=1` SUB.
    Word: `0(sf) op 0 01011 00(shift) 0 Rm(5) 000000(imm6) Rn(5) Rd(5)`. -/
def encAddSub (op d n m : Nat) : List (BitVec 8) :=
  -- bits: [31]=0 [30]=op [29]=0(S) [28:24]=01011 [23:22]=00 [21]=0
  --       [20:16]=Rm [15:10]=0 [9:5]=Rn [4:0]=Rd
  let w := (op % 2) * 0x40000000 + 0x0b000000
           + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- AND/ORR/EOR (shifted register), `W` form, `shift=LSL #0`, `N=0`.
    `opc=00` AND, `01` ORR, `10` EOR.
    Word: `0(sf) opc(2) 01010 00(shift) 0(N) Rm(5) 000000 Rn(5) Rd(5)`. -/
def encLogical (opc d n m : Nat) : List (BitVec 8) :=
  -- bits: [31]=0 [30:29]=opc [28:24]=01010 [23:22]=00 [21]=0(N)
  --       [20:16]=Rm [15:10]=0 [9:5]=Rn [4:0]=Rd
  let w := (opc % 4) * 0x20000000 + 0x0a000000
           + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- `EXTR Wd, Wn, Wm, #lsb`, `W` form (`N=0`). `ROR Wd, Wn, #sh` is the alias
    `EXTR Wd, Wn, Wn, #sh` (`Rm=Rn`, `imms=sh`).
    Word: `0(sf) 00100111 0(N) 0(o0) Rm(5) imms(6) Rn(5) Rd(5)`. -/
def encExtr (d n m imms : Nat) : List (BitVec 8) :=
  -- bits: [31]=0 [30:23]=00100111 [22]=0(N) [21]=0(o0)
  --       [20:16]=Rm [15:10]=imms [9:5]=Rn [4:0]=Rd
  let w := 0x13800000 + (m % 32) * 0x10000 + (imms % 64) * 0x400
           + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- `UBFM Wd, Wn, #immr, #imms`, `W` form (`opc=10`, `N=0`). `LSR Wd, Wn, #sh` =
    `UBFM Wd, Wn, #sh, #31`; `LSL Wd, Wn, #sh` = `UBFM Wd, Wn, #(32-sh)%32, #(31-sh)`.
    Word: `0(sf) 10(opc) 100110 0(N) immr(6) imms(6) Rn(5) Rd(5)`. -/
def encUbfm (d n immr imms : Nat) : List (BitVec 8) :=
  -- bits: [31]=0 [30:29]=10 [28:23]=100110 [22]=0(N)
  --       [21:16]=immr [15:10]=imms [9:5]=Rn [4:0]=Rd
  let w := 0x53000000 + (immr % 64) * 0x10000 + (imms % 64) * 0x400
           + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- MOVZ/MOVK (wide immediate), `W` form. `opc=10` MOVZ, `11` MOVK.
    Word: `0(sf) opc(2) 100101 hw(2) imm16(16) Rd(5)`. -/
def encMovWide (opc d imm16 hw : Nat) : List (BitVec 8) :=
  -- bits: [31]=0 [30:29]=opc [28:23]=100101 [22:21]=hw [20:5]=imm16 [4:0]=Rd
  let w := (opc % 4) * 0x20000000 + 0x12800000 + (hw % 4) * 0x200000
           + (imm16 % 0x10000) * 0x20 + (d % 32)
  wordLE w

/-! ## 3. The per-`AInst` encoder

Each arm resolves its register names through the allocation `alloc`, then dispatches
to the fixed-field builder with the C4.1 opcode field for the mnemonic. `MOV Wd, Wn`
is emitted as the canonical alias `ORR Wd, WZR, Wn` (`Rn=31`). The ChaCha rotate is
`ROR`, emitted as the `EXTR Wd, Wn, Wn, #imm` alias. -/

/-- Encode one scalar `AInst` to its AArch64 machine bytes (a single 4-byte word),
    resolving register names through `alloc`. -/
def encodeAInst (alloc : GpAlloc) : AInst → List (BitVec 8)
  | .add d a b => encAddSub 0 (wNum (gpOf alloc d)) (wNum (gpOf alloc a)) (wNum (gpOf alloc b))
  | .sub d a b => encAddSub 1 (wNum (gpOf alloc d)) (wNum (gpOf alloc a)) (wNum (gpOf alloc b))
  | .and d a b => encLogical 0 (wNum (gpOf alloc d)) (wNum (gpOf alloc a)) (wNum (gpOf alloc b))
  | .orr d a b => encLogical 1 (wNum (gpOf alloc d)) (wNum (gpOf alloc a)) (wNum (gpOf alloc b))
  | .eor d a b => encLogical 2 (wNum (gpOf alloc d)) (wNum (gpOf alloc a)) (wNum (gpOf alloc b))
  | .ror d a imm => encExtr (wNum (gpOf alloc d)) (wNum (gpOf alloc a)) (wNum (gpOf alloc a)) (imm % 32)
  | .lsr d a imm => encUbfm (wNum (gpOf alloc d)) (wNum (gpOf alloc a)) (imm % 32) 31
  | .lsl d a imm => encUbfm (wNum (gpOf alloc d)) (wNum (gpOf alloc a)) ((32 - imm % 32) % 32) (31 - imm % 32)
  | .mov d s   => encLogical 1 (wNum (gpOf alloc d)) 31 (wNum (gpOf alloc s))  -- ORR Wd, WZR, Ws

/-- Encode a whole block: concatenate the 4-byte word encodings of its instructions.
    The contiguous machine-code stream a `.text` section / loader consumes. -/
def encodeABlock (alloc : GpAlloc) (block : List AInst) : List (BitVec 8) :=
  block.flatMap (encodeAInst alloc)

/-! ### 3b. The branch / control-flow encoders (the looped-emission words, #551)

A64 branches carry a **PC-relative immediate offset** to the target label, in
units of 4 bytes (the offset is `(target_addr - branch_addr) / 4`, a *signed*
field). The looped emission's back-edge jumps *backwards* to the loop top, so the
offset is negative; the encoder takes the offset as a two's-complement value
already reduced into the field width (`imm26` for `B`, `imm19` for `B.cond`/`CBNZ`),
matching what the assembler computes from the label. The fixed opcode bits are the
C4.1 "Branches, exception generating and system instructions" forms:

* **B** (unconditional immediate) — `000101 imm26`. Top byte `0x14`.
* **B.cond** (conditional immediate) — `0101010 0 imm19 0 cond`. Top byte `0x54`.
* **CBNZ/CBZ** (compare-and-branch, `W` form `sf=0`) — `0 011010 op imm19 Rt`
  with `op=1` CBNZ / `op=0` CBZ. Top byte `0x35` / `0x34`.

`imm19`/`imm26` are masked into their field width (the encoder's caller supplies
the already-resolved signed offset; only the low field bits matter for the word). -/

/-- `B label` — unconditional branch. `imm26` is the PC-relative word offset
    (signed, masked to 26 bits). Word: `000101(opc) imm26(26)`. -/
def encB (imm26 : Nat) : List (BitVec 8) :=
  let w := 0x14000000 + (imm26 % 0x4000000)
  wordLE w

/-- `B.cond label` — conditional branch on the 4-bit condition `cond`. `imm19` is
    the PC-relative word offset (signed, masked to 19 bits).
    Word: `0101010 0 imm19(19) 0 cond(4)`. -/
def encBcond (cond imm19 : Nat) : List (BitVec 8) :=
  let w := 0x54000000 + (imm19 % 0x80000) * 0x20 + (cond % 16)
  wordLE w

/-- `CBNZ Wt, label` (`op=1`) / `CBZ Wt, label` (`op=0`), `W` form (`sf=0`).
    `imm19` is the PC-relative word offset (signed, masked to 19 bits).
    Word: `0(sf) 011010 op imm19(19) Rt(5)`. -/
def encCmpBranch (op t imm19 : Nat) : List (BitVec 8) :=
  let w := 0x34000000 + (op % 2) * 0x1000000 + (imm19 % 0x80000) * 0x20 + (t % 32)
  wordLE w

/-- Encode one `ABranch` to its AArch64 machine bytes. A `label` is a pure
    assembler symbol with **no** machine word, so it encodes to the empty byte
    list; the branches resolve their PC-relative offset through `resolve` (the
    word offset to the target label, signed-masked into the field). The
    `resolve` argument is the label-resolution step the assembler performs
    (computing `(target - here)/4`); the encoder takes it as a parameter so the
    byte-diff harness can supply the same offsets `as` computes. -/
def encodeABranch (alloc : GpAlloc) (resolve : ALabel → Nat) : ABranch → List (BitVec 8)
  | .label _   => []
  | .b l       => encB (resolve l)
  | .bcond c l => encBcond c.num (resolve l)
  | .cbnz t l  => encCmpBranch 1 (wNum (gpOf alloc t)) (resolve l)
  | .cbz t l   => encCmpBranch 0 (wNum (gpOf alloc t)) (resolve l)

/-! ## 4. Structural well-formedness (the unconditional half of the trust story)

Every `encodeAInst` output is exactly one 4-byte A64 word — the fixed-width shape
the decoder requires, proved for all inputs (the encoder analogue of x86's
`encAluRR_length`). -/

@[simp] theorem wordLE_length (w : Nat) : (wordLE w).length = 4 := by
  simp [wordLE]

/-- Every `AInst` encodes to exactly 4 bytes (one fixed-width A64 word). -/
theorem encodeAInst_length (alloc : GpAlloc) (i : AInst) :
    (encodeAInst alloc i).length = 4 := by
  cases i <;> simp [encodeAInst, encAddSub, encLogical, encExtr, encUbfm]

/-- `encodeABlock` produces `4 * |block|` bytes (a fixed-width stream). -/
theorem encodeABlock_length (alloc : GpAlloc) (block : List AInst) :
    (encodeABlock alloc block).length = 4 * block.length := by
  induction block with
  | nil => rfl
  | cons i is ih =>
      simp only [encodeABlock, List.flatMap_cons, List.length_append, List.length_cons]
      rw [show encodeABlock alloc is = is.flatMap (encodeAInst alloc) from rfl] at ih
      rw [encodeAInst_length, ih]; omega

/-! ## 5. Differential pins against `aarch64-linux-gnu-as` (the gas anchor)

These pin the emitted 32-bit word to the exact little-endian bytes
`aarch64-linux-gnu-as` produces for the same mnemonic in the ChaCha quarter-round
(`bench/arm_compare`; the words appear in `objdump -d` as the big-endian-printed
hex shown in each comment). The bytes are little-endian, so e.g. `add w0,w0,w1`
(`objdump` `0b010000`) is the byte list `[0x00,0x00,0x01,0x0b]`. Together with
`SailArmDecoder`'s `decode (encode i) = i`, the encoder is both gas-matched and
decode-round-trip-proved. -/

/-- A helper allocation pinning `a b c d` (and temps) to `w0 w1 w2 w3`. -/
def qrAlloc : GpAlloc :=
  [("a","w0"), ("b","w1"), ("c","w2"), ("d","w3")]

-- `add w0, w0, w1` — gas word `0x0b010000`, little-endian `00 00 01 0b`.
#guard encodeAInst qrAlloc (.add "a" "a" "b")
    == [0x00, 0x00, 0x01, 0x0b].map (BitVec.ofNat 8)

-- `eor w3, w3, w0` — gas word `0x4a000063`, little-endian `63 00 00 4a`.
#guard encodeAInst qrAlloc (.eor "d" "d" "a")
    == [0x63, 0x00, 0x00, 0x4a].map (BitVec.ofNat 8)

-- `ror w3, w3, #16` — gas word `0x13834063`, little-endian `63 40 83 13`.
#guard encodeAInst qrAlloc (.ror "d" "d" 16)
    == [0x63, 0x40, 0x83, 0x13].map (BitVec.ofNat 8)

-- `ror w1, w1, #20` — gas word `0x13815021`, little-endian `21 50 81 13`.
#guard encodeAInst qrAlloc (.ror "b" "b" 20)
    == [0x21, 0x50, 0x81, 0x13].map (BitVec.ofNat 8)

-- `add w2, w2, w3` — gas word `0x0b030042`, little-endian `42 00 03 0b`.
#guard encodeAInst qrAlloc (.add "c" "c" "d")
    == [0x42, 0x00, 0x03, 0x0b].map (BitVec.ofNat 8)

/-! ### 5b. Branch-encoder well-formedness + gas differential pins (#551)

Each branch instruction is one 4-byte word (a label is 0 bytes); the words are
pinned to `aarch64-linux-gnu-as` for the looped back-edge offsets. The reference
words (from `objdump -d` on a back-edge to the loop top) are: `cbnz w9, .L`
(offset −1) `0x35ffffe9`; `b.ne .L` (offset −2) `0x54ffffc1`; `b .L` (offset −3)
`0x17fffffd`; `cbz w9, .L` (offset −4) `0x34ffff89`. -/

/-- Each branch word is exactly 4 bytes; a label is 0 bytes. -/
theorem encodeABranch_length (alloc : GpAlloc) (resolve : ALabel → Nat) (i : ABranch) :
    (encodeABranch alloc resolve i).length = (match i with | .label _ => 0 | _ => 4) := by
  cases i <;> simp [encodeABranch, encB, encBcond, encCmpBranch]

-- `cbnz w9, .L` with back-edge offset `−1` (`imm19 = 2^19−1`) — gas word
-- `0x35ffffe9`, little-endian `e9 ff ff 35`.
#guard encCmpBranch 1 9 (0x80000 - 1)
    == [0xe9, 0xff, 0xff, 0x35].map (BitVec.ofNat 8)

-- `b.ne .L` with offset `−2` (`imm19 = 2^19−2`) — gas word `0x54ffffc1`,
-- little-endian `c1 ff ff 54`.
#guard encBcond 1 (0x80000 - 2)
    == [0xc1, 0xff, 0xff, 0x54].map (BitVec.ofNat 8)

-- `b .L` with offset `−3` (`imm26 = 2^26−3`) — gas word `0x17fffffd`,
-- little-endian `fd ff ff 17`.
#guard encB (0x4000000 - 3)
    == [0xfd, 0xff, 0xff, 0x17].map (BitVec.ofNat 8)

-- `cbz w9, .L` with offset `−4` (`imm19 = 2^19−4`) — gas word `0x34ffff89`,
-- little-endian `89 ff ff 34`.
#guard encCmpBranch 0 9 (0x80000 - 4)
    == [0x89, 0xff, 0xff, 0x34].map (BitVec.ofNat 8)

/-! ## 6. The 64-bit bignum/field instruction encoder (#547)

The A64 analogue of the x86 ADX/BMI2 carry-chain encoder, for the
`ArmModel.BInst` 64-bit subset. The field layouts are transcribed from the same
sail-arm `aarch_decode.sail` `decode64` clauses (the `decodeBignumWord` dispatch
in `SailArmDecoder` reads exactly these positions); `sf=1` (the leading `1` in
each constant) selects the 64-bit `X` operand size. -/

/-- The numeric index `0..31` of an `xN` register name (`x0=0 … x30=30`,
    `xzr=31`). Same table shape as `wNum`, for the 64-bit register file. -/
def xNum (r : String) : Nat :=
  if r = "xzr" then 31
  else (List.range 31).findIdx? (fun i => r = "x" ++ toString i) |>.getD 0

/-- ADD/SUB (shifted register), `X` form (`sf=1`), `shift=LSL #0`. `op=0` ADD,
    `op=1` SUB; `S` is the flag-setting bit (`S=1` ⇒ ADDS/SUBS).
    Word: `1(sf) op S 01011 00 0 Rm(5) 000000 Rn(5) Rd(5)`. -/
def encAddSubX (op s d n m : Nat) : List (BitVec 8) :=
  let w := 0x80000000 + (op % 2) * 0x40000000 + (s % 2) * 0x20000000 + 0x0b000000
           + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- ADC/SBC (add/subtract with carry), `X` form. `op=0` ADC, `op=1` SBC; `S` the
    flag-setting bit. Word: `1(sf) op S 11010000 Rm(5) 000000 Rn(5) Rd(5)`. -/
def encAddSubCarry (op s d n m : Nat) : List (BitVec 8) :=
  let w := 0x80000000 + (op % 2) * 0x40000000 + (s % 2) * 0x20000000 + 0x1a000000
           + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- `MADD Xd, Xn, Xm, Xa`, `X` form. `MUL Xd,Xn,Xm = MADD Xd,Xn,Xm,XZR` (`Ra=31`).
    Word: `1(sf) 0011011 000 Rm(5) 0(o0) Ra(5) Rn(5) Rd(5)`. -/
def encMadd (d n m a : Nat) : List (BitVec 8) :=
  let w := 0x9b000000 + (m % 32) * 0x10000 + (a % 32) * 0x400
           + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- `UMULH Xd, Xn, Xm`, `X` form. Word: `1(sf) 0011011 110 Rm(5) 0(o0) 11111(Ra)
    Rn(5) Rd(5)` (`U=1` via bit[23], `Ra=31`). -/
def encUmulh (d n m : Nat) : List (BitVec 8) :=
  -- 0b10011011110 = 0x4DE at bits[31:21]; +Ra=31 in [14:10] = 31*0x400
  let w := 0x9bc00000 + (m % 32) * 0x10000 + 31 * 0x400
           + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- `CSEL Xd, Xn, Xm, cond` (conditional select), `X` form (`op=0`, `S=0`, `o2=0`).
    `cond` is the 4-bit condition (`cc=0b0011=3`, `cs=0b0010=2`).
    Word: `1(sf) 0 0 11010100 Rm(5) cond(4) 0(o2) 0 Rn(5) Rd(5)`. -/
def encCsel (d n m cond : Nat) : List (BitVec 8) :=
  let w := 0x9a800000 + (m % 32) * 0x10000 + (cond % 16) * 0x1000
           + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- MOVZ/MOVK (wide immediate), `X` form (`sf=1`). `opc=10` MOVZ, `11` MOVK.
    Word: `1(sf) opc(2) 100101 hw(2) imm16(16) Rd(5)`. -/
def encMovWideX (opc d imm16 hw : Nat) : List (BitVec 8) :=
  let w := 0x80000000 + (opc % 4) * 0x20000000 + 0x12800000 + (hw % 4) * 0x200000
           + (imm16 % 0x10000) * 0x20 + (d % 32)
  wordLE w

/-- ORR (shifted register), `X` form (`sf=1`, `opc=01`, `N=0`, `shift=LSL #0`).
    `MOV Xd, Xs = ORR Xd, XZR, Xs` (`Rn=31`).
    Word: `1(sf) 01(opc) 01010 00 0(N) Rm(5) 000000 Rn(5) Rd(5)`. -/
def encOrrX (d n m : Nat) : List (BitVec 8) :=
  let w := 0xaa000000 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- AND (shifted register), `X` form (`sf=1`, `opc=00`, `N=0`, `shift=LSL #0`).
    Word base `0x8a000000`: `1(sf) 00(opc) 01010 00 0(N) Rm(5) 000000 Rn(5) Rd(5)`. -/
def encAndX (d n m : Nat) : List (BitVec 8) :=
  let w := 0x8a000000 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- EOR (shifted register), `X` form (`sf=1`, `opc=10`, `N=0`, `shift=LSL #0`).
    Word base `0xca000000`: `1(sf) 10(opc) 01010 00 0(N) Rm(5) 000000 Rn(5) Rd(5)`. -/
def encEorX (d n m : Nat) : List (BitVec 8) :=
  let w := 0xca000000 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- UBFM, `X` form (`sf=1`, `opc=10`, `N=1`), the bitfield-move base of the
    `LSR`/`LSL`/`UBFX` aliases. Word base `0xd3400000`:
    `1(sf) 10(opc) 100110 1(N) immr(6) imms(6) Rn(5) Rd(5)`.
    `LSR Xd,Xn,#sh` = `UBFM Xd,Xn,#sh,#63`;
    `LSL Xd,Xn,#sh` = `UBFM Xd,Xn,#((64−sh) mod 64),#(63−sh)`. -/
def encUbfmX (immr imms n d : Nat) : List (BitVec 8) :=
  let w := 0xd3400000 + (immr % 64) * 0x10000 + (imms % 64) * 0x400
            + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- The cc/cs condition-code numbers (`cc/LO = 0b0011`, `cs/HS = 0b0010`). -/
def acondNum : ACond → Nat
  | .cc => 3
  | .cs => 2

/-- Encode one 64-bit `BInst` to its AArch64 machine bytes (a single 4-byte
    word), resolving register names through `alloc` (an `xN` assignment). `MOV`
    is the `ORR Xd, XZR, Xs` alias on the 64-bit logical form. -/
def encodeBInst (alloc : GpAlloc) : BInst → List (BitVec 8)
  | .add d a b => encAddSubX 0 0 (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .sub d a b => encAddSubX 1 0 (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .adds d a b => encAddSubX 0 1 (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .subs d a b => encAddSubX 1 1 (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .adc d a b => encAddSubCarry 0 0 (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .adcs d a b => encAddSubCarry 0 1 (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .sbc d a b => encAddSubCarry 1 0 (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .sbcs d a b => encAddSubCarry 1 1 (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .mul d a b => encMadd (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b)) 31
  | .umulh d a b => encUmulh (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .and d a b => encAndX (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .orr d a b => encOrrX (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .eor d a b => encEorX (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b))
  | .csel d a b c => encCsel (xNum (gpOf alloc d)) (xNum (gpOf alloc a)) (xNum (gpOf alloc b)) (acondNum c)
  | .movz d imm16 => encMovWideX 2 (xNum (gpOf alloc d)) (imm16 % 0x10000) 0
  | .movk d imm16 hw => encMovWideX 3 (xNum (gpOf alloc d)) (imm16 % 0x10000) hw
  | .lsr d a sh => encUbfmX (sh % 64) 63 (xNum (gpOf alloc a)) (xNum (gpOf alloc d))
  | .lsl d a sh => encUbfmX ((64 - sh % 64) % 64) (63 - sh % 64) (xNum (gpOf alloc a)) (xNum (gpOf alloc d))
  | .mov d s => encOrrX (xNum (gpOf alloc d)) 31 (xNum (gpOf alloc s)) -- ORR Xd, XZR, Xs

/-- Encode a whole 64-bit block: concatenate the 4-byte word encodings. -/
def encodeBBlock (alloc : GpAlloc) (block : List BInst) : List (BitVec 8) :=
  block.flatMap (encodeBInst alloc)

/-- Every `BInst` encodes to exactly 4 bytes (one fixed-width A64 word). -/
theorem encodeBInst_length (alloc : GpAlloc) (i : BInst) :
    (encodeBInst alloc i).length = 4 := by
  cases i <;>
    simp [encodeBInst, encAddSubX, encAddSubCarry, encMadd, encUmulh, encCsel,
      encMovWideX, encOrrX, encAndX, encEorX, encUbfmX]

/-! ### Differential pins against `aarch64-linux-gnu-as` (the bignum gas anchor)

These pin the emitted 64-bit word to the exact little-endian bytes
`aarch64-linux-gnu-as` produces for the `bignum_add_p256` mnemonics (verified in
the bench `addp256-bytes-diff` target). A `bignum_add_p256`-shaped allocation
pins the SSA names to the s2n register choices `x0..x11`. -/

/-- A `bignum_add_p256` register allocation (the s2n choices `d0..d3=x4..x7`,
    `n0..n3=x8..x11`, `c=x3`, constants `p0/p1/p3=x12..x14`). -/
def addp256Alloc : GpAlloc :=
  [ ("d0","x4"),("d1","x5"),("d2","x6"),("d3","x7")
  , ("n0","x8"),("n1","x9"),("n2","x10"),("n3","x11")
  , ("c","x3"),("p0","x12"),("p1","x13"),("p3","x14") ]

-- `adds x4, x4, x8` — gas word `0xab080084`, little-endian `84 00 08 ab`.
#guard encodeBInst addp256Alloc (.adds "d0" "d0" "n0")
    == [0x84, 0x00, 0x08, 0xab].map (BitVec.ofNat 8)

-- `adcs x5, x5, x9` — gas word `0xba0900a5`, little-endian `a5 00 09 ba`.
#guard encodeBInst addp256Alloc (.adcs "d1" "d1" "n1")
    == [0xa5, 0x00, 0x09, 0xba].map (BitVec.ofNat 8)

-- `adc x3, xzr, xzr` — gas word `0x9a1f03e3`, little-endian `e3 03 1f 9a`.
#guard encodeBInst addp256Alloc (.adc "c" "xzr" "xzr")
    == [0xe3, 0x03, 0x1f, 0x9a].map (BitVec.ofNat 8)

-- `subs x8, x4, x12` — gas word `0xeb0c0088`, little-endian `88 00 0c eb`.
#guard encodeBInst addp256Alloc (.subs "n0" "d0" "p0")
    == [0x88, 0x00, 0x0c, 0xeb].map (BitVec.ofNat 8)

-- `sbcs x9, x5, x13` — gas word `0xfa0d00a9`, little-endian `a9 00 0d fa`.
#guard encodeBInst addp256Alloc (.sbcs "n1" "d1" "p1")
    == [0xa9, 0x00, 0x0d, 0xfa].map (BitVec.ofNat 8)

-- `sbcs x10, x6, xzr` — gas word `0xfa1f00ca`, little-endian `ca 00 1f fa`.
#guard encodeBInst addp256Alloc (.sbcs "n2" "d2" "xzr")
    == [0xca, 0x00, 0x1f, 0xfa].map (BitVec.ofNat 8)

-- `csel x4, x4, x8, cc` — gas word `0x9a883084`, little-endian `84 30 88 9a`.
#guard encodeBInst addp256Alloc (.csel "d0" "d0" "n0" .cc)
    == [0x84, 0x30, 0x88, 0x9a].map (BitVec.ofNat 8)

-- `movz x12, #0xffff` — gas word `0xd29fffec`, little-endian `ec ff 9f d2`.
#guard encodeBInst addp256Alloc (.movz "p0" 0xffff)
    == [0xec, 0xff, 0x9f, 0xd2].map (BitVec.ofNat 8)

-- `movk x12, #0xffff, lsl #16` — gas word `0xf2bfffec`, little-endian `ec ff bf f2`.
#guard encodeBInst addp256Alloc (.movk "p0" 0xffff 1)
    == [0xec, 0xff, 0xbf, 0xf2].map (BitVec.ofNat 8)

/-! ### 64-bit logical-op pins (the Plonky3 AArch64 Merkle-mixer ops)

The owned AArch64 Plonky3 scalar Poseidon2 path (`plonky3_merkle_compress_rc` /
`plonky3_merkle_hash_leaf_rc`, `bench/arm_compare/plonky3_kernels_a64_emit.lean`)
uses the 64-bit logical ops; these pin them to `aarch64-linux-gnu-as`. -/

-- `eor x16, x16, x17` — gas word `0xca110210`, little-endian `10 02 11 ca`.
#guard encodeBInst [("d","x16"),("a","x16"),("b","x17")] (.eor "d" "a" "b")
    == [0x10, 0x02, 0x11, 0xca].map (BitVec.ofNat 8)

-- `and x0, x1, x2` — gas word `0x8a020020`, little-endian `20 00 02 8a`.
#guard encodeBInst [("d","x0"),("a","x1"),("b","x2")] (.and "d" "a" "b")
    == [0x20, 0x00, 0x02, 0x8a].map (BitVec.ofNat 8)

-- `orr x3, x4, x5` — gas word `0xaa050083`, little-endian `83 00 05 aa`.
#guard encodeBInst [("d","x3"),("a","x4"),("b","x5")] (.orr "d" "a" "b")
    == [0x83, 0x00, 0x05, 0xaa].map (BitVec.ofNat 8)

-- `mul x0, x1, x2` — gas word `0x9b027c20`, little-endian `20 7c 02 9b`.
#guard encodeBInst [("lo","x0"),("a","x1"),("b","x2")] (.mul "lo" "a" "b")
    == [0x20, 0x7c, 0x02, 0x9b].map (BitVec.ofNat 8)

-- `umulh x0, x1, x2` — gas word `0x9bc27c20`, little-endian `20 7c c2 9b`.
#guard encodeBInst [("hi","x0"),("a","x1"),("b","x2")] (.umulh "hi" "a" "b")
    == [0x20, 0x7c, 0xc2, 0x9b].map (BitVec.ofNat 8)

-- `mov x4, x8` (= `ORR x4, xzr, x8`) — gas word `0xaa0803e4`, little-endian
-- `e4 03 08 aa`.
#guard encodeBInst [("d","x4"),("s","x8")] (.mov "d" "s")
    == [0xe4, 0x03, 0x08, 0xaa].map (BitVec.ofNat 8)

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
