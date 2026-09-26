/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
public import CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
public meta import CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCryptCore.Tactics.KatGuard

/-!
# VEX.256 machine bytes of the `YmmOp` op set

`encodeYmmInst op d a b` is the x86-64 machine encoding of one register-only
`YmmOp`, with `d` the destination `%ymm` number, `a` the first source and `b` the
second source (ignored by the unary ops). The operand roles are those of the
denotation `YmmOp.denoteBinary`: `a` is `VEX.vvvv` (Intel src1) and `b` is
`ModRM.rm` (Intel src2) for the three-register ops; for the immediate shifts `d`
is `VEX.vvvv` and `a` is `ModRM.rm` with the opcode extension in `ModRM.reg`; for
the unary moves and permutes `d` is `ModRM.reg`, `a` is `ModRM.rm` and `vvvv` is
unused. The AT&T line `VIR.YmmAsmPrint.renderYmmInstr` renders for the same
`(op, d, a, b)` is `op b, a, d` (binary), `op a, d` (unary), with `$imm` first
for the immediate-carrying ops.

Every arm is a VEX.256 (`L = 1`) encoding built from the prefix layer of
`X86Backend.CryptoExt` (`encAvx2Alu`, `encAvx2_0F38`, `encVex3`, `encVexAuto`,
`encVpermq`, `encVpblendd`) and from `VsimdByteEncoder` (`encodeVsimdShiftImm`,
`encVpshufdU`). The 2-byte `C5` form is chosen exactly when gas chooses it: map
`0F`, `W = 0` and `ModRM.rm` below 8.

Two ops have no VEX encoding: `vpmullq` (AVX-512DQ) and `vprolq` (AVX-512F), both
EVEX-only. They encode as `UD2`, as does any instruction naming a register
numbered 16 or higher, which VEX cannot address.

## Main results

* `encodeYmmVex`: the per-constructor VEX.256 encoding.
* `encodeYmmInst`: `encodeYmmVex` on VEX-addressable registers, `UD2` otherwise.
* `encodeYmmInst_*_eq_gas`: per-family pins against GNU as 2.42
  (`as --64` + `objdump -d`), each over the register triples
  `(d, a, b) = (3, 5, 7)`, `(2, 1, 9)` and `(12, 4, 6)` for the binary ops and
  `(d, a) = (3, 5)`, `(2, 9)` and `(12, 4)` for the unary ops, which cover the
  2-byte form, the 3-byte form forced by a high `ModRM.rm`, and a high
  destination.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmByteEncoder

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect (YmmOp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
  (encUd2 encodeVsimdShiftImm encVpshufdU)

/-! ## 1. The encoder -/

/-- The VEX.256 encoding of one `YmmOp` with destination `d`, first source `a`
    (`VEX.vvvv`) and second source `b` (`ModRM.rm`). The immediate shifts put
    `d` in `vvvv` and `a` in `ModRM.rm`; the unary moves and permutes put `d` in
    `ModRM.reg` and `a` in `ModRM.rm`. `vpmullq` and `vprolq` are EVEX-only and
    encode as `UD2`. Register numbers are read modulo 16. -/
def encodeYmmVex : YmmOp → (d a b : Nat) → List (BitVec 8)
  -- `66 0F` three-register ALU ops (2-byte VEX when `b < 8`).
  | .vpsubq,      d, a, b => encAvx2Alu 0xfb 1 d a b
  | .vpaddd,      d, a, b => encAvx2Alu 0xfe 1 d a b
  | .vpsubd,      d, a, b => encAvx2Alu 0xfa 1 d a b
  | .vpmuludq,    d, a, b => encAvx2Alu 0xf4 1 d a b
  | .vpaddq,      d, a, b => encAvx2Alu 0xd4 1 d a b
  | .vpand,       d, a, b => encAvx2Alu 0xdb 1 d a b
  | .vpor,        d, a, b => encAvx2Alu 0xeb 1 d a b
  | .vpxor,       d, a, b => encAvx2Alu 0xef 1 d a b
  | .vpandn,      d, a, b => encAvx2Alu 0xdf 1 d a b
  | .vpaddw,      d, a, b => encAvx2Alu 0xfd 1 d a b
  | .vpsubw,      d, a, b => encAvx2Alu 0xf9 1 d a b
  | .vpmullw,     d, a, b => encAvx2Alu 0xd5 1 d a b
  | .vpmulhw,     d, a, b => encAvx2Alu 0xe5 1 d a b
  | .vpmaddwd,    d, a, b => encAvx2Alu 0xf5 1 d a b
  | .vpcmpgtw,    d, a, b => encAvx2Alu 0x65 1 d a b
  | .vpcmpgtd,    d, a, b => encAvx2Alu 0x66 1 d a b
  | .vpcmpeqd,    d, a, b => encAvx2Alu 0x76 1 d a b
  | .vpacksswb,   d, a, b => encAvx2Alu 0x63 1 d a b
  | .vpackssdw,   d, a, b => encAvx2Alu 0x6b 1 d a b
  | .vpunpckldq,  d, a, b => encAvx2Alu 0x62 1 d a b
  | .vpunpckhdq,  d, a, b => encAvx2Alu 0x6a 1 d a b
  | .vpunpcklqdq, d, a, b => encAvx2Alu 0x6c 1 d a b
  | .vpunpckhqdq, d, a, b => encAvx2Alu 0x6d 1 d a b
  -- `66 0F38` three-register ops (always 3-byte VEX, `W = 0`).
  | .vpmuldq,     d, a, b => encAvx2_0F38 0x28 1 d a b
  | .vpshufb,     d, a, b => encAvx2_0F38 0x00 1 d a b
  | .vpsrlvd,     d, a, b => encAvx2_0F38 0x45 1 d a b
  | .vpsllvd,     d, a, b => encAvx2_0F38 0x47 1 d a b
  | .vpmulld,     d, a, b => encAvx2_0F38 0x40 1 d a b
  | .vpsignd,     d, a, b => encAvx2_0F38 0x0a 1 d a b
  | .vpermd,      d, a, b => encAvx2_0F38 0x36 1 d a b
  -- `66 0F38` three-register ops with `W = 1` (qword lanes).
  | .vpsrlvq,     d, a, b => encVex3 0b00010 0b01 1 1 0x45 d a b none
  | .vpsllvq,     d, a, b => encVex3 0b00010 0b01 1 1 0x47 d a b none
  -- `66 0F3A` three-register ops with a trailing `imm8`.
  | .vpblendd imm,   d, a, b => encVpblendd 1 d a b imm
  | .vpblendw imm,   d, a, b => encVex3 0b00011 0b01 0 1 0x0e d a b (some imm)
  | .vperm2i128 imm, d, a, b => encVex3 0b00011 0b01 0 1 0x46 d a b (some imm)
  -- Unary ops, `vvvv` unused.
  | .vmovshdup,   d, a, _ => encVexAuto 0b00001 0b10 0 1 0x16 d 0 a
  | .vpabsd,      d, a, _ => encAvx2_0F38 0x1e 1 d 0 a
  | .vpshufd imm, d, a, _ => encVpshufdU 1 d a imm
  | .vpermq imm,  d, a, _ => encVpermq 1 d a imm
  -- Immediate shifts `66 0F 71/72/73 /ext ib`: `/2` logical right, `/4`
  -- arithmetic right, `/6` left, `/3` whole-half byte right.
  | .vpsrlw imm,  d, a, _ => encodeVsimdShiftImm 0x71 2 1 d a imm
  | .vpsraw imm,  d, a, _ => encodeVsimdShiftImm 0x71 4 1 d a imm
  | .vpsllw imm,  d, a, _ => encodeVsimdShiftImm 0x71 6 1 d a imm
  | .vpsrld imm,  d, a, _ => encodeVsimdShiftImm 0x72 2 1 d a imm
  | .vpsrad imm,  d, a, _ => encodeVsimdShiftImm 0x72 4 1 d a imm
  | .vpslld imm,  d, a, _ => encodeVsimdShiftImm 0x72 6 1 d a imm
  | .vpsrlq imm,  d, a, _ => encodeVsimdShiftImm 0x73 2 1 d a imm
  | .vpsllq imm,  d, a, _ => encodeVsimdShiftImm 0x73 6 1 d a imm
  | .vpsrldq imm, d, a, _ => encodeVsimdShiftImm 0x73 3 1 d a imm
  -- EVEX-only ops.
  | .vpmullq,     _, _, _ => encUd2
  | .vprolq _,    _, _, _ => encUd2

/-- The registers of `(op, d, a, b)` are VEX-addressable: `d`, `a` and, for a
    binary op, `b` are below 16. -/
def ymmRegsVex (op : YmmOp) (d a b : Nat) : Bool :=
  d < 16 && a < 16 && (!op.isBinary || b < 16)

/-- The machine encoding of one `YmmOp` with destination `d`, first source `a`
    and second source `b`: `encodeYmmVex` when every register it reads or writes
    is below 16, `UD2` otherwise. -/
def encodeYmmInst (op : YmmOp) (d a b : Nat) : List (BitVec 8) :=
  if ymmRegsVex op d a b then encodeYmmVex op d a b else encUd2

/-- A byte list written as natural numbers. -/
def ymmBytes (l : List Nat) : List (BitVec 8) := l.map (BitVec.ofNat 8)

/-! ## 2. Gas pins

Each group below is the encoder's output against `objdump -d` of the object GNU
as 2.42 (`as --64`) assembles from the listed AT&T lines, which are the lines
`renderYmmInstr` prints for the same operands. -/

/-- The `66 0F` add, subtract, multiply and bitwise ops against the gas lines
    `vpsubq|vpaddd|vpsubd|vpmuludq|vpaddq|vpand|vpor|vpxor|vpandn %ymm7, %ymm5, %ymm3`,
    `… %ymm9, %ymm1, %ymm2` and `… %ymm6, %ymm4, %ymm12`. -/
theorem encodeYmmInst_alu_eq_gas :
    encodeYmmInst .vpsubq 3 5 7 = ymmBytes [0xc5, 0xd5, 0xfb, 0xdf] ∧
    encodeYmmInst .vpsubq 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xfb, 0xd1] ∧
    encodeYmmInst .vpsubq 12 4 6 = ymmBytes [0xc5, 0x5d, 0xfb, 0xe6] ∧
    encodeYmmInst .vpaddd 3 5 7 = ymmBytes [0xc5, 0xd5, 0xfe, 0xdf] ∧
    encodeYmmInst .vpaddd 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xfe, 0xd1] ∧
    encodeYmmInst .vpaddd 12 4 6 = ymmBytes [0xc5, 0x5d, 0xfe, 0xe6] ∧
    encodeYmmInst .vpsubd 3 5 7 = ymmBytes [0xc5, 0xd5, 0xfa, 0xdf] ∧
    encodeYmmInst .vpsubd 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xfa, 0xd1] ∧
    encodeYmmInst .vpsubd 12 4 6 = ymmBytes [0xc5, 0x5d, 0xfa, 0xe6] ∧
    encodeYmmInst .vpmuludq 3 5 7 = ymmBytes [0xc5, 0xd5, 0xf4, 0xdf] ∧
    encodeYmmInst .vpmuludq 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xf4, 0xd1] ∧
    encodeYmmInst .vpmuludq 12 4 6 = ymmBytes [0xc5, 0x5d, 0xf4, 0xe6] ∧
    encodeYmmInst .vpaddq 3 5 7 = ymmBytes [0xc5, 0xd5, 0xd4, 0xdf] ∧
    encodeYmmInst .vpaddq 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xd4, 0xd1] ∧
    encodeYmmInst .vpaddq 12 4 6 = ymmBytes [0xc5, 0x5d, 0xd4, 0xe6] ∧
    encodeYmmInst .vpand 3 5 7 = ymmBytes [0xc5, 0xd5, 0xdb, 0xdf] ∧
    encodeYmmInst .vpand 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xdb, 0xd1] ∧
    encodeYmmInst .vpand 12 4 6 = ymmBytes [0xc5, 0x5d, 0xdb, 0xe6] ∧
    encodeYmmInst .vpor 3 5 7 = ymmBytes [0xc5, 0xd5, 0xeb, 0xdf] ∧
    encodeYmmInst .vpor 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xeb, 0xd1] ∧
    encodeYmmInst .vpor 12 4 6 = ymmBytes [0xc5, 0x5d, 0xeb, 0xe6] ∧
    encodeYmmInst .vpxor 3 5 7 = ymmBytes [0xc5, 0xd5, 0xef, 0xdf] ∧
    encodeYmmInst .vpxor 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xef, 0xd1] ∧
    encodeYmmInst .vpxor 12 4 6 = ymmBytes [0xc5, 0x5d, 0xef, 0xe6] ∧
    encodeYmmInst .vpandn 3 5 7 = ymmBytes [0xc5, 0xd5, 0xdf, 0xdf] ∧
    encodeYmmInst .vpandn 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xdf, 0xd1] ∧
    encodeYmmInst .vpandn 12 4 6 = ymmBytes [0xc5, 0x5d, 0xdf, 0xe6] := by
  decide

/-- The `66 0F` 16-bit lane ops against the gas lines
    `vpaddw|vpsubw|vpmullw|vpmulhw|vpmaddwd %ymm7, %ymm5, %ymm3`,
    `… %ymm9, %ymm1, %ymm2` and `… %ymm6, %ymm4, %ymm12`. -/
theorem encodeYmmInst_word_eq_gas :
    encodeYmmInst .vpaddw 3 5 7 = ymmBytes [0xc5, 0xd5, 0xfd, 0xdf] ∧
    encodeYmmInst .vpaddw 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xfd, 0xd1] ∧
    encodeYmmInst .vpaddw 12 4 6 = ymmBytes [0xc5, 0x5d, 0xfd, 0xe6] ∧
    encodeYmmInst .vpsubw 3 5 7 = ymmBytes [0xc5, 0xd5, 0xf9, 0xdf] ∧
    encodeYmmInst .vpsubw 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xf9, 0xd1] ∧
    encodeYmmInst .vpsubw 12 4 6 = ymmBytes [0xc5, 0x5d, 0xf9, 0xe6] ∧
    encodeYmmInst .vpmullw 3 5 7 = ymmBytes [0xc5, 0xd5, 0xd5, 0xdf] ∧
    encodeYmmInst .vpmullw 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xd5, 0xd1] ∧
    encodeYmmInst .vpmullw 12 4 6 = ymmBytes [0xc5, 0x5d, 0xd5, 0xe6] ∧
    encodeYmmInst .vpmulhw 3 5 7 = ymmBytes [0xc5, 0xd5, 0xe5, 0xdf] ∧
    encodeYmmInst .vpmulhw 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xe5, 0xd1] ∧
    encodeYmmInst .vpmulhw 12 4 6 = ymmBytes [0xc5, 0x5d, 0xe5, 0xe6] ∧
    encodeYmmInst .vpmaddwd 3 5 7 = ymmBytes [0xc5, 0xd5, 0xf5, 0xdf] ∧
    encodeYmmInst .vpmaddwd 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0xf5, 0xd1] ∧
    encodeYmmInst .vpmaddwd 12 4 6 = ymmBytes [0xc5, 0x5d, 0xf5, 0xe6] := by
  decide

/-- The `66 0F` compare, pack and unpack ops against the gas lines
    `vpcmpgtw|vpcmpgtd|vpcmpeqd|vpacksswb|vpackssdw|vpunpckldq|vpunpckhdq|`
    `vpunpcklqdq|vpunpckhqdq %ymm7, %ymm5, %ymm3`, `… %ymm9, %ymm1, %ymm2` and
    `… %ymm6, %ymm4, %ymm12`. -/
theorem encodeYmmInst_cmpPack_eq_gas :
    encodeYmmInst .vpcmpgtw 3 5 7 = ymmBytes [0xc5, 0xd5, 0x65, 0xdf] ∧
    encodeYmmInst .vpcmpgtw 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x65, 0xd1] ∧
    encodeYmmInst .vpcmpgtw 12 4 6 = ymmBytes [0xc5, 0x5d, 0x65, 0xe6] ∧
    encodeYmmInst .vpcmpgtd 3 5 7 = ymmBytes [0xc5, 0xd5, 0x66, 0xdf] ∧
    encodeYmmInst .vpcmpgtd 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x66, 0xd1] ∧
    encodeYmmInst .vpcmpgtd 12 4 6 = ymmBytes [0xc5, 0x5d, 0x66, 0xe6] ∧
    encodeYmmInst .vpcmpeqd 3 5 7 = ymmBytes [0xc5, 0xd5, 0x76, 0xdf] ∧
    encodeYmmInst .vpcmpeqd 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x76, 0xd1] ∧
    encodeYmmInst .vpcmpeqd 12 4 6 = ymmBytes [0xc5, 0x5d, 0x76, 0xe6] ∧
    encodeYmmInst .vpacksswb 3 5 7 = ymmBytes [0xc5, 0xd5, 0x63, 0xdf] ∧
    encodeYmmInst .vpacksswb 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x63, 0xd1] ∧
    encodeYmmInst .vpacksswb 12 4 6 = ymmBytes [0xc5, 0x5d, 0x63, 0xe6] ∧
    encodeYmmInst .vpackssdw 3 5 7 = ymmBytes [0xc5, 0xd5, 0x6b, 0xdf] ∧
    encodeYmmInst .vpackssdw 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x6b, 0xd1] ∧
    encodeYmmInst .vpackssdw 12 4 6 = ymmBytes [0xc5, 0x5d, 0x6b, 0xe6] ∧
    encodeYmmInst .vpunpckldq 3 5 7 = ymmBytes [0xc5, 0xd5, 0x62, 0xdf] ∧
    encodeYmmInst .vpunpckldq 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x62, 0xd1] ∧
    encodeYmmInst .vpunpckldq 12 4 6 = ymmBytes [0xc5, 0x5d, 0x62, 0xe6] ∧
    encodeYmmInst .vpunpckhdq 3 5 7 = ymmBytes [0xc5, 0xd5, 0x6a, 0xdf] ∧
    encodeYmmInst .vpunpckhdq 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x6a, 0xd1] ∧
    encodeYmmInst .vpunpckhdq 12 4 6 = ymmBytes [0xc5, 0x5d, 0x6a, 0xe6] ∧
    encodeYmmInst .vpunpcklqdq 3 5 7 = ymmBytes [0xc5, 0xd5, 0x6c, 0xdf] ∧
    encodeYmmInst .vpunpcklqdq 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x6c, 0xd1] ∧
    encodeYmmInst .vpunpcklqdq 12 4 6 = ymmBytes [0xc5, 0x5d, 0x6c, 0xe6] ∧
    encodeYmmInst .vpunpckhqdq 3 5 7 = ymmBytes [0xc5, 0xd5, 0x6d, 0xdf] ∧
    encodeYmmInst .vpunpckhqdq 2 1 9 = ymmBytes [0xc4, 0xc1, 0x75, 0x6d, 0xd1] ∧
    encodeYmmInst .vpunpckhqdq 12 4 6 = ymmBytes [0xc5, 0x5d, 0x6d, 0xe6] := by
  decide

/-- The `66 0F38` three-register ops against the gas lines
    `vpmuldq|vpshufb|vpsrlvd|vpsllvd|vpmulld|vpsignd|vpermd %ymm7, %ymm5, %ymm3`,
    `… %ymm9, %ymm1, %ymm2` and `… %ymm6, %ymm4, %ymm12`. -/
theorem encodeYmmInst_map0F38_eq_gas :
    encodeYmmInst .vpmuldq 3 5 7 = ymmBytes [0xc4, 0xe2, 0x55, 0x28, 0xdf] ∧
    encodeYmmInst .vpmuldq 2 1 9 = ymmBytes [0xc4, 0xc2, 0x75, 0x28, 0xd1] ∧
    encodeYmmInst .vpmuldq 12 4 6 = ymmBytes [0xc4, 0x62, 0x5d, 0x28, 0xe6] ∧
    encodeYmmInst .vpshufb 3 5 7 = ymmBytes [0xc4, 0xe2, 0x55, 0x00, 0xdf] ∧
    encodeYmmInst .vpshufb 2 1 9 = ymmBytes [0xc4, 0xc2, 0x75, 0x00, 0xd1] ∧
    encodeYmmInst .vpshufb 12 4 6 = ymmBytes [0xc4, 0x62, 0x5d, 0x00, 0xe6] ∧
    encodeYmmInst .vpsrlvd 3 5 7 = ymmBytes [0xc4, 0xe2, 0x55, 0x45, 0xdf] ∧
    encodeYmmInst .vpsrlvd 2 1 9 = ymmBytes [0xc4, 0xc2, 0x75, 0x45, 0xd1] ∧
    encodeYmmInst .vpsrlvd 12 4 6 = ymmBytes [0xc4, 0x62, 0x5d, 0x45, 0xe6] ∧
    encodeYmmInst .vpsllvd 3 5 7 = ymmBytes [0xc4, 0xe2, 0x55, 0x47, 0xdf] ∧
    encodeYmmInst .vpsllvd 2 1 9 = ymmBytes [0xc4, 0xc2, 0x75, 0x47, 0xd1] ∧
    encodeYmmInst .vpsllvd 12 4 6 = ymmBytes [0xc4, 0x62, 0x5d, 0x47, 0xe6] ∧
    encodeYmmInst .vpmulld 3 5 7 = ymmBytes [0xc4, 0xe2, 0x55, 0x40, 0xdf] ∧
    encodeYmmInst .vpmulld 2 1 9 = ymmBytes [0xc4, 0xc2, 0x75, 0x40, 0xd1] ∧
    encodeYmmInst .vpmulld 12 4 6 = ymmBytes [0xc4, 0x62, 0x5d, 0x40, 0xe6] ∧
    encodeYmmInst .vpsignd 3 5 7 = ymmBytes [0xc4, 0xe2, 0x55, 0x0a, 0xdf] ∧
    encodeYmmInst .vpsignd 2 1 9 = ymmBytes [0xc4, 0xc2, 0x75, 0x0a, 0xd1] ∧
    encodeYmmInst .vpsignd 12 4 6 = ymmBytes [0xc4, 0x62, 0x5d, 0x0a, 0xe6] ∧
    encodeYmmInst .vpermd 3 5 7 = ymmBytes [0xc4, 0xe2, 0x55, 0x36, 0xdf] ∧
    encodeYmmInst .vpermd 2 1 9 = ymmBytes [0xc4, 0xc2, 0x75, 0x36, 0xd1] ∧
    encodeYmmInst .vpermd 12 4 6 = ymmBytes [0xc4, 0x62, 0x5d, 0x36, 0xe6] := by
  decide

/-- The `66 0F3A` immediate three-register ops against the gas lines
    `vpblendd $170, …`, `vpblendw $85, …` and `vperm2i128 $49, …` over
    `%ymm7, %ymm5, %ymm3`, `%ymm9, %ymm1, %ymm2` and `%ymm6, %ymm4, %ymm12`. -/
theorem encodeYmmInst_map0F3A_eq_gas :
    encodeYmmInst (.vpblendd 170) 3 5 7 = ymmBytes [0xc4, 0xe3, 0x55, 0x02, 0xdf, 0xaa] ∧
    encodeYmmInst (.vpblendd 170) 2 1 9 = ymmBytes [0xc4, 0xc3, 0x75, 0x02, 0xd1, 0xaa] ∧
    encodeYmmInst (.vpblendd 170) 12 4 6 = ymmBytes [0xc4, 0x63, 0x5d, 0x02, 0xe6, 0xaa] ∧
    encodeYmmInst (.vpblendw 85) 3 5 7 = ymmBytes [0xc4, 0xe3, 0x55, 0x0e, 0xdf, 0x55] ∧
    encodeYmmInst (.vpblendw 85) 2 1 9 = ymmBytes [0xc4, 0xc3, 0x75, 0x0e, 0xd1, 0x55] ∧
    encodeYmmInst (.vpblendw 85) 12 4 6 = ymmBytes [0xc4, 0x63, 0x5d, 0x0e, 0xe6, 0x55] ∧
    encodeYmmInst (.vperm2i128 49) 3 5 7 = ymmBytes [0xc4, 0xe3, 0x55, 0x46, 0xdf, 0x31] ∧
    encodeYmmInst (.vperm2i128 49) 2 1 9 = ymmBytes [0xc4, 0xc3, 0x75, 0x46, 0xd1, 0x31] ∧
    encodeYmmInst (.vperm2i128 49) 12 4 6 =
      ymmBytes [0xc4, 0x63, 0x5d, 0x46, 0xe6, 0x31] := by
  decide

/-- The unary moves and permutes against the gas lines
    `vmovshdup|vpabsd %ymm5, %ymm3`, `vpshufd $245, …` and `vpermq $238, …`, each
    also over `%ymm9, %ymm2` and `%ymm4, %ymm12`. -/
theorem encodeYmmInst_unary_eq_gas :
    encodeYmmInst .vmovshdup 3 5 0 = ymmBytes [0xc5, 0xfe, 0x16, 0xdd] ∧
    encodeYmmInst .vmovshdup 2 9 0 = ymmBytes [0xc4, 0xc1, 0x7e, 0x16, 0xd1] ∧
    encodeYmmInst .vmovshdup 12 4 0 = ymmBytes [0xc5, 0x7e, 0x16, 0xe4] ∧
    encodeYmmInst .vpabsd 3 5 0 = ymmBytes [0xc4, 0xe2, 0x7d, 0x1e, 0xdd] ∧
    encodeYmmInst .vpabsd 2 9 0 = ymmBytes [0xc4, 0xc2, 0x7d, 0x1e, 0xd1] ∧
    encodeYmmInst .vpabsd 12 4 0 = ymmBytes [0xc4, 0x62, 0x7d, 0x1e, 0xe4] ∧
    encodeYmmInst (.vpshufd 245) 3 5 0 = ymmBytes [0xc5, 0xfd, 0x70, 0xdd, 0xf5] ∧
    encodeYmmInst (.vpshufd 245) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x7d, 0x70, 0xd1, 0xf5] ∧
    encodeYmmInst (.vpshufd 245) 12 4 0 = ymmBytes [0xc5, 0x7d, 0x70, 0xe4, 0xf5] ∧
    encodeYmmInst (.vpermq 238) 3 5 0 = ymmBytes [0xc4, 0xe3, 0xfd, 0x00, 0xdd, 0xee] ∧
    encodeYmmInst (.vpermq 238) 2 9 0 = ymmBytes [0xc4, 0xc3, 0xfd, 0x00, 0xd1, 0xee] ∧
    encodeYmmInst (.vpermq 238) 12 4 0 = ymmBytes [0xc4, 0x63, 0xfd, 0x00, 0xe4, 0xee] := by
  decide

/-- The immediate shifts against the gas lines `vpsrlq $26`, `vpsllq $23`,
    `vpsrld $20`, `vpslld $12`, `vpsrad $31`, `vpsllw $3`, `vpsrlw $10`,
    `vpsraw $15` and `vpsrldq $8`, each over `%ymm5, %ymm3`, `%ymm9, %ymm2` and
    `%ymm4, %ymm12`. -/
theorem encodeYmmInst_shiftImm_eq_gas :
    encodeYmmInst (.vpsrlq 26) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x73, 0xd5, 0x1a] ∧
    encodeYmmInst (.vpsrlq 26) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x73, 0xd1, 0x1a] ∧
    encodeYmmInst (.vpsrlq 26) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x73, 0xd4, 0x1a] ∧
    encodeYmmInst (.vpsllq 23) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x73, 0xf5, 0x17] ∧
    encodeYmmInst (.vpsllq 23) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x73, 0xf1, 0x17] ∧
    encodeYmmInst (.vpsllq 23) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x73, 0xf4, 0x17] ∧
    encodeYmmInst (.vpsrld 20) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x72, 0xd5, 0x14] ∧
    encodeYmmInst (.vpsrld 20) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x72, 0xd1, 0x14] ∧
    encodeYmmInst (.vpsrld 20) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x72, 0xd4, 0x14] ∧
    encodeYmmInst (.vpslld 12) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x72, 0xf5, 0x0c] ∧
    encodeYmmInst (.vpslld 12) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x72, 0xf1, 0x0c] ∧
    encodeYmmInst (.vpslld 12) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x72, 0xf4, 0x0c] ∧
    encodeYmmInst (.vpsrad 31) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x72, 0xe5, 0x1f] ∧
    encodeYmmInst (.vpsrad 31) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x72, 0xe1, 0x1f] ∧
    encodeYmmInst (.vpsrad 31) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x72, 0xe4, 0x1f] ∧
    encodeYmmInst (.vpsllw 3) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x71, 0xf5, 0x03] ∧
    encodeYmmInst (.vpsllw 3) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x71, 0xf1, 0x03] ∧
    encodeYmmInst (.vpsllw 3) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x71, 0xf4, 0x03] ∧
    encodeYmmInst (.vpsrlw 10) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x71, 0xd5, 0x0a] ∧
    encodeYmmInst (.vpsrlw 10) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x71, 0xd1, 0x0a] ∧
    encodeYmmInst (.vpsrlw 10) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x71, 0xd4, 0x0a] ∧
    encodeYmmInst (.vpsraw 15) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x71, 0xe5, 0x0f] ∧
    encodeYmmInst (.vpsraw 15) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x71, 0xe1, 0x0f] ∧
    encodeYmmInst (.vpsraw 15) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x71, 0xe4, 0x0f] ∧
    encodeYmmInst (.vpsrldq 8) 3 5 0 = ymmBytes [0xc5, 0xe5, 0x73, 0xdd, 0x08] ∧
    encodeYmmInst (.vpsrldq 8) 2 9 0 = ymmBytes [0xc4, 0xc1, 0x6d, 0x73, 0xd9, 0x08] ∧
    encodeYmmInst (.vpsrldq 8) 12 4 0 = ymmBytes [0xc5, 0x9d, 0x73, 0xdc, 0x08] := by
  decide

/-- The EVEX-only ops and a register VEX cannot address encode as `UD2`
    (`0F 0B`). Gas encodes `vpmullq %ymm7, %ymm5, %ymm3` as the EVEX
    `62 f2 d5 28 40 df` and `vprolq $7, %ymm5, %ymm3` as `62 f1 e5 28 72 cd 07`;
    those are outside this encoder. -/
theorem encodeYmmInst_ud2 :
    encodeYmmInst .vpmullq 3 5 7 = ymmBytes [0x0f, 0x0b] ∧
    encodeYmmInst (.vprolq 7) 3 5 0 = ymmBytes [0x0f, 0x0b] ∧
    encodeYmmInst .vpaddq 16 5 7 = ymmBytes [0x0f, 0x0b] ∧
    encodeYmmInst .vpaddq 3 5 21 = ymmBytes [0x0f, 0x0b] ∧
    encodeYmmInst (.vpsrlq 26) 3 16 0 = ymmBytes [0x0f, 0x0b] := by
  decide

/- The per-lane qword shifts are `VEX.256.66.0F38.W1 47 /r` (`vpsllvq`) and
   `VEX.256.66.0F38.W1 45 /r` (`vpsrlvq`) in the Intel SDM. For
   `vpsllvq %ymm2, %ymm1, %ymm0` (`d, a, b = 0, 1, 2`): `C4`; `R̄ X̄ B̄ = 111` and map
   `00010` give `E2`; `W = 1`, `v̄v̄v̄v̄ = ~1 = 1110`, `L = 1`, `pp = 01` give `F5`; the
   opcode; `ModRM` `11 000 010` gives `C2`. The high-register lines
   `… %ymm9, %ymm1, %ymm2` (`B̄ = 0`) and `… %ymm6, %ymm4, %ymm12` (`R̄ = 0`,
   `vvvv = 4`) differ from the `vpsllvd`/`vpsrlvd` pins above only in the `W` bit. -/
#kat encodeYmmInst .vpsllvq 0 1 2 == ymmBytes [0xc4, 0xe2, 0xf5, 0x47, 0xc2]
#kat encodeYmmInst .vpsrlvq 0 1 2 == ymmBytes [0xc4, 0xe2, 0xf5, 0x45, 0xc2]
#kat encodeYmmInst .vpsllvq 2 1 9 == ymmBytes [0xc4, 0xc2, 0xf5, 0x47, 0xd1]
#kat encodeYmmInst .vpsrlvq 12 4 6 == ymmBytes [0xc4, 0x62, 0xdd, 0x45, 0xe6]

end CatCrypt.Crypto.SecureCompilation.VIR.YmmByteEncoder
