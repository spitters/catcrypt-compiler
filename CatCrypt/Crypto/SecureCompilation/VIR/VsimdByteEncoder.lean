/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExtEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExtEncoder

/-!
# Standalone machine-byte encoder for the unified `vsimd` op set (Vec128 teardown)

`VsimdAsmPrint` renders a `vsimd` fragment of `Com jasminDialect` to AT&T `.s`
*text* (`renderVsimdInstr`), but nothing on the unified stack produced the
machine *bytes* — the byte (VEX/EVEX) encoder lived only in the bespoke
`X86Backend.Vec128Encoder` (`encodeVInst`/`encodeVCryptInst`), whose AES-ECB-block
byte artifact (`X86Backend.SimdBytes.encodeAesEcbBlock`, gas-pinned by
`encodeAesEcbBlock_eq_gas`) keeps the whole `Vec128*` IR — and through it the
shared `Vec128Encoder` — alive.

This module reproduces that byte-encoder **capability** on the unified `SimdOp`
op set, standalone:

```
SimdOp (+ reg operands)  ──encodeVsimdInst──▶  List (BitVec 8)   (VEX bytes)
```

It imports **no** `Vec128*` file. The only non-trivial dependency is the shared
VEX/EVEX prefix-byte primitive layer `X86Backend.CryptoExtEncoder`
(`encVaes`/`encVpclmul`/`encVgf2p8mulb`/…), which is the audited bit-layout
construction `Vec128Encoder` *itself* is built on — it lives in
`CryptoExtEncoder.lean` (imports only `AsmPrinter` → `X86Dialect`), not in any
`Vec128*` file, so depending on it does not keep the Vec128 stack alive. The
`vmovdqu` memory loads/stores and `ret` (which live in the `Vec128*`-importing
`SimdBytes.lean`) are **re-defined here standalone**, so this module's whole
byte-output path is independent of the Vec128 teardown surface.

The capstone is `encodeVsimdAesEcbBlock_eq_gas`: the whole AES-128 ECB single-block
encrypt kernel, encoded entirely off the unified `SimdOp` set, is byte-for-byte
identical to the exact `gas` reference (`gasVsimdAesEcbBlockText`, the 134-byte
`.text` inlined verbatim from `SimdBytes.gasAesEcbBlockText`). This reproduces
`SimdBytes.encodeAesEcbBlock_eq_gas` on the unified stack with **zero**
`Vec128*` imports — the equal-strength replacement that unblocks the
`Vec128Encoder` deletion.

## Trust posture

Identical in kind to the bespoke `Vec128Encoder`/`SimdBytes` byte path: each VEX
prefix builder is `CryptoExt`'s audited construction, and the whole-kernel byte
string is gas-pinned (`as --64` + `objdump -d`). The decode round-trip
(`decode (encode i) = id`) for the crypto-ext / VEX SIMD opcodes is the same
gas-pinned tier (the ACL2 x86isa / sail-x86 model has no VEX SIMD decode tables);
this is the honest residual, the same ceiling `SimdBytes` records.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (SimdOp JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt

/-! ## 1. The per-instruction byte encoder for the unified `SimdOp` set

`encodeVsimdInst op d a b imm` encodes the unified `SimdOp` to its x86-64 VEX
machine bytes, taking the **destination** xmm number `d`, the two source xmm
numbers `a`/`b` (the second is ignored for unary ops), at 128-bit width (`l=0`).
Each arm reuses `CryptoExt`'s prefix builders so the byte layout is **identical**
to the corresponding `Vec128Encoder.encodeVCryptInst` / `encodeVInst` arm:

| `SimdOp`            | reuses                              | Vec128 twin              |
|---------------------|-------------------------------------|--------------------------|
| `.vaesenc`          | `encVaes 0xDC`                      | `.vaesenc`               |
| `.vaesenclast`      | `encVaes 0xDD`                      | `.vaesenclast`           |
| `.vaeskeygen rcon`  | `encVex3 0F3A DF` (`vvvv` unused)   | `.vaeskeygen`            |
| `.vpshufd imm`      | 2-byte VEX `0F 70` / 3-byte         | `.vpshufd`               |
| `.clmul imm`        | `encVpclmul`                        | `.vpclmul`               |
| `.gf2p8mulb`        | `encVgf2p8mulb`                     | `.vgf2p8mulb`            |
| `.affineqb imm`     | `encVgf2p8affineqb`                 | `.vgf2p8affineqb`        |
| `.vpshufb`          | `encAvx2_0F38 0x00`                 | `.vpshufb`               |
| `.bitwise .and`     | `encAvx2Alu 0xDB`                   | `.vpandq`                |
| `.bitwise .or`      | `encAvx2Alu 0xEB`                   | `.vpor`                  |
| `.bitwise .xor`     | `encAvx2Alu 0xEF`                   | `.vpxor`/`.vpxorq`       |
| `.packed .add 32`   | `encAvx2Alu 0xFE`                   | `.vpaddd`                |
| `.packed .add 64`   | `encAvx2Alu 0xD4`                   | `.vpaddq`                |
| `.packed .sub 32`   | `encAvx2Alu 0xFA`                   | (AVX2 `VPSUBD`)          |
| `.packed .sub 64`   | `encAvx2Alu 0xFB`                   | (AVX2 `VPSUBQ`)          |
| `.packed .add 16`   | `encAvx2Alu 0xFD`                   | (AVX2 `VPADDW`)          |
| `.packed .sub 16`   | `encAvx2Alu 0xF9`                   | (AVX2 `VPSUBW`)          |
| `.packed .mul 16`   | `encAvx2Alu 0xD5`                   | (AVX2 `VPMULLW`)         |
| `.packed .shl 32`   | `encVex3 … 0x47`                    | (AVX2 `VPSLLVD`)         |
| `.packed .shr 32`   | `encVex3 … 0x45`                    | (AVX2 `VPSRLVD`)         |
| `.packed .shl 64`   | `encVex3 … 0x47` W=1                | (AVX2 `VPSLLVQ`)         |
| `.packed .shr 64`   | `encVex3 … 0x45` W=1                | (AVX2 `VPSRLVQ`)         |
| `.packedImm .shl/.shr 16/32/64 n` | `encodeVsimdShiftImm 0x71/72/73 /6 or /2` | (`VPS{LL,RL}{W,D,Q} $n`) |
| `.mulhi16`          | `encAvx2Alu 0xE5`                   | `.vpmulhw`               |

A packed shift by a register count is the per-lane variable shift, because its
denotation `v128PackLanesW` shifts each lane by its own lane of the count
operand. The uniform-count `VPSLLD`/`VPSRLD` with a register count encodes a
different operation — its count is the low quadword of the source, not one count
per lane — and is not reachable from `SimdOp`. The immediate form is
`packedImm`, whose count is the same in every lane by construction; a
`packedImm` with no x86 instruction encodes as `UD2`.

The two byte-shift ops `vpslldq`/`vpsrldq` are `JasminOp` arms (not `SimdOp`), so
they are encoded by `encodeVsimdShift` below. -/

/-- The 2-byte-or-3-byte VEX encoding of `VPSHUFD dst, src, imm8` (`0F 70`,
    `vvvv` unused), ported byte-for-byte from `Vec128Encoder.encVpshufd`. -/
def encVpshufdU (l dst src imm : Nat) : List (BitVec 8) :=
  if bit src 3 = 0 then
    [0xc5, vex2p1 (bit dst 3) 0 l 0b01, 0x70, modRMReg dst src, imm &&& 0xff].map (BitVec.ofNat 8)
  else
    encVex3 0b00001 0b01 0 l 0x70 dst 0 src (some imm)

/-- The VEX encoding of `VAESKEYGENASSIST dst, src, imm8` (`0F3A DF`, 2-operand,
    `vvvv` unused), ported from `Vec128Encoder.encVaeskeygen`. -/
def encVaeskeygenU (l dst src imm : Nat) : List (BitVec 8) :=
  encVex3 0b00011 0b01 0 l 0xdf dst 0 src (some imm)

/-- Encode a VEX shift by an immediate, `0F <opc> /<ext> ib`: `opc = 0x71` word,
    `0x72` dword, `0x73` qword (and the whole-register byte shifts); `ext` is the
    ModRM digit (`/6` left, `/2` logical right, `/7`/`/3` the byte shifts). `dst`
    is the written register (VEX `vvvv`), `src` the `ModRM.rm`. -/
def encodeVsimdShiftImm (opc ext l dst src imm : Nat) : List (BitVec 8) :=
  if bit src 3 = 0 then
    [0xc5, vex2p1 (bit ext 3) dst l 0b01, opc, modRMReg ext src, imm &&& 0xff].map (BitVec.ofNat 8)
  else
    encVex3 0b00001 0b01 0 l opc ext dst src (some imm)

/-- `UD2` (`0F 0B`), which raises #UD when executed: the encoding of an op that
    has no x86 instruction, so that it faults rather than computing something
    else. -/
def encUd2 : List (BitVec 8) := [0x0f, 0x0b].map (BitVec.ofNat 8)

/-- Encode one unified `SimdOp` to its 128-bit (`l = 0`) VEX machine bytes.
    `d` = dst xmm number, `a` = src1 xmm number, `b` = src2 xmm number (ignored
    for the unary `vaeskeygen`/`vpshufd`/`packedImm` arms). Byte-identical to the
    matching `Vec128Encoder.encodeVCryptInst` / `encodeVInst` arm. -/
def encodeVsimdInst : SimdOp → (d a b : Nat) → List (BitVec 8)
  | .vaesenc,        d, a, b => encVaes 0xdc 0 d a b
  | .vaesenclast,    d, a, b => encVaes 0xdd 0 d a b
  | .vaeskeygen rc,  d, a, _ => encVaeskeygenU 0 d a rc.toNat
  | .vpshufd imm,    d, a, _ => encVpshufdU 0 d a imm
  | .clmul imm,      d, a, b => encVpclmul 0 d a b imm
  | .gf2p8mulb,      d, a, b => encVgf2p8mulb 0 d a b
  | .affineqb imm,   d, a, b => encVgf2p8affineqb 0 d a b imm.toNat
  | .vpshufb,        d, a, b => encAvx2_0F38 0x00 0 d a b
  | .bitwise .and,   d, a, b => encAvx2Alu 0xdb 0 d a b
  | .bitwise .or,    d, a, b => encAvx2Alu 0xeb 0 d a b
  | .bitwise .xor,   d, a, b => encAvx2Alu 0xef 0 d a b
  | .bitwise _,      d, a, b => encAvx2Alu 0xef 0 d a b
  | .packed .add 16, d, a, b => encAvx2Alu 0xfd 0 d a b
  | .packed .add 32, d, a, b => encAvx2Alu 0xfe 0 d a b
  | .packed .add 64, d, a, b => encAvx2Alu 0xd4 0 d a b
  | .packed .sub 16, d, a, b => encAvx2Alu 0xf9 0 d a b
  | .packed .sub 32, d, a, b => encAvx2Alu 0xfa 0 d a b
  | .packed .sub 64, d, a, b => encAvx2Alu 0xfb 0 d a b
  | .packed .mul 16, d, a, b => encAvx2Alu 0xd5 0 d a b
  -- The shift arms encode the VARIABLE-shift opcodes, matching
  -- `VsimdAsmPrint.SimdOp.attMnemonic`: `packed bop laneW` denotes by the
  -- per-lane fold `v128PackLanesW`, whose machine form is `VPSLLVD`/`VPSRLVD`.
  -- Routing them to the `encAvx2Alu` catch-all below would encode a `VPADDD`.
  | .packed .shl 32, d, a, b => encVex3 0b00010 0b01 0 0 0x47 d a b none
  | .packed .shl 64, d, a, b => encVex3 0b00010 0b01 1 0 0x47 d a b none
  | .packed .shr 32, d, a, b => encVex3 0b00010 0b01 0 0 0x45 d a b none
  | .packed .shr 64, d, a, b => encVex3 0b00010 0b01 1 0 0x45 d a b none
  | .packed _ _,     d, a, b => encAvx2Alu 0xfe 0 d a b
  -- The immediate shifts: `0F 71/72/73 /6` left, `/2` logical right.
  | .packedImm .shl 16 imm, d, a, _ => encodeVsimdShiftImm 0x71 6 0 d a imm
  | .packedImm .shr 16 imm, d, a, _ => encodeVsimdShiftImm 0x71 2 0 d a imm
  | .packedImm .shl 32 imm, d, a, _ => encodeVsimdShiftImm 0x72 6 0 d a imm
  | .packedImm .shr 32 imm, d, a, _ => encodeVsimdShiftImm 0x72 2 0 d a imm
  | .packedImm .shl 64 imm, d, a, _ => encodeVsimdShiftImm 0x73 6 0 d a imm
  | .packedImm .shr 64 imm, d, a, _ => encodeVsimdShiftImm 0x73 2 0 d a imm
  | .packedImm _ _ _, _, _, _ => encUd2
  | .mulhi16,        d, a, b => encAvx2Alu 0xe5 0 d a b

/-- Encode a `vpslldq`/`vpsrldq` byte-shift (`0F 73 /digit ib`, `/7`=SLL,
    `/3`=SRL), ported from `Vec128Encoder.encVexShiftImmOp 0x73`. `dst` is the
    written reg (VEX `vvvv`, NDD), `src` the `ModRM.rm`. -/
def encodeVsimdShift (ext l dst src imm : Nat) : List (BitVec 8) :=
  encodeVsimdShiftImm 0x73 ext l dst src imm

/-- `VPSLLDQ $imm, src, dst` (`0F 73 /7`). -/
def encVpslldqU (l dst src imm : Nat) : List (BitVec 8) := encodeVsimdShift 7 l dst src imm

/-- `VPSRLDQ $imm, src, dst` (`0F 73 /3`). -/
def encVpsrldqU (l dst src imm : Nat) : List (BitVec 8) := encodeVsimdShift 3 l dst src imm

/-! ### SHA-NI (Intel SHA extensions): legacy-SSE `NP 0F 38 CB/CC/CD`

`SHA256RNDS2`/`SHA256MSG1`/`SHA256MSG2` are **legacy-SSE** (no VEX) two-operand
instructions `NP 0F 38 CB/CC/CD /r`: the `reg` field = destination xmm, the `rm`
field = source xmm, register-direct (`mod = 11`). `SHA256RNDS2` additionally
reads its round-constant operand implicitly in `%xmm0` (staged by the caller,
the register-allocation constraint). A `REX.RB` prefix is emitted iff `dst`/`src`
`≥ 8`. The opcodes were read off `gas`/`objdump` (`as --64`), not the SDM
tables — note the SDM's often-mis-quoted `CA` for `SHA256MSG2` is actually `CD`
(`CA` is `SHA256MSG2`'s SHA-1 sibling slot); `gas` is the ground truth. -/

/-- The optional REX byte for a SHA-NI reg/reg op: `REX.R` if `dst ≥ 8`,
    `REX.B` if `src ≥ 8`; absent when both are low registers. -/
def shaNiRex (dst src : Nat) : List (BitVec 8) :=
  let r := if dst ≥ 8 then 1 else 0
  let b := if src ≥ 8 then 1 else 0
  if r = 1 ∨ b = 1 then [BitVec.ofNat 8 (0x40 ||| (r <<< 2) ||| b)] else []

/-- Encode a legacy-SSE SHA-NI two-operand op `NP 0F 38 opc /r` at dst/src xmm
    numbers (register-direct `mod = 11`, `reg = dst`, `rm = src`), with a
    `REX.RB` prefix for high registers. -/
def encShaNi (opc dst src : Nat) : List (BitVec 8) :=
  shaNiRex dst src
    ++ [BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0x38, BitVec.ofNat 8 opc,
        BitVec.ofNat 8 (0xC0 ||| ((dst % 8) <<< 3) ||| (src % 8))]

/-- `SHA256RNDS2 %xmm0, %xmmSRC, %xmmDST` (`0F 38 CB /r`): two SHA-256 compression
    rounds. `%xmm0` (implicit, caller-staged) holds `W+K` for the two rounds; on
    input `src` provides the ABEF lane group and `dst` the CDGH group, and `dst`
    receives the updated ABEF. -/
def encSha256Rnds2 (dst src : Nat) : List (BitVec 8) := encShaNi 0xCB dst src

/-- `SHA256MSG1 %xmmSRC, %xmmDST` (`0F 38 CC /r`): σ0 partial message-schedule. -/
def encSha256Msg1 (dst src : Nat) : List (BitVec 8) := encShaNi 0xCC dst src

/-- `SHA256MSG2 %xmmSRC, %xmmDST` (`0F 38 CD /r`): σ1 message-schedule completion. -/
def encSha256Msg2 (dst src : Nat) : List (BitVec 8) := encShaNi 0xCD dst src

/-! ### Per-arm gas pins (the differential byte half, mirroring `Vec128Encoder` §7)

Each pin is the exact `gas` output (`as --64`, `objdump -d`) for the named
mnemonic with `d↦%xmm3 a↦%xmm2 b↦%xmm1`, copied from `Vec128Encoder.lean`'s
validation section — confirming the unified `encodeVsimdInst` reproduces the
bespoke byte output op-by-op. -/

-- gas: `vaesenc %xmm1, %xmm2, %xmm3`        →  c4 e2 69 dc d9
#guard encodeVsimdInst .vaesenc 3 2 1 == [0xc4,0xe2,0x69,0xdc,0xd9].map (BitVec.ofNat 8)

-- gas: `vaesenclast %xmm1, %xmm2, %xmm3`    →  c4 e2 69 dd d9
#guard encodeVsimdInst .vaesenclast 3 2 1 == [0xc4,0xe2,0x69,0xdd,0xd9].map (BitVec.ofNat 8)

-- gas: `vaeskeygenassist $0x1, %xmm2, %xmm3` →  c4 e3 79 df da 01
#guard encodeVsimdInst (.vaeskeygen 1) 3 2 0 == [0xc4,0xe3,0x79,0xdf,0xda,0x01].map (BitVec.ofNat 8)

-- gas: `vpshufd $0xff, %xmm2, %xmm3`        →  c5 f9 70 da ff
#guard encodeVsimdInst (.vpshufd 0xff) 3 2 0 == [0xc5,0xf9,0x70,0xda,0xff].map (BitVec.ofNat 8)

-- gas: `vpclmulqdq $0x11, %xmm1, %xmm2, %xmm3` →  c4 e3 69 44 d9 11
#guard encodeVsimdInst (.clmul 0x11) 3 2 1 == [0xc4,0xe3,0x69,0x44,0xd9,0x11].map (BitVec.ofNat 8)

-- gas: `vgf2p8mulb %xmm1, %xmm2, %xmm3`     →  c4 e2 69 cf d9
#guard encodeVsimdInst .gf2p8mulb 3 2 1 == [0xc4,0xe2,0x69,0xcf,0xd9].map (BitVec.ofNat 8)

-- gas: `vgf2p8affineqb $0x7, %xmm1, %xmm2, %xmm3` →  c4 e3 e9 ce d9 07
#guard encodeVsimdInst (.affineqb 0x07) 3 2 1 == [0xc4,0xe3,0xe9,0xce,0xd9,0x07].map (BitVec.ofNat 8)

-- gas: `vpshufb %xmm1, %xmm2, %xmm3`        →  c4 e2 69 00 d9
#guard encodeVsimdInst .vpshufb 3 2 1 == [0xc4,0xe2,0x69,0x00,0xd9].map (BitVec.ofNat 8)

-- gas: `vpand %xmm1, %xmm2, %xmm3`          →  c5 e9 db d9
#guard encodeVsimdInst (.bitwise .and) 3 2 1 == [0xc5,0xe9,0xdb,0xd9].map (BitVec.ofNat 8)

-- gas: `vpor %xmm1, %xmm2, %xmm3`           →  c5 e9 eb d9
#guard encodeVsimdInst (.bitwise .or) 3 2 1 == [0xc5,0xe9,0xeb,0xd9].map (BitVec.ofNat 8)

-- gas: `vpxor %xmm1, %xmm2, %xmm3`          →  c5 e9 ef d9
#guard encodeVsimdInst (.bitwise .xor) 3 2 1 == [0xc5,0xe9,0xef,0xd9].map (BitVec.ofNat 8)

-- gas: `vpaddd %xmm1, %xmm2, %xmm3`         →  c5 e9 fe d9
#guard encodeVsimdInst (.packed .add 32) 3 2 1 == [0xc5,0xe9,0xfe,0xd9].map (BitVec.ofNat 8)

-- gas: `vpaddq %xmm1, %xmm2, %xmm3`         →  c5 e9 d4 d9
#guard encodeVsimdInst (.packed .add 64) 3 2 1 == [0xc5,0xe9,0xd4,0xd9].map (BitVec.ofNat 8)

-- gas: `vpmulhw %xmm1, %xmm2, %xmm3`        →  c5 e9 e5 d9
#guard encodeVsimdInst .mulhi16 3 2 1 == [0xc5,0xe9,0xe5,0xd9].map (BitVec.ofNat 8)

/-- A packed shift by a register count encodes as the AVX2 variable shift, to the
    bytes gas assembles for `vpsllvd`/`vpsrlvd`/`vpsllvq`/`vpsrlvq %xmm1, %xmm2,
    %xmm3` (`c4 e2 69 47 d9`, `c4 e2 69 45 d9`, `c4 e2 e9 47 d9`, `c4 e2 e9 45 d9`). -/
theorem encodeVsimdInst_packed_shift_bytes :
    encodeVsimdInst (.packed .shl 32) 3 2 1
      = [0xc4,0xe2,0x69,0x47,0xd9].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packed .shr 32) 3 2 1
      = [0xc4,0xe2,0x69,0x45,0xd9].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packed .shl 64) 3 2 1
      = [0xc4,0xe2,0xe9,0x47,0xd9].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packed .shr 64) 3 2 1
      = [0xc4,0xe2,0xe9,0x45,0xd9].map (BitVec.ofNat 8) := by
  decide

/-- A packed shift by an immediate encodes to the bytes gas assembles for
    `vps{ll,rl}{w,d,q} $7, %xmm2, %xmm3`, and for the two register-extension
    cases `vpslld $7, %xmm10, %xmm3` (3-byte VEX) and `vpslld $7, %xmm2, %xmm11`. -/
theorem encodeVsimdInst_packedImm_bytes :
    encodeVsimdInst (.packedImm .shl 16 7) 3 2 0
      = [0xc5,0xe1,0x71,0xf2,0x07].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packedImm .shr 16 7) 3 2 0
      = [0xc5,0xe1,0x71,0xd2,0x07].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packedImm .shl 32 7) 3 2 0
      = [0xc5,0xe1,0x72,0xf2,0x07].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packedImm .shr 32 7) 3 2 0
      = [0xc5,0xe1,0x72,0xd2,0x07].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packedImm .shl 64 7) 3 2 0
      = [0xc5,0xe1,0x73,0xf2,0x07].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packedImm .shr 64 7) 3 2 0
      = [0xc5,0xe1,0x73,0xd2,0x07].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packedImm .shl 32 7) 3 10 0
      = [0xc4,0xc1,0x61,0x72,0xf2,0x07].map (BitVec.ofNat 8) ∧
    encodeVsimdInst (.packedImm .shl 32 7) 11 2 0
      = [0xc5,0xa1,0x72,0xf2,0x07].map (BitVec.ofNat 8) := by
  decide

-- gas: `vpslldq $0x8, %xmm2, %xmm3`         →  c5 e1 73 fa 08
#guard encVpslldqU 0 3 2 0x08 == [0xc5,0xe1,0x73,0xfa,0x08].map (BitVec.ofNat 8)

-- gas: `vpsrldq $0x8, %xmm2, %xmm3`         →  c5 e1 73 da 08
#guard encVpsrldqU 0 3 2 0x08 == [0xc5,0xe1,0x73,0xda,0x08].map (BitVec.ofNat 8)

-- SHA-NI byte pins (gas `as --64` + `objdump -d`, ground truth):
-- gas: `sha256rnds2 %xmm0, %xmm2, %xmm1`     →  0f 38 cb ca   (dst=1, src=2)
#guard encSha256Rnds2 1 2 == [0x0f,0x38,0xcb,0xca].map (BitVec.ofNat 8)
-- gas: `sha256rnds2 %xmm0, %xmm1, %xmm2`     →  0f 38 cb d1   (dst=2, src=1)
#guard encSha256Rnds2 2 1 == [0x0f,0x38,0xcb,0xd1].map (BitVec.ofNat 8)
-- gas: `sha256rnds2 %xmm0, %xmm10, %xmm11`   →  45 0f 38 cb da  (REX.RB, dst=11, src=10)
#guard encSha256Rnds2 11 10 == [0x45,0x0f,0x38,0xcb,0xda].map (BitVec.ofNat 8)
-- gas: `sha256msg1 %xmm4, %xmm7`             →  0f 38 cc fc   (dst=7, src=4)
#guard encSha256Msg1 7 4 == [0x0f,0x38,0xcc,0xfc].map (BitVec.ofNat 8)
-- gas: `sha256msg1 %xmm12, %xmm9`            →  45 0f 38 cc cc  (REX.RB, dst=9, src=12)
#guard encSha256Msg1 9 12 == [0x45,0x0f,0x38,0xcc,0xcc].map (BitVec.ofNat 8)
-- gas: `sha256msg2 %xmm6, %xmm7`             →  0f 38 cd fe   (dst=7, src=6)
#guard encSha256Msg2 7 6 == [0x0f,0x38,0xcd,0xfe].map (BitVec.ofNat 8)
-- gas: `sha256msg2 %xmm4, %xmm5`             →  0f 38 cd ec   (dst=5, src=4)
#guard encSha256Msg2 5 4 == [0x0f,0x38,0xcd,0xec].map (BitVec.ofNat 8)

/-! ## 2. `vmovdqu` mem loads/stores + `ret` (re-defined standalone)

These ABI glue encoders live in `X86Backend.SimdBytes` (which imports
`Vec128Encoder`); to keep this module free of `Vec128*`, they are re-defined here.
They use only `CryptoExt`'s `cbit`/`bit`, so the construction is the same audited
prefix layout. `vmovdqu disp(%rdi), %xmmD` is the VEX `0F 6F`/`0F 7F`, `pp=F3`,
2-byte VEX form against base `%rdi` (rm=7, no SIB), `mod` selected by `disp`. -/

/-- VEX 2-byte `P1` for the `vmovdqu` forms (`R̄ vvvv L pp`, `vvvv` unused = 1111,
    `L=0`, `pp=F3`), from `SimdBytes.vmovP1`. -/
def vmovP1U (d : Nat) : Nat := (cbit (bit d 3)) * 128 + 0b1111 * 8 + 0 * 4 + 0b10

/-- The four little-endian bytes of a 32-bit displacement. -/
def disp32BytesU (disp : Nat) : List Nat :=
  [disp &&& 0xff, (disp >>> 8) &&& 0xff, (disp >>> 16) &&& 0xff, (disp >>> 24) &&& 0xff]

/-- A `vmovdqu` against base `%rdi` (rm = 7) at byte `disp`, opcode `op`
    (`0x6F` load / `0x7F` store), dst/src xmm number `d`. `mod` selected by `disp`
    exactly as `gas` (mod=00 / 01 disp8 / 10 disp32). From `SimdBytes.encVmovdquMem`. -/
def encVmovdquMemU (op d disp : Nat) : List (BitVec 8) :=
  if disp = 0 then
    [0xc5, vmovP1U d, op, modRMReg d 7 - 0xC0].map (BitVec.ofNat 8)
  else if disp ≤ 127 then
    [0xc5, vmovP1U d, op, modRMReg d 7 - 0xC0 + 0x40, disp].map (BitVec.ofNat 8)
  else
    ([0xc5, vmovP1U d, op, modRMReg d 7 - 0xC0 + 0x80] ++ disp32BytesU disp).map (BitVec.ofNat 8)

/-- `vmovdqu disp(%rdi), %xmmD` (load, `0F 6F`). -/
def encVmovdquLoadU (d disp : Nat) : List (BitVec 8) := encVmovdquMemU 0x6F d disp

/-- `vmovdqu %xmmD, disp(%rdi)` (store, `0F 7F`). -/
def encVmovdquStoreU (d disp : Nat) : List (BitVec 8) := encVmovdquMemU 0x7F d disp

/-- The `ret` (near return) opcode byte. -/
def encRetU : List (BitVec 8) := [BitVec.ofNat 8 0xc3]

/-! ## 3. The whole AES-128 ECB single-block encrypt kernel as bytes (unified)

`encodeVsimdAesEcbBlock` is the WHOLE AES-128 ECB single-block encrypt kernel,
encoded entirely off the unified `SimdOp` set: load the 11 round keys + plaintext
from `(%rdi + 16·k)`, run `st = pt ^ rk0` then nine `VAESENC` + one `VAESENCLAST`,
store the ciphertext to `(%rdi + 192)`, `ret`. Register allocation pins
`ct↦xmm0 st↦xmm1 rk0..rk10↦xmm2..12` — identical to `SimdBytes.aesEcbAlloc` — and
the whole VAES round body is produced by `encodeVsimdInst`, so the byte output
matches `SimdBytes.encodeAesEcbBlock` with **no** `Vec128*` import. -/

/-- The 12 input loads as `(xmmNum, disp)` pairs: rk_k ↦ xmm(2+k) @ `(%rdi+16k)`,
    then plaintext ct ↦ xmm0 @ `(%rdi+176)`. -/
def aesEcbLoadsU : List (Nat × Nat) :=
  ((List.range 11).map (fun k => (2 + k, 16 * k))) ++ [(0, 176)]

/-- The VAES round body, encoded entirely off the unified `SimdOp` set, with
    `st↦xmm1`, `rk_k↦xmm(2+k)`, `ct↦xmm0`: `st = ct ^ rk0` (`bitwise .xor`), nine
    `VAESENC(st, rk_i)`, one `VAESENCLAST(st, rk10)`. -/
def aesEcbBodyU : List (BitVec 8) :=
  encodeVsimdInst (.bitwise .xor) 1 0 2
    ++ ((List.range 9).flatMap (fun i => encodeVsimdInst .vaesenc 1 1 (3 + i)))
    ++ encodeVsimdInst .vaesenclast 1 1 12

/-- The whole AES-128 ECB-encrypt kernel as machine bytes: `vmovdqu` loads ++ VAES
    body ++ `vmovdqu` ciphertext store ++ `ret`. Encoded entirely off the unified
    `SimdOp` set, with **no** `Vec128*` import. -/
def encodeVsimdAesEcbBlock : List (BitVec 8) :=
  (aesEcbLoadsU.flatMap (fun (d, disp) => encVmovdquLoadU d disp))
    ++ aesEcbBodyU
    ++ encVmovdquStoreU 1 192
    ++ encRetU

/-! ## 4. The byte-equality capstone: unified `.text` = `gas` reference

`gasVsimdAesEcbBlockText` is the exact 134-byte `.text` `gas` emits for the
`aes128_ecb_block` kernel (`as --64`, `objdump -d`), inlined verbatim from
`X86Backend.SimdBytes.gasAesEcbBlockText` — copied as a `List UInt8` literal so
this byte-equality result depends on **no** `Vec128*` file. -/

/-- The exact 134-byte `.text` `gas` emits for `aes128_ecb_block` (inlined from
    `SimdBytes.gasAesEcbBlockText`, the gas/`objdump` reference). -/
def gasVsimdAesEcbBlockText : List (BitVec 8) :=
  [ 0xc5,0xfa,0x6f,0x17,                       -- vmovdqu (%rdi),%xmm2            [rk0]
    0xc5,0xfa,0x6f,0x5f,0x10,                  -- vmovdqu 0x10(%rdi),%xmm3        [rk1]
    0xc5,0xfa,0x6f,0x67,0x20,                  -- vmovdqu 0x20(%rdi),%xmm4        [rk2]
    0xc5,0xfa,0x6f,0x6f,0x30,                  -- vmovdqu 0x30(%rdi),%xmm5        [rk3]
    0xc5,0xfa,0x6f,0x77,0x40,                  -- vmovdqu 0x40(%rdi),%xmm6        [rk4]
    0xc5,0xfa,0x6f,0x7f,0x50,                  -- vmovdqu 0x50(%rdi),%xmm7        [rk5]
    0xc5,0x7a,0x6f,0x47,0x60,                  -- vmovdqu 0x60(%rdi),%xmm8        [rk6]
    0xc5,0x7a,0x6f,0x4f,0x70,                  -- vmovdqu 0x70(%rdi),%xmm9        [rk7]
    0xc5,0x7a,0x6f,0x97,0x80,0x00,0x00,0x00,   -- vmovdqu 0x80(%rdi),%xmm10       [rk8]
    0xc5,0x7a,0x6f,0x9f,0x90,0x00,0x00,0x00,   -- vmovdqu 0x90(%rdi),%xmm11       [rk9]
    0xc5,0x7a,0x6f,0xa7,0xa0,0x00,0x00,0x00,   -- vmovdqu 0xa0(%rdi),%xmm12       [rk10]
    0xc5,0xfa,0x6f,0x87,0xb0,0x00,0x00,0x00,   -- vmovdqu 0xb0(%rdi),%xmm0        [pt]
    0xc5,0xf9,0xef,0xca,                       -- vpxor   %xmm2,%xmm0,%xmm1       st = pt^rk0
    0xc4,0xe2,0x71,0xdc,0xcb,                  -- vaesenc %xmm3,%xmm1,%xmm1
    0xc4,0xe2,0x71,0xdc,0xcc,                  -- vaesenc %xmm4,%xmm1,%xmm1
    0xc4,0xe2,0x71,0xdc,0xcd,                  -- vaesenc %xmm5,%xmm1,%xmm1
    0xc4,0xe2,0x71,0xdc,0xce,                  -- vaesenc %xmm6,%xmm1,%xmm1
    0xc4,0xe2,0x71,0xdc,0xcf,                  -- vaesenc %xmm7,%xmm1,%xmm1
    0xc4,0xc2,0x71,0xdc,0xc8,                  -- vaesenc %xmm8,%xmm1,%xmm1       (B̄=0)
    0xc4,0xc2,0x71,0xdc,0xc9,                  -- vaesenc %xmm9,%xmm1,%xmm1
    0xc4,0xc2,0x71,0xdc,0xca,                  -- vaesenc %xmm10,%xmm1,%xmm1
    0xc4,0xc2,0x71,0xdc,0xcb,                  -- vaesenc %xmm11,%xmm1,%xmm1
    0xc4,0xc2,0x71,0xdd,0xcc,                  -- vaesenclast %xmm12,%xmm1,%xmm1
    0xc5,0xfa,0x7f,0x8f,0xc0,0x00,0x00,0x00,   -- vmovdqu %xmm1,0xc0(%rdi)        [ct]
    0xc3 ].map (BitVec.ofNat 8)                -- ret

/-- **Whole-kernel byte-identity vs `gas`, on the unified stack.** The AES-128 ECB
    single-block kernel, encoded entirely off the unified `SimdOp` set
    (`encodeVsimdInst`) with **no** `Vec128*` import, is byte-for-byte identical to
    the exact `gas` reference. This is the equal-strength reproduction of
    `X86Backend.SimdBytes.encodeAesEcbBlock_eq_gas` on the unified stack — the byte
    artifact that unblocks the `Vec128Encoder` teardown. -/
theorem encodeVsimdAesEcbBlock_eq_gas :
    encodeVsimdAesEcbBlock = gasVsimdAesEcbBlockText := by native_decide

/-- The whole unified VAES kernel is 134 bytes, the same length `gas` produces. -/
theorem encodeVsimdAesEcbBlock_length : encodeVsimdAesEcbBlock.length = 134 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
