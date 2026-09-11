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
# Standalone ChaCha byte-helper layer (Vec128 teardown)

The whole ChaCha20 4-way owned kernel (`X86Backend.Chacha4WayEmit`) is a
`Vec128*` consumer: its quarter-round body bytes and its AoS↔SoA 4×4 transpose
body bytes are produced by `X86Backend.SimdBytes.encodeVBlock` over the bespoke
`Vec128.VInst` IR (`cbQR`/`transpose4Block`, register-resolved through the
`Vec128.encodeVInst` per-op encoder), and its ABI glue (`vmovdqu` mem loads /
stores, the `%rsp`-frame `vpaddd` feed-forward, `sub`/`add $imm,%rsp`, the
two-pointer `mov %rdi,%rax ; ret` epilogue) lives in `SimdBytes.lean`, which
imports `Vec128Encoder`. So the 4-way ChaCha kernel keeps the whole `Vec128*`
stack alive.

This module reproduces that ChaCha byte-helper **capability** standalone, on the
shared VEX prefix-byte layer `X86Backend.CryptoExtEncoder`
(`vex2p1`/`encVex3`/`modRMReg`/`encAvx2Alu`/…), exactly as
`VIR.VsimdByteEncoder` did for the AES-ECB block.  It imports **no** `Vec128*`
file:

```
  cbQRBytesU      (RFC 8439 §2.1 quarter-round body)  : List (BitVec 8)
  transpose4BytesU (the _MM_TRANSPOSE4 4×4 interleave) : List (BitVec 8)
  + vmovdqu loads/stores, %rsp vpaddd, sub/add %rsp, mov %rdi,%rax ; ret
```

Each helper's byte output is built from `CryptoExt`'s audited prefix builders
(the same construction `Vec128.encodeVInst` is built on) and pinned, byte-for-byte,
to the exact `SimdBytes`/gas reference via `native_decide` — so the migrated
`Chacha4WayVsimdEmit` kernel is byte-identical to the `SimdBytes`-based
`Chacha4WayEmit` with **zero** `Vec128*` imports.

## Trust posture

Identical in kind to `SimdBytes` / `VsimdByteEncoder`: each VEX builder is
`CryptoExt`'s audited bit-layout construction, and every helper byte string is
gas-pinned (`as --64` + `objdump -d`).  The decode round-trip for the VEX SIMD
opcodes is the same gas-pinned tier (the ACL2 x86isa / sail-x86 model has no VEX
SIMD decode tables) — the residual, the same ceiling `SimdBytes` records.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VsimdChachaByteEncoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt

/-! ## 1. The per-op VEX byte builders the ChaCha body needs (standalone)

The quarter-round body uses the three-register `0F`-map ALU ops
(`VPADDD`/`VPXOR`/`VPOR`) — all the `encAvx2Alu` shape (`CryptoExt`) — and the
two NDD imm-shift ops (`VPSLLD`/`VPSRLD`, `0F 72 /6` / `/2`).  The transpose body
uses the four `VPUNPCK{L,H}{DQ,QDQ}` interleaves (the `encAvx2Alu` shape, opcodes
`62`/`6A`/`6C`/`6D`).  The imm-shift form lives only in `Vec128Encoder`, so it is
re-defined here standalone (the AES port re-defined the `0F 73` byte-shift the
same way). -/

/-- A VEX lane imm-shift (`0F 72 /digit ib`): `/6`=SLL, `/2`=SRL.  NDD — the
    written reg is VEX `vvvv` (`dst`), the source is `ModRM.rm` (`src`), and
    `ModRM.reg` is the `/digit` group extension `ext`.  2-byte VEX when `src` is
    low, else 3-byte.  (The `Vec128.encVexShiftImm`/`encVpslld`/`encVpsrld`
    re-definition, byte-identical.) -/
def encVexShiftLaneU (ext l dst src imm : Nat) : List (BitVec 8) :=
  if bit src 3 = 0 then
    [0xc5, vex2p1 (bit ext 3) dst l 0b01, 0x72, modRMReg ext src, imm &&& 0xff].map (BitVec.ofNat 8)
  else
    encVex3 0b00001 0b01 0 l 0x72 ext dst src (some imm)

/-- `VPSLLD $imm, src, dst` (`0F 72 /6`). -/
def encVpslldU (l dst src imm : Nat) : List (BitVec 8) := encVexShiftLaneU 6 l dst src imm

/-- `VPSRLD $imm, src, dst` (`0F 72 /2`). -/
def encVpsrldU (l dst src imm : Nat) : List (BitVec 8) := encVexShiftLaneU 2 l dst src imm

/-! ### Per-arm gas pins (the byte half, mirroring `Vec128Encoder` §4)

The lane shifts are gas-pinned with `d↦%xmm3 a↦%xmm2`, copied from
`Vec128Encoder.lean`'s validation section. -/

-- gas: `vpslld $0x10, %xmm2, %xmm3`  →  c5 e1 72 f2 10  (NDD: vvvv=dst=xmm3, /6, rm=xmm2)
example : encVpslldU 0 3 2 0x10 = [0xc5,0xe1,0x72,0xf2,0x10].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpsrld $0x10, %xmm2, %xmm3`  →  c5 e1 72 d2 10  (/2)
example : encVpsrldU 0 3 2 0x10 = [0xc5,0xe1,0x72,0xd2,0x10].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpaddd %xmm1, %xmm2, %xmm3`  →  c5 e9 fe d9
example : encAvx2Alu 0xfe 0 3 2 1 = [0xc5,0xe9,0xfe,0xd9].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpxor %xmm1, %xmm2, %xmm3`   →  c5 e9 ef d9
example : encAvx2Alu 0xef 0 3 2 1 = [0xc5,0xe9,0xef,0xd9].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpor %xmm1, %xmm2, %xmm3`    →  c5 e9 eb d9
example : encAvx2Alu 0xeb 0 3 2 1 = [0xc5,0xe9,0xeb,0xd9].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpunpckldq %xmm1,%xmm2,%xmm3`  →  c5 e9 62 d9
example : encAvx2Alu 0x62 0 3 2 1 = [0xc5,0xe9,0x62,0xd9].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpunpckhdq %xmm1,%xmm2,%xmm3`  →  c5 e9 6a d9
example : encAvx2Alu 0x6a 0 3 2 1 = [0xc5,0xe9,0x6a,0xd9].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpunpcklqdq %xmm1,%xmm2,%xmm3`  →  c5 e9 6c d9
example : encAvx2Alu 0x6c 0 3 2 1 = [0xc5,0xe9,0x6c,0xd9].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpunpckhqdq %xmm1,%xmm2,%xmm3`  →  c5 e9 6d d9
example : encAvx2Alu 0x6d 0 3 2 1 = [0xc5,0xe9,0x6d,0xd9].map (BitVec.ofNat 8) := by native_decide

/-! ## 2. The ChaCha quarter-round body bytes (`cbAlloc`-resolved, standalone)

`cbQRBytesU` is the RFC 8439 §2.1 quarter-round on the four single-block groups
`a b c d` with a rotate scratch `t`, register-resolved through the *exact*
`SimdBytes.cbAlloc` (`a↦xmm0 b↦xmm1 c↦xmm2 d↦xmm3 t↦xmm4`) — the same byte string
`SimdBytes.encodeVBlock cbAlloc cbQR` produces, built standalone off the
`CryptoExt` per-op builders.  The `cbRotl x n` idiom is
`t = x<<n ; x = x>>(32-n) ; x = x|t` (AT&T `vpor %t,%x,%x` ⇒ dst=x vvvv=x rm=t). -/

/-- The `cbAlloc` register numbers: `a↦0 b↦1 c↦2 d↦3 t↦4`. -/
def cbA : Nat := 0
def cbB : Nat := 1
def cbC : Nat := 2
def cbD : Nat := 3
def cbT : Nat := 4

/-- The `cbRotl x n` rotate idiom bytes (`VPSLLD ; VPSRLD ; VPOR`), with scratch
    `t = cbT`: `t = x<<n ; x = x>>(32-n) ; x = x | t`.  AT&T `vpor %t,%x,%x`
    encodes dst=`x`, vvvv=`x`, rm=`t`. -/
def cbRotlBytesU (x n : Nat) : List (BitVec 8) :=
  encVpslldU 0 cbT x n
    ++ encVpsrldU 0 x x (32 - n)
    ++ encAvx2Alu 0xeb 0 x x cbT

/-- The whole RFC 8439 §2.1 quarter-round body bytes, `cbAlloc`-resolved
    (`a↦xmm0 b↦xmm1 c↦xmm2 d↦xmm3 t↦xmm4`): `a+=b; d^=a; d<<<16; c+=d; b^=c;
    b<<<12; a+=b; d^=a; d<<<8; c+=d; b^=c; b<<<7`.  Byte-identical to
    `SimdBytes.encodeVBlock cbAlloc cbQR`. -/
def cbQRBytesU : List (BitVec 8) :=
  -- a += b ; d ^= a ; d <<< 16
  encAvx2Alu 0xfe 0 cbA cbA cbB ++ encAvx2Alu 0xef 0 cbD cbD cbA ++ cbRotlBytesU cbD 16
  -- c += d ; b ^= c ; b <<< 12
  ++ encAvx2Alu 0xfe 0 cbC cbC cbD ++ encAvx2Alu 0xef 0 cbB cbB cbC ++ cbRotlBytesU cbB 12
  -- a += b ; d ^= a ; d <<< 8
  ++ encAvx2Alu 0xfe 0 cbA cbA cbB ++ encAvx2Alu 0xef 0 cbD cbD cbA ++ cbRotlBytesU cbD 8
  -- c += d ; b ^= c ; b <<< 7
  ++ encAvx2Alu 0xfe 0 cbC cbC cbD ++ encAvx2Alu 0xef 0 cbB cbB cbC ++ cbRotlBytesU cbB 7

/-- The exact 88-byte quarter-round body `gas` emits (`as --64` + `objdump -d`),
    copied from the `SimdBytes` gas references — the `cbAlloc`-resolved `cbQR`. -/
def gasCbQRBody : List (BitVec 8) :=
  [ 0xc5,0xf9,0xfe,0xc1,0xc5,0xe1,0xef,0xd8,0xc5,0xd9,0x72,0xf3,0x10,0xc5,0xe1,0x72,
    0xd3,0x10,0xc5,0xe1,0xeb,0xdc,0xc5,0xe9,0xfe,0xd3,0xc5,0xf1,0xef,0xca,0xc5,0xd9,
    0x72,0xf1,0x0c,0xc5,0xf1,0x72,0xd1,0x14,0xc5,0xf1,0xeb,0xcc,0xc5,0xf9,0xfe,0xc1,
    0xc5,0xe1,0xef,0xd8,0xc5,0xd9,0x72,0xf3,0x08,0xc5,0xe1,0x72,0xd3,0x18,0xc5,0xe1,
    0xeb,0xdc,0xc5,0xe9,0xfe,0xd3,0xc5,0xf1,0xef,0xca,0xc5,0xd9,0x72,0xf1,0x07,0xc5,
    0xf1,0x72,0xd1,0x19,0xc5,0xf1,0xeb,0xcc ].map (BitVec.ofNat 8)

/-- **Quarter-round body byte-identity vs `gas`.**  The standalone `cbQRBytesU`,
    built entirely off the `CryptoExt` per-op builders with **no** `Vec128*`
    import, is byte-for-byte identical to the `SimdBytes`/gas reference for the
    `cbAlloc`-resolved `cbQR`. -/
theorem cbQRBytesU_eq_gas : cbQRBytesU = gasCbQRBody := by native_decide

/-! ## 3. The 4×4 transpose body bytes (`transposeAlloc`-resolved, standalone)

`transpose4BytesU` is the canonical `_MM_TRANSPOSE4` 8-op interleave on rows
`r0..r3`, producing columns `c0..c3`, register-resolved through the exact
`SimdBytes.transposeAlloc` (`r0..r3↦xmm0..3 t0..t3↦xmm4..7 c0..c3↦xmm8..11`) — the
same byte string `SimdBytes.encodeVBlock transposeAlloc transpose4Block`
produces, built standalone off `CryptoExt`. -/

/-- The `transposeAlloc` register numbers: `r0..r3↦0..3 t0..t3↦4..7 c0..c3↦8..11`. -/
def trR (j : Nat) : Nat := j        -- r0..r3 ↦ xmm0..3
def trT (j : Nat) : Nat := 4 + j    -- t0..t3 ↦ xmm4..7
def trC (j : Nat) : Nat := 8 + j    -- c0..c3 ↦ xmm8..11

/-- The whole `_MM_TRANSPOSE4` body bytes, `transposeAlloc`-resolved:
    `t0=ldq(r0,r1) t1=hdq(r0,r1) t2=ldq(r2,r3) t3=hdq(r2,r3)`,
    `c0=lqdq(t0,t2) c1=hqdq(t0,t2) c2=lqdq(t1,t3) c3=hqdq(t1,t3)`.  Byte-identical
    to `SimdBytes.encodeVBlock transposeAlloc transpose4Block`. -/
def transpose4BytesU : List (BitVec 8) :=
  encAvx2Alu 0x62 0 (trT 0) (trR 0) (trR 1)   -- vpunpckldq t0, r0, r1
    ++ encAvx2Alu 0x6a 0 (trT 1) (trR 0) (trR 1)  -- vpunpckhdq t1, r0, r1
    ++ encAvx2Alu 0x62 0 (trT 2) (trR 2) (trR 3)  -- vpunpckldq t2, r2, r3
    ++ encAvx2Alu 0x6a 0 (trT 3) (trR 2) (trR 3)  -- vpunpckhdq t3, r2, r3
    ++ encAvx2Alu 0x6c 0 (trC 0) (trT 0) (trT 2)  -- vpunpcklqdq c0, t0, t2
    ++ encAvx2Alu 0x6d 0 (trC 1) (trT 0) (trT 2)  -- vpunpckhqdq c1, t0, t2
    ++ encAvx2Alu 0x6c 0 (trC 2) (trT 1) (trT 3)  -- vpunpcklqdq c2, t1, t3
    ++ encAvx2Alu 0x6d 0 (trC 3) (trT 1) (trT 3)  -- vpunpckhqdq c3, t1, t3

/-- The exact 32-byte transpose body `gas` emits (`as --64` + `objdump -d`),
    copied from `SimdBytes.gasTransposeGroup0`'s interleave fragment. -/
def gasTransposeBody : List (BitVec 8) :=
  [ 0xc5,0xf9,0x62,0xe1, 0xc5,0xf9,0x6a,0xe9, 0xc5,0xe9,0x62,0xf3, 0xc5,0xe9,0x6a,0xfb,
    0xc5,0x59,0x6c,0xc6, 0xc5,0x59,0x6d,0xce, 0xc5,0x51,0x6c,0xd7, 0xc5,0x51,0x6d,0xdf
  ].map (BitVec.ofNat 8)

/-- **Transpose body byte-identity vs `gas`.**  The standalone `transpose4BytesU`,
    built entirely off the `CryptoExt` per-op builders with **no** `Vec128*`
    import, is byte-for-byte identical to the `SimdBytes`/gas reference for the
    `transposeAlloc`-resolved `transpose4Block`. -/
theorem transpose4BytesU_eq_gas : transpose4BytesU = gasTransposeBody := by native_decide

/-! ## 4. `vmovdqu` mem loads/stores + ABI glue (re-defined standalone)

These ABI encoders live in `SimdBytes.lean` (which imports `Vec128Encoder`); to
keep this module free of `Vec128*`, they are re-defined here off only
`CryptoExt`'s `cbit`/`bit`/`modRMReg` (the same audited prefix layout).  Byte
forms: `vmovdqu` is VEX `0F 6F`/`0F 7F`, `pp=F3` (`P1` via `vmovP1U`); `vpaddd`
mem is VEX `0F FE` with a `%rsp`-SIB operand; `sub`/`add $imm32,%rsp` are
`REX.W 81 /digit id`; the two-pointer epilogue is `mov %rdi,%rax ; ret`. -/

/-- VEX 2-byte `P1` for the unaligned `vmovdqu` forms (`R̄ vvvv L pp`, `vvvv`
    unused = `1111`, `L=0`, `pp=F3`), from `SimdBytes.vmovP1`. -/
def vmovP1U (d : Nat) : Nat := (cbit (bit d 3)) * 128 + 0b1111 * 8 + 0 * 4 + 0b10

/-- The four little-endian bytes of a 32-bit displacement. -/
def disp32BytesU (disp : Nat) : List Nat :=
  [disp &&& 0xff, (disp >>> 8) &&& 0xff, (disp >>> 16) &&& 0xff, (disp >>> 24) &&& 0xff]

/-- A `vmovdqu` against an explicit low base register `rm` (`%rdi = 7`, `%rsi = 6`)
    at byte `disp`, opcode `op` (`0x6F` load / `0x7F` store), dst/src xmm number
    `d`.  `mod` selected by `disp` (mod=00 / 01 disp8 / 10 disp32), exactly as
    `gas`.  From `SimdBytes.encVmovdquBase`. -/
def encVmovdquBaseU (op d rm disp : Nat) : List (BitVec 8) :=
  if disp = 0 then
    [0xc5, vmovP1U d, op, modRMReg d rm - 0xC0].map (BitVec.ofNat 8)
  else if disp ≤ 127 then
    [0xc5, vmovP1U d, op, modRMReg d rm - 0xC0 + 0x40, disp].map (BitVec.ofNat 8)
  else
    ([0xc5, vmovP1U d, op, modRMReg d rm - 0xC0 + 0x80] ++ disp32BytesU disp).map (BitVec.ofNat 8)

/-- `vmovdqu disp(%rdi), %xmmD` (load, `0F 6F`, base %rdi). -/
def encVmovdquLoadU (d disp : Nat) : List (BitVec 8) := encVmovdquBaseU 0x6F d 7 disp

/-- `vmovdqu %xmmD, disp(%rdi)` (store, `0F 7F`, base %rdi). -/
def encVmovdquStoreU (d disp : Nat) : List (BitVec 8) := encVmovdquBaseU 0x7F d 7 disp

/-- `vmovdqu disp(%rsi), %xmmD` (load from the input pointer, `0F 6F`, base %rsi). -/
def encVmovdquLoadRsiU (d disp : Nat) : List (BitVec 8) := encVmovdquBaseU 0x6F d 6 disp

/-- A `vmovdqu` against base `%rsp` (rm = 100, SIB-forced) at byte `disp`, opcode
    `op` (`0x6F` load / `0x7F` store), xmm number `d`.  SIB = `0x24`.  From
    `SimdBytes.encVmovdquRsp`. -/
def encVmovdquRspU (op d disp : Nat) : List (BitVec 8) :=
  let reg := d &&& 7
  if disp = 0 then
    [0xc5, vmovP1U d, op, reg * 8 + 4, 0x24].map (BitVec.ofNat 8)
  else if disp ≤ 127 then
    [0xc5, vmovP1U d, op, 0x40 + reg * 8 + 4, 0x24, disp].map (BitVec.ofNat 8)
  else
    ([0xc5, vmovP1U d, op, 0x80 + reg * 8 + 4, 0x24] ++ disp32BytesU disp).map (BitVec.ofNat 8)

/-- `vmovdqu %xmmD, disp(%rsp)` — unaligned frame store (`0F 7F`). -/
def encVmovdquStoreRspU (d disp : Nat) : List (BitVec 8) := encVmovdquRspU 0x7F d disp

/-- `vmovdqu disp(%rsp), %xmmD` — unaligned frame load (`0F 6F`). -/
def encVmovdquLoadRspU (d disp : Nat) : List (BitVec 8) := encVmovdquRspU 0x6F d disp

/-- `vpaddd disp(%rsp), %xmmV, %xmmD` — packed-u32 add of a `%rsp`-frame memory
    operand (the frame-snapshot feed-forward).  `d` = dst (`ModRM.reg`), `v` =
    in-register addend (VEX `vvvv`).  SIB = `0x24`.  From
    `SimdBytes.encVpadddMemRsp`. -/
def encVpadddMemRspU (d v disp : Nat) : List (BitVec 8) :=
  let p1 := vex2p1 (bit d 3) v 0 0b01
  let reg := d &&& 7
  if disp = 0 then
    [0xc5, p1, 0xfe, reg * 8 + 4, 0x24].map (BitVec.ofNat 8)
  else if disp ≤ 127 then
    [0xc5, p1, 0xfe, 0x40 + reg * 8 + 4, 0x24, disp].map (BitVec.ofNat 8)
  else
    ([0xc5, p1, 0xfe, 0x80 + reg * 8 + 4, 0x24] ++ disp32BytesU disp).map (BitVec.ofNat 8)

/-- `sub $imm32, %rsp` — reserve the spill frame (`48 81 ec id`). -/
def encSubRspU (imm : Nat) : List (BitVec 8) :=
  ([0x48, 0x81, 0xec] ++ disp32BytesU imm).map (BitVec.ofNat 8)

/-- `add $imm32, %rsp` — release the spill frame (`48 81 c4 id`). -/
def encAddRspU (imm : Nat) : List (BitVec 8) :=
  ([0x48, 0x81, 0xc4] ++ disp32BytesU imm).map (BitVec.ofNat 8)

/-- The two-pointer return-value epilogue: `mov %rdi,%rax ; ret`
    (`48 89 f8 c3`), from `SimdBytes.encRetOutPtr`. -/
def encRetOutPtrU : List (BitVec 8) := [0x48, 0x89, 0xf8, 0xc3].map (BitVec.ofNat 8)

/-! ### ABI byte pins (mirroring the `SimdBytes` validation examples) -/

-- gas: `vmovdqu (%rdi), %xmm0`        →  c5 fa 6f 07
example : encVmovdquLoadU 0 0 = [0xc5,0xfa,0x6f,0x07].map (BitVec.ofNat 8) := by native_decide

-- gas: `vmovdqu %xmm1, 0x10(%rdi)`    →  c5 fa 7f 4f 10
example : encVmovdquStoreU 1 16 = [0xc5,0xfa,0x7f,0x4f,0x10].map (BitVec.ofNat 8) := by native_decide

-- gas: `vmovdqu (%rsi), %xmm0`        →  c5 fa 6f 06   (rm=6)
example : encVmovdquLoadRsiU 0 0 = [0xc5,0xfa,0x6f,0x06].map (BitVec.ofNat 8) := by native_decide

-- gas: `vmovdqu 0x80(%rsi), %xmm3`    →  c5 fa 6f 9e 80 00 00 00   (disp32)
example : encVmovdquLoadRsiU 3 128 = [0xc5,0xfa,0x6f,0x9e,0x80,0x00,0x00,0x00].map (BitVec.ofNat 8) := by
  native_decide

-- gas: `vmovdqu %xmm0,(%rsp)`        →  c5 fa 7f 04 24   (SIB rsp)
example : encVmovdquStoreRspU 0 0 = [0xc5,0xfa,0x7f,0x04,0x24].map (BitVec.ofNat 8) := by native_decide

-- gas: `vmovdqu (%rsp),%xmm0`        →  c5 fa 6f 04 24
example : encVmovdquLoadRspU 0 0 = [0xc5,0xfa,0x6f,0x04,0x24].map (BitVec.ofNat 8) := by native_decide

-- gas: `vpaddd (%rsp),%xmm0,%xmm0`    →  c5 f9 fe 04 24
example : encVpadddMemRspU 0 0 0 = [0xc5,0xf9,0xfe,0x04,0x24].map (BitVec.ofNat 8) := by native_decide

-- gas: `sub $0x100,%rsp`  →  48 81 ec 00 01 00 00
example : encSubRspU 256 = [0x48,0x81,0xec,0x00,0x01,0x00,0x00].map (BitVec.ofNat 8) := by native_decide

-- gas: `add $0x100,%rsp`  →  48 81 c4 00 01 00 00
example : encAddRspU 256 = [0x48,0x81,0xc4,0x00,0x01,0x00,0x00].map (BitVec.ofNat 8) := by native_decide

-- gas: `mov %rdi, %rax ; ret`  →  48 89 f8 c3
example : encRetOutPtrU = [0x48,0x89,0xf8,0xc3].map (BitVec.ofNat 8) := by native_decide

/-- `encVmovdquBaseU` against `%rdi` (rm = 7) agrees with the original
    `encVmovdquLoadU`/`encVmovdquStoreU` (conservative extension, the
    `SimdBytes.encVmovdquBase_rdi` analogue). -/
theorem encVmovdquLoadU_eq_base (d disp : Nat) :
    encVmovdquLoadU d disp = encVmovdquBaseU 0x6F d 7 disp := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.VsimdChachaByteEncoder
