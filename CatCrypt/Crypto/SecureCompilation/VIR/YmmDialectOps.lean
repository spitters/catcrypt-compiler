/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import Mathlib.Data.Fin.VecNotation

/-!
# The 256-bit YMM op family (`YmmOp`)

This module is the **dialect-side** op family for 256-bit vector ALU work: the
256-bit (VEX.256 / AVX2) analogue of the 128-bit `SimdOp` in
`JasminDialect.lean`. Its first consumer is the AVX2 ML-DSA NTT kernel
(`X86Backend/Avx2YmmNttEmit.lean`), which uses it in place of the bespoke
`Avx2YmmModel.YInst` machine model; the arithmetic/logic/shift/shuffle arms
beyond that kernel's needs cover the 4-way and 8-way lane-parallel kernels
(Poly1305, packed-field 2625×4, ChaCha20 8-way, LEA/LSH multi-buffer).

Two structural differences from `SimdOp`:

* **256-bit lane shape.** All register operands/results are `reg 256`
  (`BitVec 256`), where `SimdOp` is `reg 128`.
* **Mixed arity, per-arm denote dispatch.** `SimdOp.denote` has a *fixed*
  binary signature `BitVec 128 → BitVec 128 → BitVec 128`. The NTT op set mixes
  unary ops (`vmovshdup`) with binary ops (`vpmuldq`, `vpsubq`, `vpaddd`,
  `vpsubd`, `vpblendd`) and `imm8`-carrying permutes (`vpblendd`, `vpshufd`,
  `vpermq`). So `YmmOp.denote` reads up to **two** `BitVec 256` inputs and
  dispatches per arm; the unary arms simply ignore the second operand. This is
  the design from the start (NOT a fixed binary signature retro-fitted later) —
  the integration into `Com` projects the actual arity through `argTys`.

## The op set (mirrors `Avx2YmmModel`'s register-only fragment)

| arm        | arity   | lane shape          | semantics                                    |
|------------|---------|---------------------|----------------------------------------------|
| `vpmuldq`  | binary  | 4 × (even u32→u64)  | **signed** 32×32→64 of the EVEN dword lanes  |
| `vmovshdup`| unary   | 8 × u32 dup-odd     | dword `2i,2i+1 ← src 2i+1` (high-dup)        |
| `vpsubq`   | binary  | 4 × u64             | wrapping 64-bit-lane subtract                |
| `vpaddd`   | binary  | 8 × u32             | wrapping 32-bit-lane add                     |
| `vpsubd`   | binary  | 8 × u32             | wrapping 32-bit-lane subtract                |
| `vpblendd` | binary  | 8 × u32, `imm8`     | per-dword select (`imm` bit i ⇒ src2)        |
| `vpshufd`  | unary   | 8 × u32, `imm8`     | per-128-lane dword shuffle (2-bit fields)    |
| `vpermq`   | unary   | 4 × u64, `imm8`     | cross-lane qword permute (2-bit fields)      |
| `vpmuludq` | binary  | 4 × (even u32→u64)  | **unsigned** 32×32→64 of the EVEN dword lanes|
| `vpaddq`   | binary  | 4 × u64             | wrapping 64-bit-lane add                     |
| `vpmullq`  | binary  | 4 × u64             | low 64 bits of the 64×64 product             |
| `vpand`    | binary  | bitwise             | bitwise AND of the two registers             |
| `vpor`     | binary  | bitwise             | bitwise OR of the two registers              |
| `vpxor`    | binary  | bitwise             | bitwise XOR of the two registers             |
| `vpshufb`  | binary  | 2 × 16 × u8         | per-128-lane byte gather under a control vec  |
| `vpsrlq`   | unary   | 4 × u64, `imm8`     | logical shift right of each qword lane       |
| `vpsllq`   | unary   | 4 × u64, `imm8`     | logical shift left of each qword lane        |
| `vpsrld`   | unary   | 8 × u32, `imm8`     | logical shift right of each dword lane       |
| `vpslld`   | unary   | 8 × u32, `imm8`     | logical shift left of each dword lane        |

## VEX vs EVEX spellings

`vpand`/`vpor`/`vpxor` are the VEX.256 (AVX2) spellings. The EVEX forms
`vpandd`/`vpandq`, `vpord`/`vporq`, `vpxord`/`vpxorq` differ only in encoding
and element granularity for masking; on a plain register operand with no mask
register and no broadcast they compute the same 256-bit bitwise function. The
family carries ONE arm per operation, spelled VEX, since the whole family is
VEX.256/AVX2. `vpmullq` is the exception with no VEX encoding at all — it needs
AVX512DQ+VL even at 256 bits, and is spelled accordingly.

## The anchor

The lane denote bodies are **copied verbatim** (with a `W` suffix) from the
KAT-pinned `Avx2YmmModel.lean` — `yDwordW`/`yQwordW`/`yOfDwordsW`/`yOfQwordsW`
plus each op. Faithfulness rests on the same anchor as the model: the lane ops
are the obviously-correct per-lane integer ops (auditable against the Intel SDM)
and the integration witness is the ML-DSA NTT KAT byte-identity
(`bench/mldsa_compare/`, PQClean reference). The signed `vpmuldq` is the one op
where signedness is required (Montgomery reduction); its body sign-extends
the even dwords and is re-pinned on negative-input vectors below.

## RESIDUAL scoped OUT of this module

The SIMD→GPR **extract** `vpmovmskb` (`X86Backend/MpnSimdExtractEmit.lean`) is NOT
modelled here. It leaves the vector register file: it reads a `BitVec 256` and
writes a `BitVec 32` *into a GPR*, so its result type is **not** `reg 256`
(it is `reg 32`, a cross-file move). The whole `YmmOp` family is closed under
`reg 256 → reg 256` (`argTys`/`retTy` below), so adding `vpmovmskb` would break
that uniformity and needs a `reg 32` return arm. It is left to the integration
step / a follow-up op.

The **memory-broadcast** `vpbroadcastq` is likewise not an arm here. Every use in
the emitted 4-way/8-way artifacts sources it from memory
(`vpbroadcastq disp(%base), %ymm` / `sym(%rip), %ymm`), so it is a load, not a
`reg 256 → reg 256` op. Its register form `vpbroadcastq %xmm, %ymm` takes a
`reg 128` source and breaks the family's closure for the same reason
`vpmovmskb` does.

The **data movement** mnemonics `vmovdqu`/`vmovdqu64`/`vmovdqa64` and the
`vzeroupper` prologue hygiene are not ops either: they cross the
register/memory boundary or act on the whole vector state. `vmovdqu` lives at
the instruction level as `YmmAsmPrint.YmmInstr.ymov`/`.yload`/`.ystore`.

## NOT done here (orchestrator integration step)

This module is the **standalone op family + denote + smoke pins only**. It is
deliberately NOT wired into `JasminOp`. The orchestrator's integration step is
to add a `JasminOp.vymm (op : YmmOp)` constructor (mirroring `JasminOp.vsimd`),
register a 256-bit `JasminTy` (`reg 256` already exists, so just route
`argTys`/`retTy`/`denote` through `YmmOp`), and then migrate the kernel.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Lane views (verbatim from `Avx2YmmModel`, `W` suffix)

A 256-bit register is read as either 8 × u32 (dword) or 4 × u64 (qword) lanes,
with dword/qword `j` at bit offset `32·j` / `64·j` (little-endian, `gas` `%ymm`
byte order). `yOfDwordsW` / `yOfQwordsW` reassemble lanes into a `BitVec 256`. -/

/-- The `j`-th 32-bit dword lane (`j < 8`). Verbatim copy of `Avx2Ymm.yDword`. -/
@[reducible] def yDwordW (v : BitVec 256) (j : Nat) : BitVec 32 := BitVec.extractLsb' (32 * j) 32 v

/-- The `j`-th 64-bit qword lane (`j < 4`). Verbatim copy of `Avx2Ymm.yQword`. -/
@[reducible] def yQwordW (v : BitVec 256) (j : Nat) : BitVec 64 := BitVec.extractLsb' (64 * j) 64 v

/-- Reassemble 8 dword lanes into a `BitVec 256` (lane `j` at bit `32·j`).
    Verbatim copy of `Avx2Ymm.yOfDwords`. -/
def yOfDwordsW (f : Fin 8 → BitVec 32) : BitVec 256 :=
  Fin.foldl 8 (init := (0 : BitVec 256)) (fun acc j => acc ||| ((f j).setWidth 256 <<< (32 * j.val)))

/-- Reassemble 4 qword lanes into a `BitVec 256` (lane `j` at bit `64·j`).
    Verbatim copy of `Avx2Ymm.yOfQwords`. -/
def yOfQwordsW (f : Fin 4 → BitVec 64) : BitVec 256 :=
  Fin.foldl 4 (init := (0 : BitVec 256)) (fun acc j => acc ||| ((f j).setWidth 256 <<< (64 * j.val)))

/-! ## 2. The per-lane ALU semantics (verbatim from `Avx2YmmModel`, `W` suffix)

Each is the obvious per-lane integer op, auditable against the Intel SDM. -/

/-- One `vpmuldq` qword lane: signed product of the even dwords `2j` of `a`,`b`.
    `BitVec.signExtend` realises the two's-complement sign extension; the 64-bit
    multiply is then exact (the full signed 32×32 product fits in 64 bits).
    Verbatim copy of `Avx2Ymm.laneMulDq`. -/
@[reducible] def laneMulDqW (a b : BitVec 256) (j : Nat) : BitVec 64 :=
  (BitVec.signExtend 64 (yDwordW a (2 * j))) * (BitVec.signExtend 64 (yDwordW b (2 * j)))

/-- `VPMULDQ a, b`: 4 signed even-lane 32×32→64 products.
    Verbatim copy of `Avx2Ymm.vpmuldq`. -/
def vpmuldqW (a b : BitVec 256) : BitVec 256 := yOfQwordsW (fun j => laneMulDqW a b j.val)

/-- `VMOVSHDUP a`: duplicate each ODD 32-bit dword into the adjacent even slot —
    result dword `2i` and `2i+1` both equal source dword `2i+1` (the "high
    duplicate" of `_mm256_movehdup_ps`). Verbatim copy of `Avx2Ymm.vmovshdup`. -/
def vmovshdupW (a : BitVec 256) : BitVec 256 :=
  yOfDwordsW (fun i => yDwordW a (2 * (i.val / 2) + 1))

/-- `VPSUBQ a, b`: 4 wrapping 64-bit-lane subtractions (`a_j − b_j` mod 2⁶⁴).
    Verbatim copy of `Avx2Ymm.vpsubq`. -/
def vpsubqW (a b : BitVec 256) : BitVec 256 := yOfQwordsW (fun j => yQwordW a j.val - yQwordW b j.val)

/-- `VPADDD a, b`: 8 wrapping 32-bit-lane additions.
    Verbatim copy of `Avx2Ymm.vpaddd`. -/
def vpadddW (a b : BitVec 256) : BitVec 256 := yOfDwordsW (fun i => yDwordW a i.val + yDwordW b i.val)

/-- `VPSUBD a, b`: 8 wrapping 32-bit-lane subtractions.
    Verbatim copy of `Avx2Ymm.vpsubd`. -/
def vpsubdW (a b : BitVec 256) : BitVec 256 := yOfDwordsW (fun i => yDwordW a i.val - yDwordW b i.val)

/-- `VPBLENDD a, b, imm8`: per-dword select. For each of the 8 dword lanes `i`,
    if bit `i` of `imm` is set the result dword is `b`'s, else `a`'s (Intel SDM
    `VPBLENDD`: `a` = src1 = `vvvv`, `b` = src2 = `ModRM.rm`).
    Verbatim copy of `Avx2Ymm.vpblendd`. -/
def vpblenddW (a b : BitVec 256) (imm : Nat) : BitVec 256 :=
  yOfDwordsW (fun i => if (imm >>> i.val) &&& 1 = 1 then yDwordW b i.val else yDwordW a i.val)

/-- `VPSHUFD a, imm8`: within EACH 128-bit lane, select the four output dwords by
    the four 2-bit fields of `imm8`. The same `imm` controls both 128-bit lanes
    (lane `h ∈ {0,1}`: output dword `4h+k ← src dword 4h + field k`).
    Verbatim copy of `Avx2Ymm.vpshufd`. -/
def vpshufdW (a : BitVec 256) (imm : Nat) : BitVec 256 :=
  yOfDwordsW (fun i =>
    let h := i.val / 4          -- which 128-bit lane (0 or 1)
    let k := i.val % 4          -- position within the lane
    let sel := (imm >>> (2 * k)) &&& 3
    yDwordW a (4 * h + sel))

/-- `VPERMQ a, imm8`: cross-lane qword permute. Output qword `j` is source qword
    given by the `j`-th 2-bit field of `imm8` (Intel SDM `VPERMQ`).
    Verbatim copy of `Avx2Ymm.vpermq`. -/
def vpermqW (a : BitVec 256) (imm : Nat) : BitVec 256 :=
  yOfQwordsW (fun j => yQwordW a ((imm >>> (2 * j.val)) &&& 3))

/-! ## 2b. Byte lane views and the remaining ALU lane semantics

The byte views serve `vpshufb`, the only op in the family whose lane granularity
is 8 bits. `yByteW` / `yOfBytesW` are the byte analogues of `yDwordW` /
`yOfDwordsW`, with byte `j` at bit offset `8·j`. -/

/-- The `j`-th 8-bit byte lane (`j < 32`). -/
@[reducible] def yByteW (v : BitVec 256) (j : Nat) : BitVec 8 := BitVec.extractLsb' (8 * j) 8 v

/-- Reassemble 32 byte lanes into a `BitVec 256` (lane `j` at bit `8·j`). -/
def yOfBytesW (f : Fin 32 → BitVec 8) : BitVec 256 :=
  Fin.foldl 32 (init := (0 : BitVec 256)) (fun acc j => acc ||| ((f j).setWidth 256 <<< (8 * j.val)))

/-- One `vpmuludq` qword lane: UNSIGNED product of the even dwords `2j` of
    `a`,`b`. `BitVec.setWidth` widening a `BitVec 32` to `BitVec 64` is
    zero extension, so the 64-bit multiply is the exact unsigned 32×32 product.
    The unsigned counterpart of `laneMulDqW`. -/
@[reducible] def laneMulUDqW (a b : BitVec 256) (j : Nat) : BitVec 64 :=
  ((yDwordW a (2 * j)).setWidth 64) * ((yDwordW b (2 * j)).setWidth 64)

/-- `VPMULUDQ a, b`: 4 unsigned even-lane 32×32→64 products. AVX2. -/
def vpmuludqW (a b : BitVec 256) : BitVec 256 := yOfQwordsW (fun j => laneMulUDqW a b j.val)

/-- `VPADDQ a, b`: 4 wrapping 64-bit-lane additions (`a_j + b_j` mod 2⁶⁴). AVX2. -/
def vpaddqW (a b : BitVec 256) : BitVec 256 := yOfQwordsW (fun j => yQwordW a j.val + yQwordW b j.val)

/-- `VPMULLQ a, b`: 4 lanes of the LOW 64 bits of the 64×64 product
    (`BitVec 64` multiplication is already mod 2⁶⁴). Requires AVX512DQ+VL: no
    VEX.256 encoding of this operation exists. -/
def vpmullqW (a b : BitVec 256) : BitVec 256 := yOfQwordsW (fun j => yQwordW a j.val * yQwordW b j.val)

/-- `VPAND a, b`: bitwise AND of the two 256-bit registers. Lane-wise at every
    granularity — a bitwise op commutes with any lane split, so lane-map
    reasoning applies at 8/32/64-bit lanes alike. AVX2 (VEX) spelling; the
    EVEX spellings `VPANDD`/`VPANDQ` denote the same function on a register
    operand with no mask and no broadcast. -/
def vpandW (a b : BitVec 256) : BitVec 256 := a &&& b

/-- `VPOR a, b`: bitwise OR of the two 256-bit registers. Lane-wise at every
    granularity (see `vpandW`). AVX2 (VEX) spelling; EVEX `VPORD`/`VPORQ`
    denote the same function. -/
def vporW (a b : BitVec 256) : BitVec 256 := a ||| b

/-- `VPXOR a, b`: bitwise XOR of the two 256-bit registers. Lane-wise at every
    granularity (see `vpandW`). AVX2 (VEX) spelling; EVEX `VPXORD`/`VPXORQ`
    denote the same function. -/
def vpxorW (a b : BitVec 256) : BitVec 256 := a ^^^ b

/-- `VPSRLQ a, imm8`: 4 × logical shift right of each 64-bit lane by `imm8`.
    `BitVec` `>>>` saturates to zero once the count reaches the lane width,
    which is exactly the x86 behaviour for `imm8 ≥ 64`. AVX2. -/
def vpsrlqW (a : BitVec 256) (imm : Nat) : BitVec 256 :=
  yOfQwordsW (fun j => yQwordW a j.val >>> imm)

/-- `VPSLLQ a, imm8`: 4 × logical shift left of each 64-bit lane by `imm8`.
    `BitVec` `<<<` truncates to the lane width, so a count of `imm8 ≥ 64`
    yields zero, matching x86. AVX2. -/
def vpsllqW (a : BitVec 256) (imm : Nat) : BitVec 256 :=
  yOfQwordsW (fun j => yQwordW a j.val <<< imm)

/-- `VPSRLD a, imm8`: 8 × logical shift right of each 32-bit lane by `imm8`
    (zero for `imm8 ≥ 32`, matching x86). AVX2. -/
def vpsrldW (a : BitVec 256) (imm : Nat) : BitVec 256 :=
  yOfDwordsW (fun i => yDwordW a i.val >>> imm)

/-- `VPSLLD a, imm8`: 8 × logical shift left of each 32-bit lane by `imm8`
    (zero for `imm8 ≥ 32`, matching x86). AVX2. -/
def vpslldW (a : BitVec 256) (imm : Nat) : BitVec 256 :=
  yOfDwordsW (fun i => yDwordW a i.val <<< imm)

/-- `VPSHUFB a, b`: within EACH 128-bit lane, gather bytes of the data operand
    `a` under the control operand `b`. For output byte `i` with `h = i / 16` the
    128-bit lane and control byte `m = b`'s byte `i`: if bit 7 of `m` is set the
    output byte is zero, otherwise it is `a`'s byte `16·h + (m mod 16)`
    (Intel SDM `VPSHUFB`: `a` = src1 = `vvvv`, `b` = src2 = `ModRM.rm`).
    This is a per-128-lane byte GATHER, not a pointwise lane map — the same
    posture as `vpshufdW`/`vpermqW`. AVX2. -/
def vpshufbW (a b : BitVec 256) : BitVec 256 :=
  yOfBytesW (fun i =>
    let h := i.val / 16                       -- which 128-bit lane (0 or 1)
    let m := yByteW b i.val                   -- the control byte at this position
    if (m >>> 7) = 1 then 0
    else yByteW a (16 * h + (m &&& 0x0F).toNat))

/-! ## 3. The op family

`YmmOp` is the dialect op set: the register-only AVX2 NTT fragment, MIXED arity
(unary `vmovshdup`/`vpshufd`/`vpermq`, binary `vpmuldq`/`vpsubq`/`vpaddd`/
`vpsubd`/`vpblendd`). The `imm8`-carrying permutes bake the immediate into the
op (same convention as `SimdOp.clmul`/`SimdOp.affineqb`). -/

/-- A single 256-bit YMM dialect op (the VEX.256 AVX2 NTT register-only set). -/
inductive YmmOp where
  /-- `VPMULDQ a, b` — SIGNED even-lane 32×32→64 multiply. Binary. -/
  | vpmuldq
  /-- `VMOVSHDUP a` — high-dup of the odd dwords. Unary. -/
  | vmovshdup
  /-- `VPSUBQ a, b` — 4×u64 wrapping subtract. Binary. -/
  | vpsubq
  /-- `VPADDD a, b` — 8×u32 wrapping add. Binary. -/
  | vpaddd
  /-- `VPSUBD a, b` — 8×u32 wrapping subtract. Binary. -/
  | vpsubd
  /-- `VPBLENDD a, b, imm8` — per-dword blend (`imm8` baked in). Binary. -/
  | vpblendd (imm : Nat)
  /-- `VPSHUFD a, imm8` — per-128-lane dword shuffle (`imm8` baked in). Unary. -/
  | vpshufd (imm : Nat)
  /-- `VPERMQ a, imm8` — cross-lane qword permute (`imm8` baked in). Unary. -/
  | vpermq (imm : Nat)
  /-- `VPMULUDQ a, b` — UNSIGNED even-lane 32×32→64 multiply. Binary. -/
  | vpmuludq
  /-- `VPADDQ a, b` — 4×u64 wrapping add. Binary. -/
  | vpaddq
  /-- `VPMULLQ a, b` — 4×u64 low product (AVX512DQ+VL). Binary. -/
  | vpmullq
  /-- `VPAND a, b` — bitwise AND. Binary. -/
  | vpand
  /-- `VPOR a, b` — bitwise OR. Binary. -/
  | vpor
  /-- `VPXOR a, b` — bitwise XOR. Binary. -/
  | vpxor
  /-- `VPSHUFB a, b` — per-128-lane byte gather under a control vector. Binary. -/
  | vpshufb
  /-- `VPSRLQ a, imm8` — 4×u64 logical shift right (`imm8` baked in). Unary. -/
  | vpsrlq (imm : Nat)
  /-- `VPSLLQ a, imm8` — 4×u64 logical shift left (`imm8` baked in). Unary. -/
  | vpsllq (imm : Nat)
  /-- `VPSRLD a, imm8` — 8×u32 logical shift right (`imm8` baked in). Unary. -/
  | vpsrld (imm : Nat)
  /-- `VPSLLD a, imm8` — 8×u32 logical shift left (`imm8` baked in). Unary. -/
  | vpslld (imm : Nat)
  deriving DecidableEq, Repr

/-- Whether the op consumes one (`false`) or two (`true`) register operands.
    The binary ops are `vpmuldq`/`vpsubq`/`vpaddd`/`vpsubd`/`vpblendd`; the
    unary ops are `vmovshdup`/`vpshufd`/`vpermq`. -/
def YmmOp.isBinary : YmmOp → Bool
  | .vpmuldq => true
  | .vmovshdup => false
  | .vpsubq => true
  | .vpaddd => true
  | .vpsubd => true
  | .vpblendd _ => true
  | .vpshufd _ => false
  | .vpermq _ => false
  | .vpmuludq => true
  | .vpaddq => true
  | .vpmullq => true
  | .vpand => true
  | .vpor => true
  | .vpxor => true
  | .vpshufb => true
  | .vpsrlq _ => false
  | .vpsllq _ => false
  | .vpsrld _ => false
  | .vpslld _ => false

/-- Argument types: every register operand is a `reg 256`. Unary ops take a
    single `reg 256`, binary ops take two. (When wired into `Com`, this drives
    the per-op arity — the unary arms have a 1-element `argTys`.) -/
def YmmOp.argTys : YmmOp → List JasminTy
  | .vpmuldq => [.reg 256, .reg 256]
  | .vmovshdup => [.reg 256]
  | .vpsubq => [.reg 256, .reg 256]
  | .vpaddd => [.reg 256, .reg 256]
  | .vpsubd => [.reg 256, .reg 256]
  | .vpblendd _ => [.reg 256, .reg 256]
  | .vpshufd _ => [.reg 256]
  | .vpermq _ => [.reg 256]
  | .vpmuludq => [.reg 256, .reg 256]
  | .vpaddq => [.reg 256, .reg 256]
  | .vpmullq => [.reg 256, .reg 256]
  | .vpand => [.reg 256, .reg 256]
  | .vpor => [.reg 256, .reg 256]
  | .vpxor => [.reg 256, .reg 256]
  | .vpshufb => [.reg 256, .reg 256]
  | .vpsrlq _ => [.reg 256]
  | .vpsllq _ => [.reg 256]
  | .vpsrld _ => [.reg 256]
  | .vpslld _ => [.reg 256]

/-- Result type: every `YmmOp` produces a single `reg 256`.
    (The SIMD→GPR `vpmovmskb` extract, which would return `reg 32`, is the
    residual scoped OUT of this family — see the module docstring.) -/
def YmmOp.retTy : YmmOp → JasminTy
  | _ => .reg 256

/-- The jasmin/x86 (gas / AT&T) mnemonic of a `YmmOp` for asm emit. The AT&T
    print is lower-case with operands in `src…, dst` order; the printer adds the
    `$imm`/`%ymm` operands. -/
def YmmOp.attMnemonic : YmmOp → String
  | .vpmuldq => "vpmuldq"
  | .vmovshdup => "vmovshdup"
  | .vpsubq => "vpsubq"
  | .vpaddd => "vpaddd"
  | .vpsubd => "vpsubd"
  | .vpblendd _ => "vpblendd"
  | .vpshufd _ => "vpshufd"
  | .vpermq _ => "vpermq"
  | .vpmuludq => "vpmuludq"
  | .vpaddq => "vpaddq"
  | .vpmullq => "vpmullq"
  | .vpand => "vpand"
  | .vpor => "vpor"
  | .vpxor => "vpxor"
  | .vpshufb => "vpshufb"
  | .vpsrlq _ => "vpsrlq"
  | .vpsllq _ => "vpsllq"
  | .vpsrld _ => "vpsrld"
  | .vpslld _ => "vpslld"

/-- The jasmin/Intel-SDM mnemonic of a `YmmOp` (upper-case, matching the
    `SimdOp.mnemonic` convention used by the dialect printer). -/
def YmmOp.jasminMnemonic : YmmOp → String
  | .vpmuldq => "VPMULDQ"
  | .vmovshdup => "VMOVSHDUP"
  | .vpsubq => "VPSUBQ"
  | .vpaddd => "VPADDD"
  | .vpsubd => "VPSUBD"
  | .vpblendd _ => "VPBLENDD"
  | .vpshufd _ => "VPSHUFD"
  | .vpermq _ => "VPERMQ"
  | .vpmuludq => "VPMULUDQ"
  | .vpaddq => "VPADDQ"
  | .vpmullq => "VPMULLQ"
  | .vpand => "VPAND"
  | .vpor => "VPOR"
  | .vpxor => "VPXOR"
  | .vpshufb => "VPSHUFB"
  | .vpsrlq _ => "VPSRLQ"
  | .vpsllq _ => "VPSLLQ"
  | .vpsrld _ => "VPSRLD"
  | .vpslld _ => "VPSLLD"

/-! ## 4. Per-arm denotation (mixed arity)

`YmmOp.denote` reads up to two `BitVec 256` inputs and dispatches per arm to the
verbatim lane bodies. Unary arms ignore the second operand `b`. This is the
single denote the `Com` integration will use; the integration projects the
actual arity through `argTys` (binary arms get `[a, b]`, unary arms `[a]` with a
dummy second operand at the call site — or, equivalently, the integration step
may split `denote` into `denoteUnary`/`denoteBinary`; both are provided). -/

/-- The unary-op denotation (`vmovshdup`/`vpshufd`/`vpermq`). For the binary ops
    this is unused. -/
def YmmOp.denoteUnary : YmmOp → BitVec 256 → BitVec 256
  | .vmovshdup, a => vmovshdupW a
  | .vpshufd imm, a => vpshufdW a imm
  | .vpermq imm, a => vpermqW a imm
  | .vpsrlq imm, a => vpsrlqW a imm
  | .vpsllq imm, a => vpsllqW a imm
  | .vpsrld imm, a => vpsrldW a imm
  | .vpslld imm, a => vpslldW a imm
  -- binary ops: only the first operand is meaningful here; the
  -- two-operand semantics is `denoteBinary`. Provided total for convenience.
  | .vpmuldq, a => vpmuldqW a a
  | .vpsubq, a => vpsubqW a a
  | .vpaddd, a => vpadddW a a
  | .vpsubd, a => vpsubdW a a
  | .vpblendd imm, a => vpblenddW a a imm
  | .vpmuludq, a => vpmuludqW a a
  | .vpaddq, a => vpaddqW a a
  | .vpmullq, a => vpmullqW a a
  | .vpand, a => vpandW a a
  | .vpor, a => vporW a a
  | .vpxor, a => vpxorW a a
  | .vpshufb, a => vpshufbW a a

/-- The binary-op denotation (`vpmuldq`/`vpsubq`/`vpaddd`/`vpsubd`/`vpblendd`).
    The unary arms ignore `b`. -/
def YmmOp.denoteBinary : YmmOp → BitVec 256 → BitVec 256 → BitVec 256
  | .vpmuldq, a, b => vpmuldqW a b
  | .vpsubq, a, b => vpsubqW a b
  | .vpaddd, a, b => vpadddW a b
  | .vpsubd, a, b => vpsubdW a b
  | .vpblendd imm, a, b => vpblenddW a b imm
  | .vpmuludq, a, b => vpmuludqW a b
  | .vpaddq, a, b => vpaddqW a b
  | .vpmullq, a, b => vpmullqW a b
  | .vpand, a, b => vpandW a b
  | .vpor, a, b => vporW a b
  | .vpxor, a, b => vpxorW a b
  | .vpshufb, a, b => vpshufbW a b
  | .vmovshdup, a, _ => vmovshdupW a
  | .vpshufd imm, a, _ => vpshufdW a imm
  | .vpermq imm, a, _ => vpermqW a imm
  | .vpsrlq imm, a, _ => vpsrlqW a imm
  | .vpsllq imm, a, _ => vpsllqW a imm
  | .vpsrld imm, a, _ => vpsrldW a imm
  | .vpslld imm, a, _ => vpslldW a imm

/-- The uniform per-arm denotation, reading two `BitVec 256` operands (the unary
    arms ignore the second). This is the single dispatch the `Com` integration
    routes `JasminOp.vymm` through; it agrees with `denoteBinary` by definition,
    and with `denoteUnary` on the unary arms. -/
def YmmOp.denote : YmmOp → BitVec 256 → BitVec 256 → BitVec 256 :=
  YmmOp.denoteBinary

/-! ## 5. Smoke pins (matching `Avx2YmmModel`'s lane KATs)

These re-run the model's lane KATs against the `W`-suffixed copies through the
`YmmOp.denote` dispatch, so the standalone op family is pinned to the same lane
semantics as the bespoke model before any migration. -/

/-- `vpmuldq` POSITIVE pin (matches the model's positive lane KAT): even dword 0
    of `a = 7`, of `b = 3`, product `21` in qword lane 0; odd dwords ignored. -/
example :
    yQwordW (YmmOp.denote .vpmuldq
      (yOfDwordsW ![7, 999, 0, 0, 0, 0, 0, 0])
      (yOfDwordsW ![3, 888, 0, 0, 0, 0, 0, 0])) 0 = (21 : BitVec 64) := by native_decide

/-- `vpmuldq` NEGATIVE pin (signedness required): `-2` (`0xFFFFFFFE`) times
    `3` is the SIGNED product `-6` (`0xFFFFFFFFFFFFFFFA`). -/
example :
    yQwordW (YmmOp.denote .vpmuldq
      (yOfDwordsW ![BitVec.ofNat 32 0xFFFFFFFE, 0, 0, 0, 0, 0, 0, 0])
      (yOfDwordsW ![3, 0, 0, 0, 0, 0, 0, 0])) 0
    = BitVec.ofNat 64 0xFFFFFFFFFFFFFFFA := by native_decide

/-- `vmovshdup` pin (unary): source dwords `[0,1,2,3,4,5,6,7]` ⇒ `[1,1,3,3,5,5,7,7]`. -/
example :
    let r := YmmOp.denote .vmovshdup (yOfDwordsW ![0, 1, 2, 3, 4, 5, 6, 7]) 0;
    (yDwordW r 0 = 1) ∧ (yDwordW r 1 = 1) ∧ (yDwordW r 2 = 3) ∧ (yDwordW r 3 = 3) ∧
    (yDwordW r 6 = 7) ∧ (yDwordW r 7 = 7) := by native_decide

/-- `vpsubq` pin: `0 − 1 = 2⁶⁴−1` in lane 0 with NO borrow into lane 1. -/
example :
    let r := YmmOp.denote .vpsubq (yOfQwordsW ![0, 5, 0, 0]) (yOfQwordsW ![1, 2, 0, 0]);
    (yQwordW r 0 = BitVec.allOnes 64) ∧ (yQwordW r 1 = 3) := by native_decide

/-- `vpaddd` pin: `(2³²−1) + 1 = 0` in dword 0, independent of the other dwords. -/
example :
    yDwordW (YmmOp.denote .vpaddd (yOfDwordsW ![BitVec.allOnes 32, 0, 0, 0, 0, 0, 0, 0])
                   (yOfDwordsW ![1, 0, 0, 0, 0, 0, 0, 0])) 0 = 0 := by native_decide

/-- `vpsubd` pin: `0 − 1 = 2³²−1` in dword 0, 32-bit-lane wrap. -/
example :
    yDwordW (YmmOp.denote .vpsubd (yOfDwordsW ![0, 0, 0, 0, 0, 0, 0, 0])
                   (yOfDwordsW ![1, 0, 0, 0, 0, 0, 0, 0])) 0 = BitVec.allOnes 32 := by
  native_decide

/-- `vpblendd $0xAA` pin: `0xAA = 0b10101010` selects `b` for odd dwords, `a` for
    even ⇒ `[a0,b1,a2,b3,a4,b5,a6,b7]` (the exact `$170` blend the NTT uses). -/
example :
    let a := yOfDwordsW ![0, 0, 0, 0, 0, 0, 0, 0];
    let b := yOfDwordsW ![1, 1, 1, 1, 1, 1, 1, 1];
    let r := YmmOp.denote (.vpblendd 0xAA) a b;
    (yDwordW r 0 = 0) ∧ (yDwordW r 1 = 1) ∧ (yDwordW r 2 = 0) ∧ (yDwordW r 3 = 1) ∧
    (yDwordW r 4 = 0) ∧ (yDwordW r 5 = 1) ∧ (yDwordW r 6 = 0) ∧ (yDwordW r 7 = 1) := by
  native_decide

/-- `vpshufd $0xFF` pin (unary): broadcast dword 3 within each 128-bit lane ⇒
    `[a3,a3,a3,a3, a7,a7,a7,a7]`. -/
example :
    let r := YmmOp.denote (.vpshufd 0xFF) (yOfDwordsW ![0, 1, 2, 3, 4, 5, 6, 7]) 0;
    (yDwordW r 0 = 3) ∧ (yDwordW r 3 = 3) ∧ (yDwordW r 4 = 7) ∧ (yDwordW r 7 = 7) := by
  native_decide

/-- `vpermq $0x4E` pin (unary, `0b01_00_11_10`): output qwords `[a2,a3,a0,a1]`
    (the 128-bit halves swapped). -/
example :
    let r := YmmOp.denote (.vpermq 0x4E) (yOfQwordsW ![0, 1, 2, 3]) 0;
    (yQwordW r 0 = 2) ∧ (yQwordW r 1 = 3) ∧ (yQwordW r 2 = 0) ∧ (yQwordW r 3 = 1) := by
  native_decide

/-- Cross-check: `YmmOp.denote` agrees with `Avx2YmmModel`'s lane ops on the
    Montgomery-mul fragment head — `vpmuldq` then `vmovshdup`, with a negative
    coefficient in the even-lane product. -/
example :
    let a := yOfDwordsW ![5, 0, BitVec.ofNat 32 0xFFFFFFFF, 0, 0, 0, 0, 0];
    let b := yOfDwordsW ![3, 11, 7, 22, 0, 0, 0, 0];
    let prod := YmmOp.denote .vpmuldq a b;
    let dup := YmmOp.denote .vmovshdup b 0;
    -- lane 0 = 5 * 3 = 15 (signed, positive)
    (yQwordW prod 0 = (15 : BitVec 64)) ∧
    -- lane 1 = (-1) * 7 = -7 (signed; even dword 2 of a = 0xFFFFFFFF = -1)
    (yQwordW prod 1 = BitVec.ofNat 64 0xFFFFFFFFFFFFFFF9) ∧
    -- vmovshdup of b: odd-dup ⇒ [11,11,22,22,0,0,0,0]
    (yDwordW dup 0 = 11) ∧ (yDwordW dup 1 = 11) ∧
    (yDwordW dup 2 = 22) ∧ (yDwordW dup 3 = 22) := by native_decide

/-! ## 6. Smoke pins for the added ALU ops

One pin per added op whose denotation could plausibly be mis-stated: the
signedness of `vpmuludq`, the lane boundary of `vpaddq`/`vpslld`, the low-product
truncation of `vpmullq`, the over-shift-to-zero of `vpsrlq`, and the byte gather
plus high-bit zeroing of `vpshufb`. The bitwise trio `vpand`/`vpor`/`vpxor` is
definitionally the whole-register operation, so a value pin adds nothing. -/

/-- `vpmuludq` UNSIGNED pin (this is what distinguishes it from `vpmuldq`):
    `0xFFFFFFFE` zero-extends to `4294967294`, so the product with `3` is
    `0x2FFFFFFFA`, not the signed `-6`. -/
example :
    yQwordW (YmmOp.denote .vpmuludq
      (yOfDwordsW ![BitVec.ofNat 32 0xFFFFFFFE, 0, 0, 0, 0, 0, 0, 0])
      (yOfDwordsW ![3, 0, 0, 0, 0, 0, 0, 0])) 0
    = BitVec.ofNat 64 0x2FFFFFFFA := by native_decide

/-- `vpaddq` pin: `(2⁶⁴−1) + 1 = 0` in lane 0 with NO carry into lane 1. -/
example :
    let r := YmmOp.denote .vpaddq (yOfQwordsW ![BitVec.allOnes 64, 5, 0, 0])
                                  (yOfQwordsW ![1, 2, 0, 0]);
    (yQwordW r 0 = 0) ∧ (yQwordW r 1 = 7) := by native_decide

/-- `vpmullq` pin: `2³³ · 2³³ = 2⁶⁶`, whose low 64 bits are zero. -/
example :
    yQwordW (YmmOp.denote .vpmullq (yOfQwordsW ![BitVec.ofNat 64 (2 ^ 33), 0, 0, 0])
      (yOfQwordsW ![BitVec.ofNat 64 (2 ^ 33), 0, 0, 0])) 0 = 0 := by native_decide

/-- `vpsrlq` pin: `2³⁰ >>> 26 = 2⁴` per qword lane, and a count at the lane width
    yields zero (the x86 `imm8 ≥ 64` behaviour). -/
example :
    let r := YmmOp.denote (.vpsrlq 26) (yOfQwordsW ![BitVec.ofNat 64 (2 ^ 30), 0, 0, 0]) 0;
    let z := YmmOp.denote (.vpsrlq 64) (yOfQwordsW ![BitVec.allOnes 64, 0, 0, 0]) 0;
    (yQwordW r 0 = BitVec.ofNat 64 (2 ^ 4)) ∧ (yQwordW z 0 = 0) := by native_decide

/-- `vpslld` pin: `0xF0000001 <<< 4` truncates within the 32-bit lane to
    `0x00000010`, with no bleed into dword lane 1. -/
example :
    let r := YmmOp.denote (.vpslld 4)
      (yOfDwordsW ![BitVec.ofNat 32 0xF0000001, 0, 0, 0, 0, 0, 0, 0]) 0;
    (yDwordW r 0 = BitVec.ofNat 32 0x00000010) ∧ (yDwordW r 1 = 0) := by native_decide

/-- `vpshufb` pin: with data byte `j = j`, control byte 0 = `3` gathers `a`'s byte
    3; control byte 1 = `0x80` zeroes the byte; control byte 16 = `0` gathers
    within the HIGH 128-bit lane, giving `a`'s byte 16 (not byte 0). -/
example :
    let a := yOfBytesW (fun i => BitVec.ofNat 8 i.val);
    let ctl := yOfBytesW (fun i => if i.val = 0 then 3 else if i.val = 1 then 0x80 else 0);
    let r := YmmOp.denote .vpshufb a ctl;
    (yByteW r 0 = 3) ∧ (yByteW r 1 = 0) ∧ (yByteW r 16 = 16) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
