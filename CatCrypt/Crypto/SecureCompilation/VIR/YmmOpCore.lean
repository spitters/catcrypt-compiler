/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Fin.VecNotation

/-!
# The 256-bit YMM op family core (`YmmOp`), `JasminTy`-free

The `JasminTy`-free part of the 256-bit YMM op family: the lane views, the
per-lane ALU semantics, the `YmmOp` inductive, its mnemonics, and its per-arm
denotation over `BitVec 256`. Everything here is pure `BitVec`/`String`; nothing
mentions `JasminTy`. The `argTys`/`retTy` routing into `JasminTy` and the smoke
pins live in `YmmDialectOps.lean`, which imports this file.

Splitting these definitions out of `YmmDialectOps.lean` breaks the import cycle
that would otherwise arise once `JasminDialect` gains a `JasminOp.vymm` arm:
`JasminDialect` imports this core, and `YmmDialectOps` imports both.

## Main results

* `YmmOp`: the 256-bit VEX.256/AVX2 register-only op inductive.
* `YmmOp.isBinary`: the per-op arity (one vs two `reg 256` operands).
* `YmmOp.denoteUnary` / `denoteBinary` / `denote`: the per-arm `BitVec 256`
  semantics.
* `yDwordW` / `yOfDwordsW` (and the qword/byte analogues): the lane views the
  ALU semantics are stated over.

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

## The anchor

The lane denote bodies are **copied verbatim** (with a `W` suffix) from the
KAT-pinned `Avx2YmmModel.lean` — `yDwordW`/`yQwordW`/`yOfDwordsW`/`yOfQwordsW`
plus each op. Faithfulness rests on the same anchor as the model: the lane ops
are the obviously-correct per-lane integer ops (auditable against the Intel SDM)
and the integration witness is the ML-DSA NTT KAT byte-identity
(`bench/mldsa_compare/`, PQClean reference). The signed `vpmuldq` is the one op
where signedness is required (Montgomery reduction); its body sign-extends
the even dwords.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

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

/-- `VPSRLVD a, b`: 8 × logical shift right of each 32-bit lane of `a` by the
    corresponding 32-bit count lane of `b` (zero for a count `≥ 32`, matching x86 —
    `BitVec.ushiftRight` by `≥ width` is `0`). AVX2 variable per-lane shift. -/
def vpsrlvdW (a b : BitVec 256) : BitVec 256 :=
  yOfDwordsW (fun i => yDwordW a i.val >>> (yDwordW b i.val).toNat)

/-- `VPSLLVD a, b`: 8 × logical shift left of each 32-bit lane of `a` by the
    corresponding 32-bit count lane of `b` (zero for a count `≥ 32`). AVX2
    variable per-lane shift. -/
def vpsllvdW (a b : BitVec 256) : BitVec 256 :=
  yOfDwordsW (fun i => yDwordW a i.val <<< (yDwordW b i.val).toNat)

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
  /-- `VPSRLVD a, b` — 8×u32 logical shift right by a per-lane count vector. Binary. -/
  | vpsrlvd
  /-- `VPSLLVD a, b` — 8×u32 logical shift left by a per-lane count vector. Binary. -/
  | vpsllvd
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
  | .vpsrlvd => true
  | .vpsllvd => true

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
  | .vpsrlvd => "vpsrlvd"
  | .vpsllvd => "vpsllvd"

/-- The jasmin/Intel-SDM mnemonic of a `YmmOp` (upper-case, matching the
    `SimdOp.mnemonic` convention used by the dialect printer). -/
def YmmOp.jasminMnemonic : YmmOp → String
  | .vpmuldq => "VPMULDQ"
  | .vmovshdup => "VMOVSHDUP"
  | .vpsubq => "VPSUBQ"
  | .vpaddd => "VPADDD"
  | .vpsubd => "VPSUBD"
  | .vpblendd n => "VPBLENDD:" ++ toString n
  | .vpshufd n => "VPSHUFD:" ++ toString n
  | .vpermq n => "VPERMQ:" ++ toString n
  | .vpmuludq => "VPMULUDQ"
  | .vpaddq => "VPADDQ"
  | .vpmullq => "VPMULLQ"
  | .vpand => "VPAND"
  | .vpor => "VPOR"
  | .vpxor => "VPXOR"
  | .vpshufb => "VPSHUFB"
  | .vpsrlq n => "VPSRLQ:" ++ toString n
  | .vpsllq n => "VPSLLQ:" ++ toString n
  | .vpsrld n => "VPSRLD:" ++ toString n
  | .vpslld n => "VPSLLD:" ++ toString n
  | .vpsrlvd => "VPSRLVD"
  | .vpsllvd => "VPSLLVD"

/-! ## 4. Per-arm denotation (mixed arity)

`YmmOp.denote` reads up to two `BitVec 256` inputs and dispatches per arm to the
verbatim lane bodies. Unary arms ignore the second operand `b`. This is the
single denote the `Com` integration uses; the integration projects the actual
arity through `argTys` (binary arms get `[a, b]`, unary arms `[a]`); `denote`
splits into `denoteUnary`/`denoteBinary`, both provided. -/

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
  | .vpsrlvd, a => vpsrlvdW a a
  | .vpsllvd, a => vpsllvdW a a

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
  | .vpsrlvd, a, b => vpsrlvdW a b
  | .vpsllvd, a, b => vpsllvdW a b

/-- The uniform per-arm denotation, reading two `BitVec 256` operands (the unary
    arms ignore the second). This is the single dispatch the `Com` integration
    routes `JasminOp.vymm` through; it agrees with `denoteBinary` by definition,
    and with `denoteUnary` on the unary arms. -/
def YmmOp.denote : YmmOp → BitVec 256 → BitVec 256 → BitVec 256 :=
  YmmOp.denoteBinary

end CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
