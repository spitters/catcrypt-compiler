/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import Mathlib.Data.Fin.VecNotation

/-!
# The 256-bit YMM op family (`YmmOp`) for the AVX2 ML-DSA NTT

This module is the **dialect-side** op family that the AVX2 ML-DSA NTT kernel
(`X86Backend/Avx2YmmNttOwnedEmit.lean`) needs in order to migrate off the
bespoke `Avx2YmmModel.YInst` machine model — the last/hardest of the model
deletions. It is the 256-bit (VEX.256 / AVX2) analogue of the 128-bit `SimdOp`
in `JasminDialect.lean`.

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

## The honest anchor

The lane denote bodies are **copied verbatim** (with a `W` suffix) from the
KAT-pinned `Avx2YmmModel.lean` — `yDwordW`/`yQwordW`/`yOfDwordsW`/`yOfQwordsW`
plus each op. Faithfulness rests on the same anchor as the model: the lane ops
are the obviously-correct per-lane integer ops (auditable against the Intel SDM)
and the integration witness is the ML-DSA NTT KAT byte-identity
(`bench/mldsa_compare/`, PQClean reference). The signed `vpmuldq` is the one op
where signedness is load-bearing (Montgomery reduction); its body sign-extends
the even dwords and is re-pinned on negative-input vectors below.

## RESIDUAL scoped OUT of this module

The SIMD→GPR **extract** `vpmovmskb` (`X86Backend/Avx2ExtractEmit.lean`) is NOT
modelled here. It leaves the vector register file: it reads a `BitVec 256` and
writes a `BitVec 32` *into a GPR*, so its result type is **not** `reg 256`
(it is `reg 32`, a cross-file move). The whole `YmmOp` family is closed under
`reg 256 → reg 256` (`argTys`/`retTy` below), so adding `vpmovmskb` would break
that uniformity and needs a `reg 32` return arm. It is left to the integration
step / a follow-up op.

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
  -- binary ops: only the first operand is meaningful here; the genuine
  -- two-operand semantics is `denoteBinary`. Provided total for convenience.
  | .vpmuldq, a => vpmuldqW a a
  | .vpsubq, a => vpsubqW a a
  | .vpaddd, a => vpadddW a a
  | .vpsubd, a => vpsubdW a a
  | .vpblendd imm, a => vpblenddW a a imm

/-- The binary-op denotation (`vpmuldq`/`vpsubq`/`vpaddd`/`vpsubd`/`vpblendd`).
    The unary arms ignore `b`. -/
def YmmOp.denoteBinary : YmmOp → BitVec 256 → BitVec 256 → BitVec 256
  | .vpmuldq, a, b => vpmuldqW a b
  | .vpsubq, a, b => vpsubqW a b
  | .vpaddd, a, b => vpadddW a b
  | .vpsubd, a, b => vpsubdW a b
  | .vpblendd imm, a, b => vpblenddW a b imm
  | .vmovshdup, a, _ => vmovshdupW a
  | .vpshufd imm, a, _ => vpshufdW a imm
  | .vpermq imm, a, _ => vpermqW a imm

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

/-- `vpmuldq` NEGATIVE pin (signedness load-bearing): `-2` (`0xFFFFFFFE`) times
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

end CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
