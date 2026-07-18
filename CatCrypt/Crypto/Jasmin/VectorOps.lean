/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumExec

set_option autoImplicit false

/-!
# AVX2 vector-op scaffolding for InstrR / JasminAST

This file is a *starting point* that lays down a clean op surface for
AVX2 256-bit vector instructions in the InstrR / JasminAST tree, so
that future work on vector-grade ML-KEM (Kyber NTT) and other SIMD-heavy
ports has a stable landing pad to extend.

The motivation is that the current ML-KEM pipeline lands as scalar
`extCall` leaves (commit `a541cd92`, K-PQ.1) which is functionally
complete but ~3-5× slower than the AVX2 path. Folding in a verified
vector op surface lets later K-PQ.1 / K-PQ.2 / NTT-heavy ports target
this file rather than each minting their own opcode dialect.

## Audit boundary

Each helper in §1 below mirrors **one** Intel SDM Vol. 2 operation as
a closed-form `BitVec` computation. The operand widths and lane shapes
are pinned to the AVX2 ymm-register conventions: a `BitVec 256` split
into 16 lanes of `BitVec 16` (the dominant shape for ML-KEM NTT, where
Kyber works in `Z/3329` representable in 13 bits per lane).

## Design template

Following `Examples/Curve25519CryptoptOps.lean` (commit `e5da8b41`):
this file is a **pure wrapper**. It does not edit `JasminAST.lean`,
`LowCT.lean`, `BignumExec.lean`, or any other file in the tree.
Future agents fold these op names into the main dispatcher when the
state model is extended to carry vector registers.

## Explicitly deferred (out of scope here)

- Semantics-equivalence proofs (`vpaddw_correct` etc.) against an
  Intel SDM reference.
- Preservation through `CryptoSSA → Jasmin` lowering.
- `BignumExec` dispatch — the existing `BignumState` only models a
  scalar register file (`String → BitVec 64`); a vector dispatch
  needs a `vregs : String → BitVec 256` field added there. Until
  that lands the wrapper interpreter below returns `none` on the new
  opcodes, signalling "vector state not modelled yet".
- Writeback of vector results into `LVal` shapes that include memory
  stores or array updates (only `[.Lvar v256]` is handled).
-/

namespace CatCrypt.Crypto.Jasmin.VectorOps

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec

/-! ## §1. Vector-op pure semantics scaffolding

Each function below mirrors one AVX2 256-bit instruction. Lane width
is fixed at 16 bits (the Kyber NTT shape: 16 lanes per ymm). Helpers
work directly on `BitVec 256`. -/

/-- Extract lane `i` (0-15) of a 16×i16 packed `BitVec 256`. -/
def lane16 (v : BitVec 256) (i : Nat) : BitVec 16 :=
  (v >>> (i * 16)).extractLsb' 0 16

/-- Pack a length-16 list of `BitVec 16` into a `BitVec 256`. The list
    is in little-lane order: head = lane 0 = low 16 bits. Lists of
    other lengths are padded / truncated to 16 lanes (with `0`). -/
def pack16 (lanes : List (BitVec 16)) : BitVec 256 :=
  lanes.foldr
    (fun lane (acc : BitVec 256) =>
      (acc <<< (16 : Nat)) ||| BitVec.ofNat 256 lane.toNat)
    (0 : BitVec 256)

/-- Per-lane unary map. -/
def map16 (f : BitVec 16 → BitVec 16) (v : BitVec 256) : BitVec 256 :=
  pack16 ((List.range 16).map (fun i => f (lane16 v i)))

/-- Per-lane binary map. -/
def zip16 (f : BitVec 16 → BitVec 16 → BitVec 16) (a b : BitVec 256) :
    BitVec 256 :=
  pack16 ((List.range 16).map (fun i => f (lane16 a i) (lane16 b i)))

/-- `VPADDW ymm, ymm, ymm` — packed add of 16×i16, wrapping mod 2^16. -/
def vpaddw (a b : BitVec 256) : BitVec 256 := zip16 (· + ·) a b

/-- `VPSUBW ymm, ymm, ymm` — packed sub of 16×i16, wrapping mod 2^16. -/
def vpsubw (a b : BitVec 256) : BitVec 256 := zip16 (· - ·) a b

/-- `VPMULLW ymm, ymm, ymm` — packed multiply, low 16 bits per lane.
    `BitVec.mul` already wraps to the destination width (16). -/
def vpmullw (a b : BitVec 256) : BitVec 256 := zip16 (· * ·) a b

/-- `VPMULHW ymm, ymm, ymm` — packed signed multiply, high 16 bits per
    lane. Computed by sign-extending each lane to 32 bits, multiplying,
    and extracting bits [31:16]. -/
def vpmulhw (a b : BitVec 256) : BitVec 256 :=
  zip16 (fun x y =>
    let xs : BitVec 32 := x.signExtend 32
    let ys : BitVec 32 := y.signExtend 32
    ((xs * ys) >>> 16).extractLsb' 0 16) a b

/-- `VPAND ymm, ymm, ymm` — bitwise AND of the full 256-bit register.
    No need to lane-decompose: `&&&` already commutes with `pack16`. -/
def vpand (a b : BitVec 256) : BitVec 256 := a &&& b

/-- `VPXOR ymm, ymm, ymm` — bitwise XOR of the full 256-bit register. -/
def vpxor (a b : BitVec 256) : BitVec 256 := a ^^^ b

/-- `VPSRAW ymm, ymm, imm8` — per-lane arithmetic right shift by `n`.
    SDM: shift counts ≥ 16 saturate to all sign-bits. We handle this by
    masking `n` to `min n 15` for the in-range case and falling back to
    sign-broadcast otherwise. -/
def vpsraw (v : BitVec 256) (n : Nat) : BitVec 256 :=
  if n ≥ 16 then
    -- saturate: each lane becomes its sign-bit broadcast.
    map16 (fun x => if x.msb then BitVec.ofNat 16 0xFFFF else 0) v
  else
    map16 (fun x => BitVec.sshiftRight x n) v

/-- `VPSRLW ymm, ymm, imm8` — per-lane logical right shift by `n`.
    SDM: shift counts ≥ 16 zero the lane. -/
def vpsrlw (v : BitVec 256) (n : Nat) : BitVec 256 :=
  if n ≥ 16 then 0 else map16 (fun x => x >>> n) v

/-- `VPBROADCASTW ymm, m16/xmm` — replicate a 16-bit source into all
    16 lanes. -/
def vpbroadcastw (w : BitVec 16) : BitVec 256 :=
  pack16 (List.replicate 16 w)

/-- `VPERMQ ymm, ymm, imm8` — permute the four 64-bit lanes by the
    2-bit fields of `imm8` (lane `i` of the result = lane `(imm8 >> 2i) &
    3` of the source). This is the SDM 4-lane permute used by Kyber's
    NTT shuffles. -/
def vpermq (v : BitVec 256) (imm8 : Nat) : BitVec 256 :=
  let lane64 (i : Nat) : BitVec 64 :=
    (v >>> (i * 64)).extractLsb' 0 64
  let pick (i : Nat) : BitVec 64 := lane64 ((imm8 >>> (2 * i)) &&& 3)
  let l0 := BitVec.ofNat 256 (pick 0).toNat
  let l1 := BitVec.ofNat 256 (pick 1).toNat <<< 64
  let l2 := BitVec.ofNat 256 (pick 2).toNat <<< 128
  let l3 := BitVec.ofNat 256 (pick 3).toNat <<< 192
  l0 ||| l1 ||| l2 ||| l3

/-! ## §2. LVal write helpers for vector bundles

Every AVX2 op above writes to a single 256-bit destination register
(no flag bundle, no two-output split). The corresponding LVal shape
is therefore the singleton `[.Lvar v256]`.

Note: `BignumState.regs : String → BitVec 64` cannot hold a `BitVec
256`. The helpers below are typed stubs that make the LVal shape
explicit; actually committing the result requires the future
`vregs : String → BitVec 256` extension of `BignumState`. -/

/-- The single-LVal vector-destination shape: `[.Lvar v256]`. Returns
    the destination variable name on a match, `none` otherwise. -/
def matchVecDst : List LVal → Option String
  | [.Lvar v] => some v.var.vname
  | _         => none

/-- Stub: write a 256-bit result into a single-LVal bundle.

    Returns `none` deliberately: `BignumState` does not model vector
    registers yet (see module docstring "Explicitly deferred"). When
    the `vregs` field is added, this helper is the single point that
    needs to update — every §3 dispatch goes through it. -/
def writeVec256 (_s : BignumState) (lvs : List LVal) (_v : BitVec 256) :
    Option BignumState :=
  match matchVecDst lvs with
  | some _ => none   -- placeholder for `setVReg s name v`
  | none   => none

/-! ## §3. Wrapper interpreter scaffolding

`execVectorInstrPlus` matches the new opcode names and produces the
abstract `BitVec 256` result via §1, then would commit it via §2.
Until `BignumState` is extended with vector registers, every dispatch
arm calls `writeVec256` which currently returns `none`. This file is
the explicit hook future agents extend; no fall-through to
`BignumExec.execInstr` is sound here, because the scalar interpreter
has no notion of these opcodes either. -/

/-- Best-effort 256-bit operand fetch. Real vector loads need a
    `BignumState.vregs` lookup; until that field exists this stub
    always returns `none`, which propagates through the `do` block. -/
def evalPExpr256 (_s : BignumState) (_e : PExpr) : Option (BitVec 256) :=
  none

/-- Wrapper interpreter for AVX2 256-bit ops. All arms currently
    return `none` (vector state not modelled), but the *structure* of
    the dispatch — opcode-name table, operand-arity, LVal shape — is
    final. -/
def execVectorInstrPlus (s : BignumState) : InstrR → Option BignumState
  | .Copn lvs _ (.Oasm op) args =>
    match op.name, args with
    | "VPADDW_256",  [ea, eb] => do
        let a ← evalPExpr256 s ea
        let b ← evalPExpr256 s eb
        writeVec256 s lvs (vpaddw a b)
    | "VPSUBW_256",  [ea, eb] => do
        let a ← evalPExpr256 s ea
        let b ← evalPExpr256 s eb
        writeVec256 s lvs (vpsubw a b)
    | "VPMULLW_256", [ea, eb] => do
        let a ← evalPExpr256 s ea
        let b ← evalPExpr256 s eb
        writeVec256 s lvs (vpmullw a b)
    | "VPMULHW_256", [ea, eb] => do
        let a ← evalPExpr256 s ea
        let b ← evalPExpr256 s eb
        writeVec256 s lvs (vpmulhw a b)
    | "VPAND_256",   [ea, eb] => do
        let a ← evalPExpr256 s ea
        let b ← evalPExpr256 s eb
        writeVec256 s lvs (vpand a b)
    | "VPXOR_256",   [ea, eb] => do
        let a ← evalPExpr256 s ea
        let b ← evalPExpr256 s eb
        writeVec256 s lvs (vpxor a b)
    | "VPSRAW_256",  [ea, .Pconst k] => do
        let a ← evalPExpr256 s ea
        writeVec256 s lvs (vpsraw a k.toNat)
    | "VPSRLW_256",  [ea, .Pconst k] => do
        let a ← evalPExpr256 s ea
        writeVec256 s lvs (vpsrlw a k.toNat)
    | "VPBROADCASTW_256", [ea] => do
        let a ← evalPExpr s ea          -- 64-bit scalar source register
        writeVec256 s lvs (vpbroadcastw (a.extractLsb' 0 16))
    | "VPERMQ_256",  [ea, .Pconst k] => do
        let a ← evalPExpr256 s ea
        writeVec256 s lvs (vpermq a k.toNat)
    | _, _ => none
  | _ => none

/-! ## §4. Sanity examples

Each example pins down a concrete `BitVec 256` identity for one of
the §1 helpers, decided by `native_decide`. These are deliberately
small (no large lane lists) so the file does not bloat compile time.
-/

/-- Adding two broadcast-of-1 vectors gives broadcast-of-2. -/
example :
    vpaddw (vpbroadcastw 1) (vpbroadcastw 1) = vpbroadcastw 2 := by
  native_decide

/-- Subtracting equals zeroes out. -/
example :
    vpsubw (vpbroadcastw 0x1234) (vpbroadcastw 0x1234) = 0 := by
  native_decide

/-- Multiplying broadcasts: low-16 of 7 × 11 = 77. -/
example :
    vpmullw (vpbroadcastw 7) (vpbroadcastw 11) = vpbroadcastw 77 := by
  native_decide

/-- VPMULHW of broadcast-0xFFFF × broadcast-0xFFFF (both = -1 signed)
    yields broadcast-0: signed (-1) * (-1) = 1, low 16 bits = 1, high
    16 bits = 0. -/
example :
    vpmulhw (vpbroadcastw 0xFFFF) (vpbroadcastw 0xFFFF) = 0 := by
  native_decide

/-- AND of broadcast 0x00FF and broadcast 0x0F0F is broadcast 0x000F. -/
example :
    vpand (vpbroadcastw 0x00FF) (vpbroadcastw 0x0F0F) = vpbroadcastw 0x000F := by
  native_decide

/-- XOR-self is zero. -/
example :
    vpxor (vpbroadcastw 0xCAFE) (vpbroadcastw 0xCAFE) = 0 := by
  native_decide

/-- VPSRLW by 4 of broadcast-0x00F0 = broadcast-0x000F. -/
example :
    vpsrlw (vpbroadcastw 0x00F0) 4 = vpbroadcastw 0x000F := by
  native_decide

/-- VPBROADCASTW commits to all 16 lanes — extracting any lane gives
    back the source. -/
example :
    lane16 (vpbroadcastw 0xBEEF) 7 = 0xBEEF := by
  native_decide

end CatCrypt.Crypto.Jasmin.VectorOps
