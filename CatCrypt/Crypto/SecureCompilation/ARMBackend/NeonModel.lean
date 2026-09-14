/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types

/-!
# A Lean AArch64 NEON/ASIMD machine model, 128-bit V-register, 4 × u32 lane shape (#548)

`X86Backend/Vec128Model.lean` is the **128-bit XMM, 4 × u32-lane** owned x86 SIMD
machine layer (the AVX analogue of `ArmModel`'s scalar GP file), and the ChaCha
4-way kernel rides it end-to-end. This module is its **AArch64 NEON/ASIMD**
analogue: a named 128-bit `V`-register file (`NState`) over the A64 vector
registers (`v0 … v31`), and the per-instruction semantics
(`evalNInst` / `runNBlock`) of the packed ASIMD ops the ChaCha 4-way
quarter-round emits — the V-register sibling of `ArmModel`'s scalar `AState` /
64-bit `BState`.

`NeonLowering.lean` lifts a register-named op alphabet (`NOp`) onto this model
with the block-lowering denotation theorem `neonBlock_lowering_denote` (proved by
induction with no new custom axioms); `NeonAsmPrinter.lean` renders the lowered `NInst`
block to GAS AArch64 ASIMD assembly text with a linear-scan V allocator;
`NeonEncoder.lean` + `SailNeonDecoder.lean` give the verified-to-bytes
`decode(encode i) = i` against the hand-transcribed `rems-project/sail-arm`
`decode64` ASIMD clauses (upstream is not vendored in this repo and the
transcription is not machine-checked).

## The honest anchor (same posture as the x86 Vec128 model)

As with the XMM model, there is no ported authoritative model for the packed-u32
ASIMD ALU semantics here; the faithfulness of `evalNInst` rests on **differential
validation against the RFC 8439 KAT** of the emitted ChaCha 4-way kernel (run
under qemu-aarch64 in `bench/arm_compare/`). The semantics is written to be
*obviously the per-lane integer op the mnemonic computes* (a `VectorTy.map₂` /
`map₁imm` over `BitVec 32` lanes), auditable against the Arm ARM by eye. The
**lowering** `NOp → NInst → NState transform` is verified down to this model
(`NeonLowering.neonBlock_lowering_denote`, no new custom axioms); the model's
lane semantics is differential-validated, exactly the trust shape documented in
`Vec128Model.lean`.

## The packed-u32 ASIMD ops we model (the NEON subset ChaCha 4-way emits)

| mnemonic        | shape           | lane op (4 × u32 / 16 × u8)        |
|-----------------|-----------------|------------------------------------|
| `ADD  Vd.4S`    | `v,v→v`         | `aᵢ + bᵢ`   (wrapping 32-bit)      |
| `SUB  Vd.4S`    | `v,v→v`         | `aᵢ - bᵢ`   (wrapping 32-bit)      |
| `MUL  Vd.4S`    | `v,v→v`         | `aᵢ * bᵢ`   (wrapping 32-bit)      |
| `AND  Vd.16B`   | `v,v→v`         | `aᵢ &&& bᵢ` (bitwise and)          |
| `ORR  Vd.16B`   | `v,v→v`         | `aᵢ ||| bᵢ` (bitwise or)           |
| `EOR  Vd.16B`   | `v,v→v`         | `aᵢ ^^^ bᵢ` (bitwise xor)          |
| `SHL  Vd.4S,#n` | `v,imm→v`       | `aᵢ <<< n`  (logical shl)          |
| `USHR Vd.4S,#n` | `v,imm→v`       | `aᵢ >>> n`  (logical shr)          |

A64 NEON has no packed rotate, so the ChaCha rotate `x <<<ʳ n` is realized as
`SHL t, x, #n ; USHR x, x, #(32-n) ; ORR x, t, x` (the portable shift+or idiom,
register-for-register the same shape as the x86 `VPSLLD;VPSRLD;VPOR`). We model
the three primitives directly. (`MUL.4S` and `SUB.4S` are modelled for the
butterfly/field SIMD path; `REV32`/`EXT` byte-permute shuffles are in
`NeonShuffle` below for the rotate-by-shuffle optimization the bench uses.)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The V-register lane type and register state

A 128-bit A64 `V` register, modelled as **4 × u32 lanes**
(`VectorTy (BitVec 32) 4`, i.e. the lane function `Fin 4 → BitVec 32`) — the same
ChaCha 4-way SoA shape as the x86 XMM model: register holding word-position `j`
carries that word across the 4 parallel blocks. -/

/-- A 128-bit A64 `V` register as 4 × u32 lanes (the ChaCha 4-way packed view). -/
abbrev Vec128 : Type := VectorTy (BitVec 32) 4

/-- The A64 `V` register file: a name → `Vec128` function. The NEON analogue of
    `Vec128Model.VState`. An absent name reads as the all-zero register. -/
structure NState where
  /-- The `v` register file (`v0 … v31`, named by string). -/
  vregs : String → Vec128

namespace NState

/-- Read a `v` register. An absent name reads as the zero register. -/
@[simp] def get (s : NState) (r : String) : Vec128 := s.vregs r

/-- Write a `v` register, leaving the others unchanged. -/
def setV (s : NState) (r : String) (v : Vec128) : NState :=
  { vregs := fun r' => if r' = r then v else s.vregs r' }

@[simp] theorem get_setV_same (s : NState) (r : String) (v : Vec128) :
    (s.setV r v).get r = v := by simp [setV, get]

@[simp] theorem get_setV_other (s : NState) (r r' : String) (v : Vec128)
    (h : r' ≠ r) : (s.setV r v).get r' = s.get r' := by simp [setV, get, h]

end NState

/-! ## 2. Per-lane packed-u32 ASIMD ALU semantics

Each op is the obvious per-lane integer op over `BitVec 32` lanes — auditable
against the Arm ARM ASIMD descriptions by eye. -/

/-- `ADD Vd.4S` lane op: wrapping 32-bit add. -/
@[simp] def laneAdd (a b : BitVec 32) : BitVec 32 := a + b

/-- `SUB Vd.4S` lane op: wrapping 32-bit subtract. -/
@[simp] def laneSub (a b : BitVec 32) : BitVec 32 := a - b

/-- `MUL Vd.4S` lane op: wrapping 32-bit multiply (low 32 bits). -/
@[simp] def laneMul (a b : BitVec 32) : BitVec 32 := a * b

/-- `AND Vd.16B` lane op: bitwise and (per 32-bit lane equal to per-byte and). -/
@[simp] def laneAnd (a b : BitVec 32) : BitVec 32 := a &&& b

/-- `ORR Vd.16B` lane op: bitwise or. -/
@[simp] def laneOrr (a b : BitVec 32) : BitVec 32 := a ||| b

/-- `EOR Vd.16B` lane op: bitwise xor. -/
@[simp] def laneEor (a b : BitVec 32) : BitVec 32 := a ^^^ b

/-- `SHL Vd.4S, #n` lane op: logical left shift by an immediate count. -/
@[simp] def laneShl (a : BitVec 32) (m : Nat) : BitVec 32 := a <<< m

/-- `USHR Vd.4S, #n` lane op: logical right shift by an immediate count. -/
@[simp] def laneUshr (a : BitVec 32) (m : Nat) : BitVec 32 := a >>> m

/-! ## 3. The NEON instruction set

The packed-u32 ASIMD subset the ChaCha 4-way kernel emits. Each arm names its
destination + source `v` registers (or an immediate count, for the shifts). The
machine-level analogue of `Vec128Model.VInst`, at 4 × u32 / 16 × u8 lane shape. -/

/-- A single packed-u32 NEON instruction over named `V` registers. -/
inductive NInst where
  /-- `ADD Vd.4S, Vn.4S, Vm.4S` — packed 4×u32 add. -/
  | add (d a b : String)
  /-- `SUB Vd.4S, Vn.4S, Vm.4S` — packed 4×u32 subtract. -/
  | sub (d a b : String)
  /-- `MUL Vd.4S, Vn.4S, Vm.4S` — packed 4×u32 multiply. -/
  | mul (d a b : String)
  /-- `AND Vd.16B, Vn.16B, Vm.16B` — packed bitwise and. -/
  | and (d a b : String)
  /-- `ORR Vd.16B, Vn.16B, Vm.16B` — packed bitwise or. -/
  | orr (d a b : String)
  /-- `EOR Vd.16B, Vn.16B, Vm.16B` — packed bitwise xor. -/
  | eor (d a b : String)
  /-- `SHL Vd.4S, Vn.4S, #imm` — packed logical shift-left by immediate. -/
  | shl (d a : String) (imm : Nat)
  /-- `USHR Vd.4S, Vn.4S, #imm` — packed logical shift-right by immediate. -/
  | ushr (d a : String) (imm : Nat)
  /-- `MOV Vd.16B, Vn.16B` — register move (the `ORR Vd, Vn, Vn` alias). -/
  | mov (d s : String)
  deriving Repr, DecidableEq

/-- The semantics of one NEON instruction: read source register(s), apply the
    per-lane op, write the destination. The analogue of `Vec128Model.evalVInst`. -/
def evalNInst (s : NState) : NInst → NState
  | .add d a b  => s.setV d (VectorTy.map₂ laneAdd (s.get a) (s.get b))
  | .sub d a b  => s.setV d (VectorTy.map₂ laneSub (s.get a) (s.get b))
  | .mul d a b  => s.setV d (VectorTy.map₂ laneMul (s.get a) (s.get b))
  | .and d a b  => s.setV d (VectorTy.map₂ laneAnd (s.get a) (s.get b))
  | .orr d a b  => s.setV d (VectorTy.map₂ laneOrr (s.get a) (s.get b))
  | .eor d a b  => s.setV d (VectorTy.map₂ laneEor (s.get a) (s.get b))
  | .shl d a m  => s.setV d (VectorTy.map₁imm laneShl m (s.get a))
  | .ushr d a m => s.setV d (VectorTy.map₁imm laneUshr m (s.get a))
  | .mov d s'   => s.setV d (s.get s')

/-- `runNBlock`: a straight-line fold of `evalNInst`, the NEON analogue of
    `Vec128Model.runVBlock`. -/
def runNBlock (s : NState) : List NInst → NState
  | [] => s
  | i :: is => runNBlock (evalNInst s i) is

@[simp] theorem runNBlock_nil (s : NState) : runNBlock s [] = s := rfl

@[simp] theorem runNBlock_cons (s : NState) (i : NInst) (is : List NInst) :
    runNBlock s (i :: is) = runNBlock (evalNInst s i) is := rfl

/-! ## 4. Differential-validation lane pins (the packed-u32 ASIMD anchor)

Unit-level witnesses for the lane ops; the integration witness is the ChaCha
4-way KAT byte-identity (`bench/arm_compare/`, RFC 8439 §2.1.1, qemu-aarch64). -/

/-- `ADD.4S` lane pin: wrapping 32-bit add, `(2³²-1) + 3 = 2`. -/
example : laneAdd (BitVec.allOnes 32) (3 : BitVec 32) = 2 := by native_decide

/-- `EOR.16B` lane pin: `0xff00ff00 ^ 0x00ff00ff = 0xffffffff`. -/
example : laneEor (BitVec.ofNat 32 0xff00ff00) (BitVec.ofNat 32 0x00ff00ff)
    = BitVec.allOnes 32 := by native_decide

/-- `SHL`/`USHR`/`ORR` realize the ChaCha rotate `x <<<ʳ 16`: on
    `x = 0x12345678`, `(x<<16) | (x>>16) = 0x56781234`. -/
example :
    laneOrr (laneShl (BitVec.ofNat 32 0x12345678) 16)
            (laneUshr (BitVec.ofNat 32 0x12345678) 16)
      = BitVec.ofNat 32 0x56781234 := by native_decide

/-- `MUL.4S` lane pin: `0x10001 * 0x10001 = 0x...20001` (low 32 bits). -/
example : laneMul (BitVec.ofNat 32 0x10001) (BitVec.ofNat 32 0x10001)
    = BitVec.ofNat 32 0x20001 := by native_decide

/-! ## 5. The 8 × i16 register view + signed high-multiply (the FIPS-203 NTT path) (#4)

The packed-`u32` section models the `V` register as `4 × u32` (the ChaCha SoA
view). The ML-KEM NTT Montgomery butterfly instead treats each `V` register as
**8 × i16** lanes (`Vd.8H`), and its packed signed high-multiply realizes
`hi16(signed aᵢ · signed bᵢ)`. On A64 this exact high-half product is obtained by
the `SMULL Vt.4S, Vn.4H, Vm.4H` / `SMULL2 Vt2.4S, Vn.8H, Vm.8H` widening pair
followed by `UZP2 Vd.8H, Vt.8H, Vt2.8H` (extract the high 16 bits of each 32-bit
product); the `SQDMULH Vd.8H, Vn.8H, Vm.8H` instruction computes the same high
half up to the architectural doubling/rounding (the mlkem-native AArch64 kernel
uses `SQRDMULH` with pre-scaled twiddle constants). We model the **mathematical
signed high-half** `mulhs.8h` directly — identical to `laneMulHiS16` — so the
`tileMontMulS16` lowering (`TileS16HighMul §4b`) is a first-class bridge of the
`ninst_is_tile_lowering` shape, with the instruction-selection note above honest
about the realizing A64 sequence. -/

/-- A 128-bit A64 `V` register in the **8 × i16** view (`Tile 8 16`), the ML-KEM
    NTT lane shape. Disjoint from the `4 × u32` `Vec128` view. -/
abbrev Vec128S16 : Type := VectorTy (BitVec 16) 8

/-- The A64 `V` register file in the 8 × i16 view (the FIPS-203 NTT bank). -/
structure NState8x16 where
  /-- The `v` register file at 8 × i16 (`v0 … v31`, named by string). -/
  vregs : String → Vec128S16

namespace NState8x16

/-- Read a `v` register (8 × i16 view). -/
@[simp] def get (s : NState8x16) (r : String) : Vec128S16 := s.vregs r

/-- Write a `v` register (8 × i16 view). -/
def setV (s : NState8x16) (r : String) (v : Vec128S16) : NState8x16 :=
  { vregs := fun r' => if r' = r then v else s.vregs r' }

@[simp] theorem get_setV_same (s : NState8x16) (r : String) (v : Vec128S16) :
    (s.setV r v).get r = v := by simp [setV, get]

@[simp] theorem get_setV_other (s : NState8x16) (r r' : String) (v : Vec128S16)
    (h : r' ≠ r) : (s.setV r v).get r' = s.get r' := by simp [setV, get, h]

end NState8x16

/-- The signed high-16 lane op (the `SMULL/SMULL2/UZP2` high-half, equal to the
    `SQDMULH` high half up to the architectural doubling). -/
@[simp] def laneMulHiS16 (a b : BitVec 16) : BitVec 16 :=
  ((a.signExtend 32 * b.signExtend 32).sshiftRight 16).truncate 16

/-- The 8 × i16 signed high-multiply instruction (the ML-KEM NTT op). -/
inductive NInst8x16 where
  /-- `MULHS Vd.8H, Vn.8H, Vm.8H` — packed 8 × i16 signed high multiply (the
      `SMULL/SMULL2/UZP2` high-half; Kyber NTT Montgomery butterfly). -/
  | mulhs (d a b : String)
  deriving Repr, DecidableEq

/-- The semantics of one 8 × i16 NEON instruction: the per-lane signed high-half
    product. -/
def evalNInst8x16 (s : NState8x16) : NInst8x16 → NState8x16
  | .mulhs d a b => s.setV d (VectorTy.map₂ laneMulHiS16 (s.get a) (s.get b))

/-- Lane pin: `hi16(signed(-2) · signed(0x4000)) = -1 = 0xffff`. -/
example : laneMulHiS16 (BitVec.ofNat 16 0xfffe) (BitVec.ofNat 16 0x4000)
    = BitVec.ofNat 16 0xffff := by native_decide

/-- Lane pin: `hi16(signed(0x4000)²) = 0x1000`. -/
example : laneMulHiS16 (BitVec.ofNat 16 0x4000) (BitVec.ofNat 16 0x4000)
    = BitVec.ofNat 16 0x1000 := by native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon
