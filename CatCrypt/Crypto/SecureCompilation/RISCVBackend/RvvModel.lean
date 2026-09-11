/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types

/-!
# A Lean RISC-V RVV (vector extension) machine model — fixed VLEN=128, SEW=32, 4 × u32 lanes (#549 RVV residual)

`ARMBackend/NeonModel.lean` is the 128-bit AArch64 NEON V-register machine layer
(the fixed-128-bit ASIMD analogue of `ArmModel`'s scalar GP file), and the ChaCha
4-way kernel rides it end-to-end. This module is its **RISC-V RVV** analogue: a
named vector-register file (`VState`) over the RVV registers (`v0 … v31`), and the
per-instruction semantics (`evalVInst` / `runVBlock`) of the packed RVV ops the
ChaCha 4-way quarter-round emits.

## RVV is length-agnostic — we pin a fixed VLEN to match the ChaCha 4-way shape

Unlike NEON's architecturally-fixed 128-bit `V` registers, RVV is
*vector-length-agnostic*: the active element count `vl` is held in the `vl` CSR
and set by `vsetvli`, and `VLEN` is an implementation parameter. To match the
ChaCha 4-way SoA shape (and the NEON 128-bit/4×u32 sibling) we model a **fixed
`VLEN = 128`, `SEW = 32` (e32), `LMUL = 1` (m1)**, giving **4 × u32 lanes** — and
treat the `vsetvli` that pins `VL = 4` (`e32, m1`) as the model prelude that
selects this lane shape (`VConfig` below). Every packed op below then operates on
exactly the 4 active u32 lanes. (A length-agnostic model would carry
`vl`/`vtype` as state and prove the per-lane ops mask above `vl`; that is the
honest residual — we fix the configuration the ChaCha 4-way kernel uses, the same
posture as the fixed-128-bit NEON model.)

## The honest anchor (same posture as the NEON / x86 Vec128 model)

There is no ported authoritative model for the packed-u32 RVV ALU semantics here;
the faithfulness of `evalVInst` rests on **differential validation against the RFC
8439 KAT** of the emitted ChaCha 4-way kernel (run under qemu-riscv64 with RVV
enabled in `bench/riscv_compare/`). The semantics is written to be *obviously the
per-lane integer op the mnemonic computes* (a `VectorTy.map₂` / `map₁imm` over
`BitVec 32` lanes), auditable against the RVV spec by eye. The **lowering**
(`RvvLowering.rvvBlock_lowering_denote`, no new custom axioms) is verified down to
this model; the model's lane semantics is differential-validated, exactly the
trust shape documented in `NeonModel.lean` / `Vec128Model.lean`.

## The packed-u32 RVV ops we model (the OPIVV/OPIVI subset ChaCha 4-way emits)

| mnemonic        | shape           | lane op (4 × u32)                  |
|-----------------|-----------------|------------------------------------|
| `vadd.vv`       | `v,v→v`         | `aᵢ + bᵢ`   (wrapping 32-bit)      |
| `vxor.vv`       | `v,v→v`         | `aᵢ ^^^ bᵢ` (bitwise xor)          |
| `vor.vv`        | `v,v→v`         | `aᵢ ||| bᵢ` (bitwise or)           |
| `vand.vv`       | `v,v→v`         | `aᵢ &&& bᵢ` (bitwise and)          |
| `vsll.vi v,#n`  | `v,imm→v`       | `aᵢ <<< n`  (logical shl)          |
| `vsrl.vi v,#n`  | `v,imm→v`       | `aᵢ >>> n`  (logical shr)          |
| `vmv.v.v`       | `v→v`           | `aᵢ`        (vector move)          |

RVV pre-`Zvbb` has **no packed vector rotate**, so the ChaCha rotate `x <<<ʳ n` is
realized as `vsll.vi t, x, #n ; vsrl.vi x, x, #(32-n) ; vor.vv x, t, x` (the
portable shift+or idiom, register-for-register the same shape as the NEON
`SHL;USHR;ORR` and x86 `VPSLLD;VPSRLD;VPOR`). We model the three primitives
directly.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The fixed vector configuration (the `vsetvli` model prelude)

The ChaCha 4-way kernel runs at `SEW = 32` (e32), `LMUL = 1` (m1), with `VL = 4`
active elements (the 4 parallel blocks). `VConfig` records that fixed selection;
the lane width and count below are derived from it. -/

/-- The fixed RVV configuration the ChaCha 4-way kernel pins via `vsetvli`:
    `SEW = 32` (element width in bits), `LMUL = 1`, `VL = 4` active u32 lanes at
    `VLEN = 128`. The model fixes this configuration (the length-agnostic residual
    is documented in the module header). -/
structure VConfig where
  /-- Selected element width in bits (`SEW`); `32` for the ChaCha 4-way path. -/
  sew : Nat := 32
  /-- The active element count `VL`; `4` for the 4-way path (`VLEN/SEW`). -/
  vl : Nat := 4

/-- The fixed `e32, m1, VL=4` configuration the 4-way kernel selects. -/
def vchacha4 : VConfig := { sew := 32, vl := 4 }

/-! ## 2. The vector-register lane type and register state

A 128-bit RVV `v` register at `e32, m1`, modelled as **4 × u32 lanes**
(`VectorTy (BitVec 32) 4`) — the same ChaCha 4-way SoA shape as the NEON / x86
models: register holding word-position `j` carries that word across the 4 parallel
blocks. -/

/-- An RVV `v` register at the fixed `e32, m1, VLEN=128` configuration, as 4 × u32
    lanes (the ChaCha 4-way packed view). -/
abbrev Vec128 : Type := VectorTy (BitVec 32) 4

/-- The RVV `v` register file: a name → `Vec128` function. An absent name reads as
    the all-zero register. The RVV analogue of `NeonModel.NState`. -/
structure VState where
  /-- The `v` register file (`v0 … v31`, named by string). -/
  vregs : String → Vec128

namespace VState

/-- Read a `v` register. An absent name reads as the zero register. -/
@[simp] def get (s : VState) (r : String) : Vec128 := s.vregs r

/-- Write a `v` register, leaving the others unchanged. -/
def setV (s : VState) (r : String) (v : Vec128) : VState :=
  { vregs := fun r' => if r' = r then v else s.vregs r' }

@[simp] theorem get_setV_same (s : VState) (r : String) (v : Vec128) :
    (s.setV r v).get r = v := by simp [setV, get]

@[simp] theorem get_setV_other (s : VState) (r r' : String) (v : Vec128)
    (h : r' ≠ r) : (s.setV r v).get r' = s.get r' := by simp [setV, get, h]

end VState

/-! ## 3. Per-lane packed-u32 RVV ALU semantics

Each op is the obvious per-lane integer op over `BitVec 32` lanes — auditable
against the RVV spec by eye. -/

/-- `vadd.vv` lane op: wrapping 32-bit add. -/
@[simp] def laneAdd (a b : BitVec 32) : BitVec 32 := a + b

/-- `vand.vv` lane op: bitwise and. -/
@[simp] def laneAnd (a b : BitVec 32) : BitVec 32 := a &&& b

/-- `vor.vv` lane op: bitwise or. -/
@[simp] def laneOr (a b : BitVec 32) : BitVec 32 := a ||| b

/-- `vxor.vv` lane op: bitwise xor. -/
@[simp] def laneXor (a b : BitVec 32) : BitVec 32 := a ^^^ b

/-- `vsll.vi v, #n` lane op: logical left shift by an immediate count. -/
@[simp] def laneSll (a : BitVec 32) (m : Nat) : BitVec 32 := a <<< m

/-- `vsrl.vi v, #n` lane op: logical right shift by an immediate count. -/
@[simp] def laneSrl (a : BitVec 32) (m : Nat) : BitVec 32 := a >>> m

/-! ## 4. The RVV instruction set

The packed-u32 OPIVV/OPIVI subset the ChaCha 4-way kernel emits. Each arm names
its destination + source `v` registers (or an immediate count, for the shifts).
The machine-level analogue of `NeonModel.NInst`, at 4 × u32 lane shape. -/

/-- A single packed-u32 RVV instruction over named `v` registers. -/
inductive VInst where
  /-- `vadd.vv vd, vs2, vs1` — packed 4×u32 add. -/
  | vadd (d a b : String)
  /-- `vand.vv vd, vs2, vs1` — packed bitwise and. -/
  | vand (d a b : String)
  /-- `vor.vv vd, vs2, vs1` — packed bitwise or. -/
  | vor (d a b : String)
  /-- `vxor.vv vd, vs2, vs1` — packed bitwise xor. -/
  | vxor (d a b : String)
  /-- `vsll.vi vd, vs2, #imm` — packed logical shift-left by immediate. -/
  | vsll (d a : String) (imm : Nat)
  /-- `vsrl.vi vd, vs2, #imm` — packed logical shift-right by immediate. -/
  | vsrl (d a : String) (imm : Nat)
  /-- `vmv.v.v vd, vs1` — vector register move. -/
  | vmv (d s : String)
  deriving Repr, DecidableEq

/-- The semantics of one RVV instruction: read source register(s), apply the
    per-lane op, write the destination. The analogue of `NeonModel.evalNInst`. The
    `vadd.vv` source order is `(vs2, vs1)` per the RVV spec; both are read, so the
    add/and/or/xor lane functions are symmetric in our naming `(a, b)`. -/
def evalVInst (s : VState) : VInst → VState
  | .vadd d a b => s.setV d (VectorTy.map₂ laneAdd (s.get a) (s.get b))
  | .vand d a b => s.setV d (VectorTy.map₂ laneAnd (s.get a) (s.get b))
  | .vor  d a b => s.setV d (VectorTy.map₂ laneOr  (s.get a) (s.get b))
  | .vxor d a b => s.setV d (VectorTy.map₂ laneXor (s.get a) (s.get b))
  | .vsll d a m => s.setV d (VectorTy.map₁imm laneSll m (s.get a))
  | .vsrl d a m => s.setV d (VectorTy.map₁imm laneSrl m (s.get a))
  | .vmv  d s'  => s.setV d (s.get s')

/-- `runVBlock`: a straight-line fold of `evalVInst`, the RVV analogue of
    `NeonModel.runNBlock`. -/
def runVBlock (s : VState) : List VInst → VState
  | [] => s
  | i :: is => runVBlock (evalVInst s i) is

@[simp] theorem runVBlock_nil (s : VState) : runVBlock s [] = s := rfl

@[simp] theorem runVBlock_cons (s : VState) (i : VInst) (is : List VInst) :
    runVBlock s (i :: is) = runVBlock (evalVInst s i) is := rfl

/-! ## 5. Differential-validation lane pins (the packed-u32 RVV anchor)

Unit-level witnesses for the lane ops; the integration witness is the ChaCha
4-way KAT byte-identity (`bench/riscv_compare/`, RFC 8439 §2.1.1, qemu-riscv64
with RVV). -/

-- `vadd.vv` lane pin: wrapping 32-bit add, `(2³²-1) + 3 = 2`.
#guard laneAdd (BitVec.allOnes 32) (3 : BitVec 32) == 2
-- `vxor.vv` lane pin: `0xff00ff00 ^ 0x00ff00ff = 0xffffffff`.
#guard laneXor (BitVec.ofNat 32 0xff00ff00) (BitVec.ofNat 32 0x00ff00ff)
    == BitVec.allOnes 32
-- `vsll`/`vsrl`/`vor` realize the ChaCha rotate `x <<<ʳ 16`: on
-- `x = 0x12345678`, `(x<<16) | (x>>16) = 0x56781234`.
#guard laneOr (laneSll (BitVec.ofNat 32 0x12345678) 16)
           (laneSrl (BitVec.ofNat 32 0x12345678) 16)
      == BitVec.ofNat 32 0x56781234

/-- The fixed 4-way config has 4 active u32 lanes. -/
example : vchacha4.vl = 4 ∧ vchacha4.sew = 32 := ⟨rfl, rfl⟩

/-! ## 6. The `SEW=16, VL=8` view + `vmulh.vv` (the FIPS-203 ML-KEM NTT path) (#4)

The packed-`u32` section fixes the `e32, m1, VL=4` ChaCha configuration. The
ML-KEM NTT Montgomery butterfly instead runs at **`SEW = 16, LMUL = 1, VL = 8`**
(`VLEN = 128`), giving **8 × i16** lanes, and its packed signed high-multiply is
`vmulh.vv vd, vs2, vs1` (OPMVV, `funct6 = MULH`) — the signed high half of each
`i16 × i16` product. This section adds the `SEW=16, VL=8` configuration, an
8 × i16 register view (`VState8x16 = Tile 8 16`), and `vmulh.vv`, so the
`tileMontMulS16` lowering (`TileS16HighMul §4c`) is a first-class bridge of the
`rvinst_is_tile_lowering` shape. The `vsetvli` that pins `e16, m1, VL=8` is the
model prelude selecting this lane shape (`vmlkem` below). -/

/-- The `e16, m1, VL=8` configuration the ML-KEM NTT path pins via `vsetvli`. -/
def vmlkem : VConfig := { sew := 16, vl := 8 }

/-- An RVV `v` register at the `e16, m1, VLEN=128` configuration, as **8 × i16**
    lanes (`Tile 8 16`), the ML-KEM NTT lane shape. -/
abbrev Vec128S16 : Type := VectorTy (BitVec 16) 8

/-- The RVV `v` register file in the 8 × i16 view (the FIPS-203 NTT bank). -/
structure VState8x16 where
  /-- The `v` register file at 8 × i16 (`v0 … v31`, named by string). -/
  vregs : String → Vec128S16

namespace VState8x16

/-- Read a `v` register (8 × i16 view). -/
@[simp] def get (s : VState8x16) (r : String) : Vec128S16 := s.vregs r

/-- Write a `v` register (8 × i16 view). -/
def setV (s : VState8x16) (r : String) (v : Vec128S16) : VState8x16 :=
  { vregs := fun r' => if r' = r then v else s.vregs r' }

@[simp] theorem get_setV_same (s : VState8x16) (r : String) (v : Vec128S16) :
    (s.setV r v).get r = v := by simp [setV, get]

@[simp] theorem get_setV_other (s : VState8x16) (r r' : String) (v : Vec128S16)
    (h : r' ≠ r) : (s.setV r v).get r' = s.get r' := by simp [setV, get, h]

end VState8x16

/-- `vmulh.vv` lane op at `SEW = 16`: the signed high 16 bits of an `i16 × i16`
    product (`hi16(signExtend a · signExtend b)`). -/
@[simp] def laneMulHiS16 (a b : BitVec 16) : BitVec 16 :=
  ((a.signExtend 32 * b.signExtend 32).sshiftRight 16).truncate 16

/-- The 8 × i16 signed high-multiply instruction (the ML-KEM NTT op). -/
inductive VInst8x16 where
  /-- `vmulh.vv vd, vs2, vs1` — packed signed high half multiply at `SEW = 16`,
      `VL = 8` (Kyber NTT Montgomery butterfly). -/
  | vmulh (d a b : String)
  deriving Repr, DecidableEq

/-- The semantics of one 8 × i16 RVV instruction: the per-lane signed high-half
    product. -/
def evalVInst8x16 (s : VState8x16) : VInst8x16 → VState8x16
  | .vmulh d a b => s.setV d (VectorTy.map₂ laneMulHiS16 (s.get a) (s.get b))

/-- The `e16, m1` config has 8 active i16 lanes. -/
example : vmlkem.vl = 8 ∧ vmlkem.sew = 16 := ⟨rfl, rfl⟩

-- Lane pin: `hi16(signed(-2) · signed(0x4000)) = -1 = 0xffff`.
#guard laneMulHiS16 (BitVec.ofNat 16 0xfffe) (BitVec.ofNat 16 0x4000)
    == BitVec.ofNat 16 0xffff
-- Lane pin: `hi16(signed(0x4000)²) = 0x1000`.
#guard laneMulHiS16 (BitVec.ofNat 16 0x4000) (BitVec.ofNat 16 0x4000)
    == BitVec.ofNat 16 0x1000

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv
