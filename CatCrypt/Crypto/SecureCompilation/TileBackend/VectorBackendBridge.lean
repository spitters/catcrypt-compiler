/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
public import CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridgeCom
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonModel
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvvModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Pi
public import Std.Tactic.BVDecide

/-!
# The vector backends are instances of the shape-generic tile lowering

The shape-polymorphic `Tile n w` lane model (`TileModel`) is meant to be the *one*
SIMD lane abstraction the per-target backends consolidate onto. This file makes
that concrete for the three 128-bit backends — x86 AVX2 (4×u32), ARM `Neon`
(`Vec128 = Tile 4 32`), and RISC-V `Rvv` (`Vec128 = Tile 4 32`) — **without
rewriting them** (so no kernel rot). Instead it *proves the consolidation*: each
backend's per-lane arithmetic instruction, transported to a `TileState 4 32`, is
exactly the shape-generic verified lowering `evalTileOp ∘ lowerRegInstr` of the
matching `regArith` op. So the existing AVX2 / NEON / RVV arithmetic IS an
instance of `TileModel.lowerRegBlock_denote`, by these bridge theorems.

For the **x86 leg** the packed ALU is re-homed onto the unified
`Com jasminDialect`: the AVX2 4×u32 packed binop is the verified dialect's
`vsimd (.packed bop 32)` op (denote `v128PackLanesW 32 bop`,
`VectorBackendBridgeCom.packAvx2Com_denote`), in the PACKED-`BitVec 128` carrier.
`v128Pack32_lane` is the packed↔lane round-trip (lane `k` of the packed result is
`bop.apply` of the input lanes), and `vpadd32_com_is_tile_lowering` ties the
unified op, transported to a `TileState 4 32` via `v128BvToTile`, to the
shape-generic `evalTileOp ∘ lowerRegInstr` of the matching `regArith` op — the
equal-strength successor of the old lane-function `vinst_is_tile_lowering`. The
x86 leg therefore no longer references `Vec128Model`.

For the ARM / RISC-V legs the key structural fact is definitional:
`VectorTy α n := Fin n → α` is reducible, so `Tile 4 32`, `Neon.Vec128`, and
`Rvv.Vec128` are **the same type**, and the backends' `VectorTy.map₂ laneOp`
writes are defeq to `evalTileOp`'s per-lane arms. The state structures differ
only by a field name (`vregs` vs `regs`), bridged by a trivial coercion. Those
two consolidations are therefore essentially `rfl` — which is the point: the
per-backend lane models were never really different.

What this does NOT touch: the immediate shifts / shuffles / moves (outside the
two-operand `regArith` binop subset) and everything above the vector layer
(control flow, scalar GP-ALU, memory) — those stay in `Com`. This is the vector
arithmetic layer collapsing onto one proof.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridge

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
  (JasminBinOp v128PackLanesW)
open CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridgeCom
  (packAvx2Com packAvx2Com_denote)

set_option autoImplicit false

/-! ## 0. The lane types coincide (definitionally) -/

/-- The ARM NEON lane type is the `4×32` tile. -/
example : ARMBackend.Neon.Vec128 = Tile 4 32 := rfl
/-- The RISC-V RVV lane type (`e32, m1, VLEN=128`) is the `4×32` tile. -/
example : RISCVBackend.Rvv.Vec128 = Tile 4 32 := rfl

/-! ## 1. x86 AVX2 (4×u32) on the unified `Com jasminDialect` → the tile lowering

The x86 leg is re-homed onto the unified dialect: the AVX2 packed 4×u32 binop is
`VectorBackendBridgeCom.packAvx2Com bop`, denoting (`packAvx2Com_denote`) to the
verified-dialect packed-lane op `v128PackLanesW 32 bop` over the PACKED-`BitVec
128` carrier. To tie that to the shape-generic `TileState 4 32` lowering we need
(a) the packed↔lane round-trip `v128Pack32_lane`, and (b) the transport
`v128BvToTile` of a packed `BitVec 128` into the lane-function tile. -/

/-- **Packed↔lane round-trip.** Lane `k` (the `[32k, 32k+32)` slice) of the
    packed 4×u32 op `v128PackLanesW 32 bop a b` is `bop.apply` of the matching
    lanes of `a` and `b` — the carrier bridge between the unified op's
    packed-`BitVec 128` result and a `Tile 4 32` lane function. Proved per lane
    (`fin_cases`) per op (`cases bop`) by `bv_decide` over the foldl-OR pack. -/
theorem v128Pack32_lane (bop : JasminBinOp) (a b : BitVec 128) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (v128PackLanesW 32 bop a b)
      = bop.apply (BitVec.extractLsb' (32 * k.val) 32 a) (BitVec.extractLsb' (32 * k.val) 32 b) := by
  fin_cases k <;> cases bop <;>
    simp only [v128PackLanesW, List.range, List.range.loop, List.foldl, JasminBinOp.apply] <;>
    bv_decide

/-- Transport a packed XMM register (`BitVec 128`) to the shape-generic
    `Tile 4 32` lane function: lane `k` is the `[32k, 32k+32)` slice. -/
def v128BvToTile (v : BitVec 128) : Tile 4 32 := fun k => BitVec.extractLsb' (32 * k.val) 32 v

/-- **x86 AVX2 arithmetic (unified-dialect form) is the shape-generic tile
    lowering.** The unified op `v128PackLanesW 32 bop a b`, transported to a
    `TileState 4 32` via `v128BvToTile`, equals `evalTileOp` of the lowered
    `regArith` op (`TileModel`'s verified lowering) at shape `4×32`, on a state
    whose `"a"`/`"b"` tiles are the transported inputs. The equal-strength
    successor of the old lane-function `vinst_is_tile_lowering`, now carried by
    the unified `Com jasminDialect` packed op rather than `Vec128Model`. -/
theorem vpadd32_com_is_tile_lowering (bop : JasminBinOp) (a b : BitVec 128) :
    v128BvToTile (v128PackLanesW 32 bop a b)
      = (evalTileOp ⟨fun nm => if nm = "b" then v128BvToTile b else v128BvToTile a⟩
           (lowerRegInstr (.bin bop "d" "a" "b"))).get "d" := by
  rw [lowerRegInstr_denote]
  funext k
  cases bop <;>
    simp only [v128BvToTile, TileState.get, TileState.set, evalRegInstr,
      String.reduceEq, if_true, if_false, JasminBinOp.apply] <;>
    rw [v128Pack32_lane] <;> simp [JasminBinOp.apply]

/-- **The unified-op form of the x86 leg.** The `Com jasminDialect` program
    `packAvx2Com bop` (its denotation `v128PackLanesW 32 bop a b` by
    `packAvx2Com_denote`), transported to a `TileState 4 32`, is the
    shape-generic tile lowering `evalTileOp ∘ lowerRegInstr`. This is the bridge
    composed through the unified op: the AVX2 packed ALU is now a `Com` in the
    verified dialect whose tile-transported meaning is the one verified
    lowering. -/
theorem packAvx2Com_is_tile_lowering (bop : JasminBinOp) (a b : BitVec 128) :
    v128BvToTile (packAvx2Com bop |>.denote (.cons a (.cons b .nil)))
      = (evalTileOp ⟨fun nm => if nm = "b" then v128BvToTile b else v128BvToTile a⟩
           (lowerRegInstr (.bin bop "d" "a" "b"))).get "d" := by
  rw [packAvx2Com_denote]; exact vpadd32_com_is_tile_lowering bop a b

/-! ## 2. ARM `Neon` → the shape-generic tile lowering -/

/-- Transport an ARM `NState` to the shape-generic `TileState 4 32`. -/
def nstateToTile (s : ARMBackend.Neon.NState) : TileState 4 32 := ⟨s.vregs⟩

/-- The `regArith` op a NEON arithmetic instruction lowers from. -/
def ninstToReg : ARMBackend.Neon.NInst → Option RegInstr
  | .add d a b => some (.bin .add d a b)
  | .sub d a b => some (.bin .sub d a b)
  | .mul d a b => some (.bin .mul d a b)
  | .and d a b => some (.bin .and d a b)
  | .orr d a b => some (.bin .or d a b)
  | .eor d a b => some (.bin .xor d a b)
  | _ => none

/-- **ARM NEON arithmetic is the shape-generic tile lowering.** Same statement as
    the x86 bridge: every NEON arithmetic instruction is `evalTileOp` of the
    lowered `regArith` op at shape `4×32`. The NEON ALU is an instance of the one
    verified lowering. -/
theorem ninst_is_tile_lowering (s : ARMBackend.Neon.NState) (i : ARMBackend.Neon.NInst)
    (r : RegInstr) (h : ninstToReg i = some r) :
    nstateToTile (ARMBackend.Neon.evalNInst s i)
      = evalTileOp (nstateToTile s) (lowerRegInstr r) := by
  cases i <;> simp only [ninstToReg, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

/-! ## 3. RISC-V `Rvv` → the shape-generic tile lowering -/

/-- Transport an RVV `VState` to the shape-generic `TileState 4 32`. -/
def rvstateToTile (s : RISCVBackend.Rvv.VState) : TileState 4 32 := ⟨s.vregs⟩

/-- The `regArith` op an RVV arithmetic instruction lowers from. (The RVV OPIVV
    subset here carries no packed multiply, so there is no `mul` arm.) -/
def rvinstToReg : RISCVBackend.Rvv.VInst → Option RegInstr
  | .vadd d a b => some (.bin .add d a b)
  | .vand d a b => some (.bin .and d a b)
  | .vor d a b  => some (.bin .or d a b)
  | .vxor d a b => some (.bin .xor d a b)
  | _ => none

/-- **RISC-V RVV arithmetic is the shape-generic tile lowering.** Same statement
    as the x86 / ARM bridges: every RVV arithmetic instruction is `evalTileOp` of
    the lowered `regArith` op at shape `4×32`. -/
theorem rvinst_is_tile_lowering (s : RISCVBackend.Rvv.VState) (i : RISCVBackend.Rvv.VInst)
    (r : RegInstr) (h : rvinstToReg i = some r) :
    rvstateToTile (RISCVBackend.Rvv.evalVInst s i)
      = evalTileOp (rvstateToTile s) (lowerRegInstr r) := by
  cases i <;> simp only [rvinstToReg, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

/-! ## 4. The consolidation, stated

Together with `TileModel.lowerRegBlock_denote` (the shape-generic keystone, proven
for every `(n, w)`), the three bridges above mean: the x86-AVX2, ARM-NEON, and
RISC-V-RVV arithmetic lane semantics, and the `Tile 8 64` ZMM / GPU tile, are
**all** the same shape-generic verified lowering — `Tile n w` at `(4,32)`,
`(8,64)`, …. The per-backend lane models are instances of one proof, not four
separate semantics. The remaining per-backend code (encoders, printers, the
non-arith ops) is the genuinely target-specific surface; the *arithmetic core*
across all four SIMD ISAs is now provably shared. -/

end CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridge
