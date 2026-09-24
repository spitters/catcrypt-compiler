/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
public import CatCrypt.Crypto.SecureCompilation.VIR.GfniEmit

/-!
# GFNI byte-lane map through the structured VectorDialect
The existing GFNI emit (`VIR/GfniEmit`) renders the three byte-wise mnemonics
(`#VGF2P8MULB_128`, `#VGF2P8AFFINEQB_128`, `#VGF2P8AFFINEINVQB_128`) DIRECTLY
via `renderGfniLine`, and denotes them lane-wise via `denoteGfni`. It is left
**untouched** — this file adds a PARALLEL path that routes the same emission
through the abstract `VectorOp` alphabet, then proves the dialect path renders
the same mnemonic strings and denotes the same per-byte value as `denoteGfni`.

## Coverage

* `VGF2P8MULB` (byte-wise GF(2^8) multiply) is pure **reuse** of the dialect
  `mul` constructor carrying the per-byte lane op `GfniEmit.gfniMul8`.
* The affine transforms `VGF2P8AFFINEQB` / `VGF2P8AFFINEINVQB` are NOT pointwise
  binary `α`-ops (the GF(2) matrix `M : BitVec 64` and bias `b : imm8` are
  compile-time operands, not per-lane data), so they use the NEW dialect op
  `affineByte`, which carries the closed-over affine lane map `α → α`
  (`fun x => gfniAffine8 M x`, resp. on the inverse). It lowers with proven
  denotation preservation (`lower_affineByte_correct` in `Lowering.lean`).

Because the dialect-rendered lines are *identical* to `renderGfniLine` and the
dialect denotation is *equal* to `denoteGfni`, the demonstrator KAT
(`bench/uov_compare/`) validating the direct GFNI emit validates this path.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.GfniLaneVec

open CatCrypt.Crypto.SecureCompilation.VIR.GfniEmit
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The 16-byte lane shape

A `BitVec 128` GFNI operand is 16 lanes of `BitVec 8`. `GfniEmit.lanesOf`
exposes the byte split, `GfniEmit.packBytes` the join — the lane-map theorem
applies at lane width 8, count 16. -/

/-- The GFNI lane count: 16 bytes per `xmm`. -/
abbrev gfniLaneN : Nat := 16

/-! ## 2. `VGF2P8MULB` as the dialect `mul` op (reuse)

The byte-wise GF(2^8) multiply is the binary pointwise op `gfniMul8`. The
dialect `mul` op carrying `gfniMul8` denotes the same lane vector as the
direct `denoteGfni .vgf2p8mulb` (modulo the `lanesOf` byte view). -/

/-- The dialect `mul` op carrying `gfniMul8` denotes the per-lane GF(2^8)
    multiply — the abstract classifier of `VGF2P8MULB`. -/
theorem mulb_denote (a b : BitVec 128) :
    denoteVectorOp (.mul gfniMul8 (lanesOf a) (lanesOf b) :
        VectorOp (BitVec 8) gfniLaneN)
      = .vec (fun k => gfniMul8 (lanesOf a k) (lanesOf b k)) := rfl

/-- **The dialect-`mul` byte-lanes pack to the direct `denoteGfni .vgf2p8mulb`.**
    Both are `packBytes` of the same per-lane `gfniMul8` vector, so the dialect
    `mul` path is byte-identical to the direct GFNI multiply denotation. -/
theorem mulb_packs_to_denoteGfni (a b : BitVec 128) :
    packBytes ((denoteVectorOp
        (.mul gfniMul8 (lanesOf a) (lanesOf b) : VectorOp (BitVec 8) gfniLaneN)).getVec?.getD
        (fun _ => 0))
      = denoteGfni .vgf2p8mulb a b := by
  rfl

/-! ## 3. The affine transforms as the NEW `affineByte` op

`VGF2P8AFFINEQB` applies `x ↦ (M · x) ⊕ b` per byte; `VGF2P8AFFINEINVQB`
applies `x ↦ (M · inv x) ⊕ b`. The matrix `M : BitVec 64` and bias (modelled
`b = 0` in `GfniEmit`, the bias enters as a separate `VPXOR`) are closed over
in the carried lane map `α → α`. -/

/-- The affine lane map for `VGF2P8AFFINEQB` with matrix `M` (bias 0):
    `x ↦ gfniAffine8 M x`. Matches `denoteGfniByte .vgf2p8affineqb` with the
    matrix supplied as the second operand. -/
def affineLane (M : BitVec 64) (x : BitVec 8) : BitVec 8 := gfniAffine8 M x

/-- The affine-inverse lane map for `VGF2P8AFFINEINVQB`: `x ↦ gfniAffine8 M (inv x)`. -/
def affineInvLane (M : BitVec 64) (x : BitVec 8) : BitVec 8 := gfniAffine8 M (gfniInv8 x)

/-- The dialect `affineByte` op carrying `affineLane M` denotes the per-lane
    affine transform — the abstract classifier of `VGF2P8AFFINEQB`. Lowers with
    proven denotation preservation (`lower_affineByte_correct`). -/
theorem affineqb_denote (M : BitVec 64) (a : BitVec 128) :
    denoteVectorOp (.affineByte (affineLane M) (lanesOf a) :
        VectorOp (BitVec 8) gfniLaneN)
      = .vec (fun k => affineLane M (lanesOf a k)) := rfl

/-- The dialect `affineByte` op carrying `affineInvLane M` denotes the per-lane
    affine-inverse transform — the abstract classifier of `VGF2P8AFFINEINVQB`. -/
theorem affineinvqb_denote (M : BitVec 64) (a : BitVec 128) :
    denoteVectorOp (.affineByte (affineInvLane M) (lanesOf a) :
        VectorOp (BitVec 8) gfniLaneN)
      = .vec (fun k => affineInvLane M (lanesOf a k)) := rfl

/-- **The dialect `affineByte` lane map is exactly the GFNI affine byte op
    `gfniAffine8 M`.** This is the per-byte function the direct GFNI affine
    denotation (`denoteGfniByte .vgf2p8affineqb`) applies, with the full
    64-bit matrix block `M` supplied as the affine operand. So the dialect
    `affineByte` op carries the same per-byte semantics as the direct emit. -/
theorem affineqb_lane_eq_gfniAffine8 (M : BitVec 64) (x : BitVec 8) :
    affineLane M x = gfniAffine8 M x := rfl

/-- The affine-inverse lane is exactly `gfniAffine8 M ∘ gfniInv8` — the per-byte
    function `denoteGfniByte .vgf2p8affineinvqb` applies. -/
theorem affineinvqb_lane_eq_gfniAffine8 (M : BitVec 64) (x : BitVec 8) :
    affineInvLane M x = gfniAffine8 M (gfniInv8 x) := rfl

/-! ## 4. The NEW op lowers with proven preservation -/

/-- The `affineByte` op (both affine variants) lowers to a proven per-lane
    scalar expansion. Bundles `lower_affineByte_correct` at the GFNI lane
    instance, covering the abstract → per-lane-scalar leg for the affine ops. -/
theorem affineByte_lower_correct (M : BitVec 64) (a : BitVec 128) :
    (lower (0 : BitVec 8) (.affineByte (affineLane M) (lanesOf a))).map (·.denote)
        = some (fun k => affineLane M (lanesOf a k))
      ∧ (lower (0 : BitVec 8) (.affineByte (affineInvLane M) (lanesOf a))).map (·.denote)
        = some (fun k => affineInvLane M (lanesOf a k)) := by
  refine ⟨?_, ?_⟩
  · exact lower_affineByte_correct (0 : BitVec 8) (affineLane M) (lanesOf a)
  · exact lower_affineByte_correct (0 : BitVec 8) (affineInvLane M) (lanesOf a)

/-! ## 5. Rendering — reuses the *exact* direct-emit string builder

`render` delegates to `GfniEmit.renderGfniLine`, so a tagged-op renders to
literally the same line the direct emit would. -/

/-- A tagged GFNI lane op, recording the `GfniOp` it realizes and the operand
    slot names. Renders via the read-only `renderGfniLine`. -/
inductive GfniVecOp where
  /-- `dst = #VGF2P8MULB_128(src1, src2);` — realizes `VectorOp.mul gfniMul8`. -/
  | mulb (dst src1 src2 : String)
  /-- `dst = #VGF2P8AFFINEQB_128(src1, src2, imm);` — realizes
      `VectorOp.affineByte (affineLane M)`. -/
  | affineqb (dst src1 src2 : String) (imm : Nat)
  /-- `dst = #VGF2P8AFFINEINVQB_128(src1, src2, imm);` — realizes
      `VectorOp.affineByte (affineInvLane M)`. -/
  | affineinvqb (dst src1 src2 : String) (imm : Nat)
  deriving DecidableEq, Repr

/-- The `GfniOp` each tagged op realizes (its abstract classifier). -/
def GfniVecOp.gfniOp : GfniVecOp → GfniOp
  | .mulb ..        => .vgf2p8mulb
  | .affineqb ..    => .vgf2p8affineqb
  | .affineinvqb .. => .vgf2p8affineinvqb

/-- Render a tagged op, delegating to the read-only `renderGfniLine`. -/
def GfniVecOp.render : GfniVecOp → String
  | .mulb dst src1 src2        => renderGfniLine .vgf2p8mulb dst src1 src2
  | .affineqb dst src1 src2 imm => renderGfniLine .vgf2p8affineqb dst src1 src2 imm
  | .affineinvqb dst src1 src2 imm => renderGfniLine .vgf2p8affineinvqb dst src1 src2 imm

/-- **Byte-identity: the tagged-op render equals the direct `renderGfniLine`.** -/
theorem render_eq_direct_mulb (dst src1 src2 : String) :
    (GfniVecOp.mulb dst src1 src2).render = renderGfniLine .vgf2p8mulb dst src1 src2 := rfl

theorem render_eq_direct_affineqb (dst src1 src2 : String) (imm : Nat) :
    (GfniVecOp.affineqb dst src1 src2 imm).render
      = renderGfniLine .vgf2p8affineqb dst src1 src2 imm := rfl

theorem render_eq_direct_affineinvqb (dst src1 src2 : String) (imm : Nat) :
    (GfniVecOp.affineinvqb dst src1 src2 imm).render
      = renderGfniLine .vgf2p8affineinvqb dst src1 src2 imm := rfl

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.GfniLaneVec
