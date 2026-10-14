/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVecCore
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordScheduleCom

/-!
# The dword ZMM lane map: sixteen scalar `u32` programs in one AVX-512 register

`laneMapZmmD` is the `Com jasminDialect → Com jasminDialect` transform that runs sixteen
independent copies of a scalar 32-bit program in the sixteen dword lanes of a ZMM
register: every `reg 32` value becomes a `reg 512`, every scalar binding
`regArith bop 32` becomes the packed binding `vpackZMMd bop`, every constant
`regConst 32 k` becomes the lane broadcast `regConst 512 (bcastD (BitVec.ofNat 32 k)).toNat`,
and every `mulhi 32` becomes the two-operand leaf `extCall "zmm_mulhi32x16"`.

The transform is `LaneMapVec.laneMapVec` at the lane shape `LaneMapVec.dwordZmm`
defined here; the definitions and theorems of this file are that shape's instances of
the generic ones in `LaneMapVecCore`. Lane `k : Fin 16` of a `reg 512` value is
`zmmLane32 v k`, bits `32k .. 32k+31`, the layout `zmmPackD` uses.

## Covered scalar ops

All nine `JasminBinOp`s at width 32 (`add`, `sub`, `mul`, `and`, `or`, `xor`, `andn`,
`shl`, `shr`), `regConst 32 k` and `mulhi 32`. `vpackZMMd bop` denotes `zmmPackD bop`,
which applies `bop.apply` at width 32 in each lane, reading the shift count of `shl` /
`shr` from the same lane of the second operand; so each packed op is the scalar op lane
by lane. The leaf `zmm_mulhi32x16` has no fixed meaning in `jasminDenote`; the lane
theorem denotes the mapped program with `jasminDenoteWith leafSem` under `MulHi32Leaf
leafSem`, the hypothesis that the leaf computes `mulHiW` in every dword lane. Every
other op takes the opaque nullary `extCall` fallback `laneMapZmmD_uncovered`, outside
the `LaneMapZmmDCovered` fragment.

## Main definitions

* `LaneMapVec.dwordZmm`: sixteen 32-bit lanes on `vpackZMMd` and `zmm_mulhi32x16`.
* `widenDTy` / `widenDCtxt` / `mapVar` / `lowering`: the shape's maps and lowering.
* `laneMapZmmD`: the whole-program lane map.
* `laneOfTy` / `laneOf`: per-type and per-valuation extraction of dword lane `k`.
* `MulHi32Leaf`: the lane-wise specification of the `zmm_mulhi32x16` leaf.
* `LaneMapZmmDCovered`: the fragment on which the lane map is lane-preserving.

## Main results

* `laneOf_lookup`: reading a mapped variable and extracting lane `k` equals reading
  the original variable against the lane-`k` valuation.
* `blockOpLane`: each covered op's packed block, denoted with `jasminDenoteWith leafSem`
  and read at lane `k`, computes the scalar op on lane `k`.
* `laneMapZmmD_denote`: for a covered program returning `reg 32`, lane `k` of the
  mapped program's denotation under `jasminDenoteWith leafSem` equals the scalar
  program's `jasminDenote` denotation on lane `k`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmDwordLane (zmmPackD_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordScheduleCom (bcastD bcastD_lane)

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD

/-- The name of the sixteen-lane high-multiply leaf. -/
def mulhiLeafName : String := "zmm_mulhi32x16"

/-- Lane `k` of the broadcast constant is the scalar constant. -/
theorem constD_lane (kk : Nat) (k : Fin 16) :
    zmmLane32 (BitVec.ofNat 512 (bcastD (BitVec.ofNat 32 kk)).toNat) k
      = BitVec.ofNat 32 kk := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, bcastD_lane]

/-- The `zmm_mulhi32x16` leaf of `leafSem` computes, in every dword lane `k`, the high
    word `mulHiW` of the product of lane `k` of its two operands. -/
def MulHi32Leaf (leafSem : LeafSem) : Prop :=
  ∀ (a b : BitVec 512) (k : Fin 16),
    zmmLane32 (leafSem mulhiLeafName [.reg 512, .reg 512] (.reg 512) (.cons a (.cons b .nil))) k
      = mulHiW (zmmLane32 a k) (zmmLane32 b k)

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

/-- Sixteen 32-bit lanes in a ZMM register, on the packed ops `vpackZMMd` and the
    high-multiply leaf `zmm_mulhi32x16`. -/
def dwordZmm : LaneShape where
  laneBits := 32
  laneCount := 16
  regBits := 512
  regBits_eq := rfl
  lane := zmmLane32
  covers := fun | .shl => false | .shr => false | _ => true
  packExpr := fun bop _ a b => ⟨.vpackZMMd bop, rfl, .cons a (.cons b .nil)⟩
  bcast := fun kk => (bcastD (BitVec.ofNat 32 kk)).toNat
  mulhiExpr := some fun _ a b =>
    ⟨.extCall LaneMapZmmD.mulhiLeafName [.reg 512, .reg 512] (.reg 512), rfl,
      .cons a (.cons b .nil)⟩
  immBlock := fun _ => none
  immCovers := fun _ _ => false
  arrWiden := false
  fallbackName := "laneMapZmmD_uncovered"
  pack_lane := fun _ bop hc _ a b V k => by
    refine (zmmPackD_lane bop (a.lookup V) (b.lookup V) k).trans ?_
    cases bop <;> first | rfl | exact absurd hc (by decide)
  const_lane := LaneMapZmmD.constD_lane
  imm_lane := by intro _ _ _ hf; cases hf
  arr_index := fun h => Bool.noConfusion h
  lane_zero := fun h => Bool.noConfusion h

/-- `MulHi32Leaf` is the high-multiply law of `dwordZmm`. -/
theorem mulhiLane_dwordZmm (leafSem : LeafSem) (hleaf : LaneMapZmmD.MulHi32Leaf leafSem) :
    dwordZmm.MulhiLane leafSem := by
  intro f hf Γ a b V k
  cases Option.some.inj hf
  exact hleaf _ _ k

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD

/-! ## 1. Type, context and variable maps -/

/-- Widen `reg 32` to `reg 512`; fix every other Jasmin type. -/
abbrev widenDTy : JasminTy → JasminTy := dwordZmm.widenTy

/-- Context map: `widenDTy` pointwise. -/
abbrev widenDCtxt (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := dwordZmm.widenCtxt Γ

/-- `List.map` is definitionally `cons`-compatible. -/
theorem mapCtx_cons (t : JasminTy) (Γ : Ctxt jasminDialect) :
    widenDCtxt (t :: Γ) = widenDTy t :: widenDCtxt Γ := rfl

/-- de Bruijn index transport along `widenDTy`. -/
abbrev mapVar {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) :
    Ctxt.Var (widenDCtxt Γ) (widenDTy t) :=
  dwordZmm.mapVar v

/-! ## 2. The block lowering -/

/-- The lane-map lowering of `dwordZmm`. -/
abbrev lowering : FieldDialectBlockDescent.BlockLoweringData jasminDialect jasminDialect :=
  dwordZmm.lowering

/-- The dword lane map of a whole scalar program: sixteen `u32` lanes in one ZMM
    register. -/
def laneMapZmmD {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect (widenDCtxt Γ) (widenDTy t) :=
  laneMapVec dwordZmm c

/-! ## 3. Lane extraction -/

/-- Extract dword lane `k` of a mapped value. A mapped `reg 32` (a `reg 512`) yields
    its lane-`k` dword `zmmLane32 v k`; every other type passes through unchanged. -/
abbrev laneOfTy (k : Fin 16) (s : JasminTy) (v : ⟦widenDTy s⟧) : ⟦s⟧ :=
  dwordZmm.laneOfTy k s v

/-- Lane extraction at `reg 32` is `zmmLane32`. -/
theorem laneOfTy_reg32 (k : Fin 16) (v : ⟦widenDTy (.reg 32)⟧) :
    laneOfTy k (.reg 32) v = zmmLane32 v k := rfl

/-- Extract dword lane `k` of a whole mapped valuation, slot by slot. -/
abbrev laneOf (k : Fin 16) (Γ : Ctxt jasminDialect) (W : Ctxt.Valuation (widenDCtxt Γ)) :
    Ctxt.Valuation Γ :=
  dwordZmm.laneOf k Γ W

/-- Reading a mapped variable and extracting lane `k` equals reading the original
    variable against the lane-`k` valuation. -/
theorem laneOf_lookup {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t)
    (W : Ctxt.Valuation (widenDCtxt Γ)) (k : Fin 16) :
    laneOfTy k t ((mapVar v).lookup W) = v.lookup (laneOf k Γ W) :=
  dwordZmm.laneOf_lookup v W k

/-! ## 4. The covered fragment -/

/-- The scalar ops `laneMapZmmD` maps lane-preservingly: every `regArith bop 32`,
    every `regConst 32 k` and `mulhi 32`. -/
abbrev CoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Prop :=
  dwordZmm.CoveredExpr e

/-- A program whose every op is covered. -/
abbrev LaneMapZmmDCovered {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Prop :=
  dwordZmm.Covered c

/-! ## 5. Lane preservation -/

/-- **Per-op lane square.** For each covered op, the packed block denoted with
    `jasminDenoteWith leafSem` and read at dword lane `k` computes the scalar op on
    lane `k`, given `MulHi32Leaf leafSem`. -/
theorem blockOpLane (leafSem : LeafSem) (hleaf : MulHi32Leaf leafSem)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : CoveredExpr e) (W : Ctxt.Valuation (widenDCtxt Γ))
    (k : Fin 16) :
    laneOfTy k t (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
        (lowering.lowerExprBlock e) W) = e.denote (laneOf k Γ W) :=
  dwordZmm.blockOpLane leafSem (mulhiLane_dwordZmm leafSem hleaf) e he W k

/-- **`laneMapZmmD` is lane-preserving.** For a covered program returning `reg 32` and
    a leaf semantics satisfying `MulHi32Leaf`, dword lane `k` of the mapped program's
    denotation under `jasminDenoteWith leafSem` equals the scalar program's
    `jasminDenote` denotation on the lane-`k` valuation. -/
theorem laneMapZmmD_denote (leafSem : LeafSem) (hleaf : MulHi32Leaf leafSem)
    {Γ : Ctxt jasminDialect} (c : Com jasminDialect Γ (.reg 32))
    (hc : LaneMapZmmDCovered c) (W : Ctxt.Valuation (widenDCtxt Γ)) (k : Fin 16) :
    zmmLane32 (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapZmmD c) W) k
      = c.denote (laneOf k Γ W) :=
  laneMapVec_denote dwordZmm leafSem (mulhiLane_dwordZmm leafSem hleaf) c hc W k

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD
