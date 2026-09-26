/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD
public import CatCrypt.Crypto.Optimizer.PackedArith256

/-!
# The lane map at four 64-bit lanes, and the lane restriction of the ZMM map

`LaneMapVecCore` defines the lane map `laneMapVec S` at a lane shape `S`; `LaneMapZmm`
and `LaneMapZmmD` are its instances at `qwordZmm` and `dwordZmm`, and `Optimizer.Batch8`
at `dwordYmm`. This file adds the shape `qwordYmm` (four 64-bit lanes on the 256-bit
`vymm` ops) and relates it to `qwordZmm`. `qwordYmm` covers `add`, `sub`, `mul`, `and`,
`or`, `xor` and `andn`; the dialect has no 256-bit packed shift by a per-lane count
(`vpsllvq` / `vpsrlvq`), so `shl` and `shr` are outside its fragment.

## Main definitions

* `qwordYmm`: four 64-bit lanes in a YMM register.

## Main results

* `laneMapZmm_low_lanes_agree`: lanes `0..3` of `laneMapZmm c` depend only on lanes
  `0..3` of the inputs.
* `laneMapYmm_denote`: the lane theorem at four 64-bit lanes on 256-bit registers.
* `laneMapZmm_low_lanes_eq_laneMapYmm`: on a program covered by `qwordYmm`, lanes
  `0..3` of `laneMapZmm c` are the lanes of `laneMapVec qwordYmm c` when the inputs
  agree on those lanes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Lane restriction of `laneMapZmm` -/

/-- **Lane restriction of `laneMapZmm`.** Qword lanes `0..3` of a covered program's
    mapped value depend only on qword lanes `0..3` of the inputs. -/
theorem laneMapZmm_low_lanes_agree {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (hc : LaneMapZmm.LaneMapZmmCovered c)
    (W W' : Ctxt.Valuation (LaneMapZmm.widenZCtxt Γ))
    (hW : ∀ k : Fin 8, k.val < 4 → LaneMapZmm.laneOf k Γ W = LaneMapZmm.laneOf k Γ W')
    (k : Fin 8) (hk : k.val < 4) :
    zmmLane ((LaneMapZmm.laneMapZmm c).denote W) k
      = zmmLane ((LaneMapZmm.laneMapZmm c).denote W') k := by
  rw [LaneMapZmm.laneMapZmm_denote c hc, LaneMapZmm.laneMapZmm_denote c hc, hW k hk]

/-! ## 2. Four 64-bit lanes on 256-bit registers -/

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
  (yQwordW yOfQwordsW vpaddqW vpsubqW vpmullqW vpandW vporW vpxorW vpandnW)

/-- The 256-bit packed expression of a scalar op on four 64-bit lanes. `shl` and `shr`
    have no 256-bit packed form with a per-lane count; they are not covered, and their
    entry `vpaddq` is never emitted. -/
def ymmPackExpr : JasminBinOp → PackBuilder 256
  | .add => fun _ a b => ⟨.vymm .vpaddq, rfl, .cons a (.cons b .nil)⟩
  | .sub => fun _ a b => ⟨.vymm .vpsubq, rfl, .cons a (.cons b .nil)⟩
  | .mul => fun _ a b => ⟨.vymm .vpmullq, rfl, .cons a (.cons b .nil)⟩
  | .and => fun _ a b => ⟨.vymm .vpand, rfl, .cons a (.cons b .nil)⟩
  | .or => fun _ a b => ⟨.vymm .vpor, rfl, .cons a (.cons b .nil)⟩
  | .xor => fun _ a b => ⟨.vymm .vpxor, rfl, .cons a (.cons b .nil)⟩
  | .andn => fun _ a b => ⟨.vymm .vpandn, rfl, .cons a (.cons b .nil)⟩
  | .shl => fun _ a b => ⟨.vymm .vpaddq, rfl, .cons a (.cons b .nil)⟩
  | .shr => fun _ a b => ⟨.vymm .vpaddq, rfl, .cons a (.cons b .nil)⟩

/-- The scalar ops with a 256-bit packed form on four 64-bit lanes: all but `shl` and
    `shr`. -/
def ymmCovers : JasminBinOp → Bool
  | .shl => false
  | .shr => false
  | _ => true

/-- Qword lane `k` of a bitwise and-not is the and-not of the lanes. -/
theorem yQwordW_andn (a b : BitVec 256) (k : Fin 4) :
    yQwordW (vpandnW a b) k.val = (~~~yQwordW a k.val) &&& yQwordW b k.val := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [vpandnW, yQwordW, BitVec.getElem_extractLsb', BitVec.getElem_and,
    BitVec.getElem_not, BitVec.getLsbD_and, BitVec.getLsbD_not]
  have h : 64 * k.val + i < 256 := by omega
  simp [h]

/-- Four 64-bit lanes in a YMM register, on the `vymm` ops. -/
def qwordYmm : LaneShape where
  laneBits := 64
  laneCount := 4
  regBits := 256
  regBits_eq := rfl
  lane := fun v k => yQwordW v k.val
  covers := ymmCovers
  packExpr := ymmPackExpr
  bcast := fun kk => (yOfQwordsW (fun _ => BitVec.ofNat 64 kk)).toNat
  mulhiExpr := none
  immBlock := fun _ => none
  immCovers := fun _ _ => false
  arrWiden := false
  fallbackName := "laneMapYmm_uncovered"
  pack_lane := by
    intro _ bop hc _ a b V k
    cases bop
    case add =>
      show yQwordW (vpaddqW (a.lookup V) (b.lookup V)) k.val = _
      rw [vpaddqW, CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]
      rfl
    case sub =>
      show yQwordW (vpsubqW (a.lookup V) (b.lookup V)) k.val = _
      rw [vpsubqW, CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]
      rfl
    case mul =>
      show yQwordW (vpmullqW (a.lookup V) (b.lookup V)) k.val = _
      rw [vpmullqW, CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]
      rfl
    case and =>
      show yQwordW (vpandW (a.lookup V) (b.lookup V)) k.val = _
      exact BitVec.extractLsb'_and
    case or =>
      show yQwordW (vporW (a.lookup V) (b.lookup V)) k.val = _
      exact BitVec.extractLsb'_or
    case xor =>
      show yQwordW (vpxorW (a.lookup V) (b.lookup V)) k.val = _
      exact BitVec.extractLsb'_xor
    case andn =>
      show yQwordW (vpandnW (a.lookup V) (b.lookup V)) k.val = _
      exact yQwordW_andn _ _ k
    case shl => exact absurd hc (by decide)
    case shr => exact absurd hc (by decide)
  const_lane := by
    intro kk k
    show yQwordW (BitVec.ofNat 256 (yOfQwordsW _).toNat) k.val = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]
  imm_lane := by intro _ _ _ hf; cases hf
  arr_index := fun h => Bool.noConfusion h
  lane_zero := fun h => Bool.noConfusion h

/-- **The lane theorem at four 64-bit lanes.** For a program covered by `qwordYmm`
    returning `reg 64`, qword lane `k` of the 256-bit mapped program's value is the
    scalar program's value on the lane-`k` valuation. -/
theorem laneMapYmm_denote (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (hc : qwordYmm.Covered c)
    (W : Ctxt.Valuation (qwordYmm.widenCtxt Γ)) (k : Fin 4) :
    yQwordW (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec qwordYmm c) W) k.val
      = c.denote (qwordYmm.laneOf k Γ W) :=
  laneMapVec_denote qwordYmm leafSem (fun _ hf => by simp [qwordYmm] at hf) c hc W k

/-- A program covered by `qwordYmm` is covered by `LaneMapZmm`. -/
theorem laneMapZmmCovered_of_qwordYmm : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → qwordYmm.Covered c → LaneMapZmm.LaneMapZmmCovered c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, hc => by
      refine ⟨?_, laneMapZmmCovered_of_qwordYmm body hc.2⟩
      have he := hc.1
      obtain ⟨op, rfl, args⟩ := e
      cases op <;> simp_all [LaneShape.CoveredExpr, qwordYmm, qwordZmm]

/-- **The 256-bit map is the low half of the 512-bit map.** For a program covered by
    `qwordYmm` returning `reg 64`, if qword lane `k < 4` of the ZMM inputs `W` agrees
    with qword lane `k` of the YMM inputs `W'`, then qword lane `k` of `laneMapZmm c` at
    `W` is qword lane `k` of `laneMapVec qwordYmm c` at `W'`. -/
theorem laneMapZmm_low_lanes_eq_laneMapYmm {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (hc : qwordYmm.Covered c)
    (W : Ctxt.Valuation (LaneMapZmm.widenZCtxt Γ)) (W' : Ctxt.Valuation (qwordYmm.widenCtxt Γ))
    (hW : ∀ k : Fin 4,
      LaneMapZmm.laneOf (Fin.castLE (by decide) k) Γ W = qwordYmm.laneOf k Γ W')
    (k : Fin 4) :
    zmmLane ((LaneMapZmm.laneMapZmm c).denote W) (Fin.castLE (by decide) k)
      = yQwordW ((laneMapVec qwordYmm c).denote W') k.val := by
  have h := laneMapVec_denote_default qwordYmm rfl c hc W' k
  rw [LaneMapZmm.laneMapZmm_denote c (laneMapZmmCovered_of_qwordYmm c hc), hW k]
  exact h.symm

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
