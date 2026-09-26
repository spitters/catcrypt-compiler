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
(`vpsllvq` / `vpsrlvq`), so `shl` and `shr` are outside its fragment. The shape
`qwordYmmImm` extends `qwordYmm` with the immediate-count ops `shlImm`, `shrImm` and
`rorImm`, lowered to `vpsllq` / `vpsrlq` (the rotate as `vpsllq; vpsrlq; vpor`).

## Main definitions

* `qwordYmm`: four 64-bit lanes in a YMM register.
* `qwordYmmImm`: `qwordYmm` with immediate-count shifts and rotates.

## Main results

* `laneMapZmm_low_lanes_agree`: lanes `0..3` of `laneMapZmm c` depend only on lanes
  `0..3` of the inputs.
* `laneMapYmm_denote`: the lane theorem at four 64-bit lanes on 256-bit registers.
* `laneMapZmm_low_lanes_eq_laneMapYmm`: on a program covered by `qwordYmm`, lanes
  `0..3` of `laneMapZmm c` are the lanes of `laneMapVec qwordYmm c` when the inputs
  agree on those lanes.
* `laneMapYmmImm_denote`: the lane theorem at `qwordYmmImm`.
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

/-! ## 3. Four 64-bit lanes with immediate-count shifts and rotates -/

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect (vpsllqW vpsrlqW)

/-- The 256-bit packed block of an immediate-count op on four 64-bit lanes: `vpsllq`
    and `vpsrlq` by the count, and the rotate right by `n` as
    `vpsllq (64 - n); vpsrlq n; vpor`. AVX2 has no packed 64-bit arithmetic right
    shift, so `sar` has no block. -/
def ymmQImmBlock : ImmOp → Option (Nat → UnaryBuilder 256)
  | .shl => some fun n _ a => Com.var ⟨.vymm (.vpsllq n), rfl, .cons a .nil⟩ (.ret .here)
  | .shr => some fun n _ a => Com.var ⟨.vymm (.vpsrlq n), rfl, .cons a .nil⟩ (.ret .here)
  | .sar => none
  | .ror => some fun n _ a =>
      Com.var ⟨.vymm (.vpsllq (64 - n)), rfl, .cons a .nil⟩
        (Com.var ⟨.vymm (.vpsrlq n), rfl, .cons a.there .nil⟩
          (Com.var ⟨.vymm .vpor, rfl, .cons (.there .here) (.cons .here .nil)⟩ (.ret .here)))

/-- The counts at which `ymmQImmBlock` is lane-correct: every count for the shifts, and
    `0 < n < 64` for the rotate. -/
def ymmQImmCovers : ImmOp → Nat → Bool
  | .ror, n => decide (0 < n ∧ n < 64)
  | _, _ => true

/-- Qword lane `k` of `vpsllqW a n` is lane `k` of `a` shifted left by `n`. -/
theorem yQwordW_vpsllqW (a : BitVec 256) (n : Nat) (k : Fin 4) :
    yQwordW (vpsllqW a n) k.val = yQwordW a k.val <<< n := by
  rw [vpsllqW, CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]

/-- Qword lane `k` of `vpsrlqW a n` is lane `k` of `a` shifted right by `n`. -/
theorem yQwordW_vpsrlqW (a : BitVec 256) (n : Nat) (k : Fin 4) :
    yQwordW (vpsrlqW a n) k.val = yQwordW a k.val >>> n := by
  rw [vpsrlqW, CatCrypt.Crypto.Optimizer.PackedArith256.yQwordW_yOfQwordsW]

/-- Qword lane `k` of `vpsllq (64 - n); vpsrlq n; vpor` is lane `k` rotated right by
    `n`, for `n < 64`. -/
theorem yQwordW_ror_synth (a : BitVec 256) (n : Nat) (hn : n < 64) (k : Fin 4) :
    yQwordW (vporW (vpsllqW a (64 - n)) (vpsrlqW a n)) k.val
      = (yQwordW a k.val).rotateRight n := by
  rw [vporW, yQwordW, BitVec.extractLsb'_or, ← yQwordW, ← yQwordW, yQwordW_vpsllqW,
    yQwordW_vpsrlqW, rorImm_denote_eq_shiftOr n hn, BitVec.or_comm]

/-- Four 64-bit lanes in a YMM register: `qwordYmm` with the immediate-count shifts
    `shlImm`, `shrImm` and the rotate `rorImm` lowered to `vpsllq` / `vpsrlq`. -/
def qwordYmmImm : LaneShape :=
  { qwordYmm with
    immBlock := ymmQImmBlock
    immCovers := ymmQImmCovers
    fallbackName := "laneMapYmmImm_uncovered"
    imm_lane := by
      intro _ op f hf n hc _ a V k
      cases op <;> cases hf
      case shl => exact yQwordW_vpsllqW (a.lookup V) n k
      case shr => exact yQwordW_vpsrlqW (a.lookup V) n k
      case ror =>
        have hn : n < 64 := (of_decide_eq_true hc).2
        exact yQwordW_ror_synth (a.lookup V) n hn k }

/-- **The lane theorem at four 64-bit lanes with immediate-count shifts.** For a
    program covered by `qwordYmmImm` returning `reg 64`, qword lane `k` of the 256-bit
    mapped program's value is the scalar program's value on the lane-`k` valuation. -/
theorem laneMapYmmImm_denote (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (hc : qwordYmmImm.Covered c)
    (W : Ctxt.Valuation (qwordYmmImm.widenCtxt Γ)) (k : Fin 4) :
    yQwordW (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec qwordYmmImm c) W)
        k.val
      = c.denote (qwordYmmImm.laneOf k Γ W) :=
  laneMapVec_denote qwordYmmImm leafSem (fun _ hf => by simp [qwordYmmImm, qwordYmm] at hf)
    c hc W k

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
