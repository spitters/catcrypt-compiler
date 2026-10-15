/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVecCore
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom

/-!
# The ZMM lane map: eight scalar `u64` programs in one AVX-512 register

`laneMapZmm` is the `Com jasminDialect → Com jasminDialect` transform that runs eight
independent copies of a scalar 64-bit program in the eight qword lanes of a ZMM
register: every `reg 64` value becomes a `reg 512`, every scalar binding
`regArith bop 64` becomes the packed binding `vpackZMM bop`, and every constant
`regConst 64 k` becomes the lane broadcast `regConst 512 (constZmm k).toNat`.

The transform is `LaneMapVec.laneMapVec` at the lane shape `LaneMapVec.qwordZmm`
defined here; the definitions and theorems of this file are that shape's instances of
the generic ones in `LaneMapVecCore`.

## Covered scalar ops

The seven `JasminBinOp`s `add`, `sub`, `mul`, `and`, `or`, `xor`, `andn` at width 64,
`regConst 64 k`, and the immediate-count shifts `shlImm 64 n` / `shrImm 64 n` at counts
`n < 64`. `vpackZMM bop` denotes `zmmPackQ bop`, which applies `bop.applyLane` in each
lane, so each covered packed op is the scalar op lane by lane. The register-count
shifts `shl` / `shr` are not covered: the packed shift gives `0` at counts of at least
64, where the scalar shift masks the count. An immediate-count shift lowers to the
broadcast of its count followed by the packed shift (`zmmQImmBlock`). Every other op
takes the opaque nullary `extCall` fallback `laneMapZmm_uncovered`, outside the
`LaneMapZmmCovered` fragment.

## Main definitions

* `LaneMapVec.qwordZmm`: eight 64-bit lanes on the packed ops `vpackZMM`.
* `widenZTy` / `widenZCtxt` / `mapVar` / `lowering`: the shape's maps and lowering.
* `laneMapZmm`: the whole-program lane map.
* `laneOfTy` / `laneOf`: per-type and per-valuation extraction of qword lane `k`.
* `LaneMapZmmCovered`: the fragment on which the lane map is lane-preserving.

## Main results

* `laneOf_lookup`: reading a mapped variable and extracting lane `k` equals reading
  the original variable against the lane-`k` valuation.
* `blockOpLane`: each covered op's packed block, read at lane `k`, computes the
  scalar op on lane `k`.
* `laneMapZmm_denote`: for a covered program returning `reg 64`, lane `k` of the
  mapped program's denotation equals the scalar program's denotation on lane `k`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom
  (zmmPackQ_lane zmmOfLanes_zmmLane' constZmm)

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm

/-- Lane `k` of the broadcast constant is the scalar constant. -/
theorem constZmm_lane (kk : Nat) (k : Fin 8) :
    zmmLane (BitVec.ofNat 512 (constZmm kk).toNat) k = BitVec.ofNat 64 kk := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, constZmm, zmmOfLanes_zmmLane']

/-- Lane `k` of the packed shift `vpackZMM bop` (`bop = shl` or `shr`) of `a` by the
    broadcast count `n < 64` is lane `k` of `a` shifted by `n`, masked as the scalar
    immediate-count shift masks it. -/
theorem zmmPackQ_shift_bcast_lane (a : BitVec 512) (n : Nat) (hn : n < 64) (k : Fin 8) :
    zmmLane (zmmPackQ .shl a (BitVec.ofNat 512 (constZmm n).toNat)) k
        = zmmLane a k <<< shiftMask 64 n ∧
      zmmLane (zmmPackQ .shr a (BitVec.ofNat 512 (constZmm n).toNat)) k
        = zmmLane a k >>> shiftMask 64 n := by
  have ht : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [zmmPackQ_lane, zmmPackQ_lane, constZmm_lane, shiftMask_of_lt hn]
  exact ⟨by rw [JasminBinOp.applyLane, ht], by rw [JasminBinOp.applyLane, ht]⟩

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

/-- The 512-bit packed block of an immediate-count shift on eight 64-bit lanes: the
    count broadcast to every lane (`regConst 512`), then the packed shift
    `vpackZMM shl` / `vpackZMM shr` by that register. The rotate and the arithmetic
    right shift have no block. -/
def zmmQImmBlock : ImmOp → Option (Nat → UnaryBuilder 512)
  | .shl => some fun n _ a =>
      Com.var ⟨.regConst 512 (constZmm n).toNat, rfl, .nil⟩
        (Com.var ⟨.vpackZMM .shl, rfl, .cons a.there (.cons .here .nil)⟩ (.ret .here))
  | .shr => some fun n _ a =>
      Com.var ⟨.regConst 512 (constZmm n).toNat, rfl, .nil⟩
        (Com.var ⟨.vpackZMM .shr, rfl, .cons a.there (.cons .here .nil)⟩ (.ret .here))
  | .sar => none
  | .ror => none

/-- The counts at which `zmmQImmBlock` is lane-correct: counts below the lane width
    64 (the packed shift gives `0` at larger counts, the masked scalar shift does
    not). -/
def zmmQImmCovers : ImmOp → Nat → Bool
  | .shl, n => decide (n < 64)
  | .shr, n => decide (n < 64)
  | _, _ => false

/-- Eight 64-bit lanes in a ZMM register, on the packed ops `vpackZMM`. -/
def qwordZmm : LaneShape where
  laneBits := 64
  laneCount := 8
  regBits := 512
  regBits_eq := rfl
  lane := zmmLane
  covers := fun | .shl => false | .shr => false | _ => true
  packExpr := fun bop _ a b => ⟨.vpackZMM bop, rfl, .cons a (.cons b .nil)⟩
  bcast := fun kk => (constZmm kk).toNat
  mulhiExpr := none
  immBlock := zmmQImmBlock
  immCovers := zmmQImmCovers
  arrWiden := false
  fallbackName := "laneMapZmm_uncovered"
  pack_lane := fun _ bop hc _ a b V k => by
    refine (zmmPackQ_lane bop (a.lookup V) (b.lookup V) k).trans ?_
    cases bop <;> first | rfl | exact absurd hc (by decide)
  const_lane := LaneMapZmm.constZmm_lane
  imm_lane := by
    intro _ op f hf n hc _ a V k
    cases op <;> cases hf
    case shl =>
      exact (LaneMapZmm.zmmPackQ_shift_bcast_lane (a.lookup V) n (of_decide_eq_true hc) k).1
    case shr =>
      exact (LaneMapZmm.zmmPackQ_shift_bcast_lane (a.lookup V) n (of_decide_eq_true hc) k).2
  arr_index := fun h => Bool.noConfusion h
  lane_zero := fun h => Bool.noConfusion h

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm

/-! ## 1. Type, context and variable maps -/

/-- Widen `reg 64` to `reg 512`; fix every other Jasmin type. -/
abbrev widenZTy : JasminTy → JasminTy := qwordZmm.widenTy

/-- Context map: `widenZTy` pointwise. -/
abbrev widenZCtxt (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := qwordZmm.widenCtxt Γ

/-- `List.map` is definitionally `cons`-compatible. -/
theorem mapCtx_cons (t : JasminTy) (Γ : Ctxt jasminDialect) :
    widenZCtxt (t :: Γ) = widenZTy t :: widenZCtxt Γ := rfl

/-- de Bruijn index transport along `widenZTy`. -/
abbrev mapVar {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) :
    Ctxt.Var (widenZCtxt Γ) (widenZTy t) :=
  qwordZmm.mapVar v

/-! ## 2. The block lowering -/

/-- The lane-map lowering of `qwordZmm`. -/
abbrev lowering : FieldDialectBlockDescent.BlockLoweringData jasminDialect jasminDialect :=
  qwordZmm.lowering

/-- The lane map of a whole scalar program: eight `u64` lanes in one ZMM register. -/
def laneMapZmm {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect (widenZCtxt Γ) (widenZTy t) :=
  laneMapVec qwordZmm c

/-! ## 3. Lane extraction -/

/-- Extract qword lane `k` of a mapped value. A mapped `reg 64` (a `reg 512`) yields
    its lane-`k` qword `zmmLane v k`; every other type passes through unchanged. -/
abbrev laneOfTy (k : Fin 8) (s : JasminTy) (v : ⟦widenZTy s⟧) : ⟦s⟧ :=
  qwordZmm.laneOfTy k s v

/-- Lane extraction at `reg 64` is `zmmLane`. -/
theorem laneOfTy_reg64 (k : Fin 8) (v : ⟦widenZTy (.reg 64)⟧) :
    laneOfTy k (.reg 64) v = zmmLane v k := rfl

/-- Extract qword lane `k` of a whole mapped valuation, slot by slot. -/
abbrev laneOf (k : Fin 8) (Γ : Ctxt jasminDialect) (W : Ctxt.Valuation (widenZCtxt Γ)) :
    Ctxt.Valuation Γ :=
  qwordZmm.laneOf k Γ W

/-- Reading a mapped variable and extracting lane `k` equals reading the original
    variable against the lane-`k` valuation. -/
theorem laneOf_lookup {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t)
    (W : Ctxt.Valuation (widenZCtxt Γ)) (k : Fin 8) :
    laneOfTy k t ((mapVar v).lookup W) = v.lookup (laneOf k Γ W) :=
  qwordZmm.laneOf_lookup v W k

/-! ## 4. The covered fragment -/

/-- The scalar ops `laneMapZmm` maps lane-preservingly: every `regArith bop 64` other
    than `shl` / `shr`, every `regConst 64 k`, and `shlImm 64 n` / `shrImm 64 n` for
    `n < 64`. -/
abbrev CoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Prop :=
  qwordZmm.CoveredExpr e

/-- A program whose every op is covered. -/
abbrev LaneMapZmmCovered {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Prop :=
  qwordZmm.Covered c

/-! ## 5. Lane preservation -/

/-- **Per-op lane square.** For each covered op, the packed block read at qword lane
    `k` computes the scalar op on lane `k`. -/
theorem blockOpLane {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (he : CoveredExpr e) (W : Ctxt.Valuation (widenZCtxt Γ)) (k : Fin 8) :
    laneOfTy k t ((lowering.lowerExprBlock e).denote W) = e.denote (laneOf k Γ W) :=
  qwordZmm.blockOpLane_default rfl e he W k

/-- **`laneMapZmm` is lane-preserving.** For a covered program returning `reg 64`,
    qword lane `k` of the mapped program's denotation equals the scalar program's
    denotation on the lane-`k` valuation. -/
theorem laneMapZmm_denote {Γ : Ctxt jasminDialect} (c : Com jasminDialect Γ (.reg 64))
    (hc : LaneMapZmmCovered c) (W : Ctxt.Valuation (widenZCtxt Γ)) (k : Fin 8) :
    zmmLane ((laneMapZmm c).denote W) k = c.denote (laneOf k Γ W) :=
  laneMapVec_denote_default qwordZmm rfl c hc W k

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmm
