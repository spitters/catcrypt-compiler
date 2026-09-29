/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVecCore
public import CatCrypt.Crypto.Optimizer.PackedArith256

/-!
# The lane map at sixteen 16-bit lanes in a YMM register

`wordYmm` is the lane shape of `LaneMapVecCore.laneMapVec` with sixteen 16-bit lanes in
one 256-bit register, on the AVX2 word ops of `YmmOpCore`. It covers the scalar
`regArith` ops `add`, `sub`, `mul`, `and`, `or`, `xor` and `andn` at width 16, lowered to
`vpaddw`, `vpsubw`, `vpmullw` (the low 16 bits of the product), `vpand`, `vpor`,
`vpxor` and `vpandn`; the immediate-count ops `shlImm`, `shrImm` and `sarImm` at counts
below `256` (the `imm8` range), lowered to `vpsllw`, `vpsrlw` and `vpsraw`, and `rorImm`
at counts `0 < n < 16`, lowered to `vpsllw (16 - n); vpsrlw n; vpor`; the broadcast of a
16-bit constant; and loads from `u16` stack arrays, which widen to arrays of packed
slots (structure-of-arrays layout, as in `dwordYmm`). AVX2 has no per-lane
variable 16-bit shift, so the register-count `shl` and `shr` are not covered, and the
shape has no high multiply.

The first consumer is the FrodoKEM matrix tile over `Z/2^16`: the rolled 640×8 tile
whose loop denotation `CatCrypt.Crypto.Frodo.FrodoMatmulSpec` relates to the schoolbook
matrix product, and the straight-line `u16` multiply-add tile of
`VIR.FrodoMatmulEmit`. The 16-bit arithmetic of ML-KEM and Falcon is in the same
fragment.

## Main definitions

* `ymmWPackExpr`: the packed expression of each scalar op on sixteen 16-bit lanes.
* `ymmWImmBlock`, `ymmWImmCovers`: the packed immediate-count blocks and their counts.
* `bcast256W`: the broadcast of a 16-bit constant into sixteen lanes.
* `wordYmm`: sixteen 16-bit lanes in a YMM register.

## Main results

* `yWordW_vpandW`, `yWordW_vporW`, `yWordW_vpxorW`, `yWordW_vpandnW`: word lane `k` of
  a bitwise op is the op on lane `k` of the operands.
* `yWordW_bcast256W`: every word lane of the broadcast is the constant.
* `yWordW_ror_synth`: word lane `k` of `vpsllw (16 - n); vpsrlw n; vpor` is lane `k`
  rotated right by `n`.
* `laneMapYmmW_denote`, `laneMapYmmW_denote_default`: the lane theorem at `wordYmm`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
  (yWordW yOfWordsW vpaddwW vpsubwW vpmullwW vpandW vporW vpxorW vpandnW vpsllwW vpsrlwW
    vpsrawW)
open CatCrypt.Crypto.Optimizer.PackedArith256
  (yWordW_yOfWordsW vpaddwW_lane vpsubwW_lane vpmullwW_lane vpsllwW_lane vpsrlwW_lane
    vpsrawW_lane)

/-! ## 1. Word-lane laws of the bitwise ops and the broadcast -/

/-- Word lane `k` of `vpandW a b` (`VPAND`) is the conjunction of lane `k` of `a` and
    `b`. -/
theorem yWordW_vpandW (a b : BitVec 256) (k : Fin 16) :
    yWordW (vpandW a b) k.val = yWordW a k.val &&& yWordW b k.val :=
  BitVec.extractLsb'_and

/-- Word lane `k` of `vporW a b` (`VPOR`) is the disjunction of lane `k` of `a` and
    `b`. -/
theorem yWordW_vporW (a b : BitVec 256) (k : Fin 16) :
    yWordW (vporW a b) k.val = yWordW a k.val ||| yWordW b k.val :=
  BitVec.extractLsb'_or

/-- Word lane `k` of `vpxorW a b` (`VPXOR`) is the exclusive or of lane `k` of `a` and
    `b`. -/
theorem yWordW_vpxorW (a b : BitVec 256) (k : Fin 16) :
    yWordW (vpxorW a b) k.val = yWordW a k.val ^^^ yWordW b k.val :=
  BitVec.extractLsb'_xor

/-- Word lane `k` of `vpandnW a b` (`VPANDN`) is the complement of lane `k` of `a`
    conjoined with lane `k` of `b`. -/
theorem yWordW_vpandnW (a b : BitVec 256) (k : Fin 16) :
    yWordW (vpandnW a b) k.val = (~~~yWordW a k.val) &&& yWordW b k.val := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [vpandnW, yWordW, BitVec.getElem_extractLsb', BitVec.getElem_and,
    BitVec.getElem_not, BitVec.getLsbD_and, BitVec.getLsbD_not]
  have h : 16 * k.val + i < 256 := by omega
  simp [h]

/-- The 256-bit register whose sixteen word lanes are the 16-bit constant `kk`. -/
def bcast256W (kk : Nat) : BitVec 256 := yOfWordsW (fun _ => BitVec.ofNat 16 kk)

/-- Word lane `k` of the broadcast of `kk` is `kk` at width 16. -/
theorem yWordW_bcast256W (kk : Nat) (k : Fin 16) :
    yWordW (bcast256W kk) k.val = BitVec.ofNat 16 kk :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpsllw (16 - n); vpsrlw n; vpor` is lane `k` rotated right by
    `n`, for `n < 16`. -/
theorem yWordW_ror_synth (a : BitVec 256) (n : Nat) (hn : n < 16) (k : Fin 16) :
    yWordW (vporW (vpsllwW a (16 - n)) (vpsrlwW a n)) k.val
      = (yWordW a k.val).rotateRight n := by
  rw [yWordW_vporW, vpsllwW_lane, vpsrlwW_lane, rorImm_denote_eq_shiftOr n hn,
    BitVec.or_comm]

/-! ## 2. The lane shape `wordYmm` -/

/-- The 256-bit packed expression of a scalar op on sixteen 16-bit lanes. `shl` and
    `shr` are not covered by `wordYmm` (AVX2 has no per-lane variable word shift), and
    their entry `vpaddw` is never emitted. -/
def ymmWPackExpr : JasminBinOp → PackBuilder 256
  | .add => fun _ a b => ⟨.vymm .vpaddw, rfl, .cons a (.cons b .nil)⟩
  | .sub => fun _ a b => ⟨.vymm .vpsubw, rfl, .cons a (.cons b .nil)⟩
  | .mul => fun _ a b => ⟨.vymm .vpmullw, rfl, .cons a (.cons b .nil)⟩
  | .and => fun _ a b => ⟨.vymm .vpand, rfl, .cons a (.cons b .nil)⟩
  | .or => fun _ a b => ⟨.vymm .vpor, rfl, .cons a (.cons b .nil)⟩
  | .xor => fun _ a b => ⟨.vymm .vpxor, rfl, .cons a (.cons b .nil)⟩
  | .andn => fun _ a b => ⟨.vymm .vpandn, rfl, .cons a (.cons b .nil)⟩
  | .shl => fun _ a b => ⟨.vymm .vpaddw, rfl, .cons a (.cons b .nil)⟩
  | .shr => fun _ a b => ⟨.vymm .vpaddw, rfl, .cons a (.cons b .nil)⟩

/-- The scalar ops `wordYmm` covers: all but the register-count `shl` and `shr`. -/
def ymmWCovers : JasminBinOp → Bool
  | .shl => false
  | .shr => false
  | _ => true

/-- The 256-bit packed block of an immediate-count op on sixteen 16-bit lanes:
    `vpsllw`, `vpsrlw` and `vpsraw` by the count, and the rotate right by `n` as
    `vpsllw (16 - n); vpsrlw n; vpor`. -/
def ymmWImmBlock : ImmOp → Option (Nat → UnaryBuilder 256)
  | .shl => some fun n _ a => Com.var ⟨.vymm (.vpsllw n), rfl, .cons a .nil⟩ (.ret .here)
  | .shr => some fun n _ a => Com.var ⟨.vymm (.vpsrlw n), rfl, .cons a .nil⟩ (.ret .here)
  | .sar => some fun n _ a => Com.var ⟨.vymm (.vpsraw n), rfl, .cons a .nil⟩ (.ret .here)
  | .ror => some fun n _ a =>
      Com.var ⟨.vymm (.vpsllw (16 - n)), rfl, .cons a .nil⟩
        (Com.var ⟨.vymm (.vpsrlw n), rfl, .cons a.there .nil⟩
          (Com.var ⟨.vymm .vpor, rfl, .cons (.there .here) (.cons .here .nil)⟩ (.ret .here)))

/-- The counts at which `ymmWImmBlock` is lowered: the `imm8` range `n < 256` for the
    shifts, whose encoding keeps the count's low eight bits, and `0 < n < 16` for the
    rotate. -/
def ymmWImmCovers : ImmOp → Nat → Bool
  | .ror, n => decide (0 < n ∧ n < 16)
  | _, n => decide (n < 256)

/-- Sixteen 16-bit lanes in a YMM register, on the `vymm` word ops, with `u16` stack
    arrays widened to arrays of packed slots. -/
def wordYmm : LaneShape where
  laneBits := 16
  laneCount := 16
  regBits := 256
  regBits_eq := rfl
  lane := fun v k => yWordW v k.val
  covers := ymmWCovers
  packExpr := ymmWPackExpr
  bcast := fun kk => (bcast256W kk).toNat
  mulhiExpr := none
  immBlock := ymmWImmBlock
  immCovers := ymmWImmCovers
  arrWiden := true
  fallbackName := "laneMapYmmW_uncovered"
  pack_lane := by
    intro _ bop hc _ a b V k
    cases bop
    case add => exact vpaddwW_lane (a.lookup V) (b.lookup V) k
    case sub => exact vpsubwW_lane (a.lookup V) (b.lookup V) k
    case mul => exact vpmullwW_lane (a.lookup V) (b.lookup V) k
    case and => exact yWordW_vpandW (a.lookup V) (b.lookup V) k
    case or => exact yWordW_vporW (a.lookup V) (b.lookup V) k
    case xor => exact yWordW_vpxorW (a.lookup V) (b.lookup V) k
    case andn => exact yWordW_vpandnW (a.lookup V) (b.lookup V) k
    case shl => exact absurd hc (by decide)
    case shr => exact absurd hc (by decide)
  const_lane := by
    intro kk k
    show yWordW (BitVec.ofNat 256 (bcast256W kk).toNat) k.val = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, yWordW_bcast256W]
  imm_lane := by
    intro _ op f hf n hc _ a V k
    cases op <;> cases hf
    case shl => exact vpsllwW_lane (a.lookup V) n k
    case shr => exact vpsrlwW_lane (a.lookup V) n k
    case sar => exact vpsrawW_lane (a.lookup V) n k
    case ror =>
      have hn : n < 16 := (of_decide_eq_true hc).2
      exact yWordW_ror_synth (a.lookup V) n hn k
  arr_index := fun _ => by decide
  lane_zero := fun _ _ => by simp

/-! ## 3. The lane theorem -/

/-- **The lane theorem at sixteen 16-bit lanes.** For a program covered by `wordYmm`
    returning `reg 16`, word lane `k` of the 256-bit mapped program's value is the
    scalar program's value on the lane-`k` valuation. -/
theorem laneMapYmmW_denote (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 16)) (hc : wordYmm.Covered c)
    (W : Ctxt.Valuation (wordYmm.widenCtxt Γ)) (k : Fin 16) :
    yWordW (@Com.denote _ _ _ (jasminDenoteWith leafSem) _ _ (laneMapVec wordYmm c) W) k.val
      = c.denote (wordYmm.laneOf k Γ W) :=
  laneMapVec_denote wordYmm leafSem (fun _ hf => by simp [wordYmm] at hf) c hc W k

/-- `laneMapYmmW_denote` under the default denotation `jasminDenote`. -/
theorem laneMapYmmW_denote_default {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 16)) (hc : wordYmm.Covered c)
    (W : Ctxt.Valuation (wordYmm.widenCtxt Γ)) (k : Fin 16) :
    yWordW ((laneMapVec wordYmm c).denote W) k.val = c.denote (wordYmm.laneOf k Γ W) :=
  laneMapVec_denote_default wordYmm rfl c hc W k

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
