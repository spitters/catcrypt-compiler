/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapLoop
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect

/-!
# The lane map at four 16-bit lanes in a general-purpose register

`wordGpr` is the lane shape with four 16-bit lanes in one 64-bit general-purpose
register (SWAR), lane `k` being bits `16k … 16k+15`. The scalar register file has no
packed instruction, so the shape covers directly only the carry-free bitwise ops `and`,
`or`, `xor` and `andn` at width 16, the broadcast of a 16-bit constant, and loads from
`u16` stack arrays, which widen to arrays of 64-bit words (element `i` of the widened
array holds element `i` of every lane's array; for a row-major `u16` matrix whose rows
are a multiple of four long, lane `L` of word `i` is column `4·(i mod r) + L`, with `r`
the words per row).

The extension `wordGprExt` (a `LaneExt wordGpr`) adds the arithmetic as blocks that keep
the lanes separate:

* `add`: `((a &&& L) + (b &&& L)) ^^^ ((a ^^^ b) &&& H)`, with `H` the top bit of each
  lane and `L` its complement, so no carry crosses a lane boundary;
* `sub`: `((a ||| H) - (b &&& L)) ^^^ ((~~~(a ^^^ b)) &&& H)`, the borrow-free
  counterpart;
* `mul` (the low 16 bits of each lane product): the four lane products
  `(a >>> 16j) * (b >>> 16j)`, each masked to 16 bits and shifted back to lane `j`, four
  64-bit multiplications. Fewer do not suffice for two packed operands: in
  `(a &&& M) * (b &&& M)`, with `M` selecting lanes `0` and `2`, the cross terms
  `a₀b₂ + a₂b₀` land in lane `2`;
* the broadcast of a 64-bit scalar into every lane, `(s &&& 0xffff) * 0x0001000100010001`,
  the image of a `castW 64 16`.

The shape has no immediate-count shifts.

## Main definitions

* `gprLane`: lane `k` of a 64-bit word.
* `wordGpr`: four 16-bit lanes in a 64-bit register.
* `gprAddW`, `gprSubW`, `gprMulW`, `gprBcastW`: the SWAR words the blocks compute.
* `wordGprExt`: the block and broadcast extension.

## Main results

* `gprAddW_lane`, `gprSubW_lane`, `gprMulW_lane`, `gprBcastW_lane`: the per-lane laws.
* `gprAddBlock_denote`, `gprSubBlock_denote`, `gprMulBlock_denote`,
  `gprBcastBlock_denote`: each block denotes its SWAR word.
* `laneMapGprW_denote`: the loop lane theorem at `wordGpr`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (ComL)

/-! ## 1. Lanes of a 64-bit word -/

/-- Lane `k` of a 64-bit word: bits `16k … 16k+15`. -/
def gprLane (v : BitVec 64) (k : Nat) : BitVec 16 := v.extractLsb' (16 * k) 16

/-- The four lanes of a 64-bit word, as a case split. -/
theorem fin4_cases (P : Nat → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ k : Fin 4, P k.val
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

/-- The word whose four lanes are the 16-bit value `x`. -/
def gprRep (x : BitVec 16) : BitVec 64 := x ++ x ++ x ++ x

theorem gprLane_gprRep (x : BitVec 16) (k : Fin 4) : gprLane (gprRep x) k.val = x := by
  refine fin4_cases (fun k => gprLane (gprRep x) k = x) ?_ ?_ ?_ ?_ k <;>
    simp only [gprLane, gprRep] <;> bv_decide

theorem gprLane_and (a b : BitVec 64) (k : Fin 4) :
    gprLane (a &&& b) k.val = gprLane a k.val &&& gprLane b k.val :=
  BitVec.extractLsb'_and

theorem gprLane_or (a b : BitVec 64) (k : Fin 4) :
    gprLane (a ||| b) k.val = gprLane a k.val ||| gprLane b k.val :=
  BitVec.extractLsb'_or

theorem gprLane_xor (a b : BitVec 64) (k : Fin 4) :
    gprLane (a ^^^ b) k.val = gprLane a k.val ^^^ gprLane b k.val :=
  BitVec.extractLsb'_xor

theorem gprLane_andn (a b : BitVec 64) (k : Fin 4) :
    gprLane ((~~~a) &&& b) k.val = (~~~gprLane a k.val) &&& gprLane b k.val := by
  refine fin4_cases (fun k => gprLane ((~~~a) &&& b) k
    = (~~~gprLane a k) &&& gprLane b k) ?_ ?_ ?_ ?_ k <;>
    simp only [gprLane] <;> bv_decide

/-! ## 2. The lane shape `wordGpr` -/

/-- The packed expression of a carry-free scalar op on four 16-bit lanes: the op itself
    at width 64. The entry of an uncovered op (`and`) is never emitted. -/
def gprPackExpr : JasminBinOp → PackBuilder 64
  | .and => fun _ a b => ⟨.regArith .and 64, rfl, .cons a (.cons b .nil)⟩
  | .or => fun _ a b => ⟨.regArith .or 64, rfl, .cons a (.cons b .nil)⟩
  | .xor => fun _ a b => ⟨.regArith .xor 64, rfl, .cons a (.cons b .nil)⟩
  | .andn => fun _ a b => ⟨.regArith .andn 64, rfl, .cons a (.cons b .nil)⟩
  | _ => fun _ a b => ⟨.regArith .and 64, rfl, .cons a (.cons b .nil)⟩

/-- The scalar ops `wordGpr` covers directly: the carry-free bitwise ops. -/
def gprCovers : JasminBinOp → Bool
  | .and => true
  | .or => true
  | .xor => true
  | .andn => true
  | _ => false

/-- Four 16-bit lanes in a 64-bit general-purpose register, with `u16` stack arrays
    widened to arrays of 64-bit words. -/
def wordGpr : LaneShape where
  laneBits := 16
  laneCount := 4
  regBits := 64
  regBits_eq := rfl
  lane := fun v k => gprLane v k.val
  covers := gprCovers
  packExpr := gprPackExpr
  bcast := fun kk => (gprRep (BitVec.ofNat 16 kk)).toNat
  mulhiExpr := none
  immBlock := fun _ => none
  immCovers := fun _ _ => false
  arrWiden := true
  fallbackName := "laneMapGprW_uncovered"
  pack_lane := by
    intro _ bop hc _ a b V k
    cases bop
    case and => exact gprLane_and (a.lookup V) (b.lookup V) k
    case or => exact gprLane_or (a.lookup V) (b.lookup V) k
    case xor => exact gprLane_xor (a.lookup V) (b.lookup V) k
    case andn => exact gprLane_andn (a.lookup V) (b.lookup V) k
    all_goals exact absurd hc (by decide)
  const_lane := by
    intro kk k
    show gprLane (BitVec.ofNat 64 (gprRep (BitVec.ofNat 16 kk)).toNat) k.val = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, gprLane_gprRep]
  imm_lane := by
    intro _ _ _ hf
    cases hf
  arr_index := fun _ => by decide
  lane_zero := fun _ _ => by simp [gprLane]

/-- `wordGpr` has four 16-bit lanes, not 64-bit ones. -/
theorem wordGpr_laneBits : wordGpr.laneBits ≠ 64 := by decide

/-! ## 3. The SWAR arithmetic words and their lane laws -/

/-- The top bit of each 16-bit lane. -/
def gprHi : Nat := 0x8000800080008000

/-- The low fifteen bits of each 16-bit lane. -/
def gprLo : Nat := 0x7fff7fff7fff7fff

/-- The SWAR lane-wise sum. -/
def gprAddW (a b : BitVec 64) : BitVec 64 :=
  ((a &&& BitVec.ofNat 64 gprLo) + (b &&& BitVec.ofNat 64 gprLo))
    ^^^ ((a ^^^ b) &&& BitVec.ofNat 64 gprHi)

/-- The SWAR lane-wise difference. -/
def gprSubW (a b : BitVec 64) : BitVec 64 :=
  ((a ||| BitVec.ofNat 64 gprHi) - (b &&& BitVec.ofNat 64 gprLo))
    ^^^ ((~~~(a ^^^ b)) &&& BitVec.ofNat 64 gprHi)

/-- The SWAR lane-wise low product: the four lane products, masked and shifted back. -/
def gprMulW (a b : BitVec 64) : BitVec 64 :=
  (((a * b) &&& BitVec.ofNat 64 65535)
      ||| ((((a >>> 16) * (b >>> 16)) &&& BitVec.ofNat 64 65535) <<< 16))
    ||| ((((a >>> 32) * (b >>> 32)) &&& BitVec.ofNat 64 65535) <<< 32)
    ||| (((a >>> 48) * (b >>> 48)) <<< 48)

/-- The broadcast of the low 16 bits of a 64-bit scalar into every lane. -/
def gprBcastW (s : BitVec 64) : BitVec 64 :=
  (s &&& BitVec.ofNat 64 65535) * BitVec.ofNat 64 0x0001000100010001

theorem gprAddW_lane (a b : BitVec 64) (k : Fin 4) :
    gprLane (gprAddW a b) k.val = gprLane a k.val + gprLane b k.val := by
  refine fin4_cases (fun k => gprLane (gprAddW a b) k = gprLane a k + gprLane b k)
    ?_ ?_ ?_ ?_ k <;> simp only [gprLane, gprAddW, gprLo, gprHi] <;> bv_decide

theorem gprSubW_lane (a b : BitVec 64) (k : Fin 4) :
    gprLane (gprSubW a b) k.val = gprLane a k.val - gprLane b k.val := by
  refine fin4_cases (fun k => gprLane (gprSubW a b) k = gprLane a k - gprLane b k)
    ?_ ?_ ?_ ?_ k <;> simp only [gprLane, gprSubW, gprLo, gprHi] <;> bv_decide

theorem gprBcastW_lane (s : BitVec 64) (k : Fin 4) :
    gprLane (gprBcastW s) k.val = s.setWidth 16 := by
  refine fin4_cases (fun k => gprLane (gprBcastW s) k = s.setWidth 16)
    ?_ ?_ ?_ ?_ k <;> simp only [gprLane, gprBcastW] <;> bv_decide

/-- Lane `k` of the masked-and-shifted combination of four words is the low 16 bits of
    word `k`. -/
theorem gprLane_combine (p0 p1 p2 p3 : BitVec 64) :
    gprLane ((((p0 &&& BitVec.ofNat 64 65535)
        ||| ((p1 &&& BitVec.ofNat 64 65535) <<< 16))
        ||| ((p2 &&& BitVec.ofNat 64 65535) <<< 32)) ||| (p3 <<< 48)) 0 = p0.setWidth 16 ∧
    gprLane ((((p0 &&& BitVec.ofNat 64 65535)
        ||| ((p1 &&& BitVec.ofNat 64 65535) <<< 16))
        ||| ((p2 &&& BitVec.ofNat 64 65535) <<< 32)) ||| (p3 <<< 48)) 1 = p1.setWidth 16 ∧
    gprLane ((((p0 &&& BitVec.ofNat 64 65535)
        ||| ((p1 &&& BitVec.ofNat 64 65535) <<< 16))
        ||| ((p2 &&& BitVec.ofNat 64 65535) <<< 32)) ||| (p3 <<< 48)) 2 = p2.setWidth 16 ∧
    gprLane ((((p0 &&& BitVec.ofNat 64 65535)
        ||| ((p1 &&& BitVec.ofNat 64 65535) <<< 16))
        ||| ((p2 &&& BitVec.ofNat 64 65535) <<< 32)) ||| (p3 <<< 48)) 3 = p3.setWidth 16 := by
  simp only [gprLane]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- The low 16 bits of a word shifted right by `16k` are lane `k`. -/
theorem setWidth_shr_lane (a : BitVec 64) :
    a.setWidth 16 = gprLane a 0 ∧ (a >>> 16).setWidth 16 = gprLane a 1 ∧
      (a >>> 32).setWidth 16 = gprLane a 2 ∧ (a >>> 48).setWidth 16 = gprLane a 3 := by
  simp only [gprLane]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem gprMulW_lane (a b : BitVec 64) (k : Fin 4) :
    gprLane (gprMulW a b) k.val = gprLane a k.val * gprLane b k.val := by
  obtain ⟨c0, c1, c2, c3⟩ := gprLane_combine (a * b) ((a >>> 16) * (b >>> 16))
    ((a >>> 32) * (b >>> 32)) ((a >>> 48) * (b >>> 48))
  obtain ⟨a0, a1, a2, a3⟩ := setWidth_shr_lane a
  obtain ⟨b0, b1, b2, b3⟩ := setWidth_shr_lane b
  have hm : ∀ x y : BitVec 64, (x * y).setWidth 16 = x.setWidth 16 * y.setWidth 16 :=
    fun x y => BitVec.setWidth_mul x y (by decide)
  refine fin4_cases (fun k => gprLane (gprMulW a b) k = gprLane a k * gprLane b k)
    ?_ ?_ ?_ ?_ k
  · show gprLane (gprMulW a b) 0 = _
    rw [gprMulW, c0, hm, a0, b0]
  · show gprLane (gprMulW a b) 1 = _
    rw [gprMulW, c1, hm, a1, b1]
  · show gprLane (gprMulW a b) 2 = _
    rw [gprMulW, c2, hm, a2, b2]
  · show gprLane (gprMulW a b) 3 = _
    rw [gprMulW, c3, hm, a3, b3]

/-! ## 4. The blocks and the extension `wordGprExt` -/

/-- The block of the SWAR lane-wise sum `gprAddW`. -/
def gprAddBlock : BinBuilder 64 := fun _ a b =>
  Com.var ⟨.regConst 64 gprLo, rfl, .nil⟩
  (Com.var ⟨.regArith .and 64, rfl, .cons (.there a) (.cons .here .nil)⟩
  (Com.var ⟨.regArith .and 64, rfl, .cons (.there (.there b)) (.cons (.there .here) .nil)⟩
  (Com.var ⟨.regArith .add 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (Com.var ⟨.regArith .xor 64, rfl, .cons (.there (.there (.there (.there a))))
    (.cons (.there (.there (.there (.there b)))) .nil)⟩
  (Com.var ⟨.regConst 64 gprHi, rfl, .nil⟩
  (Com.var ⟨.regArith .and 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (Com.var ⟨.regArith .xor 64, rfl, .cons (.there (.there (.there .here))) (.cons .here .nil)⟩
  (.ret .here))))))))

/-- The block of the SWAR lane-wise difference `gprSubW`. -/
def gprSubBlock : BinBuilder 64 := fun _ a b =>
  Com.var ⟨.regConst 64 gprHi, rfl, .nil⟩
  (Com.var ⟨.regArith .or 64, rfl, .cons (.there a) (.cons .here .nil)⟩
  (Com.var ⟨.regConst 64 gprLo, rfl, .nil⟩
  (Com.var ⟨.regArith .and 64, rfl, .cons (.there (.there (.there b))) (.cons .here .nil)⟩
  (Com.var ⟨.regArith .sub 64, rfl, .cons (.there (.there .here)) (.cons .here .nil)⟩
  (Com.var ⟨.regArith .xor 64, rfl, .cons (.there (.there (.there (.there (.there a)))))
    (.cons (.there (.there (.there (.there (.there b))))) .nil)⟩
  (Com.var ⟨.regArith .andn 64, rfl,
    .cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)⟩
  (Com.var ⟨.regArith .xor 64, rfl, .cons (.there (.there .here)) (.cons .here .nil)⟩
  (.ret .here))))))))

/-- The block of the SWAR lane-wise low product `gprMulW`. -/
def gprMulBlock : BinBuilder 64 := fun _ a b =>
  Com.var ⟨.regArith .mul 64, rfl, .cons a (.cons b .nil)⟩
  (Com.var ⟨.shrImm 64 16, rfl, .cons (.there a) .nil⟩
  (Com.var ⟨.shrImm 64 16, rfl, .cons (.there (.there b)) .nil⟩
  (Com.var ⟨.regArith .mul 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (Com.var ⟨.shrImm 64 32, rfl, .cons (.there (.there (.there (.there a)))) .nil⟩
  (Com.var ⟨.shrImm 64 32, rfl, .cons (.there (.there (.there (.there (.there b))))) .nil⟩
  (Com.var ⟨.regArith .mul 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (Com.var ⟨.shrImm 64 48, rfl,
    .cons (.there (.there (.there (.there (.there (.there (.there a))))))) .nil⟩
  (Com.var ⟨.shrImm 64 48, rfl,
    .cons (.there (.there (.there (.there (.there (.there (.there (.there b)))))))) .nil⟩
  (Com.var ⟨.regArith .mul 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (Com.var ⟨.regConst 64 65535, rfl, .nil⟩
  (Com.var ⟨.regArith .and 64, rfl, .cons
    (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.cons .here .nil)⟩
  (Com.var ⟨.regArith .and 64, rfl, .cons
    (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.cons (.there .here) .nil)⟩
  (Com.var ⟨.shlImm 64 16, rfl, .cons .here .nil⟩
  (Com.var ⟨.regArith .and 64, rfl, .cons
    (.there (.there (.there (.there (.there (.there (.there .here)))))))
    (.cons (.there (.there (.there .here))) .nil)⟩
  (Com.var ⟨.shlImm 64 32, rfl, .cons .here .nil⟩
  (Com.var ⟨.shlImm 64 48, rfl,
    .cons (.there (.there (.there (.there (.there (.there .here)))))) .nil⟩
  (Com.var ⟨.regArith .or 64, rfl, .cons (.there (.there (.there (.there (.there .here)))))
    (.cons (.there (.there (.there .here))) .nil)⟩
  (Com.var ⟨.regArith .or 64, rfl, .cons .here (.cons (.there (.there .here)) .nil)⟩
  (Com.var ⟨.regArith .or 64, rfl, .cons .here (.cons (.there (.there .here)) .nil)⟩
  (.ret .here))))))))))))))))))))

/-- The block of the broadcast `gprBcastW` of a 64-bit scalar. -/
def gprBcastBlock : CastBuilder 64 64 := fun _ s =>
  Com.var ⟨.regConst 64 65535, rfl, .nil⟩
  (Com.var ⟨.regArith .and 64, rfl, .cons (.there s) (.cons .here .nil)⟩
  (Com.var ⟨.regConst 64 0x0001000100010001, rfl, .nil⟩
  (Com.var ⟨.regArith .mul 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (.ret .here))))

theorem gprAddBlock_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
    (V : Ctxt.Valuation Γ) : (gprAddBlock Γ a b).denote V = gprAddW (a.lookup V) (b.lookup V) :=
  rfl

theorem gprSubBlock_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
    (V : Ctxt.Valuation Γ) : (gprSubBlock Γ a b).denote V = gprSubW (a.lookup V) (b.lookup V) :=
  rfl

theorem gprMulBlock_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
    (V : Ctxt.Valuation Γ) : (gprMulBlock Γ a b).denote V = gprMulW (a.lookup V) (b.lookup V) :=
  rfl

theorem gprBcastBlock_denote {Γ : Ctxt jasminDialect} (s : Ctxt.Var Γ (.reg 64))
    (V : Ctxt.Valuation Γ) : (gprBcastBlock Γ s).denote V = gprBcastW (s.lookup V) :=
  rfl

/-- The SWAR blocks of `wordGpr`: `add`, `sub` and `mul`. -/
def gprBinBlock : JasminBinOp → Option (BinBuilder 64)
  | .add => some gprAddBlock
  | .sub => some gprSubBlock
  | .mul => some gprMulBlock
  | _ => none

/-- The broadcast block of `wordGpr`: from a 64-bit scalar. -/
def gprCastBlock : (w : Nat) → Option (CastBuilder w 64)
  | 64 => some gprBcastBlock
  | _ => none

/-- The SWAR extension of `wordGpr`: lane-separating `add`, `sub` and `mul` blocks and
    the broadcast of a 64-bit scalar. -/
def wordGprExt : LaneExt wordGpr where
  binBlock := gprBinBlock
  bin_lane := by
    intro bop f hf Γ a b V k
    cases bop <;> cases hf
    case add => exact gprAddW_lane (a.lookup V) (b.lookup V) k
    case sub => exact gprSubW_lane (a.lookup V) (b.lookup V) k
    case mul => exact gprMulW_lane (a.lookup V) (b.lookup V) k
  castBlock := gprCastBlock
  cast_lane := by
    intro w f hf Γ a V k
    unfold gprCastBlock at hf
    split at hf
    · cases hf
      exact gprBcastW_lane (a.lookup V) k
    · cases hf

/-! ## 5. The lane theorem -/

/-- **The loop lane theorem at four 16-bit lanes in a 64-bit register.** For a loop
    program covered by `wordGpr` with its SWAR extension, lane `k` of the lane-mapped
    program's value is the scalar program's value on the lane-`k` valuation. -/
theorem laneMapGprW_denote {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (hc : wordGpr.CoveredL wordGprExt c) (W : Ctxt.Valuation (wordGpr.widenCtxt Γ))
    (k : Fin 4) :
    wordGpr.laneOfTy k t ((laneMapLoop wordGpr wordGprExt wordGpr_laneBits c).denote W)
      = c.denote (wordGpr.laneOf k Γ W) :=
  laneMapLoop_denote wordGpr wordGprExt wordGpr_laneBits (fun _ hf => by cases hf) c hc W k

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
