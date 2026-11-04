/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NarrowWordSquares
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin

/-!
# Widening the narrow words of a structured Jasmin program

The narrow widths are `8`, `16` and `32` (`narrowB`). `wideTy` sends a register `reg w` and a
stack array `stackArr w n` of a narrow width to the same type at width `64`, and keeps every
other type (`wideW`). A value is carried along `wideTy` by zero extension (`transTy`): a
narrow word `v` is held in a 64-bit register as `v.setWidth 64`, with its high bits zero, the
invariant `nfToCat` keeps for the scalars of hax.

`widenP : PartialBlockLowering jasminDialect jasminDialect` has the type map `wideTy`, the
context map `List.map wideTy`, and gives each operation at a narrow width `w` its 64-bit
implementation (`opBlock?`), with `m = 2 ^ w - 1`:

* `regArith` `add`, `sub`, `mul`: the operation at `64`, then the conjunction with `m`
  (`withMask`); `and`, `or`, `xor`, `andn`: the operation at `64`;
* `regArith` `shl`, `shr`: the count conjoined with `31` (the count a shift of a register of
  width at most `32` applies), the shift at `64`, and for `shl` the mask (`countThen`);
* `shlImm w k`, `shrImm w k`: the shift at `64` by `shiftMask w k`, the left shift masked;
* `rorImm w k`: `shrImm 64 (k % w)`, `shlImm 64 (w - k % w)`, their disjunction, the mask;
* `sarImm w k`: `shlImm 64 (64 - w)`, `sarImm 64 (64 - w + k)`, the mask;
* `mulhi w`: the product at `64` shifted right by `w`;
* `addCarryLo w`, `addCarryHi w`: the carry-in zero-extended, the sum at `64`; the data word
  is the masked sum and the carry is bit `w` of the sum, cast to one bit;
* `castW w w'`: the cast between the widened widths, masked when it truncates to a narrow
  width; `regConst w n`, `cmpImm c w n`: the constant `n % 2 ^ w` at `64`;
* `select`, `cmp`, `stackLoad`, `stackStore`, `stackZero`, `stackStoreImm`: the operation at
  the widened width.

At a width that is not narrow every operation is kept, at `wideW w = w`. The external calls,
the multi-result calls and the vector operations, which the region back half does not export,
are refused.

`widenJ p` is `NFProg.map?` along `widenP` at the identity renaming. Its preservation theorem
`widenJ_denote` is `NFProg.map?_denote_call` with the four leaves of `widenP`: the variable and
binding leaves hold by the definition of `mapVal`, the region leaves because the trip counter
`reg 64` and the bit `reg 1` are not narrow, and the block leaf `opBlock?_denote` by the
squares of `NarrowWordSquares`.

The context of `widenJ p` is `Γ.map wideTy`, which is not `Γ` up to definitional unfolding
when `Γ` is a variable. When `wideTy` fixes every type of `Γ` and of the result types, an
equation that `decide` proves at a concrete context, the widened valuation is the valuation
and the transport of the results is the identity, up to the cast of their types
(`mapVal_heq_of_wide`, `widenJ_denote_of_wide`).

## Main definitions

* `narrowB`, `wideW`, `wideTy`, `transTy`, `mapVar`, `mapVal`.
* `withMask`, `countThen`, `opBlock?` — the blocks.
* `widenP`, `widenJ` — the lowering and the pass.

## Main results

* `opBlock?_denote` — the block of an operation denotes, on the widened valuation, the
  widened value of the operation.
* `widenJ_denote` — the pass preserves the denotation along `transTy`, at every fuel and at
  call environments that agree along `transTy` at the calls of the program.
* `widenJ_denote_empty` — the same at the empty call environment of `jasminDialect`.
* `transTy_heq_of_wide`, `mapVal_heq_of_wide`, `widenJ_denote_of_wide` — on types that
  `wideTy` fixes, the transport is the identity up to the cast, and the widened program
  denotes what the program denotes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

open Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open BlockLoweringExtend (transArgs)

/-! ## 1. The type map and the transports -/

/-- The narrow widths: `8`, `16` and `32`. -/
def narrowB (w : Nat) : Bool := w == 8 || w == 16 || w == 32

/-- The width of the register that holds a word of width `w`: `64` at a narrow width, `w`
    otherwise. -/
def wideW (w : Nat) : Nat := if narrowB w then 64 else w

/-- The narrow widths are `8`, `16` and `32`. -/
theorem narrowB_iff {w : Nat} : narrowB w = true ↔ w = 8 ∨ w = 16 ∨ w = 32 := by
  simp [narrowB, or_assoc]

/-- A narrow word is held at width `64`. -/
theorem wideW_of_narrow {w : Nat} (h : narrowB w = true) : wideW w = 64 := by
  simp [wideW, h]

/-- A word of a width that is not narrow is held at its width. -/
theorem wideW_of_not {w : Nat} (h : narrowB w = false) : wideW w = w := by
  simp [wideW, h]

/-- A narrow width is at most `32`. -/
theorem le32_of_narrow {w : Nat} (h : narrowB w = true) : w ≤ 32 := by
  rcases narrowB_iff.mp h with rfl | rfl | rfl <;> decide

/-- A narrow width is at least `8`. -/
theorem pos_of_narrow {w : Nat} (h : narrowB w = true) : 8 ≤ w := by
  rcases narrowB_iff.mp h with rfl | rfl | rfl <;> decide

/-- A narrow width is a width of at most `32` bits. -/
theorem wordLe32_of_narrow {w : Nat} (h : narrowB w = true) : WordLe32 w :=
  ⟨le32_of_narrow h⟩

/-- The width a word is held at is at least the width of the word. -/
theorem le_wideW (w : Nat) : w ≤ wideW w := by
  unfold wideW
  split
  · exact Nat.le_trans (le32_of_narrow (by assumption)) (by decide)
  · exact Nat.le_refl w

/-- The type a value is held at: a narrow register or stack array at width `64`. -/
def wideTy : JasminTy → JasminTy
  | .reg w => .reg (wideW w)
  | .stackArr w n => .stackArr (wideW w) n
  | .inlineInt => .inlineInt
  | .bool => .bool

/-- The value transport: zero extension of a word and of each word of a stack array. -/
def transTy : {t : JasminTy} → ⟦t⟧ → ⟦wideTy t⟧
  | .reg w, x => BitVec.setWidth (wideW w) (x : BitVec w)
  | .stackArr w _, a => fun i => BitVec.setWidth (wideW w) ((a : Fin _ → BitVec w) i)
  | .inlineInt, x => x
  | .bool, b => b

/-- The variable map along `wideTy`. -/
def mapVar : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Var Γ t →
    Var (d := jasminDialect) (Γ.map wideTy) (wideTy t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVar v)

/-- The valuation transport: `transTy` at every variable. -/
def mapVal {Γ : Ctxt jasminDialect} (V : Valuation Γ) :
    Valuation (d := jasminDialect) (Γ.map wideTy) :=
  transArgs wideTy transTy V

/-- A mapped variable reads the transported value. -/
theorem lookup_mapVar_mapVal : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Var Γ t)
    (V : Valuation Γ), (mapVar v).lookup (mapVal V) = transTy (v.lookup V)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVar_mapVal v xs

/-! ## 2. The blocks -/

section Blocks

variable {Δ : Ctxt jasminDialect}

/-- The conjunction of a value of width `W` with the constant `2 ^ w - 1`, when the option
    names a width `w`. -/
def maskOpt (W : Nat) : Option Nat → BitVec W → BitVec W
  | some w, x => x &&& BitVec.ofNat W (2 ^ w - 1)
  | none, x => x

/-- The expression `e`, followed by the mask of width `w` when `m = some w`. -/
def withMask (W : Nat) (m : Option Nat) (e : Expr jasminDialect Δ (.reg W)) :
    Com jasminDialect Δ (.reg W) :=
  match m with
  | some w =>
      .var e (.var ⟨.regConst W (2 ^ w - 1), rfl, .nil⟩
        (.var ⟨.regArith .and W, rfl, .cons (.there .here) (.cons .here .nil)⟩ (.ret .here)))
  | none => .var e (.ret .here)

/-- The value of `withMask`. -/
theorem withMask_denote (W : Nat) (m : Option Nat) (e : Expr jasminDialect Δ (.reg W))
    (V : Valuation Δ) : (withMask W m e).denote V = maskOpt W m (e.denote V) := by
  cases m <;> rfl

/-- The register shift `bop` of `a` by the count `b` conjoined with `31`, followed by the
    mask `m`. -/
def countThen (W : Nat) (bop : JasminBinOp) (m : Option Nat) (a b : Var Δ (.reg W)) :
    Com jasminDialect Δ (.reg W) :=
  .var ⟨.regConst W 31, rfl, .nil⟩
    (.var ⟨.regArith .and W, rfl, .cons (.there b) (.cons .here .nil)⟩
      (withMask W m ⟨.regArith bop W, rfl, .cons (.there (.there a)) (.cons .here .nil)⟩))

/-- The value of `countThen`. -/
theorem countThen_denote (W : Nat) (bop : JasminBinOp) (m : Option Nat)
    (a b : Var Δ (.reg W)) (V : Valuation Δ) (x y : BitVec W) (ha : a.lookup V = x)
    (hb : b.lookup V = y) :
    (countThen W bop m a b).denote V = maskOpt W m (bop.apply x (y &&& BitVec.ofNat W 31)) := by
  subst ha hb
  simp only [countThen, Com.denote, withMask_denote]
  rfl

/-- The one-binding block of an expression. -/
abbrev one {t : JasminTy} (e : Expr jasminDialect Δ t) : Com jasminDialect Δ t :=
  .var e (.ret .here)

/-- The block of `regArith bop w` on arguments held at width `W`. -/
def arithBlock (W w : Nat) (bop : JasminBinOp) (a b : Var Δ (.reg W)) :
    Com jasminDialect Δ (.reg W) :=
  if narrowB w then
    match bop with
    | .add | .sub | .mul => withMask W (some w) ⟨.regArith bop W, rfl, .cons a (.cons b .nil)⟩
    | .shl => countThen W .shl (some w) a b
    | .shr => countThen W .shr none a b
    | .and | .or | .xor | .andn => one ⟨.regArith bop W, rfl, .cons a (.cons b .nil)⟩
  else one ⟨.regArith bop W, rfl, .cons a (.cons b .nil)⟩

/-- The block of `castW w w'` on an argument held at width `W`, with the result held at
    width `W'`: the cast, masked when it truncates to a narrow width. -/
def castBlock (W W' w w' : Nat) (a : Var Δ (.reg W)) : Com jasminDialect Δ (.reg W') :=
  withMask W' (if narrowB w' && decide (w' < w) then some w' else none)
    ⟨.castW W W', rfl, .cons a .nil⟩

/-- The block of `mulhi w`: at a narrow width, the product shifted right by `w`. -/
def mulhiBlock (W w : Nat) (a b : Var Δ (.reg W)) : Com jasminDialect Δ (.reg W) :=
  if narrowB w then
    .var ⟨.regArith .mul W, rfl, .cons a (.cons b .nil)⟩
      (one ⟨.shrImm W w, rfl, .cons .here .nil⟩)
  else one ⟨.mulhi W, rfl, .cons a (.cons b .nil)⟩

/-- The block of `addCarryLo w`: at a narrow width, the masked sum of the arguments and the
    zero-extended carry-in. -/
def addLoBlock (W w : Nat) (a b : Var Δ (.reg W)) (c : Var Δ (.reg 1)) :
    Com jasminDialect Δ (.reg W) :=
  if narrowB w then
    .var ⟨.castW 1 W, rfl, .cons c .nil⟩
      (.var ⟨.regArith .add W, rfl, .cons (.there a) (.cons (.there b) .nil)⟩
        (withMask W (some w) ⟨.regArith .add W, rfl, .cons .here (.cons (.there .here) .nil)⟩))
  else one ⟨.addCarryLo W, rfl, .cons a (.cons b (.cons c .nil))⟩

/-- The block of `addCarryHi w`: at a narrow width, bit `w` of the sum of the arguments and
    the zero-extended carry-in. -/
def addHiBlock (W w : Nat) (a b : Var Δ (.reg W)) (c : Var Δ (.reg 1)) :
    Com jasminDialect Δ (.reg 1) :=
  if narrowB w then
    .var ⟨.castW 1 W, rfl, .cons c .nil⟩
      (.var ⟨.regArith .add W, rfl, .cons (.there a) (.cons (.there b) .nil)⟩
        (.var ⟨.regArith .add W, rfl, .cons .here (.cons (.there .here) .nil)⟩
          (.var ⟨.shrImm W w, rfl, .cons .here .nil⟩
            (one ⟨.castW W 1, rfl, .cons .here .nil⟩))))
  else one ⟨.addCarryHi W, rfl, .cons a (.cons b (.cons c .nil))⟩

/-- The block of `rorImm w k`: at a narrow width, the masked disjunction of the shifts by
    `k % w` and `w - k % w`. -/
def rorBlock (W w k : Nat) (a : Var Δ (.reg W)) : Com jasminDialect Δ (.reg W) :=
  if narrowB w then
    .var ⟨.shrImm W (k % w), rfl, .cons a .nil⟩
      (.var ⟨.shlImm W (w - k % w), rfl, .cons (.there a) .nil⟩
        (withMask W (some w) ⟨.regArith .or W, rfl, .cons (.there .here) (.cons .here .nil)⟩))
  else one ⟨.rorImm W k, rfl, .cons a .nil⟩

/-- The block of `sarImm w k`: at a narrow width, the shift of the word to the top of the
    register, the arithmetic shift by `64 - w + k`, and the mask. -/
def sarBlock (W w k : Nat) (a : Var Δ (.reg W)) : Com jasminDialect Δ (.reg W) :=
  if narrowB w then
    .var ⟨.shlImm W (64 - w), rfl, .cons a .nil⟩
      (withMask W (some w) ⟨.sarImm W (64 - w + k), rfl, .cons .here .nil⟩)
  else one ⟨.sarImm W k, rfl, .cons a .nil⟩

/-- The block of `shlImm w k`: at a narrow width, the masked shift by `shiftMask w k`. -/
def shlBlock (W w k : Nat) (a : Var Δ (.reg W)) : Com jasminDialect Δ (.reg W) :=
  if narrowB w then withMask W (some w) ⟨.shlImm W (shiftMask w k), rfl, .cons a .nil⟩
  else one ⟨.shlImm W k, rfl, .cons a .nil⟩

/-- The constant `n` at width `w`, held at the widened width. -/
def wideConst (w n : Nat) : Nat := if narrowB w then n % 2 ^ w else n

/-- The count of `shrImm w k` at the widened width. -/
def wideCount (w k : Nat) : Nat := if narrowB w then shiftMask w k else k

end Blocks

/-! ## 3. The values of the blocks -/

section Values

variable {Δ : Ctxt jasminDialect}

/-- A 64-bit register whose low `w` bits encode `v` and whose high bits are zero is the zero
    extension of `v`. -/
theorem strict_of {w : Nat} (hw : w ≤ 64) {z : BitVec 64} {v : BitVec w} (h : lowW w z = v)
    (hz : HighZero w z) : z = v.setWidth 64 :=
  (eq_setWidth_iff hw z v).mpr ⟨h, hz⟩

/-- A masked 64-bit register whose low `w` bits encode `v` is the zero extension of `v`. -/
theorem masked_of {w : Nat} (hw : w ≤ 64) {z : BitVec 64} {v : BitVec w} (h : lowW w z = v) :
    maskOpt 64 (some w) z = v.setWidth 64 := by
  change z &&& maskW w = _
  rw [and_maskW hw, h]

/-- A conjunction with a register whose high bits are zero has zero high bits. -/
theorem highZero_and {w : Nat} {x y : BitVec 64} (hy : HighZero w y) : HighZero w (x &&& y) :=
  Nat.lt_of_le_of_lt (by rw [BitVec.toNat_and]; exact Nat.and_le_right) hy

/-- A disjunction of registers whose high bits are zero has zero high bits. -/
theorem highZero_or {w : Nat} {x y : BitVec 64} (hx : HighZero w x) (hy : HighZero w y) :
    HighZero w (x ||| y) := by
  unfold HighZero at *
  rw [BitVec.toNat_or]
  exact Nat.or_lt_two_pow hx hy

/-- An exclusive disjunction of registers whose high bits are zero has zero high bits. -/
theorem highZero_xor {w : Nat} {x y : BitVec 64} (hx : HighZero w x) (hy : HighZero w y) :
    HighZero w (x ^^^ y) := by
  unfold HighZero at *
  rw [BitVec.toNat_xor]
  exact Nat.xor_lt_two_pow hx hy

/-- A logical right shift keeps the high bits zero. -/
theorem highZero_ushiftRight {w : Nat} {x : BitVec 64} (k : Nat) (hx : HighZero w x) :
    HighZero w (x >>> k) := by
  unfold HighZero at *
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx

/-- A one-bit value is held as itself. -/
theorem setWidth_one (c : BitVec 1) : BitVec.setWidth (wideW 1) c = c := BitVec.setWidth_eq c

/-- The zero extension of a one-bit carry is the constant of its value. -/
theorem setWidth_carry (c : BitVec 1) : c.setWidth 64 = BitVec.ofNat 64 c.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := c.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A count below `64` is not changed by the mask of a 64-bit shift. -/
theorem shiftMask_64_of_lt {k : Nat} (h : k < 64) : shiftMask 64 k = k := shiftMask_of_lt h

/-- The count of a shift at a width of at most `32` is below `64`. -/
theorem shiftMask_lt32 {w : Nat} (h : w ≤ 32) (k : Nat) : shiftMask w k < 64 := by
  rw [shiftMask_of_le32 h]
  exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)

/-- The block of `regArith bop w` denotes the widened value of the operation. -/
theorem arithBlock_denote (W w : Nat) (hW : W = wideW w) (bop : JasminBinOp)
    (a b : Var Δ (.reg W)) (V : Valuation Δ) (x y : BitVec w)
    (ha : a.lookup V = x.setWidth W) (hb : b.lookup V = y.setWidth W) :
    (arithBlock W w bop a b).denote V = (bop.apply x y).setWidth W := by
  unfold arithBlock
  split
  · rename_i h
    have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    have hle : w ≤ 64 := WordLe64.le
    have hx := highZero_setWidth hle x
    have hy := highZero_setWidth hle y
    have lx := lowW_setWidth hle x
    have ly := lowW_setWidth hle y
    cases bop
    · rw [withMask_denote]; apply masked_of hle
      change lowW w (JasminBinOp.apply .add (a.lookup V) (b.lookup V)) = x + y
      rw [ha, hb]
      exact (addSq.comm _ _).trans (by rw [lx, ly])
    · rw [withMask_denote]; apply masked_of hle
      change lowW w (JasminBinOp.apply .sub (a.lookup V) (b.lookup V)) = x - y
      rw [ha, hb]
      exact (subSq.comm _ _).trans (by rw [lx, ly])
    · rw [withMask_denote]; apply masked_of hle
      change lowW w (JasminBinOp.apply .mul (a.lookup V) (b.lookup V)) = x * y
      rw [ha, hb]
      exact (mulSq.comm _ _).trans (by rw [lx, ly])
    · change JasminBinOp.apply .and (a.lookup V) (b.lookup V) = _
      rw [ha, hb]
      exact BitVec.setWidth_and.symm
    · change JasminBinOp.apply .or (a.lookup V) (b.lookup V) = _
      rw [ha, hb]
      exact BitVec.setWidth_or.symm
    · change JasminBinOp.apply .xor (a.lookup V) (b.lookup V) = _
      rw [ha, hb]
      exact BitVec.setWidth_xor.symm
    · rw [countThen_denote _ _ _ _ _ _ _ _ ha hb]; apply masked_of hle
      rw [shlRegSq.comm _ _ hy, lx, ly]
    · rw [countThen_denote _ _ _ _ _ _ _ _ ha hb]
      simp only [maskOpt]
      apply strict_of hle
      · rw [shrRegSq.comm _ _ ⟨hx, hy⟩, lx, ly]
      · exact highZero_ushiftRight _ hx
    · change JasminBinOp.apply .andn (a.lookup V) (b.lookup V) = _
      rw [ha, hb]
      apply strict_of hle
      · exact ((andnSq (w := w)).comm _ _).trans (by rw [lx, ly]; rfl)
      · exact highZero_and hy
  · rename_i h
    have hw : W = w := hW.trans (wideW_of_not (by simpa using h))
    subst hw
    change bop.apply (a.lookup V) (b.lookup V) = _
    rw [ha, hb, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- At a width that is not narrow the held width is the width. -/
theorem eq_of_not_narrow {W w : Nat} (hW : W = wideW w) (h : ¬ narrowB w = true) : W = w :=
  hW.trans (wideW_of_not (by simpa using h))

/-- The block of `castW w w'` denotes the widened cast. -/
theorem castBlock_denote (W W' w w' : Nat) (hW : W = wideW w) (hW' : W' = wideW w')
    (a : Var Δ (.reg W)) (V : Valuation Δ) (x : BitVec w) (ha : a.lookup V = x.setWidth W) :
    (castBlock W W' w w' a).denote V = (x.setWidth w').setWidth W' := by
  have hwW : w ≤ W := hW ▸ le_wideW w
  have hwW' : w' ≤ W' := hW' ▸ le_wideW w'
  rw [castBlock, withMask_denote]
  have he : (Expr.denote (⟨.castW W W', rfl, .cons a .nil⟩ : Expr jasminDialect Δ (.reg W')) V)
      = (x.setWidth W).setWidth W' := by
    change BitVec.zeroExtend W' (a.lookup V) = _
    rw [ha]
  rw [he]
  by_cases hn : narrowB w' = true
  · have h64 : W' = 64 := hW'.trans (wideW_of_narrow hn)
    subst h64
    have hle : w' ≤ 64 := Nat.le_trans (le32_of_narrow hn) (by decide)
    by_cases hlt : w' < w
    · simp only [hn, hlt, decide_true, Bool.and_self, ite_true]
      apply masked_of hle
      simp only [lowW, BitVec.setWidth_setWidth_of_le _ hle,
        BitVec.setWidth_setWidth_of_le _ (Nat.le_trans (Nat.le_of_lt hlt) hwW)]
    · simp only [hn, hlt, decide_false, Bool.and_false, Bool.false_eq_true, ite_false, maskOpt]
      rw [BitVec.setWidth_setWidth (by omega), BitVec.setWidth_setWidth (by omega)]
  · have hW'e : W' = w' := eq_of_not_narrow hW' hn
    subst hW'e
    simp only [hn, Bool.false_and, Bool.false_eq_true, ite_false, maskOpt,
      BitVec.setWidth_eq]
    by_cases hlt : W' ≤ W
    · exact BitVec.setWidth_setWidth_of_le _ hlt
    · rw [BitVec.setWidth_setWidth (by omega)]

/-- The block of `mulhi w` denotes the widened high word of the product. -/
theorem mulhiBlock_denote (W w : Nat) (hW : W = wideW w) (a b : Var Δ (.reg W))
    (V : Valuation Δ) (x y : BitVec w) (ha : a.lookup V = x.setWidth W)
    (hb : b.lookup V = y.setWidth W) :
    (mulhiBlock W w a b).denote V = (mulHiW x y).setWidth W := by
  unfold mulhiBlock
  split
  · rename_i h
    have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    have h32 := le32_of_narrow h
    have hle : w ≤ 64 := WordLe64.le
    change (JasminBinOp.apply .mul (a.lookup V) (b.lookup V)) >>> shiftMask 64 w = _
    rw [ha, hb, shiftMask_64_of_lt (by omega)]
    have hx := highZero_setWidth hle x
    have hy := highZero_setWidth hle y
    apply strict_of hle
    · exact ((mulhiSq (w := w)).comm _ _ ⟨hx, hy⟩).trans
        (by rw [lowW_setWidth hle, lowW_setWidth hle])
    · unfold HighZero at *
      have h2 : (BitVec.setWidth 64 x * BitVec.setWidth 64 y).toNat < 2 ^ w * 2 ^ w := by
        rw [BitVec.toNat_mul]
        exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mul_lt_mul_of_lt_of_lt hx hy)
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)
  · rename_i h
    have hw := eq_of_not_narrow hW h
    subst hw
    change mulHiW (w := W) (a.lookup V) (b.lookup V) = _
    rw [ha, hb, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- The block of `addCarryLo w` denotes the widened data word. -/
theorem addLoBlock_denote (W w : Nat) (hW : W = wideW w) (a b : Var Δ (.reg W))
    (c : Var Δ (.reg 1)) (V : Valuation Δ) (x y : BitVec w) (z : BitVec 1)
    (ha : a.lookup V = x.setWidth W) (hb : b.lookup V = y.setWidth W) (hc : c.lookup V = z) :
    (addLoBlock W w a b c).denote V = (addCarryWord x y z).setWidth W := by
  unfold addLoBlock
  split
  · rename_i h
    have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    have hle : w ≤ 64 := WordLe64.le
    simp only [Com.denote, withMask_denote]
    apply masked_of hle
    change lowW w (JasminBinOp.apply .add (JasminBinOp.apply .add (a.lookup V) (b.lookup V))
      (BitVec.zeroExtend 64 (c.lookup V))) = _
    rw [ha, hb, hc]
    change lowW w (x.setWidth 64 + y.setWidth 64 + z.setWidth 64) = _
    rw [setWidth_carry, (addCarryLoSq (w := w) z).comm, lowW_setWidth hle, lowW_setWidth hle]
  · rename_i h
    have hw := eq_of_not_narrow hW h
    subst hw
    change addCarryWord (w := W) (a.lookup V) (b.lookup V) (c.lookup V) = _
    rw [ha, hb, hc, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- The block of `addCarryHi w` denotes the carry bit. -/
theorem addHiBlock_denote (W w : Nat) (hW : W = wideW w) (a b : Var Δ (.reg W))
    (c : Var Δ (.reg 1)) (V : Valuation Δ) (x y : BitVec w) (z : BitVec 1)
    (ha : a.lookup V = x.setWidth W) (hb : b.lookup V = y.setWidth W) (hc : c.lookup V = z) :
    (addHiBlock W w a b c).denote V = carryOutBit x y z := by
  unfold addHiBlock
  split
  · rename_i h
    have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    have h32 := le32_of_narrow h
    change BitVec.zeroExtend 1 (BitVec.ushiftRight (JasminBinOp.apply .add
      (JasminBinOp.apply .add (a.lookup V) (b.lookup V)) (BitVec.zeroExtend 64 (c.lookup V)))
      (shiftMask 64 w)) = _
    rw [ha, hb, hc, shiftMask_64_of_lt (by omega), carryOutBit_wide, ← setWidth_carry]
    rfl
  · rename_i h
    have hw := eq_of_not_narrow hW h
    subst hw
    change carryOutBit (w := W) (a.lookup V) (b.lookup V) (c.lookup V) = _
    rw [ha, hb, hc, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- The block of `rorImm w k` denotes the widened rotation. -/
theorem rorBlock_denote (W w k : Nat) (hW : W = wideW w) (a : Var Δ (.reg W))
    (V : Valuation Δ) (x : BitVec w) (ha : a.lookup V = x.setWidth W) :
    (rorBlock W w k a).denote V = (x.rotateRight k).setWidth W := by
  unfold rorBlock
  split
  · rename_i h
    have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    have h32 := le32_of_narrow h
    have h8 := pos_of_narrow h
    have hle : w ≤ 64 := WordLe64.le
    simp only [Com.denote, withMask_denote]
    apply masked_of hle
    change lowW w (JasminBinOp.apply .or (BitVec.ushiftRight (a.lookup V) (shiftMask 64 (k % w)))
      (BitVec.shiftLeft (a.lookup V) (shiftMask 64 (w - k % w)))) = _
    have hk : k % w < w := Nat.mod_lt _ (by omega)
    rw [ha, shiftMask_64_of_lt (by omega), shiftMask_64_of_lt (by omega)]
    change lowW w ((x.setWidth 64 >>> (k % w)) ||| (x.setWidth 64 <<< (w - k % w))) = _
    rw [(rorImmSq (w := w) k).comm _ (highZero_setWidth hle x), lowW_setWidth hle]
  · rename_i h
    have hw := eq_of_not_narrow hW h
    subst hw
    change BitVec.rotateRight (w := W) (a.lookup V) k = _
    rw [ha, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- The block of `sarImm w k` denotes the widened arithmetic shift. -/
theorem sarBlock_denote (W w k : Nat) (hW : W = wideW w) (a : Var Δ (.reg W))
    (V : Valuation Δ) (x : BitVec w) (ha : a.lookup V = x.setWidth W) :
    (sarBlock W w k a).denote V = (x.sshiftRight k).setWidth W := by
  unfold sarBlock
  split
  · rename_i h
    have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    have h8 := pos_of_narrow h
    have hle : w ≤ 64 := WordLe64.le
    simp only [Com.denote, withMask_denote]
    apply masked_of hle
    change lowW w (BitVec.sshiftRight (BitVec.shiftLeft (a.lookup V) (shiftMask 64 (64 - w)))
      (64 - w + k)) = _
    rw [ha, shiftMask_64_of_lt (by omega)]
    change lowW w ((x.setWidth 64 <<< (64 - w)).sshiftRight (64 - w + k)) = _
    rw [(sarImmSq (w := w) k).comm, lowW_setWidth hle]
  · rename_i h
    have hw := eq_of_not_narrow hW h
    subst hw
    change BitVec.sshiftRight (n := W) (a.lookup V) k = _
    rw [ha, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- The block of `shlImm w k` denotes the widened shift. -/
theorem shlBlock_denote (W w k : Nat) (hW : W = wideW w) (a : Var Δ (.reg W))
    (V : Valuation Δ) (x : BitVec w) (ha : a.lookup V = x.setWidth W) :
    (shlBlock W w k a).denote V = (x <<< shiftMask w k).setWidth W := by
  unfold shlBlock
  split
  · rename_i h
    have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    have hle : w ≤ 64 := WordLe64.le
    rw [withMask_denote]
    apply masked_of hle
    change lowW w (BitVec.shiftLeft (a.lookup V) (shiftMask 64 (shiftMask w k))) = _
    rw [ha, shiftMask_64_of_lt (shiftMask_lt32 (le32_of_narrow h) k)]
    change lowW w (x.setWidth 64 <<< shiftMask w k) = _
    rw [(shlImmSq (w := w) _).comm, lowW_setWidth hle]
  · rename_i h
    have hw := eq_of_not_narrow hW h
    subst hw
    change BitVec.shiftLeft (n := W) (a.lookup V) (shiftMask W k) = _
    rw [ha, BitVec.setWidth_eq, BitVec.setWidth_eq]
    rfl

/-- The logical right shift by an immediate, at the widened width and count. -/
theorem shr_wide (W w k : Nat) (hW : W = wideW w) (x : BitVec w) :
    (x.setWidth W) >>> shiftMask W (wideCount w k) = (x >>> shiftMask w k).setWidth W := by
  unfold wideCount
  by_cases h : narrowB w = true
  · have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    have hle : w ≤ 64 := WordLe64.le
    simp only [h, ite_true]
    rw [shiftMask_64_of_lt (shiftMask_lt32 (le32_of_narrow h) k)]
    apply strict_of hle
    · rw [(shrImmSq (w := w) _).comm _ (highZero_setWidth hle x), lowW_setWidth hle]
    · exact highZero_ushiftRight _ (highZero_setWidth hle x)
  · have hw := eq_of_not_narrow hW h
    subst hw
    simp only [h, Bool.false_eq_true, ite_false, BitVec.setWidth_eq]

/-- The constant at the widened width. -/
theorem const_wide (W w n : Nat) (hW : W = wideW w) :
    BitVec.ofNat W (wideConst w n) = (BitVec.ofNat w n).setWidth W := by
  unfold wideConst
  by_cases h : narrowB w = true
  · have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    simp only [h, ite_true]
    exact constSq n
  · have hw := eq_of_not_narrow hW h
    subst hw
    simp only [h, Bool.false_eq_true, ite_false, BitVec.setWidth_eq]

/-- A comparison at the widened width. -/
theorem cmpBit_wide (W w : Nat) (hW : W = wideW w) (c : JasminCmp) (x y : BitVec w) :
    cmpBit c (x.setWidth W) (y.setWidth W) = cmpBit c x y := by
  by_cases h : narrowB w = true
  · have h64 : W = 64 := hW.trans (wideW_of_narrow h)
    subst h64
    have := wordLe32_of_narrow h
    exact cmpBit_setWidth c x y
  · have hw := eq_of_not_narrow hW h
    subst hw
    rw [BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- A select at the widened width. -/
theorem selectW_wide (W w : Nat) (z : BitVec 1) (x y : BitVec w) :
    selectW z (x.setWidth W) (y.setWidth W) = (selectW z x y).setWidth W := by
  unfold selectW
  split <;> rfl

/-- A total read of a stack array whose words are all zero-extended. -/
theorem stackGet_wide (W w n : Nat) (arr : Fin n → BitVec w) (i : Nat) :
    stackGet (fun j => (arr j).setWidth W) i = (stackGet arr i).setWidth W := by
  cases n with
  | zero => simp [stackGet]
  | succ m => rfl

/-- A total write of a zero-extended word into a stack array of zero-extended words. -/
theorem stackSet_wide (W w n : Nat) (arr : Fin n → BitVec w) (i : Nat) (v : BitVec w) :
    stackSet (fun j => (arr j).setWidth W) i (v.setWidth W) =
      fun j => (stackSet arr i v j).setWidth W := by
  cases n with
  | zero => funext j; simp [stackSet]
  | succ m =>
      funext j
      simp only [stackSet]
      split <;> rfl

end Values

/-- **The block of an operation.** The 64-bit implementation of an operation at a narrow
    width, the operation itself at the widened width otherwise; `none` for an external call,
    a multi-result call and a vector operation. -/
def opBlock? {Γ : Ctxt jasminDialect} : (op : JasminOp) →
    HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op) →
    Option (Com jasminDialect (Γ.map wideTy)
      (wideTy (DialectSignature.ret (d := jasminDialect) op)))
  | .regArith bop w, args =>
      some (arithBlock (wideW w) w bop (mapVar args.head) (mapVar args.tail.head))
  | .stackLoad w n, args =>
      some (one ⟨.stackLoad (wideW w) n, rfl,
        .cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil)⟩)
  | .stackStore w n, args =>
      some (one ⟨.stackStore (wideW w) n, rfl,
        .cons (mapVar args.head)
          (.cons (mapVar args.tail.head) (.cons (mapVar args.tail.tail.head) .nil))⟩)
  | .castW w w', args => some (castBlock (wideW w) (wideW w') w w' (mapVar args.head))
  | .regConst w n, _ => some (one ⟨.regConst (wideW w) (wideConst w n), rfl, .nil⟩)
  | .mulhi w, args => some (mulhiBlock (wideW w) w (mapVar args.head) (mapVar args.tail.head))
  | .addCarryLo w, args =>
      some (addLoBlock (wideW w) w (mapVar args.head) (mapVar args.tail.head)
        (mapVar args.tail.tail.head))
  | .addCarryHi w, args =>
      some (addHiBlock (wideW w) w (mapVar args.head) (mapVar args.tail.head)
        (mapVar args.tail.tail.head))
  | .rorImm w k, args => some (rorBlock (wideW w) w k (mapVar args.head))
  | .shrImm w k, args => some (one ⟨.shrImm (wideW w) (wideCount w k), rfl,
      .cons (mapVar args.head) .nil⟩)
  | .sarImm w k, args => some (sarBlock (wideW w) w k (mapVar args.head))
  | .shlImm w k, args => some (shlBlock (wideW w) w k (mapVar args.head))
  | .select w, args =>
      some (one ⟨.select (wideW w), rfl,
        .cons (mapVar args.head)
          (.cons (mapVar args.tail.head) (.cons (mapVar args.tail.tail.head) .nil))⟩)
  | .cmp c w, args =>
      some (one ⟨.cmp c (wideW w), rfl,
        .cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil)⟩)
  | .cmpImm c w n, args =>
      some (one ⟨.cmpImm c (wideW w) (wideConst w n), rfl, .cons (mapVar args.head) .nil⟩)
  | .stackZero w n, _ => some (one ⟨.stackZero (wideW w) n, rfl, .nil⟩)
  | .stackStoreImm w n i, args =>
      some (one ⟨.stackStoreImm (wideW w) n i, rfl,
        .cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil)⟩)
  | _, _ => none

/-- The block of an expression: `opBlock?` of its operation. -/
def exprBlock? : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Expr jasminDialect Γ t →
    Option (Com jasminDialect (Γ.map wideTy) (wideTy t))
  | _, _, ⟨op, rfl, args⟩ => opBlock? op args

/-- **The widening of narrow words** as a partial block lowering of `jasminDialect` into
    itself. -/
def widenP : PartialBlockLowering jasminDialect jasminDialect where
  mapTy := wideTy
  mapCtx := List.map wideTy
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVar
  lowerExprBlock? := exprBlock?

/-! ## 4. The leaves of the lowering -/

/-- A 64-bit index is held as itself. -/
theorem transTy_reg64 (i : BitVec 64) : transTy (t := .reg 64) i = i := BitVec.setWidth_eq i

/-- A one-bit value is held as itself. -/
theorem transTy_reg1 (c : BitVec 1) : transTy (t := .reg 1) c = c := BitVec.setWidth_eq c

/-- **The block leaf.** The block of an operation denotes, on the widened valuation, the
    widened value of the operation. -/
theorem opBlock?_denote {Γ : Ctxt jasminDialect} (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op))
    (blk : Com jasminDialect (Γ.map wideTy)
      (wideTy (DialectSignature.ret (d := jasminDialect) op)))
    (h : opBlock? op args = some blk) (V : Valuation Γ) :
    blk.denote (mapVal V) =
      transTy (Expr.denote (⟨op, rfl, args⟩ : Expr jasminDialect Γ _) V) := by
  have L := fun {t : JasminTy} (v : Var Γ t) => lookup_mapVar_mapVal v V
  cases op <;> simp only [opBlock?, reduceCtorEq] at h <;> (injection h with h; subst h)
  case regArith bop w =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    exact arithBlock_denote _ _ rfl _ _ _ _ _ _ (L a) (L b)
  case stackLoad w n =>
    rcases args with _ | ⟨a, _ | ⟨i, _ | _⟩⟩
    change stackGet ((mapVar a).lookup (mapVal V)) (BitVec.toNat ((mapVar i).lookup (mapVal V))) = _
    rw [L a, L i, transTy_reg64]
    exact stackGet_wide _ _ _ _ _
  case stackStore w n =>
    rcases args with _ | ⟨a, _ | ⟨i, _ | ⟨v, _ | _⟩⟩⟩
    change stackSet ((mapVar a).lookup (mapVal V)) (BitVec.toNat ((mapVar i).lookup (mapVal V)))
      ((mapVar v).lookup (mapVal V)) = _
    rw [L a, L i, L v, transTy_reg64]
    exact stackSet_wide _ _ _ _ _ _
  case castW w w' =>
    rcases args with _ | ⟨a, _ | _⟩
    exact (castBlock_denote _ _ _ _ rfl rfl _ _ _ (L a)).trans rfl
  case regConst w n =>
    exact const_wide _ _ _ rfl
  case mulhi w =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    exact mulhiBlock_denote _ _ rfl _ _ _ _ _ (L a) (L b)
  case addCarryLo w =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
    exact addLoBlock_denote _ _ rfl _ _ _ _ _ _ _ (L a) (L b) ((L c).trans (transTy_reg1 _))
  case addCarryHi w =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
    exact (addHiBlock_denote _ _ rfl _ _ _ _ _ _ _ (L a) (L b)
      ((L c).trans (transTy_reg1 _))).trans (transTy_reg1 _).symm
  case rorImm w k =>
    rcases args with _ | ⟨a, _ | _⟩
    exact rorBlock_denote _ _ _ rfl _ _ _ (L a)
  case shrImm w k =>
    rcases args with _ | ⟨a, _ | _⟩
    change BitVec.ushiftRight ((mapVar a).lookup (mapVal V)) (shiftMask (wideW w) (wideCount w k))
      = _
    rw [L a]
    exact shr_wide _ _ _ rfl _
  case sarImm w k =>
    rcases args with _ | ⟨a, _ | _⟩
    exact sarBlock_denote _ _ _ rfl _ _ _ (L a)
  case shlImm w k =>
    rcases args with _ | ⟨a, _ | _⟩
    exact shlBlock_denote _ _ _ rfl _ _ _ (L a)
  case select w =>
    rcases args with _ | ⟨c, _ | ⟨a, _ | ⟨b, _ | _⟩⟩⟩
    change selectW ((mapVar c).lookup (mapVal V)) ((mapVar a).lookup (mapVal V))
      ((mapVar b).lookup (mapVal V)) = _
    rw [L c, L a, L b, transTy_reg1]
    exact selectW_wide _ _ _ _ _
  case cmp c w =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    change cmpBit c ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V)) = _
    rw [L a, L b, transTy_reg1]
    exact cmpBit_wide _ _ rfl _ _ _
  case cmpImm c w n =>
    rcases args with _ | ⟨a, _ | _⟩
    change cmpBit c ((mapVar a).lookup (mapVal V)) (BitVec.ofNat (wideW w) (wideConst w n)) = _
    rw [L a, transTy_reg1, const_wide _ _ _ rfl]
    exact cmpBit_wide _ _ rfl _ _ _
  case stackZero w n =>
    funext j
    exact (BitVec.setWidth_zero _ _).symm
  case stackStoreImm w n i =>
    rcases args with _ | ⟨a, _ | ⟨v, _ | _⟩⟩
    change stackSet ((mapVar a).lookup (mapVal V)) i ((mapVar v).lookup (mapVal V)) = _
    rw [L a, L v]
    exact stackSet_wide _ _ _ _ _ _

/-- The block leaf at an expression. -/
theorem exprBlock?_denote {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (blk : Com jasminDialect (Γ.map wideTy) (wideTy t)) (h : exprBlock? e = some blk)
    (V : Valuation Γ) : blk.denote (mapVal V) = transTy (e.denote V) := by
  obtain ⟨op, rfl, args⟩ := e
  exact opBlock?_denote op args blk h V


/-! ## 5. The pass -/

/-- The trip counter `reg 64` and the bit `reg 1` are not narrow. -/
theorem widenP_regionTypes : widenP.RegionTypes := ⟨rfl, rfl⟩

/-- The variable leaf of `widenP`. -/
theorem widenP_varTransports : widenP.VarTransports (fun x => transTy x) (fun V => mapVal V) :=
  fun v V => lookup_mapVar_mapVal v V

/-- The binding leaf of `widenP`. -/
theorem widenP_mapValExtends : widenP.MapValExtends (fun x => transTy x) (fun V => mapVal V) :=
  fun _ _ => rfl

/-- The transport is the identity on the trip counter and on the bit. -/
theorem widenP_regionTransports :
    widenP.RegionTransports widenP_regionTypes (fun x => transTy x) where
  toNat_trans x := congrArg BitVec.toNat (transTy_reg64 x)
  ofNat_trans _ := transTy_reg64 _
  toBool_trans b := congrArg (fun c : BitVec 1 => decide (c = 1#1)) (transTy_reg1 b)

/-- **The widening of the narrow words of a structured Jasmin program**: `NFProg.map?` along
    `widenP` at the identity renaming; `none` when the program has an operation `widenP`
    refuses. -/
def widenJ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    Option (NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)) :=
  NFProg.map? widenP widenP_regionTypes p (fun v => v)

/-- **Preservation.** At call environments `E` and `E'` that agree along `transTy` at every
    call of `p`, a program `widenJ` returns for `p` denotes, on the widened valuation, at `E'`
    and every fuel, the widening of the denotation of `p` at `E`. -/
theorem widenJ_denote (E : CallEnv jasminDialect) (E' : CallEnv jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hCall : E.Transports E' (fun as => as.map wideTy)
      (fun x => transArgs wideTy (fun x => transTy x) x) p.Calls)
    (V : Valuation Γ) (q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy))
    (hq : widenJ p = some q) :
    q.denoteAt E' fuel (mapVal V) =
      (p.denoteAt E fuel V).map (transArgs wideTy (fun x => transTy x)) :=
  NFProg.map?_denoteAt widenP (fun x => transTy x) (fun V => mapVal V) widenP_regionTypes
    (fun _ => True) widenP_varTransports
    (fun e _ blk hblk V => exprBlock?_denote e blk hblk V)
    widenP_mapValExtends widenP_regionTransports E E' fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p) hCall (fun v => v) V (mapVal V)
    (FieldDialectBlockDescent.pullV_id _) q hq

/-- **Preservation at the call environment of `jasminDialect`.** The environment of
    `jasminDialect` is empty, so it agrees with itself at every call. -/
theorem widenJ_denote_empty (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (V : Valuation Γ)
    (q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)) (hq : widenJ p = some q) :
    q.denote fuel (mapVal V) = (p.denote fuel V).map (transArgs wideTy (fun x => transTy x)) :=
  NFProg.map?_denote_call widenP (fun x => transTy x) (fun V => mapVal V) widenP_regionTypes
    (fun _ => True) widenP_varTransports
    (fun e _ blk hblk V => exprBlock?_denote e blk hblk V)
    widenP_mapValExtends widenP_regionTransports fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p) (CallEnv.transports_empty _ _ _)
    (fun v => v) V (mapVal V) (FieldDialectBlockDescent.pullV_id _) q hq

/-! ## 6. Programs whose types are wide -/

/-- A type that `wideTy` fixes is held as itself. -/
theorem transTy_heq_of_wide {t : JasminTy} (h : wideTy t = t) (x : ⟦t⟧) : transTy x ≍ x := by
  cases t with
  | reg w =>
      have hw : wideW w = w := by injection h
      change BitVec.setWidth (wideW w) (x : BitVec w) ≍ x
      revert h
      generalize wideW w = W at *
      intro _
      subst hw
      rw [BitVec.setWidth_eq]
  | stackArr w n =>
      have hw : wideW w = w := by injection h
      change (fun i => BitVec.setWidth (wideW w) ((x : Fin n → BitVec w) i)) ≍ x
      revert h
      generalize wideW w = W at *
      intro _
      subst hw
      simp only [BitVec.setWidth_eq]
      rfl
  | inlineInt => rfl
  | bool => rfl

/-- Heterogeneous equality of two vectors with heterogeneously equal heads and tails. -/
theorem hvector_cons_heq {f : JasminTy → Type} {a a' : JasminTy} {l l' : List JasminTy}
    (ha : a = a') (hl : l = l') {x : f a} {x' : f a'} (hx : x ≍ x') {xs : HVector f l}
    {xs' : HVector f l'} (hxs : xs ≍ xs') :
    (HVector.cons x xs : HVector f (a :: l)) ≍ (HVector.cons x' xs' : HVector f (a' :: l')) := by
  subst ha hl
  cases hx
  cases hxs
  rfl

/-- The tuple transport on types that `wideTy` fixes is the identity up to the cast of its
    type. -/
theorem transArgs_heq_of_wide : {ts : List JasminTy} → ts.map wideTy = ts →
    (xs : HVector (fun t => ⟦t⟧) ts) → transArgs wideTy (fun x => transTy x) xs ≍ xs
  | [], _, .nil => HEq.rfl
  | t :: ts, h, .cons x xs => by
      have ht : wideTy t = t := (List.cons.inj h).1
      have hts : ts.map wideTy = ts := (List.cons.inj h).2
      exact hvector_cons_heq ht hts (transTy_heq_of_wide ht x) (transArgs_heq_of_wide hts xs)

/-- **The widened valuation of a wide context** is the valuation, up to the cast of the
    context. -/
theorem mapVal_heq_of_wide {Γ : Ctxt jasminDialect} (h : Γ.map wideTy = Γ) (V : Valuation Γ) :
    mapVal V ≍ V :=
  transArgs_heq_of_wide h V

/-- A map of an option along a function that is the identity up to the cast of its type is the
    identity up to the cast. -/
theorem option_map_heq {l l' : List JasminTy} (h : l' = l)
    (f : HVector (fun t => ⟦t⟧) l → HVector (fun t => ⟦t⟧) l') (hf : ∀ r, f r ≍ r)
    (o : Option (HVector (fun t => ⟦t⟧) l)) : o.map f ≍ o := by
  subst h
  cases o with
  | none => rfl
  | some r =>
      simp only [Option.map_some]
      rw [eq_of_heq (hf r)]

/-- **On wide types the pass preserves the denotation up to the casts.** When `wideTy` fixes
    the context and the result types, a program `widenJ` returns for `p` denotes, at a
    valuation `W` of the widened context that is `V` up to the cast, what `p` denotes at
    `V`. At a concrete context the casts are equations that `decide` proves. -/
theorem widenJ_denote_of_wide (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (hΓ : Γ.map wideTy = Γ) (hts : ts.map wideTy = ts) (p : NFProg jasminDialect Γ ts)
    (V : Valuation Γ) (q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy))
    (hq : widenJ p = some q) (W : Valuation (d := jasminDialect) (Γ.map wideTy)) (hW : W ≍ V) :
    q.denote fuel W ≍ p.denote fuel V := by
  obtain rfl : W = mapVal V := eq_of_heq (hW.trans (mapVal_heq_of_wide hΓ V).symm)
  rw [widenJ_denote_empty fuel p V q hq]
  exact option_map_heq hts _ (transArgs_heq_of_wide hts) _

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords
