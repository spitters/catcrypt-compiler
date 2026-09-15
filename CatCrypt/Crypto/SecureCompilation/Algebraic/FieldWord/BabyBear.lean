/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact

/-!
# BabyBear single-word field blocks

The `SingleWordField` instance at the BabyBear prime `P = 2³¹ − 2²⁷ + 1 =
2013265921` under the canonical encoding. The multiplication block is the
Poseidon2 builder `Poseidon2WholePermCom.emitMul` (one multiply, ten folds by
`2²⁷ − 1`, two conditional subtracts); addition, subtraction, negation, constants
and copies are the modulus-generic blocks of `SingleWord`.

The reduction proof uses the fold bound and residue lemmas of
`Poseidon2BbMulFieldExact` and the generic conditional-subtract lemma
`csubW_toNat`.

## Main definitions

* `bbEnc`: the canonical encoding `ZMod P → BitVec 64`.
* `bbSub`: the subtraction word function `csub (a + (P − b))`.
* `mulBlk`: the multiplication block.
* `babyBear`: the `SingleWordField P` record.

## Main results

* `bbReduce_toNat_eq_mod`: `(bbReduce x).toNat = x.toNat % P` for `x < 2⁶²`.
* `bbMul_realizes`, `bbAdd_realizes`, `bbSub_realizes`: the Poseidon2 word functions
  realise field multiplication, addition and subtraction under `bbEnc`.
* `mulBlk_denote`: the multiplication block denotes `bbEnc (x * y)` on variables
  holding `bbEnc x` and `bbEnc y`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.BabyBear

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit (bbCsub bbReduce bbMul bbAdd)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact
  (bbCsub2 bbFold10 bbFold10_bound bbFold10_mod_p bbReduce_eq_csub2_fold10)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
  (BState emitMul emitMul_denote_ret)

/-- The BabyBear prime `2³¹ − 2²⁷ + 1`. -/
abbrev P : Nat := 2013265921

theorem two_P_le : 2 * P ≤ 2 ^ 63 := by norm_num

/-- The canonical encoding of BabyBear elements. -/
abbrev bbEnc : ZMod P → BitVec 64 := canonEnc P

/-! ## 1. Word functions -/

theorem bbCsub_eq_csubW (r : BitVec 64) : bbCsub r = csubW P r := rfl

/-- The BabyBear subtraction word function `csub (a + (P − b))`. -/
def bbSub (a b : BitVec 64) : BitVec 64 := csubW P (a + (BitVec.ofNat 64 P - b))

/-- The ten-fold, two-csub reduction is reduction modulo `P` below `2⁶²`. -/
theorem bbReduce_toNat_eq_mod (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    (bbReduce x).toNat = x.toNat % P := by
  have hx' : x.toNat < 4611686018427387904 := lt_of_lt_of_eq hx (by norm_num)
  have h10 := bbFold10_bound x hx'
  have hm := bbFold10_mod_p x hx'
  rw [bbReduce_eq_csub2_fold10]
  unfold bbCsub2
  rw [bbCsub_eq_csubW, bbCsub_eq_csubW]
  have h1 : (csubW P (bbFold10 x)).toNat = (bbFold10 x).toNat % P :=
    csubW_toNat P two_P_le _ (lt_of_lt_of_le h10 (by norm_num))
  have h1lt : (csubW P (bbFold10 x)).toNat < 2 * P := by
    rw [h1]; exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [csubW_toNat P two_P_le _ h1lt, h1, Nat.mod_mod,
    show (bbFold10 x).toNat % P = x.toNat % P from hm]

theorem bbMul_realizes (x y : ZMod P) : bbMul (bbEnc x) (bbEnc y) = bbEnc (x * y) := by
  have hx : x.val < 2013265921 := ZMod.val_lt x
  have hy : y.val < 2013265921 := ZMod.val_lt y
  have hlt : x.val * y.val < 2 ^ 62 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' hx hy) (by norm_num)
  have hprod : (bbEnc x * bbEnc y).toNat = x.val * y.val := by
    rw [BitVec.toNat_mul, canonEnc_toNat (by norm_num), canonEnc_toNat (by norm_num)]
    exact Nat.mod_eq_of_lt (lt_trans hlt (by norm_num))
  apply eq_canonEnc_of_toNat (by norm_num)
  show (bbReduce (bbEnc x * bbEnc y)).toNat = _
  rw [bbReduce_toNat_eq_mod _ (by rw [hprod]; exact hlt), hprod, ZMod.val_mul]

theorem bbAdd_realizes (x y : ZMod P) : bbAdd (bbEnc x) (bbEnc y) = bbEnc (x + y) :=
  csubW_add_canonEnc two_P_le x y

theorem bbSub_realizes (x y : ZMod P) : bbSub (bbEnc x) (bbEnc y) = bbEnc (x - y) :=
  csubW_sub_canonEnc two_P_le x y

/-! ## 2. The multiplication block -/

/-- The Poseidon2 builder state with slot 1 holding `b` and every other slot
    holding `a`. -/
def mulState {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) : BState Γ :=
  { cur := fun i => if i = ⟨1, by omega⟩ then b else a }

/-- The BabyBear multiplication block: `emitMul` from slots 0 and 1 into slot 2,
    returning slot 2. -/
def mulBlk {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  emitMul (mulState a b) ⟨2, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩
    (fun {_} s => .ret (s.cur ⟨2, by omega⟩))

theorem mulBlk_value {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (mulBlk a b).denote V = bbMul (lk a V) (lk b V) := by
  unfold mulBlk
  rw [emitMul_denote_ret _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide)]
  rfl

theorem mulBlk_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x y : ZMod P) (ha : a.lookup V = bbEnc x)
    (hb : b.lookup V = bbEnc y) : (mulBlk a b).denote V = bbEnc (x * y) := by
  rw [mulBlk_value, show lk a V = bbEnc x from ha, show lk b V = bbEnc y from hb]
  exact bbMul_realizes x y

/-! ## 3. The record -/

/-- The BabyBear `SingleWordField` on canonical representatives. -/
def babyBear : SingleWordField P :=
  SingleWordField.ofCanonical P two_P_le mulBlk mulBlk_denote

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.BabyBear
