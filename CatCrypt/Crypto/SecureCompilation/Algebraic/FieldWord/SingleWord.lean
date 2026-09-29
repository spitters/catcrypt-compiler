/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Mathlib.Data.ZMod.Basic
public import Transfer.Examples.PrimeWord
public import Mathlib.Tactic.Linarith

/-!
# Single-word prime-field blocks over `jasminDialect`

A prime field `ZMod p` with `2 p ≤ 2⁶³` is represented on one 64-bit register by
an encoding `enc : ZMod p → BitVec 64`. For each field operation this module gives
a `Com jasminDialect Γ (.reg 64)` block over context variables holding encoded
operands, and a value theorem: when the operand variables hold `enc x` and `enc y`,
the block denotes `enc (x ⋆ y)`. A block-expanding lowering splices these blocks
per source operation.

The blocks use only `regArith` and `regConst` bindings.

## Main definitions

* `SingleWordField p`: the encoding together with add, sub, neg, mul, const and
  copy blocks and their value theorems.
* `canonEnc p`: the canonical-representative encoding `x ↦ BitVec.ofNat 64 x.val`.
* `csubW P r`, `csubBlk P x`: the branch-free conditional subtract of `P`.
* `addBlk`, `subBlk`, `negBlk`, `constBlk`, `copyBlk`: the modulus-generic blocks
  on canonical representatives.
* `foldW c x`, `foldBlk c x`, `foldsBlk c n x`: the fold
  `x ↦ (x >>> 31) · c + (x & (2³¹ − 1))`, which preserves residues modulo
  `2³¹ − c`, and its `n`-fold iterate.
* `foldReduceBlk c n P x`, `foldMulBlk c n P a b`: `n` folds followed by one
  conditional subtract, and the product followed by that reduction.
* `SingleWordField.ofCanonical`: the record from a multiplication block on
  canonical representatives.

## Main results

* `csubW_toNat`: for `r < 2 P` and `2 P ≤ 2⁶³`, `(csubW P r).toNat = r.toNat % P`.
* `csubW_add_canonEnc`, `csubW_sub_canonEnc`, `csubW_neg_canonEnc`: the word
  functions of the generic blocks realise field addition, subtraction and negation
  under `canonEnc`.
* `addBlk_denote`, `subBlk_denote`, `negBlk_denote`, `constBlk_denote`,
  `copyBlk_denote`: the value theorems of the generic blocks under `canonEnc`.
* `foldW_toNat`, `foldW_mod`, `foldW_bound`: the value, residue and bound of one
  fold step for `x < 2⁶²`.
* `csubBlk_denote`, `foldsBlk_denote`, `foldReduceBlk_denote`, `foldMulBlk_denote`:
  the block denotations as word functions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (spliceCom spliceCom_denote)

/-- The 64-bit register type. -/
abbrev w64 : JasminTy := .reg 64

/-! ## 1. Atomic blocks -/

/-- The block binding `regConst 64 n` and returning it. -/
def litBlk {Γ : Ctxt jasminDialect} (n : Nat) : Com jasminDialect Γ w64 :=
  .var { op := .regConst 64 n, retTy_eq := rfl, args := .nil } (.ret .here)

/-- The block binding `regArith op 64` on `a`, `b` and returning it. -/
def binBlk {Γ : Ctxt jasminDialect} (op : JasminBinOp) (a b : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  .var { op := .regArith op 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }
    (.ret .here)

/-- The block binding `regArith op 64` on `a` and the constant `n`. -/
def binLitBlk {Γ : Ctxt jasminDialect} (op : JasminBinOp) (a : Ctxt.Var Γ w64)
    (n : Nat) : Com jasminDialect Γ w64 :=
  .var { op := .regConst 64 n, retTy_eq := rfl, args := .nil }
    (.var { op := .regArith op 64, retTy_eq := rfl,
            args := .cons a.there (.cons .here .nil) } (.ret .here))

theorem litBlk_denote {Γ : Ctxt jasminDialect} (n : Nat) (V : Ctxt.Valuation Γ) :
    (litBlk (Γ := Γ) n).denote V = BitVec.ofNat 64 n := rfl

theorem binBlk_denote {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ) :
    (binBlk op a b).denote V = op.apply (a.lookup V) (b.lookup V) := rfl

theorem binLitBlk_denote {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a : Ctxt.Var Γ w64) (n : Nat) (V : Ctxt.Valuation Γ) :
    (binLitBlk op a n).denote V = op.apply (a.lookup V) (BitVec.ofNat 64 n) := rfl

/-! ## 2. Conditional subtract -/

/-- The branch-free conditional subtract `(r − P) + (P & (0 − ((r − P) >>> 63)))`. -/
def csubW (P : Nat) (r : BitVec 64) : BitVec 64 :=
  (r - BitVec.ofNat 64 P) +
    (BitVec.ofNat 64 P &&& ((0 : BitVec 64) - ((r - BitVec.ofNat 64 P) >>> (63 : Nat))))

/-- For `r < 2 P` and `2 P ≤ 2⁶³`, the conditional subtract is reduction modulo `P`. -/
theorem csubW_toNat (P : Nat) (hP : 2 * P ≤ 2 ^ 63) (r : BitVec 64)
    (hr : r.toNat < 2 * P) : (csubW P r).toNat = r.toNat % P := by
  have hPt : (BitVec.ofNat 64 P).toNat = P := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hr64 := r.isLt
  unfold csubW
  rcases Nat.lt_or_ge r.toNat P with hlt | hge
  · have hsh : (r - BitVec.ofNat 64 P) >>> (63 : Nat) = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, hPt, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hsh, show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.sub_add_cancel, Nat.mod_eq_of_lt hlt]
  · have hsub : (r - BitVec.ofNat 64 P).toNat = r.toNat - P := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hPt]; exact hge), hPt]
    have hsh : (r - BitVec.ofNat 64 P) >>> (63 : Nat) = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, hsub, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    rw [hsh, show (0 : BitVec 64) - 0#64 = 0#64 by decide, BitVec.and_zero,
      BitVec.add_zero, hsub, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]

/-- The conditional-subtract block on `x`. -/
def csubBlk {Γ : Ctxt jasminDialect} (P : Nat) (x : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  .var { op := .regConst 64 P, retTy_eq := rfl, args := .nil } <|
  .var { op := .regArith .sub 64, retTy_eq := rfl,
         args := .cons x.there (.cons .here .nil) } <|
  .var { op := .regConst 64 63, retTy_eq := rfl, args := .nil } <|
  .var { op := .regArith .shr 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) } <|
  .var { op := .regConst 64 0, retTy_eq := rfl, args := .nil } <|
  .var { op := .regArith .sub 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) } <|
  .var { op := .regArith .and 64, retTy_eq := rfl,
         args := .cons (.there (.there (.there (.there (.there .here)))))
           (.cons .here .nil) } <|
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there (.there (.there (.there (.there .here)))))
           (.cons .here .nil) } <|
  .ret .here

theorem csubBlk_denote {Γ : Ctxt jasminDialect} (P : Nat) (x : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (csubBlk P x).denote V = csubW P (x.lookup V) := rfl

/-! ## 3. The canonical encoding -/

/-- The canonical-representative encoding `x ↦ BitVec.ofNat 64 x.val`, the canonical
    prime word `Transfer.PrimeWord.primeWord p`. -/
abbrev canonEnc (p : Nat) : ZMod p → BitVec 64 := Transfer.PrimeWord.primeWord p

theorem canonEnc_toNat {p : Nat} [NeZero p] (hp : p ≤ 2 ^ 64) (x : ZMod p) :
    (canonEnc p x).toNat = x.val := Transfer.PrimeWord.primeWord_toNat hp x

theorem canonEnc_injective {p : Nat} [NeZero p] (hp : p ≤ 2 ^ 64) :
    Function.Injective (canonEnc p) := Transfer.PrimeWord.primeWord_injective hp

/-- A word whose value is `z.val` is the encoding of `z`. -/
theorem eq_canonEnc_of_toNat {p : Nat} [NeZero p] (hp : p ≤ 2 ^ 64) (w : BitVec 64)
    (z : ZMod p) (h : w.toNat = z.val) : w = canonEnc p z :=
  Transfer.PrimeWord.eq_primeWord_of_toNat hp w z h

/-! ## 4. Modulus-generic blocks on canonical representatives -/

/-- Field addition: `a + b`, then one conditional subtract. -/
def addBlk {Γ : Ctxt jasminDialect} (P : Nat) (a b : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (binBlk .add a b) (csubBlk P .here)

/-- Field subtraction: `a + (P − b)`, then one conditional subtract. -/
def subBlk {Γ : Ctxt jasminDialect} (P : Nat) (a b : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (litBlk P) <|
  spliceCom (binBlk .sub .here b.there) <|
  spliceCom (binBlk .add a.there.there .here) <|
  csubBlk P .here

/-- Field negation: `P − a`, then one conditional subtract. -/
def negBlk {Γ : Ctxt jasminDialect} (P : Nat) (a : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (litBlk P) <|
  spliceCom (binBlk .sub .here a.there) <|
  csubBlk P .here

/-- Field constant: `regConst 64 x.val`. -/
def constBlk {Γ : Ctxt jasminDialect} (p : Nat) (x : ZMod p) : Com jasminDialect Γ w64 :=
  litBlk x.val

/-- Copy: the block returning the operand variable. -/
def copyBlk {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  .ret a

/-- The value of a 64-bit variable under a valuation, typed as `BitVec 64`. -/
abbrev lk {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ) :
    BitVec 64 :=
  a.lookup V

theorem addBlk_value {Γ : Ctxt jasminDialect} (P : Nat) (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (addBlk P a b).denote V = csubW P (lk a V + lk b V) := by
  unfold addBlk
  rw [spliceCom_denote, csubBlk_denote]
  rfl

theorem subBlk_value {Γ : Ctxt jasminDialect} (P : Nat) (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) :
    (subBlk P a b).denote V = csubW P (lk a V + (BitVec.ofNat 64 P - lk b V)) := by
  unfold subBlk
  rw [spliceCom_denote, spliceCom_denote, spliceCom_denote, csubBlk_denote]
  rfl

theorem negBlk_value {Γ : Ctxt jasminDialect} (P : Nat) (a : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) :
    (negBlk P a).denote V = csubW P (BitVec.ofNat 64 P - lk a V) := by
  unfold negBlk
  rw [spliceCom_denote, spliceCom_denote, csubBlk_denote]
  rfl

section Generic

variable {p : Nat} [NeZero p] (hp : 2 * p ≤ 2 ^ 63)
include hp

/-- Word addition followed by a conditional subtract is field addition on canonical
    representatives. -/
theorem csubW_add_canonEnc (x y : ZMod p) :
    csubW p (canonEnc p x + canonEnc p y) = canonEnc p (x + y) := by
  have hp64 : p ≤ 2 ^ 64 := by omega
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hsum : (canonEnc p x + canonEnc p y).toNat = x.val + y.val := by
    rw [BitVec.toNat_add, canonEnc_toNat hp64, canonEnc_toNat hp64]
    exact Nat.mod_eq_of_lt (by omega)
  apply eq_canonEnc_of_toNat hp64
  rw [csubW_toNat p hp _ (by omega), hsum, ZMod.val_add]

/-- `a + (p − b)` followed by a conditional subtract is field subtraction on
    canonical representatives. -/
theorem csubW_sub_canonEnc (x y : ZMod p) :
    csubW p (canonEnc p x + (BitVec.ofNat 64 p - canonEnc p y)) = canonEnc p (x - y) := by
  have hp64 : p ≤ 2 ^ 64 := by omega
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hPt : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbt : (canonEnc p y).toNat = y.val := canonEnc_toNat hp64 y
  have hat : (canonEnc p x).toNat = x.val := canonEnc_toNat hp64 x
  have hdiff : (BitVec.ofNat 64 p - canonEnc p y).toNat = p - y.val := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hPt, hbt]; omega), hPt, hbt]
  have hsum : (canonEnc p x + (BitVec.ofNat 64 p - canonEnc p y)).toNat
      = x.val + (p - y.val) := by
    rw [BitVec.toNat_add, hat, hdiff]
    exact Nat.mod_eq_of_lt (by omega)
  have hcast : x - y = (((x.val + (p - y.val)) : Nat) : ZMod p) := by
    rw [Nat.cast_add, Nat.cast_sub hy.le, ZMod.natCast_self]
    simp only [ZMod.natCast_zmod_val]
    ring
  apply eq_canonEnc_of_toNat hp64
  rw [csubW_toNat p hp _ (by omega), hsum, hcast, ZMod.val_natCast]

/-- `p − a` followed by a conditional subtract is field negation on canonical
    representatives. -/
theorem csubW_neg_canonEnc (x : ZMod p) :
    csubW p (BitVec.ofNat 64 p - canonEnc p x) = canonEnc p (-x) := by
  have hp64 : p ≤ 2 ^ 64 := by omega
  have hx := ZMod.val_lt x
  have hPt : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hat : (canonEnc p x).toNat = x.val := canonEnc_toNat hp64 x
  have hdiff : (BitVec.ofNat 64 p - canonEnc p x).toNat = p - x.val := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hPt, hat]; omega), hPt, hat]
  have hcast : -x = (((p - x.val) : Nat) : ZMod p) := by
    rw [Nat.cast_sub hx.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
    ring
  apply eq_canonEnc_of_toNat hp64
  rw [csubW_toNat p hp _ (by omega), hdiff, hcast, ZMod.val_natCast]

theorem addBlk_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x y : ZMod p)
    (ha : a.lookup V = canonEnc p x) (hb : b.lookup V = canonEnc p y) :
    (addBlk p a b).denote V = canonEnc p (x + y) := by
  rw [addBlk_value, show lk a V = canonEnc p x from ha, show lk b V = canonEnc p y from hb]
  exact csubW_add_canonEnc hp x y

theorem subBlk_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x y : ZMod p)
    (ha : a.lookup V = canonEnc p x) (hb : b.lookup V = canonEnc p y) :
    (subBlk p a b).denote V = canonEnc p (x - y) := by
  rw [subBlk_value, show lk a V = canonEnc p x from ha, show lk b V = canonEnc p y from hb]
  exact csubW_sub_canonEnc hp x y

theorem negBlk_denote {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x : ZMod p) (ha : a.lookup V = canonEnc p x) :
    (negBlk p a).denote V = canonEnc p (-x) := by
  rw [negBlk_value, show lk a V = canonEnc p x from ha]
  exact csubW_neg_canonEnc hp x

end Generic

/-! ### The word functions as registered squares along `canonEnc` -/

section Squares

variable {p : Nat} [NeZero p] [hp : Fact (2 * p ≤ 2 ^ 63)]

/-- Word addition followed by a conditional subtract realizes `+` along `canonEnc p`. -/
instance csubAddRelated :
    _root_.Transfer.RelatedBinOp (canonEnc p) (· + ·) (fun a b => csubW p (a + b)) where
  comm x y := (csubW_add_canonEnc hp.out x y).symm

/-- `a + (p − b)` followed by a conditional subtract realizes `-` along `canonEnc p`. -/
instance csubSubRelated :
    _root_.Transfer.RelatedBinOp (canonEnc p) (· - ·)
      (fun a b => csubW p (a + (BitVec.ofNat 64 p - b))) where
  comm x y := (csubW_sub_canonEnc hp.out x y).symm

/-- `p − a` followed by a conditional subtract realizes negation along `canonEnc p`. -/
instance csubNegRelated :
    _root_.Transfer.RelatedUnOp (canonEnc p) (fun x => -x)
      (fun a => csubW p (BitVec.ofNat 64 p - a)) where
  comm x := (csubW_neg_canonEnc hp.out x).symm

end Squares

theorem constBlk_denote {Γ : Ctxt jasminDialect} {p : Nat} (x : ZMod p)
    (V : Ctxt.Valuation Γ) : (constBlk (Γ := Γ) p x).denote V = canonEnc p x := rfl

theorem copyBlk_denote {Γ : Ctxt jasminDialect} {α : Type} (enc : α → BitVec 64)
    (a : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ) (x : α) (ha : a.lookup V = enc x) :
    (copyBlk a).denote V = enc x := ha

/-! ## 5. The 31-bit fold -/

/-- The fold `x ↦ (x >>> 31) · c + (x & (2³¹ − 1))`. Since `2³¹ ≡ c (mod 2³¹ − c)`,
    it preserves residues modulo `2³¹ − c`. -/
def foldW (c : Nat) (x : BitVec 64) : BitVec 64 :=
  (x >>> (31 : Nat)) * BitVec.ofNat 64 c + (x &&& BitVec.ofNat 64 2147483647)

/-- For `c < 2³¹` and `x < 2⁶²`, the fold does not wrap. -/
theorem foldW_toNat (c : Nat) (hc : c < 2 ^ 31) (x : BitVec 64)
    (hx : x.toNat < 2 ^ 62) :
    (foldW c x).toNat = x.toNat / 2 ^ 31 * c + x.toNat % 2 ^ 31 := by
  have hct : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hmt : (BitVec.ofNat 64 2147483647).toNat = 2 ^ 31 - 1 := by decide
  unfold foldW
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_and,
    hct, hmt, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have hq : x.toNat / 2 ^ 31 < 2 ^ 31 := Nat.div_lt_of_lt_mul (by omega)
  have hqc : x.toNat / 2 ^ 31 * c < 2 ^ 62 := by
    calc x.toNat / 2 ^ 31 * c ≤ x.toNat / 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul_left _ hc.le
      _ < 2 ^ 31 * 2 ^ 31 := Nat.mul_lt_mul_of_pos_right hq (by norm_num)
      _ = 2 ^ 62 := by norm_num
  have hr : x.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mod_eq_of_lt (by omega : x.toNat / 2 ^ 31 * c < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

/-- The fold preserves the residue modulo `2³¹ − c`. -/
theorem foldW_mod (c : Nat) (hc : c < 2 ^ 31) (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    (foldW c x).toNat % (2 ^ 31 - c) = x.toNat % (2 ^ 31 - c) := by
  rw [foldW_toNat c hc x hx]
  conv_rhs => rw [← Nat.div_add_mod x.toNat (2 ^ 31)]
  have h : 2 ^ 31 = (2 ^ 31 - c) + c := by omega
  generalize x.toNat / 2 ^ 31 = q
  generalize x.toNat % 2 ^ 31 = r
  rw [h, Nat.add_sub_cancel, Nat.mul_comm, Nat.add_mul, Nat.add_assoc,
    Nat.mul_add_mod]

/-- If `x < B ≤ 2⁶²`, one fold lands below `(B / 2³¹) · c + 2³¹`. -/
theorem foldW_bound (c : Nat) (hc : c < 2 ^ 31) (x : BitVec 64) (B : Nat)
    (hB : B ≤ 2 ^ 62) (hx : x.toNat < B) :
    (foldW c x).toNat < B / 2 ^ 31 * c + 2 ^ 31 := by
  rw [foldW_toNat c hc x (by omega)]
  have h1 : x.toNat / 2 ^ 31 * c ≤ B / 2 ^ 31 * c :=
    Nat.mul_le_mul_right _ (Nat.div_le_div_right hx.le)
  have h2 : x.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  omega

/-- The fold block on `x`. -/
def foldBlk {Γ : Ctxt jasminDialect} (c : Nat) (x : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (binLitBlk .shr x 31) <|
  spliceCom (binLitBlk .mul .here c) <|
  spliceCom (binLitBlk .and x.there.there 2147483647) <|
  binBlk .add (.there .here) .here

theorem foldBlk_denote {Γ : Ctxt jasminDialect} (c : Nat) (x : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (foldBlk c x).denote V = foldW c (x.lookup V) := by
  unfold foldBlk
  simp only [spliceCom_denote, binLitBlk_denote, binBlk_denote]
  rfl

/-- `n` successive folds of `x`. -/
def foldsBlk (c : Nat) : Nat → {Γ : Ctxt jasminDialect} → Ctxt.Var Γ w64 →
    Com jasminDialect Γ w64
  | 0, _, x => .ret x
  | n + 1, _, x => spliceCom (foldBlk c x) (foldsBlk c n .here)

theorem foldsBlk_denote (c : Nat) :
    ∀ (n : Nat) {Γ : Ctxt jasminDialect} (x : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ),
      (foldsBlk c n x).denote V = (foldW c)^[n] (x.lookup V)
  | 0, _, _, _ => rfl
  | n + 1, _, x, V => by
      rw [foldsBlk, spliceCom_denote, foldsBlk_denote c n, foldBlk_denote,
        Function.iterate_succ_apply]
      rfl

/-- `n` folds of `x` by `c`, then one conditional subtract of `P`. -/
def foldReduceBlk {Γ : Ctxt jasminDialect} (c n P : Nat) (x : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (foldsBlk c n x) (csubBlk P .here)

theorem foldReduceBlk_denote {Γ : Ctxt jasminDialect} (c n P : Nat) (x : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) :
    (foldReduceBlk c n P x).denote V = csubW P ((foldW c)^[n] (lk x V)) := by
  unfold foldReduceBlk
  rw [spliceCom_denote, csubBlk_denote, ← foldsBlk_denote c n x V]
  rfl

/-- The product `a · b`, then `foldReduceBlk c n P`. -/
def foldMulBlk {Γ : Ctxt jasminDialect} (c n P : Nat) (a b : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (binBlk .mul a b) (foldReduceBlk c n P .here)

theorem foldMulBlk_denote {Γ : Ctxt jasminDialect} (c n P : Nat) (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) :
    (foldMulBlk c n P a b).denote V = csubW P ((foldW c)^[n] (lk a V * lk b V)) := by
  unfold foldMulBlk
  rw [spliceCom_denote, foldReduceBlk_denote]
  rfl

/-! ## 6. The record -/

/-- A single-word representation of `ZMod p`: an encoding into 64-bit words and,
    for each field operation, a `Com jasminDialect` block over variables holding
    encoded operands whose denotation is the encoding of the result. -/
structure SingleWordField (p : Nat) where
  /-- The word encoding. -/
  enc : ZMod p → BitVec 64
  /-- The encoding is injective. -/
  enc_injective : Function.Injective enc
  /-- Addition block. -/
  addBlk : ∀ {Γ : Ctxt jasminDialect}, Ctxt.Var Γ w64 → Ctxt.Var Γ w64 → Com jasminDialect Γ w64
  /-- Subtraction block. -/
  subBlk : ∀ {Γ : Ctxt jasminDialect}, Ctxt.Var Γ w64 → Ctxt.Var Γ w64 → Com jasminDialect Γ w64
  /-- Multiplication block. -/
  mulBlk : ∀ {Γ : Ctxt jasminDialect}, Ctxt.Var Γ w64 → Ctxt.Var Γ w64 → Com jasminDialect Γ w64
  /-- Negation block. -/
  negBlk : ∀ {Γ : Ctxt jasminDialect}, Ctxt.Var Γ w64 → Com jasminDialect Γ w64
  /-- Constant block. -/
  constBlk : ∀ {Γ : Ctxt jasminDialect}, ZMod p → Com jasminDialect Γ w64
  /-- Copy block. -/
  copyBlk : ∀ {Γ : Ctxt jasminDialect}, Ctxt.Var Γ w64 → Com jasminDialect Γ w64
  addBlk_denote : ∀ {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ)
    (x y : ZMod p), a.lookup V = enc x → b.lookup V = enc y →
    (addBlk a b).denote V = enc (x + y)
  subBlk_denote : ∀ {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ)
    (x y : ZMod p), a.lookup V = enc x → b.lookup V = enc y →
    (subBlk a b).denote V = enc (x - y)
  mulBlk_denote : ∀ {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ)
    (x y : ZMod p), a.lookup V = enc x → b.lookup V = enc y →
    (mulBlk a b).denote V = enc (x * y)
  negBlk_denote : ∀ {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ)
    (x : ZMod p), a.lookup V = enc x → (negBlk a).denote V = enc (-x)
  constBlk_denote : ∀ {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (x : ZMod p),
    (constBlk x).denote V = enc x
  copyBlk_denote : ∀ {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ)
    (x : ZMod p), a.lookup V = enc x → (copyBlk a).denote V = enc x

/-- The canonical-representative `SingleWordField` from a multiplication block on
    canonical representatives, with the modulus-generic add, sub, neg, const and
    copy blocks. -/
def SingleWordField.ofCanonical (p : Nat) [NeZero p] (hp : 2 * p ≤ 2 ^ 63)
    (mulBlk : ∀ {Γ : Ctxt jasminDialect}, Ctxt.Var Γ w64 → Ctxt.Var Γ w64 →
      Com jasminDialect Γ w64)
    (mulBlk_denote : ∀ {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
      (V : Ctxt.Valuation Γ) (x y : ZMod p), a.lookup V = canonEnc p x →
      b.lookup V = canonEnc p y → (mulBlk a b).denote V = canonEnc p (x * y)) :
    SingleWordField p where
  enc := canonEnc p
  enc_injective := canonEnc_injective (by omega)
  addBlk := FieldWord.addBlk p
  subBlk := FieldWord.subBlk p
  mulBlk := mulBlk
  negBlk := FieldWord.negBlk p
  constBlk := FieldWord.constBlk p
  copyBlk := FieldWord.copyBlk
  addBlk_denote := FieldWord.addBlk_denote hp
  subBlk_denote := FieldWord.subBlk_denote hp
  mulBlk_denote := mulBlk_denote
  negBlk_denote := FieldWord.negBlk_denote hp
  constBlk_denote V x := FieldWord.constBlk_denote x V
  copyBlk_denote a V x ha := FieldWord.copyBlk_denote (canonEnc p) a V x ha

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord
