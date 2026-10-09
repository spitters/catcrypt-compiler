/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32

/-!
# Montgomery representatives of degree `k` on one 64-bit word

For a modulus `p` with `mont32Cert p`, the residue `R = 2³² mod p` is a unit of `ZMod p`.
A word holds `x` at degree `k : ℤ` when it is the canonical representative of `x · Rᵏ`:
`encK h k x = canonEnc p (x · Rᵏ)`. Degree `0` is the canonical encoding.

The reduce-multiply `redcMulW p a b = csub (redc (a · b))` maps operands at degrees `k` and
`j` to the product at degree `k + j − 1`. Addition, subtraction and negation are linear, so
the canonical blocks of `SingleWord` act correctly at every degree; a constant of degree `k`
is the canonical constant `c · Rᵏ`.

## Main definitions

* `R32 h`: the unit `2³² mod p` of `ZMod p`.
* `encK h k x`: the canonical representative of `x · Rᵏ`.
* `redcMulW p a b`, `redcMulBlk p a b`: the reduce-multiply as a word function and as a
  block over `jasminDialect`.
* `montField p h`: the single-word record at degree `1`, with multiply `redcMulBlk p`.

## Main results

* `encK_zero`, `encK_injective`: degree `0` is `canonEnc p`; each `encK h k` is injective.
* `redcMulBlk_value`: the block denotes `redcMulW p` on its operands.
* `redcMulW_encK`: `redcMulW p (encK h k x) (encK h j y) = encK h (k + j − 1) (x · y)`.
* `addBlk_encK`, `subBlk_encK`, `negBlk_encK`, `constBlk_encK`: the canonical blocks at
  degree `k`.
* `opsQuiet_redcMulBlk`: the reduce-multiply block binds register constants and register
  add, sub, mul, and, shl and shr only.
* `redcConsts_imm32`: the constants of the reduce-multiply block and every constant
  `c · Rᵏ` of `ZMod p` are 32-bit immediates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.MontDeg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (spliceCom spliceCom_denote)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32

/-! ## 1. The unit `R` and the encoding at degree `k` -/

theorem neZero_of_cert {p : Nat} (h : mont32Cert p = true) : NeZero p :=
  ⟨by have := (mont32Cert_spec h).2.1; omega⟩

theorem coprime_R {p : Nat} (h : mont32Cert p = true) : Nat.Coprime (2 ^ 32) p :=
  (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (mont32Cert_spec h).1)).pow_left 32

/-- The unit `R = 2³² mod p` of `ZMod p`. -/
def R32 {p : Nat} (h : mont32Cert p = true) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime (2 ^ 32) (coprime_R h)

theorem R32_val {p : Nat} (h : mont32Cert p = true) :
    ((R32 h : (ZMod p)ˣ) : ZMod p) = ((2 ^ 32 : Nat) : ZMod p) := rfl

/-- The word holding `x` at degree `k`: the canonical representative of `x · Rᵏ`. -/
def encK {p : Nat} (h : mont32Cert p = true) (k : ℤ) (x : ZMod p) : BitVec 64 :=
  canonEnc p (x * ↑(R32 h ^ k))

theorem encK_zero {p : Nat} (h : mont32Cert p = true) : encK h 0 = canonEnc p := by
  funext x
  simp [encK]

theorem encK_injective {p : Nat} (h : mont32Cert p = true) (k : ℤ) :
    Function.Injective (encK h k) := by
  have := neZero_of_cert h
  intro x y hxy
  have hp : p ≤ 2 ^ 64 := by have := (mont32Cert_spec h).2.2.1; omega
  have := canonEnc_injective hp hxy
  exact (Units.mul_left_inj _).mp this

/-! ## 2. The reduce-multiply -/

/-- **The reduce-multiply**: `csub (redc (a · b))`. -/
def redcMulW (p : Nat) (a b : BitVec 64) : BitVec 64 :=
  csubW p (redc32W p (mu p) (a * b))

/-- **The reduce-multiply at degrees**: operands at degrees `k` and `j` give the product at
    degree `k + j − 1`. -/
theorem redcMulW_encK {p : Nat} (h : mont32Cert p = true) (k j : ℤ) (x y : ZMod p) :
    redcMulW p (encK h k x) (encK h j y) = encK h (k + j - 1) (x * y) := by
  have := neZero_of_cert h
  obtain ⟨_, _, hp, _⟩ := mont32Cert_spec h
  have hp64 : p ≤ 2 ^ 64 := by omega
  set u := x * ↑(R32 h ^ k) with hu
  set v := y * ↑(R32 h ^ j) with hv
  have hx := ZMod.val_lt u
  have hy := ZMod.val_lt v
  have hxy : u.val * v.val < p * 2 ^ 32 := Nat.mul_lt_mul'' hx (by omega)
  have hprod : (canonEnc p u * canonEnc p v).toNat = u.val * v.val := by
    rw [BitVec.toNat_mul, canonEnc_toNat hp64, canonEnc_toNat hp64]
    exact Nat.mod_eq_of_lt (by
      have : p * 2 ^ 32 < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hp (by norm_num)
      omega)
  obtain ⟨hb, hm⟩ := redc32W_spec h (t := canonEnc p u * canonEnc p v) (by rw [hprod]; exact hxy)
  set r := redc32W p (mu p) (canonEnc p u * canonEnc p v) with hr
  rw [hprod] at hm
  have hcast : ((r.toNat : Nat) : ZMod p) * ((2 ^ 32 : Nat) : ZMod p) = u * v := by
    rw [← Nat.cast_mul, (ZMod.natCast_eq_natCast_iff' _ _ p).mpr hm, Nat.cast_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hres : ((r.toNat : Nat) : ZMod p) = x * y * ↑(R32 h ^ (k + j - 1)) := by
    rw [← R32_val h] at hcast
    apply (Units.mul_left_inj (R32 h)).mp
    have e : ((R32 h ^ (k + j - 1) : (ZMod p)ˣ) : ZMod p) * ↑(R32 h) =
        ↑(R32 h ^ k) * ↑(R32 h ^ j) := by
      rw [← Units.val_mul, ← Units.val_mul, ← zpow_add_one, ← zpow_add,
        show k + j - 1 + 1 = k + j by ring]
    rw [hcast, hu, hv]
    linear_combination (-(x * y)) * e
  unfold redcMulW encK
  rw [← hr]
  apply eq_canonEnc_of_toNat hp64
  rw [csubW_toNat p (by omega) _ hb, ← hres, ZMod.val_natCast]

/-- **The reduce-multiply block** on `a`, `b`: the product, a reduction and one conditional
    subtract of `p`. -/
def redcMulBlk (p : Nat) {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (binBlk .mul a b) <|
  spliceCom (redcBlk p (mu p) .here) <|
  csubBlk p .here

theorem redcMulBlk_value (p : Nat) {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (redcMulBlk p a b).denote V = redcMulW p (lk a V) (lk b V) := by
  unfold redcMulBlk
  simp only [spliceCom_denote, binBlk_denote, redcBlk_denote, csubBlk_denote]
  rfl

/-- On variables holding `x` at degree `k` and `y` at degree `j`, the reduce-multiply block
    denotes `x * y` at degree `k + j − 1`. -/
theorem redcMulBlk_encK {p : Nat} (h : mont32Cert p = true) {Γ : Ctxt jasminDialect}
    (a b : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ) (k j : ℤ) (x y : ZMod p)
    (ha : a.lookup V = encK h k x) (hb : b.lookup V = encK h j y) :
    (redcMulBlk p a b).denote V = encK h (k + j - 1) (x * y) := by
  rw [redcMulBlk_value, show lk a V = encK h k x from ha, show lk b V = encK h j y from hb]
  exact redcMulW_encK h k j x y

/-! ## 3. The canonical blocks at degree `k` -/

theorem two_mul_le_of_cert {p : Nat} (h : mont32Cert p = true) : 2 * p ≤ 2 ^ 63 := by
  have := (mont32Cert_spec h).2.2.1; omega

section Linear

variable {p : Nat} (h : mont32Cert p = true)

theorem addBlk_encK {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ)
    (k : ℤ) (x y : ZMod p) (ha : a.lookup V = encK h k x) (hb : b.lookup V = encK h k y) :
    (addBlk p a b).denote V = encK h k (x + y) := by
  have := neZero_of_cert h
  unfold encK at *
  rw [add_mul]
  exact addBlk_denote (two_mul_le_of_cert h) a b V _ _ ha hb

theorem subBlk_encK {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ)
    (k : ℤ) (x y : ZMod p) (ha : a.lookup V = encK h k x) (hb : b.lookup V = encK h k y) :
    (subBlk p a b).denote V = encK h k (x - y) := by
  have := neZero_of_cert h
  unfold encK at *
  rw [sub_mul]
  exact subBlk_denote (two_mul_le_of_cert h) a b V _ _ ha hb

theorem negBlk_encK {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ)
    (k : ℤ) (x : ZMod p) (ha : a.lookup V = encK h k x) :
    (negBlk p a).denote V = encK h k (-x) := by
  have := neZero_of_cert h
  unfold encK at *
  rw [neg_mul]
  exact negBlk_denote (two_mul_le_of_cert h) a V _ ha

/-- The constant `x` at degree `k` is the canonical constant `x · Rᵏ`. -/
theorem constBlk_encK {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (k : ℤ) (x : ZMod p) :
    (constBlk (Γ := Γ) p (x * ↑(R32 h ^ k))).denote V = encK h k x := rfl

end Linear

/-! ## 4. The record at degree `1` -/

/-- **The Montgomery record at `p`** under `mont32Cert p`: words hold `x · R`, the multiply
    is `redcMulBlk p`, and add, sub, neg and copy are the canonical blocks. -/
def montField (p : Nat) (h : mont32Cert p = true) : SingleWordField p where
  enc := encK h 1
  enc_injective := encK_injective h 1
  addBlk := FieldWord.addBlk p
  subBlk := FieldWord.subBlk p
  mulBlk := redcMulBlk p
  negBlk := FieldWord.negBlk p
  constBlk x := FieldWord.constBlk p (x * ↑(R32 h ^ (1 : ℤ)))
  copyBlk := FieldWord.copyBlk
  addBlk_denote a b V x y ha hb := addBlk_encK h a b V 1 x y ha hb
  subBlk_denote a b V x y ha hb := subBlk_encK h a b V 1 x y ha hb
  mulBlk_denote a b V x y ha hb := by
    have := redcMulBlk_encK h a b V 1 1 x y ha hb
    rwa [show (1 : ℤ) + 1 - 1 = 1 by norm_num] at this
  negBlk_denote a V x ha := negBlk_encK h a V 1 x ha
  constBlk_denote V x := constBlk_encK h V 1 x
  copyBlk_denote a V x ha := FieldWord.copyBlk_denote (encK h 1) a V x ha

/-! ## 5. Leakage and immediates -/

section Quiet

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (Com.OpsQuiet)

/-- **The reduce-multiply block binds constant-time operations only**: for a leakage model
    in which register constants and register add, sub, mul, and, shl and shr have no event,
    every operation of `redcMulBlk p` has no event. -/
theorem opsQuiet_redcMulBlk (M : LeakModel jasminDialect)
    (hA : ∀ (bop : JasminBinOp) (w : Nat),
      bop ∈ [.add, .sub, .mul, .and, .shl, .shr] → M.kind (.regArith bop w) = .quiet)
    (hK : ∀ w n, M.kind (.regConst w n) = .quiet)
    (p : Nat) {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) :
    Com.OpsQuiet M (redcMulBlk p a b) := by
  have hL : ∀ {Δ : Ctxt jasminDialect} (op : JasminBinOp) (x : Ctxt.Var Δ w64) (k : Nat),
      op ∈ [.add, .sub, .mul, .and, .shl, .shr] → Com.OpsQuiet M (binLitBlk op x k) :=
    fun _ _ _ hop => And.intro (hK _ _) (And.intro (hA _ _ hop) trivial)
  have hB : ∀ {Δ : Ctxt jasminDialect} (op : JasminBinOp) (x y : Ctxt.Var Δ w64),
      op ∈ [.add, .sub, .mul, .and, .shl, .shr] → Com.OpsQuiet M (binBlk op x y) :=
    fun _ _ _ hop => And.intro (hA _ _ hop) trivial
  have hR : ∀ {Δ : Ctxt jasminDialect} (t : Ctxt.Var Δ w64),
      Com.OpsQuiet M (redcBlk p (mu p) t) := fun _ =>
    opsQuiet_spliceCom M _ _ (hL _ _ _ (by decide)) <|
    opsQuiet_spliceCom M _ _ (hL _ _ _ (by decide)) <|
    opsQuiet_spliceCom M _ _ (hL _ _ _ (by decide)) <|
    opsQuiet_spliceCom M _ _ (hL _ _ _ (by decide)) <|
    opsQuiet_spliceCom M _ _ (hB _ _ _ (by decide)) (hL _ _ _ (by decide))
  have hC : Com.OpsQuiet M (csubBlk (Γ := (w64 :: w64 :: Γ)) p .here) :=
    And.intro (hK _ _) <| And.intro (hA _ _ (by decide)) <| And.intro (hK _ _) <|
    And.intro (hA _ _ (by decide)) <| And.intro (hK _ _) <| And.intro (hA _ _ (by decide)) <|
    And.intro (hA _ _ (by decide)) <| And.intro (hA _ _ (by decide)) trivial
  exact opsQuiet_spliceCom M _ _ (hB _ _ _ (by decide)) <|
    opsQuiet_spliceCom M _ _ (hR _) hC

end Quiet

/-- Under the certificate, the constants of the reduce-multiply block, `p`,
    `sext32 (mu p)`, `32`, `63` and `0`, are 32-bit immediates, and so is every constant
    `c · Rᵏ` of `ZMod p`, in particular every conversion constant `Rʲ`. -/
theorem redcConsts_imm32 {p : Nat} (h : mont32Cert p = true) :
    (∀ (k : ℤ) (c : ZMod p), (c * ↑(R32 h ^ k)).val < p ∧
      IsImm32 (c * ↑(R32 h ^ k)).val) ∧
    IsImm32 p ∧ IsImm32 (sext32 (mu p)) ∧ IsImm32 32 ∧ IsImm32 63 ∧ IsImm32 0 := by
  have := neZero_of_cert h
  obtain ⟨_, _, hp, _⟩ := mont32Cert_spec h
  refine ⟨fun k c => ?_, Or.inl hp, sext32_imm32 (mu_lt p), Or.inl (by norm_num),
    Or.inl (by norm_num), Or.inl (by norm_num)⟩
  have := ZMod.val_lt (c * ((R32 h ^ k : (ZMod p)ˣ) : ZMod p))
  exact ⟨this, Or.inl (by omega)⟩

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.MontDeg
