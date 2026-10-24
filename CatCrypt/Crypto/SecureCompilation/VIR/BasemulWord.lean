/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttWordSigned
public import CatCrypt.Crypto.SecureCompilation.VIR.RingDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.MergeComDenote

/-!
# Word lowering of the base multiplication and the pointwise product

The `ringDialect` op `basemul` denotes `RingDialect.basemulF`: after `L` layers of the
negacyclic NTT, the product within each block of length `2 ^ (logN - L)` modulo
`X ^ B − γ_c`. This module lowers it to `jasminDialect` words for one modulus at two
block lengths.

* `B = 2` (`L = logN − 1`, ML-KEM). Pair `c` holds `(a₀, a₁)`, `(b₀, b₁)` and its outputs
  are `a₀ b₀ + a₁ b₁ γ_c` and `a₀ b₁ + a₁ b₀`. The operands are signed `w`-bit words; the
  products are formed at `2 w` bits after sign extension. The second output is the sum of
  two products, reduced once. The first is `a₀ b₀ + R(a₁ b₁) · ζ_c` reduced once, where
  `R` is the signed Montgomery reduction and `ζ_c` is `γ_c · 2 ^ w` centred modulo `q`;
  the inner reduction keeps the product with the twiddle inside `2 w` bits.
* `B = 1` (`L = logN`, ML-DSA). Lane `i` is the reduction of the product `a_i b_i`.

The reduction is the signed Montgomery reduction `smont` of `NegacyclicNttWordSigned` on a
`2 w`-bit accumulator (`smontAccW`); `smontW` of the transform is its instance at a
product by a constant. Every output `z` satisfies `z · 2 ^ w ≡ spec (mod q)`.

The side conditions are the closed-form bounds `BasemulSched.Ok` and
`BasemulSched.PointwiseOk` on `ℕ`, decided by `decide +kernel` per instance. They bound
every intermediate value inside its lane and give the output bound `outB`, from which an
accumulation of several outputs before one reduction can start.

## Main definitions

* `smontAccW`: the signed Montgomery reduction of a `2 w`-bit word to `w` bits.
* `sextK`, `prodK`, `redK`: the sign extension, the product at `2 w` bits and the
  reduction as `jasminDialect` schedules in continuation form.
* `bm0K`, `bm1K`, `pwK`: the two outputs of a pair and the pointwise lane.
* `pairBlk`: the base multiplication of one pair, both outputs.
* `laneMapW`: the lane schedules `f 0, …, f (m − 1)` as one multi-return program.
* `basemulProgW`, `pointwiseProgW`: the lowerings on `2 · 2 ^ logN` input lanes (first
  operand, then second operand) and `2 ^ logN` output lanes.
* `BasemulSched`, `BasemulSched.Ok`, `BasemulSched.PointwiseOk`: the bounds certificate.
* `mlkemBasemul`, `mldsaPointwise`: the instances at `q = 3329`, `w = 16` and
  `q = 8380417`, `w = 32`.

## Main results

* `smontAccW_toInt`: on in-range operands the word reduction is `smont`.
* `blockMul_two`: the block product at block length `2`, written out.
* `bm0W_spec`, `bm1W_spec`, `pwW_spec`: each output is the reduction of its integer
  product sum and is at most `outB` in absolute value.
* `pairBlk_denote`: the pair block returns both outputs.
* `basemulProgW_denote`, `basemulProgW_basemulF`: every output word of `basemulProgW`
  is at most `outB` in absolute value and, times `2 ^ w`, is `blockMul 2` of the inputs,
  that is `basemulF` at `L = logN − 1`, modulo `q`.
* `pointwiseProgW_denote`, `pointwiseProgW_basemulF`: the same for `pointwiseProgW` and
  `basemulF` at `L = logN`.
* `mlkemBasemul_ok`, `mldsaPointwise_ok`: the instance certificates; the ML-KEM input
  bound `8 q` is the output bound of `nttProgSW mlkemNtt mlkemSigned`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id)
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral (Com.foldVarN
  Com.foldVarN_denote Com.denoteN)
open CatCrypt.Crypto.SecureCompilation.VIR.MergeComDenote (Com.concat2_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.RingDialect (Limbs basemulF basemulF_eq_mulF
  rowLanes)
open CatCrypt.Crypto.Lattice.BitReversalGeneric (bitrev)

/-! ## 1. The signed Montgomery reduction of a double-width word -/

/-- The signed Montgomery reduction of the `2 w`-bit word `a` to `w` bits:
`t = (a mod 2 ^ w) · qinv` in `w` bits, then `(a − sext t · q) >> w` truncated to `w`
bits. -/
def smontAccW (w q qinv : ℕ) (a : BitVec (2 * w)) : BitVec w :=
  (BitVec.sshiftRight (a - sextW (a.zeroExtend w * BitVec.ofNat w qinv)
    * BitVec.ofNat (2 * w) q) w).zeroExtend w

/-- The signed Montgomery multiply by a constant is the reduction of the product. -/
theorem smontW_eq_smontAccW (w q qinv z : ℕ) (x : BitVec w) :
    smontW w q qinv z x = smontAccW w q qinv (sextW x * BitVec.ofNat (2 * w) z) := rfl

/-- On in-range operands the word reduction is `smont`. -/
theorem smontAccW_toInt (w q qinv : ℕ) (a : BitVec (2 * w)) (hq : 2 * q < 2 ^ (2 * w))
    (ha : 2 * |a.toInt| + (2 ^ w : ℕ) * q < (2 ^ (2 * w) : ℕ))
    (hu : 2 * |smont w q qinv a.toInt| < (2 ^ w : ℕ)) :
    (smontAccW w q qinv a).toInt = smont w q qinv a.toInt := by
  have hRR : ((2 ^ (2 * w) : ℕ) : ℤ) = (2 ^ w : ℕ) * (2 ^ w : ℕ) := by
    push_cast; rw [two_mul, pow_add]
  have hR : (0 : ℤ) < (2 ^ w : ℕ) := by positivity
  have hq0 : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have hqv : (BitVec.ofNat (2 * w) q).toInt = q := by
    rw [BitVec.toInt_ofNat']
    exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)
  unfold smontAccW
  have hT : (sextW (a.zeroExtend w * BitVec.ofNat w qinv)).toInt
      = (a.toInt * qinv).bmod (2 ^ w) := by
    rw [sextW_toInt, BitVec.toInt_mul, toInt_zeroExtend_half, BitVec.toInt_ofNat',
      Int.bmod_mul_bmod, Int.mul_bmod_bmod]
  obtain ⟨ht1, ht2⟩ := bmod_two_pow_bounds w (a.toInt * qinv)
  generalize sextW (a.zeroExtend w * BitVec.ofNat w qinv) = tw at hT
  set t := (a.toInt * qinv).bmod (2 ^ w) with ht
  have hRq : ((2 ^ w : ℕ) : ℤ) * q < (2 ^ w : ℕ) * (2 ^ w : ℕ) := by
    rw [hRR] at ha; linarith [abs_nonneg a.toInt]
  have hTQ : (tw * BitVec.ofNat (2 * w) q).toInt = t * q := by
    rw [BitVec.toInt_mul, hT, hqv]
    apply Int.bmod_eq_of_le_mul_two <;> rw [hRR] <;>
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * t + (2 ^ w : ℕ) by linarith) hq0,
      mul_nonneg (show (0 : ℤ) ≤ (2 ^ w : ℕ) - 2 * t by linarith) hq0]
  have hD : (a - tw * BitVec.ofNat (2 * w) q).toInt = a.toInt - t * q := by
    rw [BitVec.toInt_sub, hTQ]
    apply Int.bmod_eq_of_le_mul_two <;>
    rcases abs_cases a.toInt with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hRR] at ha ⊢ <;> nlinarith
  have hS : (BitVec.sshiftRight (a - tw * BitVec.ofNat (2 * w) q) w).toInt
      = smont w q qinv a.toInt := by
    rw [BitVec.toInt_sshiftRight, hD, Int.shiftRight_eq_div_pow, smont, ht]
  rw [toInt_zeroExtend_half, hS]
  exact Int.bmod_eq_of_le_mul_two
    (by rcases abs_cases (smont w q qinv a.toInt) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
    (by rcases abs_cases (smont w q qinv a.toInt) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)

/-- The bound of `smont` from a bound `A2` on `2 |a|`. -/
theorem smont_abs_le (w q qinv : ℕ) (hN : (q * qinv) % 2 ^ w = 1) {a : ℤ} {A2 M : ℤ}
    (ha : 2 * |a| ≤ A2) (hM : A2 + (2 ^ w : ℕ) * q ≤ 2 * (2 ^ w : ℕ) * M) :
    |smont w q qinv a| ≤ M := by
  have hb := smont_bound w q qinv hN a
  have hR : (0 : ℤ) < (2 ^ w : ℕ) := by positivity
  have h : 2 * ((2 ^ w : ℕ) : ℤ) * |smont w q qinv a| ≤ 2 * ((2 ^ w : ℕ) : ℤ) * M := by
    linarith
  exact le_of_mul_le_mul_left h (by positivity)

/-- The word reduction under a bound `A2` on twice the operand and an output bound `M`
with `2 M < 2 ^ w`: it is `smont`, and `smont` is at most `M`. -/
theorem smontAccW_spec (w q qinv : ℕ) (hN : (q * qinv) % 2 ^ w = 1) (hq : 2 * q < 2 ^ (2 * w))
    (a : BitVec (2 * w)) {A2 M : ℤ} (ha : 2 * |a.toInt| ≤ A2)
    (hM : A2 + (2 ^ w : ℕ) * q ≤ 2 * (2 ^ w : ℕ) * M) (hMR : 2 * M < (2 ^ w : ℕ)) :
    (smontAccW w q qinv a).toInt = smont w q qinv a.toInt ∧
      |smont w q qinv a.toInt| ≤ M := by
  have hle := smont_abs_le w q qinv hN ha hM
  have hRR : ((2 ^ (2 * w) : ℕ) : ℤ) = (2 ^ w : ℕ) * (2 ^ w : ℕ) := by
    push_cast; rw [two_mul, pow_add]
  have hR : (0 : ℤ) < (2 ^ w : ℕ) := by positivity
  refine ⟨smontAccW_toInt w q qinv a hq ?_ (by linarith), hle⟩
  rw [hRR]
  nlinarith

/-! ## 2. Exact word arithmetic -/

theorem toInt_mul_exact {n : ℕ} (x y : BitVec n)
    (h : 2 * |x.toInt * y.toInt| < (2 ^ n : ℕ)) : (x * y).toInt = x.toInt * y.toInt := by
  rw [BitVec.toInt_mul]
  exact Int.bmod_eq_of_le_mul_two
    (by rcases abs_cases (x.toInt * y.toInt) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)
    (by rcases abs_cases (x.toInt * y.toInt) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)

theorem toInt_add_exact {n : ℕ} (x y : BitVec n)
    (h : 2 * |x.toInt + y.toInt| < (2 ^ n : ℕ)) : (x + y).toInt = x.toInt + y.toInt := by
  rw [BitVec.toInt_add]
  exact Int.bmod_eq_of_le_mul_two
    (by rcases abs_cases (x.toInt + y.toInt) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)
    (by rcases abs_cases (x.toInt + y.toInt) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)

theorem abs_mul_le_sq {x y : ℤ} {B : ℕ} (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |x * y| ≤ (B : ℤ) * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (Int.natCast_nonneg _)

/-! ## 3. The bounds certificate -/

/-- The parameters of the word base multiplication modulo `q` in signed `w`-bit words:
the Montgomery constant `qinv = q⁻¹ mod 2 ^ w`, the input bound, the bound of the inner
reduction `R(a₁ b₁)`, and the output bound, all in absolute value. -/
structure BasemulSched where
  /-- The word width. -/
  w : ℕ
  /-- The modulus. -/
  q : ℕ
  /-- The Montgomery constant `q⁻¹ mod 2 ^ w`. -/
  qinv : ℕ
  /-- Every input word is at most `inB` in absolute value. -/
  inB : ℕ
  /-- The inner reduction `R(a₁ b₁)` is at most `midB` in absolute value. -/
  midB : ℕ
  /-- Every output word is at most `outB` in absolute value. -/
  outB : ℕ

/-- The side condition of the base multiplication at block length `2`: the Montgomery
constant, the twiddle constants fit `2 w` bits, the inner reduction lies within `midB`,
and both outputs within `outB`, each below `2 ^ (w − 1)`. -/
def BasemulSched.Ok (S : BasemulSched) : Prop :=
  (S.q * S.qinv) % 2 ^ S.w = 1 ∧ 2 * S.q < 2 ^ (2 * S.w) ∧
    2 * (S.inB * S.inB) + 2 ^ S.w * S.q ≤ 2 * 2 ^ S.w * S.midB ∧
    2 * S.midB < 2 ^ S.w ∧
    2 * (S.inB * S.inB) + S.midB * S.q + 2 ^ S.w * S.q ≤ 2 * 2 ^ S.w * S.outB ∧
    4 * (S.inB * S.inB) + 2 ^ S.w * S.q ≤ 2 * 2 ^ S.w * S.outB ∧
    2 * S.outB < 2 ^ S.w

instance (S : BasemulSched) : Decidable S.Ok := by
  unfold BasemulSched.Ok; infer_instance

/-- The side condition of the pointwise product: the Montgomery constant and the output
within `outB`, below `2 ^ (w − 1)`; `midB` is not read. -/
def BasemulSched.PointwiseOk (S : BasemulSched) : Prop :=
  (S.q * S.qinv) % 2 ^ S.w = 1 ∧ 2 * S.q < 2 ^ (2 * S.w) ∧
    2 * (S.inB * S.inB) + 2 ^ S.w * S.q ≤ 2 * 2 ^ S.w * S.outB ∧
    2 * S.outB < 2 ^ S.w

instance (S : BasemulSched) : Decidable S.PointwiseOk := by
  unfold BasemulSched.PointwiseOk; infer_instance

/-! ## 4. The schedules -/

/-- `Rw (2 * w)`, the accumulator lane. -/
abbrev Rd (w : ℕ) : jasminDialect.Ty := Rw (2 * w)

/-- The context after a sign extension. -/
abbrev X3 (w : ℕ) (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := Rd w :: Rd w :: Rd w :: Γ

/-- The context after a product. -/
abbrev X7 (w : ℕ) (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := Rd w :: X3 w (X3 w Γ)

/-- The context after a reduction. -/
abbrev X11 (w : ℕ) (Γ : Ctxt jasminDialect) : Ctxt jasminDialect :=
  Rw w :: Rd w :: Rd w :: Rd w :: Rd w :: X3 w (Rw w :: Rw w :: Rw w :: Γ)

/-- A variable seen past a sign extension. -/
def up3 {w : ℕ} {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (v : Var Γ t) :
    Var (X3 w Γ) t := .there (.there (.there v))

/-- A variable seen past a product. -/
def up7 {w : ℕ} {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (v : Var Γ t) :
    Var (X7 w Γ) t := .there (up3 (w := w) (up3 (w := w) v))

/-- A variable seen past a reduction. -/
def up11 {w : ℕ} {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (v : Var Γ t) :
    Var (X11 w Γ) t :=
  .there (.there (.there (.there (.there (up3 (w := w) (.there (.there (.there v))))))))

/-- Sign extension of `v` from `w` to `2 w` bits (`sextW`), then `k`. -/
def sextK {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (w : ℕ) (v : Var Γ (Rw w))
    (k : Com jasminDialect (X3 w Γ) t) : Com jasminDialect Γ t :=
  .var (castE w (2 * w) v) <| .var (shlE (2 * w) w .here) <| .var (sarE (2 * w) w .here) k

/-- The product of the sign extensions of `u` and `v` at `2 w` bits, then `k`. -/
def prodK {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (w : ℕ) (u v : Var Γ (Rw w))
    (k : Com jasminDialect (X7 w Γ) t) : Com jasminDialect Γ t :=
  sextK w u <| sextK w (up3 v) <| .var (binE .mul (2 * w) (up3 .here) .here) k

/-- The signed Montgomery reduction of the `2 w`-bit variable `a` (`smontAccW`), then
`k`. -/
def redK {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (w q qinv : ℕ) (a : Var Γ (Rd w))
    (k : Com jasminDialect (X11 w Γ) t) : Com jasminDialect Γ t :=
  .var (castE (2 * w) w a) <|
  .var (constE w qinv) <|
  .var (binE .mul w (.there .here) .here) <|
  sextK w .here <|
  .var (constE (2 * w) q) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (binE .sub (2 * w) (.there (.there (up3 (w := w) (.there (.there (.there a)))))) .here) <|
  .var (sarE (2 * w) w .here) <|
  .var (castE (2 * w) w .here) k

/-- The valuation after `sextK w v`. -/
def sextVal {Γ : Ctxt jasminDialect} (w : ℕ) (v : Var Γ (Rw w)) (V : Valuation Γ) :
    Valuation (X3 w Γ) :=
  let V1 := V.extend ((castE w (2 * w) v).denote V)
  let V2 := V1.extend ((shlE (2 * w) w .here).denote V1)
  V2.extend ((sarE (2 * w) w .here).denote V2)

theorem sextK_denote {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (w : ℕ)
    (v : Var Γ (Rw w)) (k : Com jasminDialect (X3 w Γ) t) (V : Valuation Γ) :
    (sextK w v k).denote V = k.denote (sextVal w v V) := rfl

/-- The valuation after `prodK w u v`. -/
def prodVal {Γ : Ctxt jasminDialect} (w : ℕ) (u v : Var Γ (Rw w)) (V : Valuation Γ) :
    Valuation (X7 w Γ) :=
  let V6 := sextVal w (up3 v) (sextVal w u V)
  V6.extend ((binE .mul (2 * w) (up3 .here) .here).denote V6)

theorem prodK_denote {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (w : ℕ)
    (u v : Var Γ (Rw w)) (k : Com jasminDialect (X7 w Γ) t) (V : Valuation Γ) :
    (prodK w u v k).denote V = k.denote (prodVal w u v V) := rfl

/-- The valuation after `redK w q qinv a`. -/
def redVal {Γ : Ctxt jasminDialect} (w q qinv : ℕ) (a : Var Γ (Rd w)) (V : Valuation Γ) :
    Valuation (X11 w Γ) :=
  let V1 := V.extend ((castE (2 * w) w a).denote V)
  let V2 := V1.extend ((constE w qinv).denote V1)
  let V3 := V2.extend ((binE .mul w (.there .here) .here).denote V2)
  let V6 := sextVal w .here V3
  let V7 := V6.extend ((constE (2 * w) q).denote V6)
  let V8 := V7.extend ((binE .mul (2 * w) (.there .here) .here).denote V7)
  let V9 := V8.extend ((binE .sub (2 * w) (.there (.there (up3 (w := w)
    (.there (.there (.there a)))))) .here).denote V8)
  let V10 := V9.extend ((sarE (2 * w) w .here).denote V9)
  V10.extend ((castE (2 * w) w .here).denote V10)

theorem redK_denote {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (w q qinv : ℕ)
    (a : Var Γ (Rd w)) (k : Com jasminDialect (X11 w Γ) t) (V : Valuation Γ) :
    (redK w q qinv a k).denote V = k.denote (redVal w q qinv a V) := rfl

/-- The tail of the first output: `R(p₀ + sext r · z)`. -/
def bmTail {Γ : Ctxt jasminDialect} (w q qinv z : ℕ) (p0 : Var Γ (Rd w)) (r : Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  sextK w r <|
  .var (constE (2 * w) z) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (binE .add (2 * w) (.there (.there (up3 p0))) .here) <|
  redK w q qinv .here <|
  .ret .here

theorem bmTail_denote {Γ : Ctxt jasminDialect} (w q qinv z : ℕ) (p0 : Var Γ (Rd w))
    (r : Var Γ (Rw w)) (V : Valuation Γ) :
    (bmTail w q qinv z p0 r).denote V
      = smontAccW w q qinv ((show BitVec (2 * w) from p0.lookup V)
          + sextW (show BitVec w from r.lookup V) * BitVec.ofNat (2 * w) z) := by
  simp only [smontAccW, sextW_eq_masked]; rfl

/-- The first output of a pair: `R(a₀ b₀ + sext R(a₁ b₁) · z)`, `z` a `2 w`-bit
constant. -/
def bm0K {Γ : Ctxt jasminDialect} (w q qinv z : ℕ) (a0 a1 b0 b1 : Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  prodK w a0 b0 <|
  prodK w (up7 a1) (up7 b1) <|
  redK w q qinv .here <|
  bmTail w q qinv z (up11 (up7 .here)) .here

/-- The second output of a pair: `R(a₀ b₁ + a₁ b₀)`. -/
def bm1K {Γ : Ctxt jasminDialect} (w q qinv : ℕ) (a0 a1 b0 b1 : Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  prodK w a0 b1 <|
  prodK w (up7 a1) (up7 b0) <|
  .var (binE .add (2 * w) (up7 .here) .here) <|
  redK w q qinv .here <|
  .ret .here

/-- The pointwise lane: `R(a b)`. -/
def pwK {Γ : Ctxt jasminDialect} (w q qinv : ℕ) (a b : Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  prodK w a b <| redK w q qinv .here <| .ret .here

/-- The word semantics of `bm0K`. -/
def bm0W (w q qinv z : ℕ) (a0 a1 b0 b1 : BitVec w) : BitVec w :=
  smontAccW w q qinv (sextW a0 * sextW b0
    + sextW (smontAccW w q qinv (sextW a1 * sextW b1)) * BitVec.ofNat (2 * w) z)

/-- The word semantics of `bm1K`. -/
def bm1W (w q qinv : ℕ) (a0 a1 b0 b1 : BitVec w) : BitVec w :=
  smontAccW w q qinv (sextW a0 * sextW b1 + sextW a1 * sextW b0)

/-- The word semantics of `pwK`. -/
def pwW (w q qinv : ℕ) (a b : BitVec w) : BitVec w :=
  smontAccW w q qinv (sextW a * sextW b)

theorem bm0K_denote {Γ : Ctxt jasminDialect} (w q qinv z : ℕ) (a0 a1 b0 b1 : Var Γ (Rw w))
    (V : Valuation Γ) :
    (bm0K w q qinv z a0 a1 b0 b1).denote V
      = bm0W w q qinv z (show BitVec w from a0.lookup V) (show BitVec w from a1.lookup V)
          (show BitVec w from b0.lookup V) (show BitVec w from b1.lookup V) := by
  rw [bm0K, prodK_denote, prodK_denote, redK_denote, bmTail_denote]
  simp only [bm0W, smontAccW, sextW_eq_masked]; rfl

theorem bm1K_denote {Γ : Ctxt jasminDialect} (w q qinv : ℕ) (a0 a1 b0 b1 : Var Γ (Rw w))
    (V : Valuation Γ) :
    (bm1K w q qinv a0 a1 b0 b1).denote V
      = bm1W w q qinv (show BitVec w from a0.lookup V) (show BitVec w from a1.lookup V)
          (show BitVec w from b0.lookup V) (show BitVec w from b1.lookup V) := by
  simp only [bm1W, smontAccW, sextW_eq_masked]; rfl

theorem pwK_denote {Γ : Ctxt jasminDialect} (w q qinv : ℕ) (a b : Var Γ (Rw w))
    (V : Valuation Γ) :
    (pwK w q qinv a b).denote V
      = pwW w q qinv (show BitVec w from a.lookup V) (show BitVec w from b.lookup V) := by
  simp only [pwW, smontAccW, sextW_eq_masked]; rfl

/-! ## 5. The word theorems -/

section Spec

variable (S : BasemulSched)

/-- `2 ^ (2 w)` as the square of the radix. -/
theorem pow_two_mul_cast (w : ℕ) :
    ((2 ^ (2 * w) : ℕ) : ℤ) = (2 ^ w : ℕ) * (2 ^ w : ℕ) := by
  push_cast; rw [two_mul, pow_add]

/-- **The second output.** On inputs at most `inB`, `bm1W` is the reduction of
`a₀ b₁ + a₁ b₀`, at most `outB`. -/
theorem bm1W_spec (hS : S.Ok) (a0 a1 b0 b1 : BitVec S.w) (h0 : |a0.toInt| ≤ S.inB)
    (h1 : |a1.toInt| ≤ S.inB) (h2 : |b0.toInt| ≤ S.inB) (h3 : |b1.toInt| ≤ S.inB) :
    (bm1W S.w S.q S.qinv a0 a1 b0 b1).toInt
        = smont S.w S.q S.qinv (a0.toInt * b1.toInt + a1.toInt * b0.toInt) ∧
      |smont S.w S.q S.qinv (a0.toInt * b1.toInt + a1.toInt * b0.toInt)| ≤ S.outB := by
  obtain ⟨hN, hq, -, -, -, h6, h7⟩ := hS
  have k6 : (4 * ((S.inB : ℤ) * S.inB) + ((2 ^ S.w : ℕ) : ℤ) * S.q
      ≤ 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB) := by exact_mod_cast h6
  have k7 : (2 * (S.outB : ℤ) < ((2 ^ S.w : ℕ) : ℤ)) := by exact_mod_cast h7
  have hRR := pow_two_mul_cast S.w
  have hR : (0 : ℤ) < (2 ^ S.w : ℕ) := by positivity
  have hq0 : (0 : ℤ) ≤ S.q := Int.natCast_nonneg _
  have hfit : 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB < ((2 ^ (2 * S.w) : ℕ) : ℤ) := by
    rw [hRR]; have := mul_lt_mul_of_pos_left k7 hR; linarith
  have p1 := abs_mul_le_sq h0 h3
  have p2 := abs_mul_le_sq h1 h2
  have e1 : (sextW a0 * sextW b1).toInt = a0.toInt * b1.toInt := by
    rw [toInt_mul_exact _ _ (by rw [sextW_toInt, sextW_toInt]; nlinarith), sextW_toInt,
      sextW_toInt]
  have e2 : (sextW a1 * sextW b0).toInt = a1.toInt * b0.toInt := by
    rw [toInt_mul_exact _ _ (by rw [sextW_toInt, sextW_toInt]; nlinarith), sextW_toInt,
      sextW_toInt]
  have hs : 2 * |a0.toInt * b1.toInt + a1.toInt * b0.toInt| ≤ 4 * ((S.inB : ℤ) * S.inB) := by
    have := abs_add_le (a0.toInt * b1.toInt) (a1.toInt * b0.toInt)
    linarith
  have e3 : (sextW a0 * sextW b1 + sextW a1 * sextW b0).toInt
      = a0.toInt * b1.toInt + a1.toInt * b0.toInt := by
    rw [toInt_add_exact _ _ (by rw [e1, e2]; nlinarith), e1, e2]
  have := smontAccW_spec S.w S.q S.qinv hN hq (sextW a0 * sextW b1 + sextW a1 * sextW b0)
    (A2 := 4 * ((S.inB : ℤ) * S.inB)) (M := S.outB) (by rw [e3]; exact hs) k6 k7
  rw [e3] at this
  exact this

/-- **The first output.** On inputs at most `inB` and a twiddle constant reading `ζ`
with `2 |ζ| ≤ q`, `bm0W` is `R(a₀ b₀ + R(a₁ b₁) · ζ)`, at most `outB`. -/
theorem bm0W_spec (hS : S.Ok) (z : ℕ) (ζ : ℤ) (hz : (BitVec.ofNat (2 * S.w) z).toInt = ζ)
    (hζ : 2 * |ζ| ≤ S.q) (a0 a1 b0 b1 : BitVec S.w) (h0 : |a0.toInt| ≤ S.inB)
    (h1 : |a1.toInt| ≤ S.inB) (h2 : |b0.toInt| ≤ S.inB) (h3 : |b1.toInt| ≤ S.inB) :
    (bm0W S.w S.q S.qinv z a0 a1 b0 b1).toInt
        = smont S.w S.q S.qinv (a0.toInt * b0.toInt
            + smont S.w S.q S.qinv (a1.toInt * b1.toInt) * ζ) ∧
      |smont S.w S.q S.qinv (a0.toInt * b0.toInt
            + smont S.w S.q S.qinv (a1.toInt * b1.toInt) * ζ)| ≤ S.outB := by
  obtain ⟨hN, hq, h3c, h4, h5, -, h7⟩ := hS
  have k3 : (2 * ((S.inB : ℤ) * S.inB) + ((2 ^ S.w : ℕ) : ℤ) * S.q
      ≤ 2 * ((2 ^ S.w : ℕ) : ℤ) * S.midB) := by exact_mod_cast h3c
  have k4 : (2 * (S.midB : ℤ) < ((2 ^ S.w : ℕ) : ℤ)) := by exact_mod_cast h4
  have k5 : (2 * ((S.inB : ℤ) * S.inB) + (S.midB : ℤ) * S.q + ((2 ^ S.w : ℕ) : ℤ) * S.q
      ≤ 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB) := by exact_mod_cast h5
  have k7 : (2 * (S.outB : ℤ) < ((2 ^ S.w : ℕ) : ℤ)) := by exact_mod_cast h7
  have hRR := pow_two_mul_cast S.w
  have hR : (0 : ℤ) < (2 ^ S.w : ℕ) := by positivity
  have hq0 : (0 : ℤ) ≤ S.q := Int.natCast_nonneg _
  have hm0 : (0 : ℤ) ≤ S.midB := Int.natCast_nonneg _
  have hBB : (0 : ℤ) ≤ (S.inB : ℤ) * S.inB := by positivity
  have hRq : (0 : ℤ) ≤ ((2 ^ S.w : ℕ) : ℤ) * S.q := by positivity
  have hMq : (0 : ℤ) ≤ (S.midB : ℤ) * S.q := by positivity
  have hfit : 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB < ((2 ^ (2 * S.w) : ℕ) : ℤ) := by
    rw [hRR]; have := mul_lt_mul_of_pos_left k7 hR; linarith
  have p0 := abs_mul_le_sq h0 h2
  have p1 := abs_mul_le_sq h1 h3
  have e0 : (sextW a0 * sextW b0).toInt = a0.toInt * b0.toInt := by
    rw [toInt_mul_exact _ _ (by rw [sextW_toInt, sextW_toInt]; linarith), sextW_toInt,
      sextW_toInt]
  have e1 : (sextW a1 * sextW b1).toInt = a1.toInt * b1.toInt := by
    rw [toInt_mul_exact _ _ (by rw [sextW_toInt, sextW_toInt]; linarith), sextW_toInt,
      sextW_toInt]
  obtain ⟨er, hr⟩ := smontAccW_spec S.w S.q S.qinv hN hq (sextW a1 * sextW b1)
    (A2 := 2 * ((S.inB : ℤ) * S.inB)) (M := S.midB)
    (by rw [e1]; linarith) k3 k4
  rw [e1] at er hr
  set r := smont S.w S.q S.qinv (a1.toInt * b1.toInt) with hrdef
  have hrz : 2 * |r * ζ| ≤ (S.midB : ℤ) * S.q := by
    rw [abs_mul]
    have := mul_le_mul hr hζ (by positivity) hm0
    linarith
  have e2 : (sextW (smontAccW S.w S.q S.qinv (sextW a1 * sextW b1))
      * BitVec.ofNat (2 * S.w) z).toInt = r * ζ := by
    rw [toInt_mul_exact _ _ (by rw [sextW_toInt, er, hz]; linarith), sextW_toInt, er, hz]
  have hs : 2 * |a0.toInt * b0.toInt + r * ζ|
      ≤ 2 * ((S.inB : ℤ) * S.inB) + (S.midB : ℤ) * S.q := by
    have := abs_add_le (a0.toInt * b0.toInt) (r * ζ)
    linarith
  have e3 : (sextW a0 * sextW b0 + sextW (smontAccW S.w S.q S.qinv (sextW a1 * sextW b1))
      * BitVec.ofNat (2 * S.w) z).toInt = a0.toInt * b0.toInt + r * ζ := by
    rw [toInt_add_exact _ _ (by rw [e0, e2]; linarith), e0, e2]
  have := smontAccW_spec S.w S.q S.qinv hN hq _
    (A2 := 2 * ((S.inB : ℤ) * S.inB) + (S.midB : ℤ) * S.q) (M := S.outB)
    (by rw [e3]; exact hs) (by linarith) k7
  rw [e3] at this
  exact this

/-- **The pointwise lane.** On inputs at most `inB`, `pwW` is the reduction of `a b`, at
most `outB`. -/
theorem pwW_spec (hS : S.PointwiseOk) (a b : BitVec S.w) (ha : |a.toInt| ≤ S.inB)
    (hb : |b.toInt| ≤ S.inB) :
    (pwW S.w S.q S.qinv a b).toInt = smont S.w S.q S.qinv (a.toInt * b.toInt) ∧
      |smont S.w S.q S.qinv (a.toInt * b.toInt)| ≤ S.outB := by
  obtain ⟨hN, hq, h3, h4⟩ := hS
  have k3 : (2 * ((S.inB : ℤ) * S.inB) + ((2 ^ S.w : ℕ) : ℤ) * S.q
      ≤ 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB) := by exact_mod_cast h3
  have k4 : (2 * (S.outB : ℤ) < ((2 ^ S.w : ℕ) : ℤ)) := by exact_mod_cast h4
  have hRR := pow_two_mul_cast S.w
  have hR : (0 : ℤ) < (2 ^ S.w : ℕ) := by positivity
  have hq0 : (0 : ℤ) ≤ S.q := Int.natCast_nonneg _
  have hfit : 2 * ((2 ^ S.w : ℕ) : ℤ) * S.outB < ((2 ^ (2 * S.w) : ℕ) : ℤ) := by
    rw [hRR]; have := mul_lt_mul_of_pos_left k4 hR; linarith
  have p := abs_mul_le_sq ha hb
  have e : (sextW a * sextW b).toInt = a.toInt * b.toInt := by
    rw [toInt_mul_exact _ _ (by rw [sextW_toInt, sextW_toInt]; nlinarith), sextW_toInt,
      sextW_toInt]
  have := smontAccW_spec S.w S.q S.qinv hN hq (sextW a * sextW b)
    (A2 := 2 * ((S.inB : ℤ) * S.inB)) (M := S.outB) (by rw [e]; linarith) k3 k4
  rw [e] at this
  exact this

end Spec

/-! ## 6. The pair block -/

/-- The four-input context of a pair: `a₀`, `a₁`, `b₀`, `b₁`. -/
abbrev C4 (w : ℕ) : Ctxt jasminDialect := [Rw w, Rw w, Rw w, Rw w]

/-- The base multiplication of one pair with twiddle constant `z`: both outputs. -/
def pairBlk (w q qinv z : ℕ) : MultiReturnCom jasminDialect (C4 w) [Rw w, Rw w] :=
  Com.concat2 (bm0K w q qinv z .here (.there .here) (.there (.there .here))
      (.there (.there (.there .here))))
    (bm1K w q qinv .here (.there .here) (.there (.there .here))
      (.there (.there (.there .here))))

theorem pairBlk_denote (w q qinv z : ℕ) (a0 a1 b0 b1 : BitVec w) :
    (pairBlk w q qinv z).denote (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))
      = .cons (bm0W w q qinv z a0 a1 b0 b1) (.cons (bm1W w q qinv a0 a1 b0 b1) .nil) := by
  rw [pairBlk, Com.concat2_denote, bm0K_denote, bm1K_denote]
  rfl

/-! ## 7. The lowerings on lanes -/

/-- The lane schedules `f 0, …, f (m − 1)` as one multi-return program. -/
def laneMapW {Γ : Ctxt jasminDialect} {τ : jasminDialect.Ty} (m : ℕ)
    (f : ℕ → Com jasminDialect Γ τ) : MultiReturnCom jasminDialect Γ (List.replicate m τ) :=
  Com.foldVarN m f (Ctxt.Hom.id _) (fun {_} _ vs => .ret vs)

theorem laneMapW_denote {Γ : Ctxt jasminDialect} {τ : jasminDialect.Ty} (m : ℕ)
    (f : ℕ → Com jasminDialect Γ τ) (V : Valuation Γ) :
    (laneMapW m f).denote V = Com.denoteN m f V := by
  refine Com.foldVarN_denote m f (Ctxt.Hom.id _) V _ _ ?_
  intro Γ' h vs V' _ hvs
  show MultiReturnCom.lookupVars vs V' = _
  rw [hvs]
  exact congrArg _ (pullV_id V)

/-- The Montgomery twiddle of pair `c` after `L` layers: the balanced residue of
`ψ ^ (2 · BitRev_L c + 1) · 2 ^ w` modulo `q`. -/
def zetaM (w q psi L c : ℕ) : ℤ := ((psi ^ (2 * bitrev L c + 1) * 2 ^ w : ℕ) : ℤ).bmod q

theorem zetaM_abs (w q psi L c : ℕ) (hq : 0 < q) : 2 * |zetaM w q psi L c| ≤ q :=
  two_abs_bmod_le _ q hq

theorem zetaM_cast (w q psi L c : ℕ) :
    ((zetaM w q psi L c : ℤ) : ZMod q)
      = blockRoot (psi : ZMod q) L c * 2 ^ w := by
  rw [zetaM, bmod_cast, blockRoot]
  push_cast
  rfl

/-- Output lane `i` of the base multiplication on `n` input lanes, the first operand at
lanes `0, …, N − 1` and the second at `N, …, 2 N − 1`: the first output of pair `i / 2`
for even `i`, the second for odd `i`. -/
def bmLane (S : BasemulSched) (psi L N : ℕ) :
    (n : ℕ) → ℕ → Com jasminDialect (Ctxs S.w n) (Rw S.w)
  | 0, _ => .var (constE S.w 0) (.ret .here)
  | n + 1, i =>
    if i % 2 = 0 then
      bm0K S.w S.q S.qinv (cEnc S.w (zetaM S.w S.q psi L (i / 2)))
        (laneVarG (Rw S.w) n i) (laneVarG (Rw S.w) n (i + 1))
        (laneVarG (Rw S.w) n (N + i)) (laneVarG (Rw S.w) n (N + (i + 1)))
    else
      bm1K S.w S.q S.qinv
        (laneVarG (Rw S.w) n (i - 1)) (laneVarG (Rw S.w) n i)
        (laneVarG (Rw S.w) n (N + (i - 1))) (laneVarG (Rw S.w) n (N + i))

/-- The base multiplication at block length `2` on `2 · 2 ^ logN` input lanes. -/
def basemulProgW (S : BasemulSched) (psi logN : ℕ) :
    MultiReturnCom jasminDialect (Ctxs S.w (2 * 2 ^ logN)) (Ctxs S.w (2 ^ logN)) :=
  laneMapW (2 ^ logN) (bmLane S psi (logN - 1) (2 ^ logN) (2 * 2 ^ logN))

/-- Output lane `i` of the pointwise product on `n` input lanes. -/
def pwLane (S : BasemulSched) (N : ℕ) : (n : ℕ) → ℕ → Com jasminDialect (Ctxs S.w n) (Rw S.w)
  | 0, _ => .var (constE S.w 0) (.ret .here)
  | n + 1, i => pwK S.w S.q S.qinv (laneVarG (Rw S.w) n i) (laneVarG (Rw S.w) n (N + i))

/-- The pointwise product on `2 · 2 ^ logN` input lanes. -/
def pointwiseProgW (S : BasemulSched) (logN : ℕ) :
    MultiReturnCom jasminDialect (Ctxs S.w (2 * 2 ^ logN)) (Ctxs S.w (2 ^ logN)) :=
  laneMapW (2 ^ logN) (pwLane S (2 ^ logN) (2 * 2 ^ logN))

/-- The block product at block length `2`, written out. -/
theorem blockMul_two {R : Type*} [CommRing R] (γ : ℕ → R) (a b : ℕ → R) (i : ℕ) :
    blockMul 2 γ a b i = if i % 2 = 0 then a i * b i + a (i + 1) * b (i + 1) * γ (i / 2)
      else a (i - 1) * b i + a i * b (i - 1) := by
  unfold blockMul
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have e : i / 2 * 2 = i := by omega
    simp [h, e]
  · have e : i / 2 * 2 = i - 1 := by omega
    have e' : i - 1 + 1 = i := by omega
    simp [h, e, e']

/-- **The base multiplication on words.** On input words at most `inB` in absolute
value, every output word of `basemulProgW` is at most `outB` in absolute value and, times
`2 ^ w`, is `blockMul 2` at the block roots of `ψ` of the two operands, modulo `q`. -/
theorem basemulProgW_denote (S : BasemulSched) (hS : S.Ok) (psi logN : ℕ) (hlog : 0 < logN)
    (g : ℕ → BitVec S.w) (hg : ∀ j, j < 2 * 2 ^ logN → |(g j).toInt| ≤ S.inB) (i : ℕ)
    (hi : i < 2 ^ logN) :
    |(hvGetG (Rw S.w) (0 : BitVec S.w) ((basemulProgW S psi logN).denote
        (lanesVal (Rw S.w) g (2 * 2 ^ logN) 0)) i).toInt| ≤ S.outB ∧
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((basemulProgW S psi logN).denote
        (lanesVal (Rw S.w) g (2 * 2 ^ logN) 0)) i).toInt : ℤ) : ZMod S.q)
        * ((2 ^ S.w : ℕ) : ZMod S.q)
      = blockMul 2 (blockRoot (psi : ZMod S.q) (logN - 1))
          (fun j => ((g j).toInt : ZMod S.q)) (fun j => ((g (2 ^ logN + j)).toInt : ZMod S.q))
          i := by
  have hN2 : 2 ^ logN = 2 * 2 ^ (logN - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hqpos : 0 < S.q := by
    obtain ⟨hN, -⟩ := hS
    rcases Nat.eq_zero_or_pos S.q with h | h
    · rw [h, zero_mul, Nat.zero_mod] at hN; exact absurd hN (by norm_num)
    · exact h
  obtain ⟨n, hn⟩ : ∃ n, 2 * 2 ^ logN = n + 1 := ⟨2 * 2 ^ logN - 1, by omega⟩
  rw [basemulProgW, laneMapW_denote, hvGetG_denoteN _ _ _ _ _ _ hi, blockMul_two]
  revert hg
  rw [hn]
  intro hg
  have hlk : ∀ j, j ≤ n → (laneVarG (Rw S.w) n j).lookup (lanesVal (Rw S.w) g (n + 1) 0)
      = g j := fun j hj => by
    rw [laneVarG_lookup (Rw S.w) g n j 0 hj, Nat.zero_add]
  have hgb : ∀ j, j ≤ n → |(g j).toInt| ≤ S.inB := fun j hj => hg j (by omega)
  rw [bmLane]
  split
  · next he =>
    rw [bm0K_denote]
    simp only [hlk i (by omega), hlk (i + 1) (by omega), hlk (2 ^ logN + i) (by omega),
      hlk (2 ^ logN + (i + 1)) (by omega)]
    have hS' := hS
    obtain ⟨-, hq, -⟩ := hS'
    obtain ⟨e, hb⟩ := bm0W_spec S hS _ _ (cEnc_toInt S.w S.q _
        (zetaM_abs S.w S.q psi (logN - 1) (i / 2) hqpos) hq)
      (zetaM_abs S.w S.q psi (logN - 1) (i / 2) hqpos) _ _ _ _
      (hgb i (by omega)) (hgb (i + 1) (by omega)) (hgb (2 ^ logN + i) (by omega))
      (hgb (2 ^ logN + (i + 1)) (by omega))
    rw [e]
    refine ⟨hb, ?_⟩
    have hr := smont_mul_radix S.w S.q S.qinv hS.1
      ((g (i + 1)).toInt * (g (2 ^ logN + (i + 1))).toInt)
    have ho := smont_mul_radix S.w S.q S.qinv hS.1
      ((g i).toInt * (g (2 ^ logN + i)).toInt
        + smont S.w S.q S.qinv ((g (i + 1)).toInt * (g (2 ^ logN + (i + 1))).toInt)
          * zetaM S.w S.q psi (logN - 1) (i / 2))
    rw [ho]
    push_cast at hr ⊢
    rw [zetaM_cast]
    simp only [← Nat.add_assoc] at hr ⊢
    linear_combination (blockRoot (psi : ZMod S.q) (logN - 1) (i / 2)) * hr
  · next ho =>
    rw [bm1K_denote]
    have hi1 : 1 ≤ i := by omega
    simp only [hlk (i - 1) (by omega), hlk i (by omega), hlk (2 ^ logN + (i - 1)) (by omega),
      hlk (2 ^ logN + i) (by omega)]
    obtain ⟨e, hb⟩ := bm1W_spec S hS _ _ _ _
      (hgb (i - 1) (by omega)) (hgb i (by omega)) (hgb (2 ^ logN + (i - 1)) (by omega))
      (hgb (2 ^ logN + i) (by omega))
    rw [e]
    refine ⟨hb, ?_⟩
    rw [smont_mul_radix S.w S.q S.qinv hS.1]
    push_cast
    ring

/-- **The pointwise product on words.** On input words at most `inB` in absolute value,
every output word of `pointwiseProgW` is at most `outB` in absolute value and, times
`2 ^ w`, is the product of the two operands modulo `q`. -/
theorem pointwiseProgW_denote (S : BasemulSched) (hS : S.PointwiseOk) (logN : ℕ)
    (g : ℕ → BitVec S.w) (hg : ∀ j, j < 2 * 2 ^ logN → |(g j).toInt| ≤ S.inB) (i : ℕ)
    (hi : i < 2 ^ logN) :
    |(hvGetG (Rw S.w) (0 : BitVec S.w) ((pointwiseProgW S logN).denote
        (lanesVal (Rw S.w) g (2 * 2 ^ logN) 0)) i).toInt| ≤ S.outB ∧
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((pointwiseProgW S logN).denote
        (lanesVal (Rw S.w) g (2 * 2 ^ logN) 0)) i).toInt : ℤ) : ZMod S.q)
        * ((2 ^ S.w : ℕ) : ZMod S.q)
      = ((g i).toInt : ZMod S.q) * ((g (2 ^ logN + i)).toInt : ZMod S.q) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * 2 ^ logN = n + 1 := ⟨2 * 2 ^ logN - 1, by
    have := Nat.two_pow_pos logN; omega⟩
  rw [pointwiseProgW, laneMapW_denote, hvGetG_denoteN _ _ _ _ _ _ hi]
  revert hg
  rw [hn]
  intro hg
  rw [pwLane, pwK_denote, laneVarG_lookup (Rw S.w) g n i 0 (by omega),
    laneVarG_lookup (Rw S.w) g n (2 ^ logN + i) 0 (by omega), Nat.zero_add, Nat.zero_add]
  obtain ⟨e, hb⟩ := pwW_spec S hS _ _ (hg i (by omega)) (hg (2 ^ logN + i) (by omega))
  rw [e]
  refine ⟨hb, ?_⟩
  rw [smont_mul_radix S.w S.q S.qinv hS.1]
  push_cast
  ring

/-! ## 8. The ring-level statements -/

/-- **`basemul` at `L = logN − 1` on words.** When the residues `x`, `y` of one modulus
are the readings of the first and second operand lanes, every output word of
`basemulProgW`, times `2 ^ w`, is `basemulF` at `L = logN − 1`. -/
theorem basemulProgW_basemulF (S : BasemulSched) (hS : S.Ok) (psi logN : ℕ) (hlog : 0 < logN)
    (g : ℕ → BitVec S.w) (hg : ∀ j, j < 2 * 2 ^ logN → |(g j).toInt| ≤ S.inB)
    (x y : Limbs [S.q] (2 ^ logN))
    (hx : ∀ j (hj : j < 2 ^ logN), x ⟨0, by simp⟩ ⟨j, hj⟩ = ((g j).toInt : ZMod S.q))
    (hy : ∀ j (hj : j < 2 ^ logN), y ⟨0, by simp⟩ ⟨j, hj⟩
      = ((g (2 ^ logN + j)).toInt : ZMod S.q))
    (i : ℕ) (hi : i < 2 ^ logN) :
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((basemulProgW S psi logN).denote
        (lanesVal (Rw S.w) g (2 * 2 ^ logN) 0)) i).toInt : ℤ) : ZMod S.q)
        * ((2 ^ S.w : ℕ) : ZMod S.q)
      = basemulF logN (logN - 1) [psi] x y ⟨0, by simp⟩ ⟨i, hi⟩ := by
  rw [(basemulProgW_denote S hS psi logN hlog g hg i hi).2]
  have hB : 2 ^ (logN - (logN - 1)) = 2 := by
    rw [show logN - (logN - 1) = 1 by omega, pow_one]
  have hK : 2 ^ logN = 2 ^ (logN - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  unfold basemulF
  simp only [List.getD_cons_zero]
  rw [hB]
  refine blockMul_congr 2 (2 ^ (logN - 1)) (by norm_num) _ _ _ _ _ ?_ ?_ i (by omega)
  · intro j hj
    simp only [rowLanes, dite_eq_left (show j < 2 ^ logN by omega)]
    exact (hx j (by omega)).symm
  · intro j hj
    simp only [rowLanes, dite_eq_left (show j < 2 ^ logN by omega)]
    exact (hy j (by omega)).symm

/-- **`basemul` at `L = logN` on words.** When the residues `x`, `y` of one modulus are
the readings of the first and second operand lanes, every output word of
`pointwiseProgW`, times `2 ^ w`, is `basemulF` at `L = logN`. -/
theorem pointwiseProgW_basemulF (S : BasemulSched) (hS : S.PointwiseOk) (logN : ℕ)
    (psis : List ℕ) (g : ℕ → BitVec S.w) (hg : ∀ j, j < 2 * 2 ^ logN → |(g j).toInt| ≤ S.inB)
    (x y : Limbs [S.q] (2 ^ logN))
    (hx : ∀ j (hj : j < 2 ^ logN), x ⟨0, by simp⟩ ⟨j, hj⟩ = ((g j).toInt : ZMod S.q))
    (hy : ∀ j (hj : j < 2 ^ logN), y ⟨0, by simp⟩ ⟨j, hj⟩
      = ((g (2 ^ logN + j)).toInt : ZMod S.q))
    (i : ℕ) (hi : i < 2 ^ logN) :
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((pointwiseProgW S logN).denote
        (lanesVal (Rw S.w) g (2 * 2 ^ logN) 0)) i).toInt : ℤ) : ZMod S.q)
        * ((2 ^ S.w : ℕ) : ZMod S.q)
      = basemulF logN logN psis x y ⟨0, by simp⟩ ⟨i, hi⟩ := by
  rw [(pointwiseProgW_denote S hS logN g hg i hi).2, basemulF_eq_mulF, RingDialect.mulF,
    hx i hi, hy i hi]

/-! ## 9. Instances -/

/-- ML-KEM: `q = 3329` in signed 16-bit words, `qinv = 62209`, inputs below `8 q` (the
output bound of `nttProgSW mlkemNtt mlkemSigned`). -/
def mlkemBasemul : BasemulSched := ⟨16, 3329, 62209, 26632, 12488, 23310⟩

/-- ML-DSA: `q = 8380417` in signed 32-bit words, `qinv = 58728449`, inputs below `9 q`
(the output bound of `nttProgSW mldsaNtt mldsaSigned`). -/
def mldsaPointwise : BasemulSched := ⟨32, 8380417, 58728449, 75423753, 0, 5514723⟩

theorem mlkemBasemul_ok : mlkemBasemul.Ok := by decide +kernel

theorem mldsaPointwise_ok : mldsaPointwise.PointwiseOk := by decide +kernel

/-- The ML-KEM base multiplication on words at `ψ = 17`, `N = 256`, `L = 7`. -/
theorem mlkemBasemul_basemulF (g : ℕ → BitVec 16)
    (hg : ∀ j, j < 512 → |(g j).toInt| ≤ 26632) (x y : Limbs [3329] 256)
    (hx : ∀ j (hj : j < 256), x ⟨0, by simp⟩ ⟨j, hj⟩ = ((g j).toInt : ZMod 3329))
    (hy : ∀ j (hj : j < 256), y ⟨0, by simp⟩ ⟨j, hj⟩ = ((g (256 + j)).toInt : ZMod 3329))
    (i : ℕ) (hi : i < 256) :
    |(hvGetG (Rw 16) (0 : BitVec 16) ((basemulProgW mlkemBasemul 17 8).denote
        (lanesVal (Rw 16) g 512 0)) i).toInt| ≤ 23310 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((basemulProgW mlkemBasemul 17 8).denote
        (lanesVal (Rw 16) g 512 0)) i).toInt : ℤ) : ZMod 3329) * ((2 ^ 16 : ℕ) : ZMod 3329)
      = basemulF 8 7 [17] x y ⟨0, by simp⟩ ⟨i, hi⟩ :=
  ⟨(basemulProgW_denote mlkemBasemul mlkemBasemul_ok 17 8 (by norm_num) g hg i hi).1,
    basemulProgW_basemulF mlkemBasemul mlkemBasemul_ok 17 8 (by norm_num) g hg x y hx hy i hi⟩

end CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
