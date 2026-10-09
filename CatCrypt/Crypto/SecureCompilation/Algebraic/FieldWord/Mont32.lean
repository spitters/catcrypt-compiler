/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord
public import CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakM

/-!
# The 32-bit Montgomery multiply as a single-word field record

For an odd modulus `2 < p < 2³¹`, field multiplication on canonical representatives is
computed on one 64-bit register by two Montgomery reductions at radix `R = 2³²`:

`x · y ↦ csub (redc (redc (x · y) · R²))`, with `R² = 2⁶⁴ mod p`.

The first reduction gives `x y R⁻¹` below `2 p`, the multiplication by `R²` and the second
reduction give `x y` below `2 p`, and the conditional subtract gives the canonical
representative. Inputs and outputs are canonical, so the record is built by
`SingleWordField.ofCanonical` and shares the add, sub, neg, const and copy blocks of every
canonical record.

The reduction `redc32W p μ t = (t + ((t · μ) mod 2³²) · p) >>> 32` uses the constant
`μ = −p⁻¹ mod 2³²`, computed by `mu p` with four Newton steps and checked by the decidable
certificate `mont32Cert p`. The low word `(t · μ) mod 2³²` is taken by a shift pair, and
the constant `μ` enters the block sign-extended from 32 bits (`sext32`), so that every
constant of the block is a sign-extended 32-bit immediate.

## Main definitions

* `newtonStep`, `invMod32`, `mu`, `r2`: the Newton inverse modulo `2³²`, the Montgomery
  constant and `R² mod p`.
* `mont32Cert p`: `p` odd, `2 < p < 2³¹`, and `p · mu p + 1 ≡ 0 (mod 2³²)`.
* `sext32`, `IsImm32`: the sign extension of a 32-bit constant and the immediate range.
* `lowWord32`, `redc32W`, `mont32MulW`: the low word, the reduction and the multiply as word
  functions.
* `redcBlk`, `mont32MulBlk`: the reduction and multiply blocks over `jasminDialect`.
* `mont32Field p h`: the canonical single-word record with the Montgomery multiply.

## Main results

* `redc32W_toNat`, `redc32W_spec`: the value of the reduction, its bound `< 2 p` and its
  residue `redc32W t · 2³² ≡ t (mod p)` for `t < p · 2³²`.
* `redcBlk_denote`, `mont32MulBlk_value`: the block denotations as word functions.
* `mont32MulBlk_denote`: on canonical representatives of `x`, `y` the multiply block
  denotes the canonical representative of `x * y`.
* `opsQuiet_mont32MulBlk`: the multiply block binds register constants and register
  add, sub, mul, and, shl and shr only.
* `mont32_consts_imm32`: the constants of the block are 32-bit immediates.
* `mont32Cert_babyBear`, `mont32Cert_koalaBear`, `mont32Cert_mersenne31`: the certificate
  holds at the three primes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (spliceCom spliceCom_denote)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord

/-! ## 1. The certificate -/

/-- One Newton step for the inverse of `p` modulo `2³²`: `x ↦ x (2 − p x) mod 2³²`. -/
def newtonStep (p x : Nat) : Nat := x * (2 ^ 32 + 2 - p * x % 2 ^ 32) % 2 ^ 32

/-- Four Newton steps from `p`, an inverse of `p` modulo `2³²` for odd `p`. -/
def invMod32 (p : Nat) : Nat := (newtonStep p)^[4] p

/-- The Montgomery constant `−p⁻¹ mod 2³²`. -/
def mu (p : Nat) : Nat := (2 ^ 32 - invMod32 p) % 2 ^ 32

/-- The constant `R² mod p` with `R = 2³²`. -/
def r2 (p : Nat) : Nat := 2 ^ 64 % p

/-- **The certificate of the 32-bit Montgomery multiply at `p`**: `p` odd, `2 < p < 2³¹`,
    and `p · mu p + 1 ≡ 0 (mod 2³²)`. -/
def mont32Cert (p : Nat) : Bool :=
  decide (p % 2 = 1 ∧ 2 < p ∧ p < 2 ^ 31 ∧ (p * mu p + 1) % 2 ^ 32 = 0)

theorem mont32Cert_spec {p : Nat} (h : mont32Cert p = true) :
    p % 2 = 1 ∧ 2 < p ∧ p < 2 ^ 31 ∧ (p * mu p + 1) % 2 ^ 32 = 0 :=
  of_decide_eq_true h

theorem mu_lt (p : Nat) : mu p < 2 ^ 32 := Nat.mod_lt _ (by norm_num)

/-! ## 2. Immediates -/

/-- The 64-bit sign extension of a 32-bit constant `n`. -/
def sext32 (n : Nat) : Nat := if n < 2 ^ 31 then n else n + (2 ^ 64 - 2 ^ 32)

/-- `n` is a 64-bit word that is the sign extension of a 32-bit immediate. -/
def IsImm32 (n : Nat) : Prop := n < 2 ^ 31 ∨ (2 ^ 64 - 2 ^ 31 ≤ n ∧ n < 2 ^ 64)

theorem sext32_mod {n : Nat} (hn : n < 2 ^ 32) : sext32 n % 2 ^ 32 = n := by
  unfold sext32
  split <;> omega

theorem sext32_lt {n : Nat} (hn : n < 2 ^ 32) : sext32 n < 2 ^ 64 := by
  unfold sext32
  split <;> omega

theorem sext32_imm32{n : Nat} (hn : n < 2 ^ 32) : IsImm32 (sext32 n) := by
  unfold sext32 IsImm32
  split <;> omega

/-! ## 3. The reduction -/

/-- The low 32 bits of a word, by a shift pair. -/
def lowWord32 (x : BitVec 64) : BitVec 64 := (x <<< (32 : Nat)) >>> (32 : Nat)

theorem lowWord32_toNat (x : BitVec 64) : (lowWord32 x).toNat = x.toNat % 2 ^ 32 := by
  unfold lowWord32
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by norm_num,
    Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by norm_num)]

/-- **The Montgomery reduction at radix `2³²`**: `(t + ((t · μ) mod 2³²) · p) >>> 32`,
    with `μ` entering sign-extended. -/
def redc32W (p μ : Nat) (t : BitVec 64) : BitVec 64 :=
  (t + lowWord32 (t * BitVec.ofNat 64 (sext32 μ)) * BitVec.ofNat 64 p) >>> (32 : Nat)

/-- For `p < 2³¹`, `μ < 2³²` and `t < p · 2³²`, the reduction does not wrap. -/
theorem redc32W_toNat {p μ : Nat} (hp : p < 2 ^ 31) (hμ : μ < 2 ^ 32) (t : BitVec 64)
    (ht : t.toNat < p * 2 ^ 32) :
    (redc32W p μ t).toNat = (t.toNat + t.toNat * μ % 2 ^ 32 * p) / 2 ^ 32 := by
  have hpt : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hlo : (lowWord32 (t * BitVec.ofNat 64 (sext32 μ))).toNat = t.toNat * μ % 2 ^ 32 := by
    rw [lowWord32_toNat, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64), Nat.mod_eq_of_lt (sext32_lt hμ),
      Nat.mul_mod, sext32_mod hμ, Nat.mod_mul_mod]
  have hm : t.toNat * μ % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hmp : t.toNat * μ % 2 ^ 32 * p < 2 ^ 32 * 2 ^ 31 :=
    Nat.mul_lt_mul'' hm hp
  have hmp' : t.toNat * μ % 2 ^ 32 * p < 2 ^ 63 := by
    have : (2 : Nat) ^ 32 * 2 ^ 31 = 2 ^ 63 := by norm_num
    omega
  have htp : t.toNat < 2 ^ 63 := by
    have : p * 2 ^ 32 < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hp (by norm_num)
    have : (2 : Nat) ^ 31 * 2 ^ 32 = 2 ^ 63 := by norm_num
    omega
  unfold redc32W
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_mul, hlo, hpt,
    Nat.mod_eq_of_lt (by omega : t.toNat * μ % 2 ^ 32 * p < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- Under `p · μ + 1 ≡ 0 (mod 2³²)`, the dividend of the reduction is a multiple of `2³²`,
    by `R_dvd_T_add_mN` of `MontgomeryRedcGeneric`. -/
theorem dvd_dividend {p μ : Nat} (hμ : (p * μ + 1) % 2 ^ 32 = 0) (T : Nat) :
    2 ^ 32 ∣ T + T * μ % 2 ^ 32 * p := by
  have hN : ((p : ℤ) * μ) ≡ -1 [ZMOD (2 ^ 32 : ℤ)] := by
    have hd : (2 ^ 32 : Nat) ∣ p * μ + 1 := Nat.dvd_of_mod_eq_zero hμ
    have hd' : ((2 ^ 32 : Nat) : ℤ) ∣ ((p * μ + 1 : Nat) : ℤ) := Int.natCast_dvd_natCast.mpr hd
    push_cast at hd'
    apply Int.modEq_iff_dvd.mpr
    have : (-1 : ℤ) - p * μ = -((p : ℤ) * μ + 1) := by ring
    rw [this]
    exact (Int.dvd_neg).mpr hd'
  have h := Optimizer.Rewrite.MontgomeryRedcGeneric.R_dvd_T_add_mN (p : ℤ) (2 ^ 32) μ T hN
  unfold Optimizer.Rewrite.MontgomeryRedcGeneric.montDigit at h
  have hc : ((T + T * μ % 2 ^ 32 * p : Nat) : ℤ) = (T : ℤ) + (T : ℤ) * μ % 2 ^ 32 * p := by
    push_cast; rfl
  rw [← hc] at h
  exact_mod_cast h

/-- **The reduction under the certificate**: for `t < p · 2³²`, `redc32W p (mu p) t` lies
    below `2 p` and satisfies `redc32W t · 2³² ≡ t (mod p)`. -/
theorem redc32W_spec {p : Nat} (h : mont32Cert p = true) {t : BitVec 64}
    (ht : t.toNat < p * 2 ^ 32) :
    (redc32W p (mu p) t).toNat < 2 * p ∧
      (redc32W p (mu p) t).toNat * 2 ^ 32 % p = t.toNat % p := by
  obtain ⟨_, _, hp, hμ⟩ := mont32Cert_spec h
  rw [redc32W_toNat hp (mu_lt p) t ht]
  have hdiv := Nat.div_mul_cancel (dvd_dividend hμ t.toNat)
  have hm : t.toNat * mu p % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  refine ⟨?_, ?_⟩
  · apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ 32)
    rw [hdiv]
    have : t.toNat * mu p % 2 ^ 32 * p < 2 ^ 32 * p :=
      Nat.mul_lt_mul_of_pos_right hm (by omega)
    nlinarith
  · rw [hdiv, Nat.add_mul_mod_self_right]

/-! ## 4. The multiply -/

/-- **The 32-bit Montgomery multiply on canonical representatives**:
    `csub (redc (redc (a · b) · R²))`. -/
def mont32MulW (p : Nat) (a b : BitVec 64) : BitVec 64 :=
  csubW p (redc32W p (mu p) (redc32W p (mu p) (a * b) * BitVec.ofNat 64 (r2 p)))

/-- Under the certificate, `mont32MulW` is field multiplication on canonical
    representatives. -/
theorem mont32MulW_canonEnc {p : Nat} [NeZero p] (h : mont32Cert p = true) (x y : ZMod p) :
    mont32MulW p (canonEnc p x) (canonEnc p y) = canonEnc p (x * y) := by
  obtain ⟨hodd, hp2, hp, _⟩ := mont32Cert_spec h
  have hp64 : p ≤ 2 ^ 64 := by omega
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hR : (2 : Nat) ^ 32 = 2 ^ 31 * 2 := by norm_num
  -- the product
  have hxy : x.val * y.val < p * 2 ^ 32 :=
    Nat.mul_lt_mul'' hx (by omega)
  have hprod : (canonEnc p x * canonEnc p y).toNat = x.val * y.val := by
    rw [BitVec.toNat_mul, canonEnc_toNat hp64, canonEnc_toNat hp64]
    exact Nat.mod_eq_of_lt (by
      have : p * 2 ^ 32 < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hp (by norm_num)
      omega)
  -- the first reduction
  obtain ⟨h1b, h1m⟩ := redc32W_spec h (t := canonEnc p x * canonEnc p y) (by rw [hprod]; exact hxy)
  set r1 := redc32W p (mu p) (canonEnc p x * canonEnc p y) with hr1
  rw [hprod] at h1m
  -- the multiplication by `R²`
  have hr2 : r2 p < p := Nat.mod_lt _ (by omega)
  have hr2t : (BitVec.ofNat 64 (r2 p)).toNat = r2 p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ht2 : r1.toNat * r2 p < p * 2 ^ 32 := by
    calc r1.toNat * r2 p < (2 * p) * p := Nat.mul_lt_mul'' h1b hr2
      _ ≤ 2 ^ 32 * p := Nat.mul_le_mul_right p (by omega)
      _ = p * 2 ^ 32 := Nat.mul_comm _ _
  have ht2w : (r1 * BitVec.ofNat 64 (r2 p)).toNat = r1.toNat * r2 p := by
    rw [BitVec.toNat_mul, hr2t]
    exact Nat.mod_eq_of_lt (by
      have : p * 2 ^ 32 < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hp (by norm_num)
      omega)
  -- the second reduction
  obtain ⟨h2b, h2m⟩ := redc32W_spec h (t := r1 * BitVec.ofNat 64 (r2 p))
    (by rw [ht2w]; exact ht2)
  rw [ht2w] at h2m
  set s := redc32W p (mu p) (r1 * BitVec.ofNat 64 (r2 p)) with hs
  -- the residue of `s` is `x y`
  have hcop : Nat.Coprime p (2 ^ 64) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (by omega)))
  have e1 : r1.toNat * 2 ^ 32 ≡ x.val * y.val [MOD p] := h1m
  have e2 : s.toNat * 2 ^ 32 ≡ r1.toNat * r2 p [MOD p] := h2m
  have e3 : r2 p ≡ 2 ^ 64 [MOD p] := Nat.mod_modEq _ _
  have key : s.toNat * 2 ^ 64 ≡ x.val * y.val * 2 ^ 64 [MOD p] :=
    calc s.toNat * 2 ^ 64 = (s.toNat * 2 ^ 32) * 2 ^ 32 := by ring
      _ ≡ (r1.toNat * r2 p) * 2 ^ 32 [MOD p] := e2.mul_right _
      _ ≡ (r1.toNat * 2 ^ 64) * 2 ^ 32 [MOD p] := (e3.mul_left _).mul_right _
      _ = (r1.toNat * 2 ^ 32) * 2 ^ 64 := by ring
      _ ≡ x.val * y.val * 2 ^ 64 [MOD p] := e1.mul_right _
  have hres : s.toNat % p = x.val * y.val % p := Nat.ModEq.cancel_right_of_coprime hcop key
  apply eq_canonEnc_of_toNat hp64
  rw [mont32MulW, ← hr1, ← hs, csubW_toNat p (by omega) _ h2b, hres, ZMod.val_mul]

/-! ## 5. The blocks -/

/-- **The reduction block on `t`**: `t · sext32 μ`, the low word by a shift pair, the
    product with `P`, the sum with `t`, and the shift by `32`. -/
def redcBlk {Γ : Ctxt jasminDialect} (P μ : Nat) (t : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (binLitBlk .mul t (sext32 μ)) <|
  spliceCom (binLitBlk .shl .here 32) <|
  spliceCom (binLitBlk .shr .here 32) <|
  spliceCom (binLitBlk .mul .here P) <|
  spliceCom (binBlk .add t.there.there.there.there .here) <|
  binLitBlk .shr .here 32

theorem redcBlk_denote {Γ : Ctxt jasminDialect} (P μ : Nat) (t : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (redcBlk P μ t).denote V = redc32W P μ (t.lookup V) := by
  unfold redcBlk
  simp only [spliceCom_denote, binLitBlk_denote, binBlk_denote]
  rfl

/-- **The 32-bit Montgomery multiply block** on `a`, `b`: the product, a reduction, the
    product with `r2 p`, a reduction, and one conditional subtract of `p`. -/
def mont32MulBlk (p : Nat) {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) :
    Com jasminDialect Γ w64 :=
  spliceCom (binBlk .mul a b) <|
  spliceCom (redcBlk p (mu p) .here) <|
  spliceCom (binLitBlk .mul .here (r2 p)) <|
  spliceCom (redcBlk p (mu p) .here) <|
  csubBlk p .here

theorem mont32MulBlk_value (p : Nat) {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (mont32MulBlk p a b).denote V = mont32MulW p (lk a V) (lk b V) := by
  unfold mont32MulBlk
  simp only [spliceCom_denote, binBlk_denote, binLitBlk_denote, redcBlk_denote, csubBlk_denote]
  rfl

/-- **The Montgomery multiply under the certificate**: on variables holding the canonical
    representatives of `x` and `y`, `mont32MulBlk p` denotes the canonical representative of
    `x * y`. -/
theorem mont32MulBlk_denote {p : Nat} [NeZero p] (h : mont32Cert p = true)
    {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) (V : Ctxt.Valuation Γ) (x y : ZMod p)
    (ha : a.lookup V = canonEnc p x) (hb : b.lookup V = canonEnc p y) :
    (mont32MulBlk p a b).denote V = canonEnc p (x * y) := by
  rw [mont32MulBlk_value, show lk a V = canonEnc p x from ha,
    show lk b V = canonEnc p y from hb]
  exact mont32MulW_canonEnc h x y

/-! ## 6. The record -/

/-- **The 32-bit Montgomery record at `p`** under the certificate `mont32Cert p`: canonical
    representatives, with the multiply `mont32MulBlk p`. -/
def mont32Field (p : Nat) (h : mont32Cert p = true) : SingleWordField p :=
  haveI : NeZero p := ⟨by have := (mont32Cert_spec h).2.1; omega⟩
  SingleWordField.ofCanonical p (by have := (mont32Cert_spec h).2.2.1; omega)
    (mont32MulBlk p) (mont32MulBlk_denote h)

/-! ## 7. Leakage and immediates -/

section Quiet

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (Com.OpsQuiet)

/-- A renamed straight-line program binds the operations of the source. -/
theorem opsQuiet_rename {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    (M : LeakModel d) : ∀ {Γ Γ' : Ctxt d} {t : d.Ty} (h : Ctxt.Hom Γ Γ') (c : Com d Γ t),
      Com.OpsQuiet M c → Com.OpsQuiet M (Com.rename h c)
  | _, _, _, _, .ret _, _ => trivial
  | _, _, _, h, .var _ body, hc => by
      obtain ⟨he, hb⟩ := hc
      exact And.intro he (opsQuiet_rename M h.lift body hb)

/-- The splice of two straight-line programs of quiet operations binds quiet operations. -/
theorem opsQuiet_spliceCom {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    (M : LeakModel d) : ∀ {Γ : Ctxt d} {t s : d.Ty} (c : Com d Γ t) (k : Com d (t :: Γ) s),
      Com.OpsQuiet M c → Com.OpsQuiet M k → Com.OpsQuiet M (spliceCom c k)
  | _, _, _, .ret _, k, _, hk => opsQuiet_rename M _ k hk
  | _, _, _, .var _ body, k, hc, hk => by
      obtain ⟨he, hb⟩ := hc
      exact And.intro he (opsQuiet_spliceCom M body _ hb (opsQuiet_rename M _ k hk))

/-- **The multiply block binds constant-time operations only**: for a leakage model in
    which register constants and register add, sub, mul, and, shl and shr have no event,
    every operation of `mont32MulBlk p` has no event. -/
theorem opsQuiet_mont32MulBlk (M : LeakModel jasminDialect)
    (hA : ∀ (bop : JasminBinOp) (w : Nat),
      bop ∈ [.add, .sub, .mul, .and, .shl, .shr] → M.kind (.regArith bop w) = .quiet)
    (hK : ∀ w n, M.kind (.regConst w n) = .quiet)
    (p : Nat) {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) :
    Com.OpsQuiet M (mont32MulBlk p a b) := by
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
  have hC : Com.OpsQuiet M (csubBlk (Γ := (w64 :: w64 :: w64 :: w64 :: Γ)) p .here) :=
    And.intro (hK _ _) <| And.intro (hA _ _ (by decide)) <| And.intro (hK _ _) <|
    And.intro (hA _ _ (by decide)) <| And.intro (hK _ _) <| And.intro (hA _ _ (by decide)) <|
    And.intro (hA _ _ (by decide)) <| And.intro (hA _ _ (by decide)) trivial
  exact opsQuiet_spliceCom M _ _ (hB _ _ _ (by decide)) <|
    opsQuiet_spliceCom M _ _ (hR _) <|
    opsQuiet_spliceCom M _ _ (hL _ _ _ (by decide)) <|
    opsQuiet_spliceCom M _ _ (hR _) hC

end Quiet

/-- Under the certificate, the constants of the multiply block, `p`, `r2 p`,
    `sext32 (mu p)`, `32`, `63` and `0`, are 32-bit immediates. -/
theorem mont32_consts_imm32 {p : Nat} (h : mont32Cert p = true) :
    IsImm32 p ∧ IsImm32 (r2 p) ∧ IsImm32 (sext32 (mu p)) ∧
      IsImm32 32 ∧ IsImm32 63 ∧ IsImm32 0 := by
  obtain ⟨_, hp2, hp, _⟩ := mont32Cert_spec h
  have hr2 : r2 p < p := Nat.mod_lt _ (by omega)
  refine ⟨Or.inl hp, Or.inl (by omega), sext32_imm32 (mu_lt p), Or.inl (by norm_num),
    Or.inl (by norm_num), Or.inl (by norm_num)⟩

/-! ## 8. The three primes -/

/-- The certificate holds at BabyBear, `p = 2³¹ − 2²⁷ + 1`. -/
theorem mont32Cert_babyBear : mont32Cert 2013265921 = true := by decide

/-- The certificate holds at KoalaBear, `p = 2³¹ − 2²⁴ + 1`. -/
theorem mont32Cert_koalaBear : mont32Cert 2130706433 = true := by decide

/-- The certificate holds at Mersenne-31, `p = 2³¹ − 1`. -/
theorem mont32Cert_mersenne31 : mont32Cert 2147483647 = true := by decide

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32
