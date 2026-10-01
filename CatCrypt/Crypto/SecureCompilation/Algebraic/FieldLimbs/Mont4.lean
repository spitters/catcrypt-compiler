/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Montgomery field blocks over four 64-bit limbs for an odd modulus below `2^256`

For a record `Mont4Prime` of an odd modulus `p < 2^256` and the constant
`nInv = -p⁻¹ mod 2^64`, an element `x` of `ZMod p` is represented by the four
little-endian 64-bit limbs of the canonical representative of its Montgomery form
`x · 2^256` (`enc`). The module gives multi-result `jasminDialect` blocks for
addition, multiplication, constants, subtraction, negation and inversion, and a value
theorem for each: on operand limbs holding the Montgomery forms of `x` and `y`, the
block denotes `enc (x ⋆ y)`. Subtraction and negation act on canonical
representatives and so commute with any fixed factor; inversion is the Montgomery
power `x^(p-2)`, the inverse at a prime modulus.

The blocks reuse the list combinators of `FieldLimbs.Curve25519` (`adcR`, `rowR`,
`selR`, `constsK`, `addK`, `mulRowK`, `prodK`) and bind `regArith`, `regConst`,
`mulhi`, `addCarryLo`, `addCarryHi` and `select`. None branches or indexes on data.
The algorithm is the word-by-word Montgomery arithmetic of fiat-crypto
(`Arithmetic/WordByWordMontgomery.v`: `redc`, `add`, `conditional_sub`); a sum or a
reduced product below `2p` may exceed `2^256`, so both carry a fifth limb into the
final conditional subtraction.

* Conditional subtraction (`csubPCK`): on five limbs of value `V < p + 2^256`, the sum
  `V + (2^320 - p)` carries exactly when `p ≤ V`, and then its low four limbs are
  `V - p`; the carry selects between them and the low four input limbs.
* Addition: the carry chain over the operands extended by a zero limb, then `csubPCK`.
* Multiplication: the 4×4 schoolbook product (`prodK`), four words of Montgomery
  reduction (`redcStepK`) on a nine-limb accumulator, each adding `m · p` for the digit
  `m = (A mod 2^64) · nInv mod 2^64` and dropping the zero low limb, and `csubPCK` on
  the low five limbs. The result `A₄` satisfies `A₄ · 2^256 = x y + M p` with
  `M < 2^256` (`redc_chain`), so `A₄ < 2p`.

## Main definitions

* `Mont4Prime`: the modulus record.
* `csubPK`, `csubPCK`, `addMK`, `redcStepK`, `mulMK`: the list-level operations.
* `R`, `enc`: the Montgomery factor and the encoding.
* `addBlk`, `mulBlk`, `constBlk`: the blocks; the copy block is
  `FieldLimbs.Curve25519.copyBlk`.
* `subMK`, `subBlk`, `negBlk`: subtraction and negation modulo `p` on four limbs.
* `mulL`, `powK`, `expBits`, `invBlk`: the Montgomery power chain and the inversion
  block.

## Main results

* `redc_digit`: the digit `m` makes `A + m p` divisible by `2^64`.
* `csubPCK_denote`: the conditional subtraction on five limbs.
* `redcStepK_denote`, `mulMK_denote`: one reduction word, and the product
  `out · 2^256 ≡ x y (mod p)` with `out < p`.
* `addBlk_denote`, `mulBlk_denote`, `constBlk_denote`, `copyBlk_denote`: the value
  theorems of the blocks.
* `enc_injective`: the encoding is injective.
* `subBlk_denote`, `negBlk_denote`: the blocks on canonical representatives;
  `subBlk_denote_enc`, `negBlk_denote_enc` on Montgomery forms.
* `invBlk_denote_pow`: the inversion block gives `enc (x^(p-2))`;
  `invBlk_denote_inv` gives `enc x⁻¹` at a prime modulus (`pow_sub_two_eq_inv`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk lk1 eBin eConst eBit eConst_denote eBit_denote eBin_denote Pres Pres.id
    Pres.comp bindK bindK_denote nv nv_nil nv_cons nv_map nv_append nv_lt selR selR_denote
    constsK constsK_denote limbsNat addK addK_denote mulRowK mulRowK_denote prodK
    prodK_denote R4 limbsOf ret4 ret4_denote ofNat_mod_two_pow limbsOf_injective copyBlk
    xorR xorR_denote adcR adcR_denote)

/-! ## 1. The modulus -/

/-- An odd modulus below `2^256` with the Montgomery constant `nInv = -p⁻¹ mod 2^64`. -/
structure Mont4Prime where
  /-- The modulus. -/
  p : Nat
  /-- `-p⁻¹ mod 2^64`. -/
  nInv : Nat
  one_lt : 1 < p
  p_odd : p % 2 = 1
  p_lt : p < 2 ^ 256
  nInv_lt : nInv < 2 ^ 64
  nInv_spec : (p * nInv + 1) % 2 ^ 64 = 0

variable (P : Mont4Prime)

/-- The four little-endian 64-bit digits of `n`. -/
def digits (n : Nat) : List Nat :=
  [n % 2 ^ 64, n / 2 ^ 64 % 2 ^ 64, n / 2 ^ 128 % 2 ^ 64, n / 2 ^ 192 % 2 ^ 64]

theorem limbsNat_digits (n : Nat) (hn : n < 2 ^ 256) : limbsNat (digits n) = n := by
  simp only [digits, limbsNat]
  omega

theorem digits_lt (n : Nat) : ∀ d ∈ digits n, d < 2 ^ 64 := by
  simp only [digits, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl) <;> exact Nat.mod_lt _ (by norm_num)

theorem digits_length (n : Nat) : (digits n).length = 4 := rfl

/-- `(A + m p) ≡ 0 mod 2^64` for the Montgomery digit `m = (A mod 2^64) · nInv mod 2^64`. -/
theorem redc_digit (A : Nat) :
    (A + (A % 2 ^ 64 * P.nInv % 2 ^ 64) * P.p) % 2 ^ 64 = 0 := by
  have h : ((P.p * P.nInv + 1 : Nat) : ZMod (2 ^ 64)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero P.nInv_spec)
  refine Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp ?_)
  push_cast at h ⊢
  simp only [ZMod.natCast_mod, Nat.cast_mul]
  linear_combination (A : ZMod (2 ^ 64)) * h

/-! ## 2. Limb-list lemmas -/

theorem nv_replicate {Δ : Ctxt jasminDialect} (W : Valuation Δ) (z : Var Δ w64)
    (hz : (lk z W).toNat = 0) : ∀ n, nv W (List.replicate n z) = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, nv_cons, nv_replicate W z hz n, hz]; rfl

theorem nv_cons_mod {Δ : Ctxt jasminDialect} (W : Valuation Δ) (x : Var Δ w64)
    (xs : List (Var Δ w64)) : (lk x W).toNat = nv W (x :: xs) % 2 ^ 64 := by
  have := (lk x W).isLt
  rw [nv_cons]
  omega

theorem nv_take_four {Δ : Ctxt jasminDialect} (W : Valuation Δ) (xs : List (Var Δ w64))
    (hlen : 4 ≤ xs.length) (hv : nv W xs < 2 ^ 256) : nv W (xs.take 4) = nv W xs := by
  have hsplit := nv_append W (xs.take 4) (xs.drop 4)
  rw [List.take_append_drop, List.length_take_of_le hlen] at hsplit
  have hpos : (0 : Nat) < 2 ^ (64 * 4) := Nat.two_pow_pos _
  have h0 : nv W (xs.drop 4) = 0 := by
    by_contra hne
    have : 2 ^ (64 * 4) ≤ 2 ^ (64 * 4) * nv W (xs.drop 4) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    norm_num at this hsplit
    omega
  rw [hsplit, h0]
  simp

set_option exponentiation.threshold 600 in
theorem nv_take_five {Δ : Ctxt jasminDialect} (W : Valuation Δ) (xs : List (Var Δ w64))
    (hlen : 5 ≤ xs.length) (hv : nv W xs < 2 ^ 320) : nv W (xs.take 5) = nv W xs := by
  have hsplit := nv_append W (xs.take 5) (xs.drop 5)
  rw [List.take_append_drop, List.length_take_of_le hlen] at hsplit
  have h0 : nv W (xs.drop 5) = 0 := by
    by_contra hne
    have : 2 ^ (64 * 5) ≤ 2 ^ (64 * 5) * nv W (xs.drop 5) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    norm_num at this hsplit
    omega
  rw [hsplit, h0]
  simp

/-! ## 3. Conditional subtraction and addition -/

/-- The four digits of `2^256 - p`. -/
def negDigits : List Nat := digits (2 ^ 256 - P.p)

/-- One conditional subtraction of `p` from four limbs: the sum with `2^256 - p` is
    selected when its carry is set. -/
def csubPK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  constsK (negDigits P) fun r₁ K =>
  addK (xs.map (fun v => r₁ v)) K fun r₂ T c =>
  selR (fun v => v) c T (xs.map (fun v => r₂ (r₁ v))) fun r₃ out =>
    k (fun v => r₃ (r₂ (r₁ v))) out

theorem csubPK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : xs.length = 4)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (if P.p ≤ nv W xs then nv W xs - P.p else nv W xs) →
      (k r out).denote W' = G) :
    (csubPK P xs k).denote W = G := by
  have hp := P.p_lt
  refine constsK_denote _ _ W G (digits_lt _) fun r₁ K W₁ h₁ hK hKv => ?_
  have h1 := P.one_lt
  rw [negDigits, limbsNat_digits (2 ^ 256 - P.p) (by omega)] at hKv
  refine addK_denote _ K _ W₁ G (by simp [hlen, hK, negDigits, digits_length])
    fun r₂ T c W₂ h₂ hT hTv => ?_
  refine selR_denote (fun v => v) c T _ _ W₂ W₂ G (Pres.id W₂) (by simp [hT, hlen])
    fun r₃ out W₃ h₃ hout hval => ?_
  refine hk _ out W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) (by simp [hout, hT, hlen]) ?_
  rw [hval, nv_map (Pres.comp h₁ h₂) xs]
  rw [nv_map h₁ xs, hKv] at hTv
  simp only [List.length_map, hlen] at hTv hT
  have hX := nv_lt W xs
  have hTl := nv_lt W₂ T
  rw [hlen] at hX
  rw [hT] at hTl
  have hc2 := (lk1 c W₂).isLt
  by_cases hc : lk1 c W₂ = 1#1
  · have h1 : (lk1 c W₂).toNat = 1 := by rw [hc]; rfl
    rw [if_pos hc]
    rw [h1] at hTv
    split_ifs <;> omega
  · have h0 : (lk1 c W₂).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    rw [if_neg hc]
    split_ifs <;> omega

/-- The five digits of `2^320 - p`. -/
def negDigits5 : List Nat := digits (2 ^ 256 - P.p) ++ [2 ^ 64 - 1]

theorem negDigits5_lt : ∀ d ∈ negDigits5 P, d < 2 ^ 64 := by
  intro d hd
  simp only [negDigits5, List.mem_append, List.mem_singleton] at hd
  rcases hd with hd | rfl
  · exact digits_lt _ d hd
  · norm_num

theorem negDigits5_length : (negDigits5 P).length = 5 := rfl

theorem limbsNat_negDigits5 : limbsNat (negDigits5 P) = 2 ^ 320 - P.p := by
  have hp := P.p_lt
  have h1 := P.one_lt
  have hd := limbsNat_digits (2 ^ 256 - P.p) (by omega)
  simp only [negDigits5, digits, List.cons_append, List.nil_append, limbsNat] at hd ⊢
  omega

/-- One conditional subtraction of `p` from five limbs of value `V < p + 2^256`
    (fiat-crypto's `conditional_sub`): the sum `V + (2^320 - p)` carries exactly when
    `p ≤ V`, and the carry selects between its low four limbs and the low four input
    limbs. -/
def csubPCK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  constsK (negDigits5 P) fun r₁ K =>
  addK (xs.map (fun v => r₁ v)) K fun r₂ T c =>
  selR (fun v => v) c (T.take 4) ((xs.map (fun v => r₂ (r₁ v))).take 4) fun r₃ out =>
    k (fun v => r₃ (r₂ (r₁ v))) out

theorem csubPCK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : xs.length = 5)
    (hV : nv W xs < P.p + 2 ^ 256)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (if P.p ≤ nv W xs then nv W xs - P.p else nv W xs) →
      (k r out).denote W' = G) :
    (csubPCK P xs k).denote W = G := by
  have hp := P.p_lt
  refine constsK_denote _ _ W G (negDigits5_lt P) fun r₁ K W₁ h₁ hK hKv => ?_
  rw [limbsNat_negDigits5] at hKv
  rw [negDigits5_length] at hK
  refine addK_denote _ K _ W₁ G (by simp [hlen, hK]) fun r₂ T c W₂ h₂ hT hTv => ?_
  rw [nv_map h₁ xs, hKv] at hTv
  simp only [List.length_map, hlen] at hTv hT
  have hTl := nv_lt W₂ T
  rw [hT] at hTl
  have hc2 := (lk1 c W₂).isLt
  refine selR_denote (fun v => v) c _ _ _ W₂ W₂ G (Pres.id W₂) (by simp [hT, hlen])
    fun r₃ out W₃ h₃ hout hval => ?_
  refine hk _ out W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) (by simp [hout, hT]) ?_
  rw [hval]
  by_cases hc : lk1 c W₂ = 1#1
  · have h1 : (lk1 c W₂).toNat = 1 := by rw [hc]; rfl
    rw [if_pos hc]
    rw [h1] at hTv
    have hge : P.p ≤ nv W xs := by omega
    rw [if_pos hge, nv_take_four W₂ T (by omega) (by omega)]
    omega
  · have h0 : (lk1 c W₂).toNat = 0 := by
      have : (lk1 c W₂).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    rw [if_neg hc]
    rw [h0] at hTv
    have hlt : ¬ P.p ≤ nv W xs := by omega
    rw [if_neg hlt, nv_take_four W₂ _ (by simp [hlen]) (by rw [nv_map (Pres.comp h₁ h₂)]; omega),
      nv_map (Pres.comp h₁ h₂)]

/-- `if p ≤ V then V - p else V` is `V % p` below `2p`. -/
theorem csub_eq_mod (V : Nat) (hV : V < 2 * P.p) :
    (if P.p ≤ V then V - P.p else V) = V % P.p := by
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- Addition modulo `p` on four limbs: the carry chain over the operands extended by a
    zero limb, then the conditional subtraction on five limbs. -/
def addMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst 0) fun r₀ z =>
  addK (xs.map (fun v => r₀ v) ++ [z]) (ys.map (fun v => r₀ v) ++ [z]) fun r₁ S _ =>
  csubPCK P S fun r₂ out => k (fun v => r₂ (r₁ (r₀ v))) out

set_option exponentiation.threshold 600 in
theorem addMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4) (hys : ys.length = 4)
    (hx : nv W xs < P.p) (hy : nv W ys < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (nv W xs + nv W ys) % P.p → (k r out).denote W' = G) :
    (addMK P xs ys k).denote W = G := by
  have hp := P.p_lt
  refine bindK_denote _ _ _ _ fun r₀ z W₀ h₀ hz => ?_
  have ez : (lk z W₀).toNat = 0 := by rw [show lk z W₀ = _ from hz, eConst_denote]; rfl
  refine addK_denote _ _ _ W₀ G (by simp [hxs, hys]) fun r₁ S c W₁ h₁ hS hSv => ?_
  simp only [nv_append, nv_map h₀, nv_cons, nv_nil, ez, List.length_append, List.length_map,
    List.length_singleton, hxs, hys] at hSv hS
  have hS0 : nv W₁ S = nv W xs + nv W ys := by
    have hc := (lk1 c W₁).isLt
    have : (lk1 c W₁).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * 5) * 1 ≤ 2 ^ (64 * 5) * (lk1 c W₁).toNat :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this] at hSv
    omega
  refine csubPCK_denote P S _ W₁ G hS (by omega) fun r₂ out W₂ h₂ hout hv => ?_
  refine hk _ out W₂ (Pres.comp (Pres.comp h₀ h₁) h₂) hout ?_
  rw [hv, hS0]
  exact csub_eq_mod P _ (by omega)

/-! ## 4. Montgomery reduction -/

/-- One word of Montgomery reduction on nine limbs `acc` of value `A`: the digit
    `m = (A mod 2^64) · nInv mod 2^64`, the sum `A + m p` (whose low limb is zero),
    and its upper eight limbs followed by a zero limb. -/
def redcStepK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst 0) fun r₁ z =>
  bindK (eConst P.nInv) fun r₂ ni =>
  bindK (eBin .mul ((acc.map fun v => r₂ (r₁ v)).headD (r₂ z)) ni) fun r₃ m =>
  constsK (digits P.p) fun r₄ PL =>
  mulRowK PL (r₄ m) fun r₅ row =>
  addK (acc.map fun v => r₅ (r₄ (r₃ (r₂ (r₁ v)))))
    (row ++ List.replicate 4 (r₅ (r₄ (r₃ (r₂ z))))) fun r₆ S _ =>
  k (fun v => r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v)))))) (S.tail ++ [r₆ (r₅ (r₄ (r₃ (r₂ z))))])

set_option exponentiation.threshold 600 in
theorem redcStepK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : acc.length = 9) (hA : nv W acc < 2 ^ 512)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 9 →
      (∃ m, m < 2 ^ 64 ∧ nv W' out * 2 ^ 64 = nv W acc + m * P.p) →
      (k r out).denote W' = G) :
    (redcStepK P acc k).denote W = G := by
  have hp := P.p_lt
  obtain ⟨x, rest, rfl⟩ : ∃ x rest, acc = x :: rest := by
    cases acc with
    | nil => simp at hlen
    | cons x rest => exact ⟨x, rest, rfl⟩
  refine bindK_denote _ _ _ _ fun r₁ z W₁ h₁ hz => ?_
  refine bindK_denote _ _ _ _ fun r₂ ni W₂ h₂ hni => ?_
  refine bindK_denote _ _ _ _ fun r₃ m W₃ h₃ hm => ?_
  have ez : (lk z W₁).toNat = 0 := by rw [show lk z W₁ = _ from hz, eConst_denote]; rfl
  have eni : (lk ni W₂).toNat = P.nInv := by
    rw [show lk ni W₂ = _ from hni, eConst_denote, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt P.nInv_lt
  have ex : (lk (r₂ (r₁ x)) W₂).toNat = nv W (x :: rest) % 2 ^ 64 := by
    rw [show lk (r₂ (r₁ x)) W₂ = lk x W from (h₂ _).trans (h₁ x)]
    exact nv_cons_mod W x rest
  set M := nv W (x :: rest) % 2 ^ 64 * P.nInv % 2 ^ 64 with hM
  have em : (lk m W₃).toNat = M := by
    rw [show lk m W₃ = _ from hm, List.map_cons, List.headD_cons, eBin_denote]
    show (lk (r₂ (r₁ x)) W₂ * lk ni W₂).toNat = M
    rw [BitVec.toNat_mul, ex, eni]
  refine constsK_denote _ _ W₃ G (digits_lt _) fun r₄ PL W₄ h₄ hPL hPLv => ?_
  rw [limbsNat_digits _ (by omega)] at hPLv
  rw [digits_length] at hPL
  refine mulRowK_denote PL (r₄ m) _ W₄ G fun r₅ row W₅ h₅ hrow hrowv => ?_
  rw [hPLv, show lk (r₄ m) W₄ = lk m W₃ from h₄ m, em] at hrowv
  have ez5 : (lk (r₅ (r₄ (r₃ (r₂ z)))) W₅).toNat = 0 := by
    rw [show lk (r₅ (r₄ (r₃ (r₂ z)))) W₅ = lk z W₁ from
      (h₅ _).trans ((h₄ _).trans ((h₃ _).trans (h₂ z))), ez]
  have h1to5 : Pres (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) W W₅ :=
    Pres.comp (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄) h₅
  refine addK_denote _ _ _ W₅ G (by simp at hlen; simp [hrow, hPL]; omega)
    fun r₆ S c W₆ h₆ hS hSv => ?_
  rw [nv_map h1to5, nv_append, nv_replicate W₅ _ ez5, hrowv] at hSv
  simp only [List.length_map, hlen] at hSv hS
  have hMlt : M < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hMp : P.p * M < 2 ^ 256 * 2 ^ 64 := Nat.mul_lt_mul'' hp hMlt
  have hc := (lk1 c W₆).isLt
  have hS0 : nv W₆ S = nv W (x :: rest) + P.p * M := by
    have : (lk1 c W₆).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * 9) * 1 ≤ 2 ^ (64 * 9) * (lk1 c W₆).toNat :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this] at hSv
    omega
  obtain ⟨s₀, St, rfl⟩ : ∃ s₀ St, S = s₀ :: St := by
    cases S with
    | nil => simp at hS
    | cons s₀ St => exact ⟨s₀, St, rfl⟩
  have hdig : (nv W (x :: rest) + M * P.p) % 2 ^ 64 = 0 := redc_digit P _
  have hs₀ : (lk s₀ W₆).toNat = 0 := by
    rw [nv_cons_mod W₆ s₀ St, hS0, Nat.mul_comm P.p M, hdig]
  have hz6 : (lk (r₆ (r₅ (r₄ (r₃ (r₂ z))))) W₆).toNat = 0 := by
    rw [show lk (r₆ (r₅ (r₄ (r₃ (r₂ z))))) W₆ = lk (r₅ (r₄ (r₃ (r₂ z)))) W₅ from h₆ _, ez5]
  refine hk _ _ W₆ (Pres.comp h1to5 h₆) (by simp at hS ⊢; omega) ⟨M, hMlt, ?_⟩
  rw [List.tail_cons, nv_append, nv_cons, nv_nil, hz6]
  rw [nv_cons, hs₀] at hS0
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [Nat.mul_comm M P.p]
  omega

theorem redc_step_bound (p A A' m : Nat) (hp : p < 2 ^ 256) (hA : A < 2 ^ 512)
    (hm : m < 2 ^ 64) (e : A' * 2 ^ 64 = A + m * p) : A' < 2 ^ 512 := by
  have : m * p < 2 ^ 64 * 2 ^ 256 := Nat.mul_lt_mul'' hm hp
  omega

set_option exponentiation.threshold 600 in
/-- Four words of Montgomery reduction from `T < p²`: the result `A₄` satisfies
    `A₄ · 2^256 = T + M p` with `M < 2^256`, so `A₄ < 2p`. -/
theorem redc_chain (p T A₁ A₂ A₃ A₄ m₁ m₂ m₃ m₄ : Nat) (hp : p < 2 ^ 256)
    (hT : T < p * p) (hm₁ : m₁ < 2 ^ 64) (hm₂ : m₂ < 2 ^ 64) (hm₃ : m₃ < 2 ^ 64)
    (hm₄ : m₄ < 2 ^ 64) (e₁ : A₁ * 2 ^ 64 = T + m₁ * p) (e₂ : A₂ * 2 ^ 64 = A₁ + m₂ * p)
    (e₃ : A₃ * 2 ^ 64 = A₂ + m₃ * p) (e₄ : A₄ * 2 ^ 64 = A₃ + m₄ * p) :
    A₄ * 2 ^ 256 = T + (m₁ + 2 ^ 64 * m₂ + 2 ^ 128 * m₃ + 2 ^ 192 * m₄) * p ∧
      A₄ < 2 * p := by
  have hpp : p * p ≤ 2 ^ 256 * p := Nat.mul_le_mul_right _ hp.le
  have b₁ : m₁ * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have b₂ : m₂ * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have b₃ : m₃ * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have b₄ : m₄ * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have hEq : A₄ * 2 ^ 256 = T + (m₁ + 2 ^ 64 * m₂ + 2 ^ 128 * m₃ + 2 ^ 192 * m₄) * p := by
    linear_combination (2 ^ 192) * e₄ + 2 ^ 128 * e₃ + 2 ^ 64 * e₂ + e₁
  refine ⟨hEq, ?_⟩
  omega

/-- Montgomery multiplication on four limbs: the schoolbook product, four words of
    Montgomery reduction, and one conditional subtraction on the low five limbs. -/
def mulMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (y₀ y₁ y₂ y₃ : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  prodK xs y₀ y₁ y₂ y₃ fun r₁ T =>
  bindK (eConst 0) fun r₂ z =>
  redcStepK P (T.map (fun v => r₂ v) ++ [z]) fun r₃ A₁ =>
  redcStepK P A₁ fun r₄ A₂ =>
  redcStepK P A₂ fun r₅ A₃ =>
  redcStepK P A₃ fun r₆ A₄ =>
  csubPCK P (A₄.take 5) fun r₇ out =>
  k (fun v => r₇ (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v))))))) out

set_option exponentiation.threshold 600 in
theorem mulMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (y₀ y₁ y₂ y₃ : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4)
    (hx : nv W xs < P.p) (hy : nv W [y₀, y₁, y₂, y₃] < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 → nv W' out < P.p →
      nv W' out * 2 ^ 256 ≡ nv W xs * nv W [y₀, y₁, y₂, y₃] [MOD P.p] →
      (k r out).denote W' = G) :
    (mulMK P xs y₀ y₁ y₂ y₃ k).denote W = G := by
  have hp := P.p_lt
  refine prodK_denote xs y₀ y₁ y₂ y₃ _ W G hxs fun r₁ T W₁ h₁ hT hTv => ?_
  set X := nv W xs
  set Y := nv W [y₀, y₁, y₂, y₃]
  have hXY : X * Y < P.p * P.p := Nat.mul_lt_mul'' hx hy
  have hT510 : X * Y < 2 ^ 512 :=
    lt_of_lt_of_le hXY (le_trans (Nat.mul_le_mul hp.le hp.le) (by norm_num))
  refine bindK_denote _ _ _ _ fun r₂ z W₂ h₂ hz => ?_
  have ez : (lk z W₂).toNat = 0 := by rw [show lk z W₂ = _ from hz, eConst_denote]; rfl
  have hA0 : nv W₂ (T.map (fun v => r₂ v) ++ [z]) = X * Y := by
    rw [nv_append, nv_map h₂, nv_cons, nv_nil, ez, hTv]
    simp
  refine redcStepK_denote P _ _ W₂ G (by simp [hT]) (by rw [hA0]; exact hT510)
    fun r₃ A₁ W₃ h₃ hA₁ ⟨m₁, hm₁, e₁⟩ => ?_
  rw [hA0] at e₁
  refine redcStepK_denote P _ _ W₃ G hA₁ (redc_step_bound _ _ _ _ hp hT510 hm₁ e₁)
    fun r₄ A₂ W₄ h₄ hA₂ ⟨m₂, hm₂, e₂⟩ => ?_
  refine redcStepK_denote P _ _ W₄ G hA₂
    (redc_step_bound _ _ _ _ hp (redc_step_bound _ _ _ _ hp hT510 hm₁ e₁) hm₂ e₂)
    fun r₅ A₃ W₅ h₅ hA₃ ⟨m₃, hm₃, e₃⟩ => ?_
  refine redcStepK_denote P _ _ W₅ G hA₃
    (redc_step_bound _ _ _ _ hp (redc_step_bound _ _ _ _ hp
      (redc_step_bound _ _ _ _ hp hT510 hm₁ e₁) hm₂ e₂) hm₃ e₃)
    fun r₆ A₄ W₆ h₆ hA₄ ⟨m₄, hm₄, e₄⟩ => ?_
  obtain ⟨hEq, hlt⟩ := redc_chain _ _ _ _ _ _ _ _ _ _ hp hXY hm₁ hm₂ hm₃ hm₄ e₁ e₂ e₃ e₄
  have h2p : 2 * P.p < 2 ^ 320 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hp (by norm_num)) (by norm_num)
  have htake : nv W₆ (A₄.take 5) = nv W₆ A₄ :=
    nv_take_five W₆ A₄ (by rw [hA₄]; norm_num) (lt_trans hlt h2p)
  have hlt' : nv W₆ (A₄.take 5) < P.p + 2 ^ 256 := by
    rw [htake]
    exact lt_of_lt_of_le hlt (by rw [two_mul]; exact Nat.add_le_add_left hp.le _)
  refine csubPCK_denote P (A₄.take 5) _ W₆ G (by simp [hA₄]) hlt'
    fun r₇ out W₇ h₇ hout hv => ?_
  refine hk _ out W₇ (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp
    h₁ h₂) h₃) h₄) h₅) h₆) h₇) hout ?_ ?_
  · rw [hv, htake, csub_eq_mod P _ hlt]
    exact Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one P.one_lt)
  · rw [hv, htake, csub_eq_mod P _ hlt]
    unfold Nat.ModEq
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hEq, Nat.add_mul_mod_self_right]

/-! ## 5. The Montgomery encoding and the blocks -/

instance : NeZero P.p := ⟨by have := P.one_lt; omega⟩

/-- The Montgomery factor `2^256` in `ZMod p`. -/
def R : ZMod P.p := 2 ^ 256

theorem isUnit_R : IsUnit (R P) := by
  have h2 : IsUnit ((2 : Nat) : ZMod P.p) :=
    (ZMod.isUnit_iff_coprime 2 P.p).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr P.p_odd))
  rw [Nat.cast_ofNat] at h2
  exact h2.pow 256

/-- The encoding of `ZMod p`: the four limbs of the canonical representative of the
    Montgomery form `x · 2^256`. -/
def enc (x : ZMod P.p) : ListDenote R4 := limbsOf (x * R P).val

theorem val_lt (x : ZMod P.p) : x.val < P.p := ZMod.val_lt x

theorem val_lt_two_pow (x : ZMod P.p) : x.val < 2 ^ 256 := by
  have := ZMod.val_lt x
  have := P.p_lt
  omega

theorem enc_injective : Function.Injective (enc P) := fun x y h => by
  have hv := limbsOf_injective (val_lt_two_pow P _) (val_lt_two_pow P _) h
  have := ZMod.val_injective _ hv
  exact (isUnit_R P).mul_right_cancel this

section Blocks

variable {Γ : Ctxt jasminDialect}

/-- The addition block over the limbs `x₀ … x₃` and `y₀ … y₃`. -/
def addBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  addMK P [x₀, x₁, x₂, x₃] [y₀, y₁, y₂, y₃] fun r out => ret4 (r x₀) out

/-- The Montgomery multiplication block. -/
def mulBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  mulMK P [x₀, x₁, x₂, x₃] y₀ y₁ y₂ y₃ fun r out => ret4 (r x₀) out

/-- The constant block: the four 64-bit digits of `n` as `regConst` bindings. -/
def constBlk (n : Nat) : MC Γ R4 :=
  .var (eConst (n % 2 ^ 64)) <| .var (eConst (n / 2 ^ 64 % 2 ^ 64)) <|
  .var (eConst (n / 2 ^ 128 % 2 ^ 64)) <|
  .var (eConst (n / 2 ^ 192 % 2 ^ 64)) <|
  .ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here))
    (.cons (.there .here) (.cons .here .nil))))

variable (W : Valuation Γ)

theorem addBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) (hy : nv W [y₀, y₁, y₂, y₃] = (y * R P).val) :
    (addBlk P x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc P (x + y) := by
  refine addMK_denote P _ _ _ W _ rfl rfl (by rw [hx]; exact val_lt P _)
    (by rw [hy]; exact val_lt P _) fun r out W' _ hout hv => ?_
  rw [ret4_denote _ out W' hout, hv, hx, hy, enc, add_mul, ZMod.val_add]

theorem mulBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) (hy : nv W [y₀, y₁, y₂, y₃] = (y * R P).val) :
    (mulBlk P x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc P (x * y) := by
  refine mulMK_denote P _ _ _ _ _ _ W _ rfl (by rw [hx]; exact val_lt P _)
    (by rw [hy]; exact val_lt P _) fun r out W' _ hout hlt hmod => ?_
  rw [ret4_denote _ out W' hout, enc]
  congr 1
  rw [hx, hy] at hmod
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_val, ZMod.cast_id',
    id] at hc
  have hR : ((nv W' out : Nat) : ZMod P.p) = x * y * R P := by
    refine (isUnit_R P).mul_right_cancel ?_
    rw [show R P = 2 ^ 256 from rfl] at hc ⊢
    rw [hc]
    ring
  rw [← hR, ZMod.val_natCast_of_lt hlt]

theorem constBlk_denote (n : Nat) : (constBlk (Γ := Γ) n).denote W = limbsOf n := by
  rw [limbsOf, ← ofNat_mod_two_pow n, ← ofNat_mod_two_pow (n / 2 ^ 64),
    ← ofNat_mod_two_pow (n / 2 ^ 128), ← ofNat_mod_two_pow (n / 2 ^ 192)]
  rfl

theorem copyBlk_denote (x₀ x₁ x₂ x₃ : Var Γ w64) :
    (copyBlk x₀ x₁ x₂ x₃).denote W = limbsOf (nv W [x₀, x₁, x₂, x₃]) := by
  refine bindK_denote _ _ _ _ fun r₁ c₀ W₁ h₁ hc₀ => ?_
  refine bindK_denote _ _ _ _ fun r₂ c₁ W₂ h₂ hc₁ => ?_
  refine bindK_denote _ _ _ _ fun r₃ c₂ W₃ h₃ hc₂ => ?_
  refine bindK_denote _ _ _ _ fun r₄ c₃ W₄ h₄ hc₃ => ?_
  rw [ret4_denote _ _ W₄ rfl]
  congr 1
  simp only [nv_cons, nv_nil]
  have e0 : lk (r₄ (r₃ (r₂ c₀))) W₄ = lk x₀ W := by
    rw [show lk (r₄ (r₃ (r₂ c₀))) W₄ = lk c₀ W₁ from (h₄ _).trans ((h₃ _).trans (h₂ c₀)),
      show lk c₀ W₁ = _ from hc₀, eBin_denote]
    exact BitVec.or_self
  have e1 : lk (r₄ (r₃ c₁)) W₄ = lk x₁ W := by
    rw [show lk (r₄ (r₃ c₁)) W₄ = lk c₁ W₂ from (h₄ _).trans (h₃ c₁),
      show lk c₁ W₂ = _ from hc₁, eBin_denote,
      show lk (r₁ x₁) W₁ = lk x₁ W from h₁ x₁]
    exact BitVec.or_self
  have e2 : lk (r₄ c₂) W₄ = lk x₂ W := by
    rw [show lk (r₄ c₂) W₄ = lk c₂ W₃ from h₄ c₂, show lk c₂ W₃ = _ from hc₂, eBin_denote,
      show lk (r₂ (r₁ x₂)) W₂ = lk x₂ W from (h₂ _).trans (h₁ x₂)]
    exact BitVec.or_self
  have e3 : lk c₃ W₄ = lk x₃ W := by
    rw [show lk c₃ W₄ = _ from hc₃, eBin_denote,
      show lk (r₃ (r₂ (r₁ x₃))) W₃ = lk x₃ W from (h₃ _).trans ((h₂ _).trans (h₁ x₃))]
    exact BitVec.or_self
  rw [e0, e1, e2, e3]

end Blocks

/-! ## 6. Subtraction and negation -/

/-- The canonical representative of a difference: `b.val` subtracted from `a.val`,
    with `p` added when `b.val > a.val`. -/
theorem val_sub_eq (a b : ZMod P.p) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else a.val + P.p - b.val := by
  have ha := val_lt P a
  have hb := val_lt P b
  have key : ∀ n : Nat, n < P.p → (n : ZMod P.p) = a - b → (a - b).val = n :=
    fun n hn h => by rw [← h, ZMod.val_natCast_of_lt hn]
  split_ifs with h
  · refine key _ (by omega) ?_
    rw [Nat.cast_sub h, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · refine key _ (by omega) ?_
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_self, add_zero]

/-- Subtraction modulo `p` on four limbs: `xs + ¬ys + 1` by the carry chain; when the
    carry is clear, `p` is added, selected by the carry. -/
def subMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst (2 ^ 64 - 1)) fun r₁ m =>
  xorR r₁ m ys fun r₂ ny =>
  bindK (eBit 1) fun r₃ one =>
  adcR (fun v => v) (xs.map (fun v => r₃ (r₂ (r₁ v)))) (ny.map (fun v => r₃ v)) one
    fun r₄ D c =>
  constsK (digits P.p) fun r₅ PL =>
  addK (D.map (fun v => r₅ v)) PL fun r₆ E _ =>
  selR (fun v => v) (r₆ (r₅ c)) (D.map (fun v => r₆ (r₅ v))) E fun r₇ out =>
  k (fun v => r₇ (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v))))))) out

theorem subMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4) (hys : ys.length = 4)
    (hy : nv W ys < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (if nv W ys ≤ nv W xs then nv W xs - nv W ys else nv W xs + P.p - nv W ys) →
      (k r out).denote W' = G) :
    (subMK P xs ys k).denote W = G := by
  have hp := P.p_lt
  refine bindK_denote _ _ _ _ fun r₁ m W₁ h₁ hm => ?_
  refine xorR_denote r₁ m ys _ W W₁ G h₁ hm fun r₂ ny W₂ h₂ hny hnyv => ?_
  refine bindK_denote _ _ _ _ fun r₃ one W₃ h₃ hone => ?_
  have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W W₃ := Pres.comp (Pres.comp h₁ h₂) h₃
  have eone : (lk1 one W₃).toNat = 1 := by rw [show lk1 one W₃ = _ from hone, eBit_denote]; rfl
  refine adcR_denote (fun v => v) _ _ one _ W₃ W₃ G (Pres.id W₃) (by simp [hxs, hny, hys])
    fun r₄ D c W₄ h₄ hD hDv => ?_
  rw [nv_map h123, nv_map h₃, eone] at hDv
  simp only [List.length_map, hxs] at hDv hD
  rw [hys] at hnyv
  refine constsK_denote _ _ W₄ G (digits_lt _) fun r₅ PL W₅ h₅ hPL hPLv => ?_
  rw [limbsNat_digits _ (by omega)] at hPLv
  refine addK_denote _ PL _ W₅ G (by simp [hD, hPL, digits_length])
    fun r₆ E e W₆ h₆ hE hEv => ?_
  rw [nv_map h₅, hPLv] at hEv
  simp only [List.length_map, hD] at hEv hE
  refine selR_denote (fun v => v) _ _ E _ W₆ W₆ G (Pres.id W₆) (by simp [hE, hD])
    fun r₇ out W₇ h₇ hout hv => ?_
  refine hk _ out W₇ (Pres.comp (Pres.comp (Pres.comp (Pres.comp h123 h₄) h₅) h₆) h₇)
    (by simp [hout, hD]) ?_
  rw [hv, nv_map (Pres.comp h₅ h₆),
    show lk1 (r₆ (r₅ c)) W₆ = lk1 c W₄ from (h₆ _).trans (h₅ c)]
  have hDl := nv_lt W₄ D
  have hEl := nv_lt W₆ E
  rw [hD] at hDl
  rw [hE] at hEl
  have hc2 := (lk1 c W₄).isLt
  have he2 := (lk1 e W₆).isLt
  by_cases hc : lk1 c W₄ = 1#1
  · have h1 : (lk1 c W₄).toNat = 1 := by rw [hc]; rfl
    rw [if_pos hc]
    split_ifs <;> omega
  · have h0 : (lk1 c W₄).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    rw [if_neg hc]
    split_ifs <;> omega

section SubBlocks

variable {Γ : Ctxt jasminDialect}

/-- The subtraction block over the limbs `x₀ … x₃` and `y₀ … y₃`. -/
def subBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  subMK P [x₀, x₁, x₂, x₃] [y₀, y₁, y₂, y₃] fun r out => ret4 (r x₀) out

/-- The negation block: the subtraction of `x₀ … x₃` from four zero limbs. -/
def negBlk (x₀ x₁ x₂ x₃ : Var Γ w64) : MC Γ R4 :=
  .var (eConst 0) <| .var (eConst 0) <| .var (eConst 0) <| .var (eConst 0) <|
    subBlk P (.there (.there (.there .here))) (.there (.there .here)) (.there .here) .here
      (.there (.there (.there (.there x₀)))) (.there (.there (.there (.there x₁))))
      (.there (.there (.there (.there x₂)))) (.there (.there (.there (.there x₃))))

variable (W : Valuation Γ)

theorem subBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (a b : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = a.val) (hy : nv W [y₀, y₁, y₂, y₃] = b.val) :
    (subBlk P x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = limbsOf (a - b).val := by
  refine subMK_denote P _ _ _ W _ rfl rfl (by rw [hy]; exact val_lt P b)
    fun r out W' _ hout hv => ?_
  rw [ret4_denote _ out W' hout, hv, hx, hy, val_sub_eq]

theorem negBlk_denote (x₀ x₁ x₂ x₃ : Var Γ w64) (a : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = a.val) :
    (negBlk P x₀ x₁ x₂ x₃).denote W = limbsOf (-a).val := by
  rw [← zero_sub]
  refine subBlk_denote P _ _ _ _ _ _ _ _ _ 0 a ?_ hx
  rw [ZMod.val_zero]
  rfl

/-- On the Montgomery forms of `x` and `y`, the subtraction block gives the Montgomery
    form of `x - y`. -/
theorem subBlk_denote_enc (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) (hy : nv W [y₀, y₁, y₂, y₃] = (y * R P).val) :
    (subBlk P x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc P (x - y) := by
  rw [enc, sub_mul]
  exact subBlk_denote P W _ _ _ _ _ _ _ _ _ _ hx hy

/-- On the Montgomery form of `x`, the negation block gives the Montgomery form of
    `-x`. -/
theorem negBlk_denote_enc (x₀ x₁ x₂ x₃ : Var Γ w64) (x : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) :
    (negBlk P x₀ x₁ x₂ x₃).denote W = enc P (-x) := by
  rw [enc, neg_mul]
  exact negBlk_denote P W _ _ _ _ _ hx

end SubBlocks

/-! ## 7. The Montgomery power and the inversion block -/

/-- The Montgomery multiplication of `xs` by a list of four limbs; on a list of another
    length the continuation receives `xs`. -/
def mulL {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  match ys with
  | [y₀, y₁, y₂, y₃] => mulMK P xs y₀ y₁ y₂ y₃ k
  | _ => k (fun v => v) xs

/-- On the Montgomery forms of `x` and `y`, `mulL` gives the Montgomery form of
    `x * y`. -/
theorem mulL_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4) (hys : ys.length = 4)
    (x y : ZMod P.p) (hx : nv W xs = (x * R P).val) (hy : nv W ys = (y * R P).val)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 → nv W' out = (x * y * R P).val →
      (k r out).denote W' = G) :
    (mulL P xs ys k).denote W = G := by
  obtain ⟨y₀, y₁, y₂, y₃, rfl⟩ : ∃ a b c d, ys = [a, b, c, d] := by
    match ys, hys with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  refine mulMK_denote P xs y₀ y₁ y₂ y₃ k W G hxs (by rw [hx]; exact val_lt P _)
    (by rw [hy]; exact val_lt P _) fun r out W' hr hout hlt hmod => hk r out W' hr hout ?_
  rw [hx, hy] at hmod
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_val, ZMod.cast_id',
    id] at hc
  have hR : ((nv W' out : Nat) : ZMod P.p) = x * y * R P := by
    refine (isUnit_R P).mul_right_cancel ?_
    rw [show R P = 2 ^ 256 from rfl] at hc ⊢
    rw [hc]
    ring
  rw [← hR, ZMod.val_natCast_of_lt hlt]

/-- Left-to-right square-and-multiply over the bits `bs`, most significant first: each
    bit squares the accumulator `acc` and, on `true`, multiplies it by the base `xs`,
    all by Montgomery multiplication. -/
def powK : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → List Bool →
    List (Var Γ w64) → List (Var Γ w64) →
    (∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) → MC Γ ts
  | _, _, [], _, acc, k => k (fun v => v) acc
  | _, _, b :: bs, xs, acc, k =>
      mulL P acc acc fun r₁ sq =>
      bif b then
        mulL P sq (xs.map (fun v => r₁ v)) fun r₂ m =>
        powK bs (xs.map (fun v => r₂ (r₁ v))) m fun r₃ out => k (fun v => r₃ (r₂ (r₁ v))) out
      else
        powK bs (xs.map (fun v => r₁ v)) sq fun r₃ out => k (fun v => r₃ (r₁ v)) out

/-- The value `powK` computes from the accumulator value `u` and the base value `x`. -/
def powVal (x : ZMod P.p) : List Bool → ZMod P.p → ZMod P.p
  | [], u => u
  | b :: bs, u => powVal x bs (bif b then u * u * x else u * u)

/-- The number whose binary digits, most significant first, are `bs`, read after the
    prefix value `n`. -/
def bitsNum : List Bool → Nat → Nat
  | [], n => n
  | b :: bs, n => bitsNum bs (2 * n + b.toNat)

theorem powVal_pow (x : ZMod P.p) : ∀ (bs : List Bool) (n : Nat),
    powVal P x bs (x ^ n) = x ^ bitsNum bs n
  | [], _ => rfl
  | b :: bs, n => by
      rw [powVal, bitsNum, ← powVal_pow x bs]
      congr 1
      cases b <;> simp only [cond_true, cond_false, Bool.toNat_true, Bool.toNat_false] <;> ring

theorem bitsNum_append_single : ∀ (l : List Bool) (b : Bool) (n : Nat),
    bitsNum (l ++ [b]) n = 2 * bitsNum l n + b.toNat
  | [], _, _ => rfl
  | a :: l, b, n => bitsNum_append_single l b (2 * n + a.toNat)

/-- The binary digits of `n`, most significant first. -/
def expBits : Nat → List Bool
  | 0 => []
  | n + 1 => expBits ((n + 1) / 2) ++ [(n + 1) % 2 == 1]
decreasing_by omega

theorem bitsNum_expBits (n : Nat) : bitsNum (expBits n) 0 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [expBits]; rfl
    | succ n =>
      rw [expBits, bitsNum_append_single, ih _ (by omega)]
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> simp [h] <;> omega

/-- On the Montgomery forms of `x` and `u`, `powK` gives the Montgomery form of
    `powVal x bs u`. -/
theorem powK_denote : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (bs : List Bool)
    (xs acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (x u : ZMod P.p),
    xs.length = 4 → acc.length = 4 → nv W xs = (x * R P).val → nv W acc = (u * R P).val →
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (powVal P x bs u * R P).val → (k r out).denote W' = G) →
    (powK P bs xs acc k).denote W = G
  | _, _, [], _, acc, _, W, _, _, _, _, hacc, _, hu, hk => hk _ acc W (Pres.id W) hacc hu
  | _, _, b :: bs, xs, acc, k, W, G, x, u, hxs, hacc, hx, hu, hk => by
      rw [powK]
      refine mulL_denote P acc acc _ W G hacc hacc u u hu hu fun r₁ sq W₁ h₁ hsq hsqv => ?_
      cases b with
      | false =>
        exact powK_denote bs _ sq _ W₁ G x (u * u) (by simp [hxs]) hsq
          (by rw [nv_map h₁, hx]) hsqv fun r₃ out W₃ h₃ hout hv =>
            hk _ out W₃ (Pres.comp h₁ h₃) hout hv
      | true =>
        refine mulL_denote P sq _ _ W₁ G hsq (by simp [hxs]) (u * u) x hsqv
          (by rw [nv_map h₁, hx]) fun r₂ m W₂ h₂ hm hmv => ?_
        exact powK_denote bs _ m _ W₂ G x (u * u * x) (by simp [hxs]) hm
          (by rw [nv_map (Pres.comp h₁ h₂), hx]) hmv fun r₃ out W₃ h₃ hout hv =>
            hk _ out W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) hout hv

/-- Fermat inversion: at a prime modulus, `x^(p-2) = x⁻¹`, including at `x = 0`. -/
theorem pow_sub_two_eq_inv (hp : P.p.Prime) (x : ZMod P.p) : x ^ (P.p - 2) = x⁻¹ := by
  have := Fact.mk hp
  have h3 : 3 ≤ P.p := by have := hp.two_le; have := P.p_odd; omega
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (by omega), ZMod.inv_zero]
  · refine (ZMod.inv_eq_of_mul_eq_one _ _ _ ?_).symm
    rw [← pow_succ', show P.p - 2 + 1 = P.p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one hx

section Inv

variable {Γ : Ctxt jasminDialect}

/-- The Montgomery inversion block: the Montgomery power of `x₀ … x₃` to the exponent
    `p - 2`, from the Montgomery form of `1`. -/
def invBlk (x₀ x₁ x₂ x₃ : Var Γ w64) : MC Γ R4 :=
  constsK (digits (R P).val) fun r₁ one =>
  powK P (expBits (P.p - 2)) [r₁ x₀, r₁ x₁, r₁ x₂, r₁ x₃] one fun r₂ out =>
    ret4 (r₂ (r₁ x₀)) out

/-- On the Montgomery form of `x`, the inversion block gives the Montgomery form of
    `x^(p-2)`. -/
theorem invBlk_denote_pow (W : Valuation Γ) (x₀ x₁ x₂ x₃ : Var Γ w64) (x : ZMod P.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) :
    (invBlk P x₀ x₁ x₂ x₃).denote W = enc P (x ^ (P.p - 2)) := by
  refine constsK_denote _ _ W _ (digits_lt _) fun r₁ one W₁ h₁ hone hv => ?_
  rw [limbsNat_digits _ (val_lt_two_pow P _)] at hv
  refine powK_denote P (expBits (P.p - 2)) _ one _ W₁ _ x 1 rfl
    (hone.trans (digits_length _)) ?_ (by rw [hv, one_mul]) fun r₂ out W₂ _ hout hval => ?_
  · rw [show [r₁ x₀, r₁ x₁, r₁ x₂, r₁ x₃] = [x₀, x₁, x₂, x₃].map (fun v => r₁ v) from rfl,
      nv_map h₁, hx]
  · rw [enc, ret4_denote _ out W₂ hout, hval, ← pow_zero x, powVal_pow, bitsNum_expBits]

/-- At a prime modulus, on the Montgomery form of `x`, the inversion block gives the
    Montgomery form of `x⁻¹`. -/
theorem invBlk_denote_inv (hp : P.p.Prime) (W : Valuation Γ) (x₀ x₁ x₂ x₃ : Var Γ w64)
    (x : ZMod P.p) (hx : nv W [x₀, x₁, x₂, x₃] = (x * R P).val) :
    (invBlk P x₀ x₁ x₂ x₃).denote W = enc P x⁻¹ := by
  rw [invBlk_denote_pow P W x₀ x₁ x₂ x₃ x hx, pow_sub_two_eq_inv P hp]

end Inv

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4
