/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519

/-!
# Montgomery field blocks over four 64-bit limbs for an odd modulus below `2^255`

For a record `Mont4Prime` of an odd modulus `p < 2^255` and the constant
`nInv = -p⁻¹ mod 2^64`, an element `x` of `ZMod p` is represented by the four
little-endian 64-bit limbs of the canonical representative of its Montgomery form
`x · 2^256` (`enc`). The module gives multi-result `jasminDialect` blocks for
addition, multiplication and constants, and a value theorem for each: on operand
limbs holding the Montgomery forms of `x` and `y`, the block denotes `enc (x ⋆ y)`.

The blocks reuse the list combinators of `FieldLimbs.Curve25519` (`adcR`, `rowR`,
`selR`, `constsK`, `addK`, `mulRowK`, `prodK`) and bind `regArith`, `regConst`,
`mulhi`, `addCarryLo`, `addCarryHi` and `select`. None branches or indexes on data.

* Addition: the carry chain, then one conditional subtraction of `p` (`csubPK`),
  which adds `2^256 - p` and selects the sum when its carry is set.
* Multiplication: the 4×4 schoolbook product (`prodK`), four words of Montgomery
  reduction (`redcStepK`), each adding `m · p` for the digit
  `m = (A mod 2^64) · nInv mod 2^64` and dropping the zero low limb, and one
  conditional subtraction. The result `A₄` satisfies `A₄ · 2^256 = x y + M p` with
  `M < 2^256` (`redc_chain`), so `A₄ < 2p`.

## Main definitions

* `Mont4Prime`: the modulus record.
* `csubPK`, `addMK`, `redcStepK`, `mulMK`: the list-level operations.
* `R`, `enc`: the Montgomery factor and the encoding.
* `addBlk`, `mulBlk`, `constBlk`: the blocks; the copy block is
  `FieldLimbs.Curve25519.copyBlk`.

## Main results

* `redc_digit`: the digit `m` makes `A + m p` divisible by `2^64`.
* `redcStepK_denote`, `mulMK_denote`: one reduction word, and the product
  `out · 2^256 ≡ x y (mod p)` with `out < p`.
* `addBlk_denote`, `mulBlk_denote`, `constBlk_denote`, `copyBlk_denote`: the value
  theorems of the blocks.
* `enc_injective`: the encoding is injective.
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
    prodK_denote R4 limbsOf ret4 ret4_denote ofNat_mod_two_pow limbsOf_injective copyBlk)

/-! ## 1. The modulus -/

/-- An odd modulus below `2^255` with the Montgomery constant `nInv = -p⁻¹ mod 2^64`. -/
structure Mont4Prime where
  /-- The modulus. -/
  p : Nat
  /-- `-p⁻¹ mod 2^64`. -/
  nInv : Nat
  one_lt : 1 < p
  p_odd : p % 2 = 1
  p_lt : p < 2 ^ 255
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

/-- `if p ≤ V then V - p else V` is `V % p` below `2p`. -/
theorem csub_eq_mod (V : Nat) (hV : V < 2 * P.p) :
    (if P.p ≤ V then V - P.p else V) = V % P.p := by
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- Addition modulo `p` on four limbs: the carry chain, then one conditional
    subtraction. -/
def addMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  addK xs ys fun r₁ S _ => csubPK P S fun r₂ out => k (fun v => r₂ (r₁ v)) out

theorem addMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4) (hys : ys.length = 4)
    (hx : nv W xs < P.p) (hy : nv W ys < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (nv W xs + nv W ys) % P.p → (k r out).denote W' = G) :
    (addMK P xs ys k).denote W = G := by
  have hp := P.p_lt
  refine addK_denote xs ys _ W G (by rw [hxs, hys]) fun r₁ S c W₁ h₁ hS hSv => ?_
  refine csubPK_denote P S _ W₁ G (by rw [hS, hxs]) fun r₂ out W₂ h₂ hout hv => ?_
  refine hk _ out W₂ (Pres.comp h₁ h₂) hout ?_
  rw [hxs] at hSv
  have hc := (lk1 c W₁).isLt
  have hS0 : nv W₁ S = nv W xs + nv W ys := by
    have : (lk1 c W₁).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * 4) * 1 ≤ 2 ^ (64 * 4) * (lk1 c W₁).toNat :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this] at hSv
    omega
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
    (W : Valuation Γ) (G : ListDenote ts) (hlen : acc.length = 9) (hA : nv W acc < 2 ^ 511)
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
  have hMp : P.p * M < 2 ^ 255 * 2 ^ 64 := Nat.mul_lt_mul'' hp hMlt
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

theorem redc_step_bound (p A A' m : Nat) (hp : p < 2 ^ 255) (hA : A < 2 ^ 511)
    (hm : m < 2 ^ 64) (e : A' * 2 ^ 64 = A + m * p) : A' < 2 ^ 511 := by
  have : m * p < 2 ^ 64 * 2 ^ 255 := Nat.mul_lt_mul'' hm hp
  omega

set_option exponentiation.threshold 600 in
/-- Four words of Montgomery reduction from `T < p²`: the result `A₄` satisfies
    `A₄ · 2^256 = T + M p` with `M < 2^256`, so `A₄ < 2p`. -/
theorem redc_chain (p T A₁ A₂ A₃ A₄ m₁ m₂ m₃ m₄ : Nat) (hp : p < 2 ^ 255)
    (hT : T < p * p) (hm₁ : m₁ < 2 ^ 64) (hm₂ : m₂ < 2 ^ 64) (hm₃ : m₃ < 2 ^ 64)
    (hm₄ : m₄ < 2 ^ 64) (e₁ : A₁ * 2 ^ 64 = T + m₁ * p) (e₂ : A₂ * 2 ^ 64 = A₁ + m₂ * p)
    (e₃ : A₃ * 2 ^ 64 = A₂ + m₃ * p) (e₄ : A₄ * 2 ^ 64 = A₃ + m₄ * p) :
    A₄ * 2 ^ 256 = T + (m₁ + 2 ^ 64 * m₂ + 2 ^ 128 * m₃ + 2 ^ 192 * m₄) * p ∧
      A₄ < 2 * p := by
  have hpp : p * p ≤ 2 ^ 255 * p := Nat.mul_le_mul_right _ hp.le
  have b₁ : m₁ * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have b₂ : m₂ * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have b₃ : m₃ * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have b₄ : m₄ * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have hEq : A₄ * 2 ^ 256 = T + (m₁ + 2 ^ 64 * m₂ + 2 ^ 128 * m₃ + 2 ^ 192 * m₄) * p := by
    linear_combination (2 ^ 192) * e₄ + 2 ^ 128 * e₃ + 2 ^ 64 * e₂ + e₁
  refine ⟨hEq, ?_⟩
  omega

/-- Montgomery multiplication on four limbs: the schoolbook product, four words of
    Montgomery reduction, and one conditional subtraction. -/
def mulMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (y₀ y₁ y₂ y₃ : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  prodK xs y₀ y₁ y₂ y₃ fun r₁ T =>
  bindK (eConst 0) fun r₂ z =>
  redcStepK P (T.map (fun v => r₂ v) ++ [z]) fun r₃ A₁ =>
  redcStepK P A₁ fun r₄ A₂ =>
  redcStepK P A₂ fun r₅ A₃ =>
  redcStepK P A₃ fun r₆ A₄ =>
  csubPK P (A₄.take 4) fun r₇ out =>
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
  have hT510 : X * Y < 2 ^ 511 :=
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
  have htake : nv W₆ (A₄.take 4) = nv W₆ A₄ :=
    nv_take_four W₆ A₄ (by rw [hA₄]; norm_num) (lt_of_lt_of_le hlt (by linarith))
  refine csubPK_denote P (A₄.take 4) _ W₆ G (by simp [hA₄])
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

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4
