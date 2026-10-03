/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontCIOS
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontInstances

/-!
# No-carry CIOS Montgomery multiplication for moduli with a spare top bit

The no-carry variant of the interleaved Montgomery product (the schedule of gnark and
arkworks for moduli whose top bit is clear). The accumulator has `n` limbs, not the
`n + 2` of `mulBlkI`. For each limb `x_i` of the first operand, one fused multiply-add
row (`fmaR`) adds `x_i · y` into the `n` accumulator limbs and leaves its overflow as a
high word and two carry bits; the reduction digit `m = acc_0 · nInv mod 2^64` follows,
a second fused row adds `m · p`, and the low limb, which is zero, is dropped. The two
overflows (two high words and four carry bits) are summed into the new top limb by four
add-with-carry steps (`topK`) with no carry word beyond it.

The sum fits in one word exactly when the new accumulator, which is below `2p`
(`cios_bound`), fits in `n` limbs. This holds when `2p ≤ 2^(64n)`, the certificate
`noCarryOk` on the modulus record. The condition of arkworks (top limb of `p` at most
`2^63 - 2` and the remaining bits not all ones) implies it. After the rows one
conditional subtraction of `p` in the mask form `csubPCK` gives the result, so the block
is branch-free.

A lowering selects the block by the certificate, as `mulBlkSel` does:
`if noCarryOk P then mulBlkNC P xs ys else mulBlk P xs ys`. Both branches carry the
statement of `Mont.mulBlk_denote` (`mulBlkSel_denote`).

## Main definitions

* `noCarryOk`: the spare-bit certificate `2p ≤ 2^(64n)`.
* `topK`: the sum of two words and four carry bits, without overflow.
* `ncRowK`: one operand row and one reduction row on `n` limbs.
* `ncRowsK`, `ncMK`: the rows over a list of operand limbs, and the product.
* `mulBlkNC`, `mulBlkSel`: the block, and the selection by the certificate.

## Main results

* `nc_bound`: under the certificate the accumulator after a row is below `2p` and below
  `2^(64n)`.
* `ncRowK_denote`, `ncRowsK_denote`: one row, and the loop invariant of the rows.
* `ncMK_denote`: the Montgomery product.
* `mulBlkNC_spec`: under `noCarryOk P = true` the block denotes `enc P (x * y)`, the
  statement of `Mont.mulBlk_denote` and `Mont.mulBlkI_denote`.
* `mulBlkNC_denote_eq_mulBlk`: under the certificate the two blocks denote the same value.
* `mulBlkSel_denote`: the selected block denotes `enc P (x * y)` at every modulus.
* Certificates: true at BN254 and BLS12-381; false at P-256, secp256k1, SM2, the P-256
  and secp256k1 group orders, and P-384.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk lk1 eBin eConst eBit eAdc eConst_denote eBin_denote eBit_denote eAdc_denote
    adc_toNat Pres Pres.id Pres.comp bindK bindK_denote nv nv_nil nv_cons nv_map nv_append
    limbsNat)

variable {n : Nat} (P : LimbParams n)

/-! ## 1. The certificate and the bound -/

/-- The spare-bit certificate: `2p ≤ 2^(64n)`, so that every value below `2p` fits in
    `n` limbs. -/
def noCarryOk : Bool := decide (2 * P.p ≤ 2 ^ (64 * n))

theorem noCarryOk_iff : noCarryOk P = true ↔ 2 * P.p ≤ 2 ^ (64 * n) := by
  simp [noCarryOk]

/-- One row and one reduction word keep the accumulator below `2p`, and below `B` when
    `2p ≤ B`. -/
theorem nc_bound (B p A Y x m A' : Nat) (hB : 2 * p ≤ B) (hA : A < 2 * p) (hY : Y < p)
    (hx : x < 2 ^ 64) (hm : m < 2 ^ 64) (e : A' * 2 ^ 64 = A + Y * x + m * p) :
    A' < 2 * p ∧ A' < B := by
  have h := cios_bound p A Y x m A' hA hY hx hm e
  exact ⟨h, by omega⟩

/-! ## 2. The top limb -/

/-- An add-with-carry without overflow is the sum. -/
theorem adc_eq_of_lt (a b : BitVec 64) (c : BitVec 1)
    (h : a.toNat + b.toNat + c.toNat < 2 ^ 64) :
    (addCarryWord a b c).toNat = a.toNat + b.toNat + c.toNat := by
  have := adc_toNat a b c
  omega

/-- The sum `a + b + c₁ + c₂ + c₃ + c₄` of two words and four carry bits by four
    add-with-carry steps; `z` is a zero word. -/
def topK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (a b z : Var Γ w64)
    (c₁ c₂ c₃ c₄ : Var Γ w1)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts) : MC Γ ts :=
  bindK (eAdc a b c₁) fun r₁ t₁ =>
  bindK (eAdc t₁ (r₁ z) (r₁ c₂)) fun r₂ t₂ =>
  bindK (eAdc t₂ (r₂ (r₁ z)) (r₂ (r₁ c₃))) fun r₃ t₃ =>
  bindK (eAdc t₃ (r₃ (r₂ (r₁ z))) (r₃ (r₂ (r₁ c₄)))) fun r₄ t₄ =>
  k (fun v => r₄ (r₃ (r₂ (r₁ v)))) t₄

/-- Below `2^64` the four steps of `topK` compute the sum exactly. -/
theorem topK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (a b z : Var Γ w64)
    (c₁ c₂ c₃ c₄ : Var Γ w1)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hz : (lk z W).toNat = 0)
    (hs : (lk a W).toNat + (lk b W).toNat + (lk1 c₁ W).toNat + (lk1 c₂ W).toNat
      + (lk1 c₃ W).toNat + (lk1 c₄ W).toNat < 2 ^ 64)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (t : Var Δ w64) (W' : Valuation Δ),
      Pres r W W' → (lk t W').toNat = (lk a W).toNat + (lk b W).toNat + (lk1 c₁ W).toNat
        + (lk1 c₂ W).toNat + (lk1 c₃ W).toNat + (lk1 c₄ W).toNat → (k r t).denote W' = G) :
    (topK a b z c₁ c₂ c₃ c₄ k).denote W = G := by
  refine bindK_denote _ _ _ _ fun r₁ t₁ W₁ h₁ ht₁ => ?_
  refine bindK_denote _ _ _ _ fun r₂ t₂ W₂ h₂ ht₂ => ?_
  refine bindK_denote _ _ _ _ fun r₃ t₃ W₃ h₃ ht₃ => ?_
  refine bindK_denote _ _ _ _ fun r₄ t₄ W₄ h₄ ht₄ => ?_
  have e₁ : (lk t₁ W₁).toNat = (lk a W).toNat + (lk b W).toNat + (lk1 c₁ W).toNat := by
    rw [show lk t₁ W₁ = _ from ht₁, eAdc_denote]
    exact adc_eq_of_lt _ _ _ (by omega)
  have e₂ : (lk t₂ W₂).toNat = (lk t₁ W₁).toNat + (lk1 c₂ W).toNat := by
    rw [show lk t₂ W₂ = _ from ht₂, eAdc_denote, show lk (r₁ z) W₁ = lk z W from h₁ z,
      show lk1 (r₁ c₂) W₁ = lk1 c₂ W from h₁ c₂, adc_eq_of_lt _ _ _ (by omega), hz,
      Nat.add_zero]
  have e₃ : (lk t₃ W₃).toNat = (lk t₂ W₂).toNat + (lk1 c₃ W).toNat := by
    rw [show lk t₃ W₃ = _ from ht₃, eAdc_denote,
      show lk (r₂ (r₁ z)) W₂ = lk z W from (h₂ _).trans (h₁ z),
      show lk1 (r₂ (r₁ c₃)) W₂ = lk1 c₃ W from (h₂ _).trans (h₁ c₃),
      adc_eq_of_lt _ _ _ (by omega), hz, Nat.add_zero]
  have e₄ : (lk t₄ W₄).toNat = (lk t₃ W₃).toNat + (lk1 c₄ W).toNat := by
    rw [show lk t₄ W₄ = _ from ht₄, eAdc_denote,
      show lk (r₃ (r₂ (r₁ z))) W₃ = lk z W from (h₃ _).trans ((h₂ _).trans (h₁ z)),
      show lk1 (r₃ (r₂ (r₁ c₄))) W₃ = lk1 c₄ W from (h₃ _).trans ((h₂ _).trans (h₁ c₄)),
      adc_eq_of_lt _ _ _ (by omega), hz, Nat.add_zero]
  exact hk _ t₄ W₄ (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄) (by omega)

/-! ## 3. One row -/

/-- One row of the no-carry schedule on the `n` limbs `acc`: the fused row `x · ys + acc`,
    the digit `m = S_0 · ni mod 2^64` of its low limb, the fused row `m · p + S` over the
    digits of `p` bound at their use, and the upper `n - 1` limbs of the result followed
    by the sum of both overflows (`topK`). `ni` is the word `nInv`, `z` a zero word. -/
def ncRowK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ys : List (Var Γ w64))
    (x ni z : Var Γ w64) (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eBit 0) fun r₁ c =>
  fmaR r₁ (ys.map Sum.inl) acc (r₁ x) (r₁ z) (r₁ z) c c fun r₂ S cA₁ cB₁ g₁ =>
  bindK (eBin .mul (S.headD (r₂ (r₁ z))) (r₂ (r₁ ni))) fun r₃ m =>
  fmaR r₃ ((digits n P.p).map Sum.inr) S m (r₃ (r₂ (r₁ z))) (r₃ (r₂ (r₁ z))) (r₃ (r₂ c))
    (r₃ (r₂ c)) fun r₄ T cA₂ cB₂ g₂ =>
  topK (r₄ (r₃ g₁)) g₂ (r₄ (r₃ (r₂ (r₁ z)))) (r₄ (r₃ cA₁)) (r₄ (r₃ cB₁)) cA₂ cB₂ fun r₅ t =>
  k (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) (T.tail.map (fun v => r₅ v) ++ [t])

/-- Under the certificate one row maps an accumulator `A < 2p` to `A' < 2p` on `n` limbs
    with `A' · 2^64 = A + Y x + m p`, `m < 2^64`. -/
theorem ncRowK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ys : List (Var Γ w64))
    (x ni z : Var Γ w64) (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hc : noCarryOk P = true)
    (hys : ys.length = n) (hacc : acc.length = n) (hY : nv W ys < P.p)
    (hA : nv W acc < 2 * P.p) (hni : (lk ni W).toNat = P.nInv) (hz : (lk z W).toNat = 0)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out < 2 * P.p →
      (∃ m, m < 2 ^ 64 ∧ nv W' out * 2 ^ 64 = nv W acc + nv W ys * (lk x W).toNat + m * P.p) →
      (k r out).denote W' = G) :
    (ncRowK P ys x ni z acc k).denote W = G := by
  have hp := P.p_lt
  have hcert := (noCarryOk_iff P).mp hc
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := n_pos P; omega⟩
  have hB := two_pow_succ n'
  have hxl := (lk x W).isLt
  refine bindK_denote _ _ _ _ fun r₁ c W₁ h₁ hcv => ?_
  have ec : (lk1 c W₁).toNat = 0 := by rw [show lk1 c W₁ = _ from hcv, eBit_denote]; rfl
  have ez1 : (lk (r₁ z) W₁).toNat = 0 := by rw [show lk (r₁ z) W₁ = lk z W from h₁ z, hz]
  refine fmaR_denote r₁ _ _ _ _ _ c c _ W W₁ G h₁ ez1 (by simp [hys, hacc])
    fun r₂ S cA₁ cB₁ g₁ W₂ h₂ hS hSv => ?_
  rw [svs_inl, ez1, ec, show lk (r₁ x) W₁ = lk x W from h₁ x, hacc] at hSv
  rw [hacc] at hS
  have h12 : Pres (fun v => r₂ (r₁ v)) W W₂ := Pres.comp h₁ h₂
  obtain ⟨s₀, St, rfl⟩ : ∃ s₀ St, S = s₀ :: St := by
    cases S with
    | nil => simp at hS
    | cons s₀ St => exact ⟨s₀, St, rfl⟩
  refine bindK_denote _ _ _ _ fun r₃ m W₃ h₃ hm => ?_
  set M := nv W₂ (s₀ :: St) % 2 ^ 64 * P.nInv % 2 ^ 64 with hM
  have hMlt : M < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have em : (lk m W₃).toNat = M := by
    rw [show lk m W₃ = _ from hm, List.headD_cons, eBin_denote]
    show (lk s₀ W₂ * lk (r₂ (r₁ ni)) W₂).toNat = M
    rw [BitVec.toNat_mul, nv_cons_mod W₂ s₀ St, show lk (r₂ (r₁ ni)) W₂ = lk ni W from h12 ni,
      hni]
  have ez3 : (lk (r₃ (r₂ (r₁ z))) W₃).toNat = 0 := by
    rw [show lk (r₃ (r₂ (r₁ z))) W₃ = lk z W from (h₃ _).trans (h12 z), hz]
  have ec3 : (lk1 (r₃ (r₂ c)) W₃).toNat = 0 := by
    rw [show lk1 (r₃ (r₂ c)) W₃ = lk1 c W₁ from (h₃ _).trans (h₂ c), ec]
  refine fmaR_denote r₃ _ _ _ _ _ _ _ _ W₂ W₃ G h₃ ez3 (by simp [digits_length, hS])
    fun r₄ T cA₂ cB₂ g₂ W₄ h₄ hT hTv => ?_
  rw [svs_inr_digits, limbsNat_digits _ _ hp, em, ez3, ec3, hS] at hTv
  rw [hS] at hT
  obtain ⟨t₀, Tt, rfl⟩ : ∃ t₀ Tt, T = t₀ :: Tt := by
    cases T with
    | nil => simp at hT
    | cons t₀ Tt => exact ⟨t₀, Tt, rfl⟩
  have hTt : Tt.length = n' := by simpa using hT
  have hdig : (nv W₂ (s₀ :: St) + M * P.p) % 2 ^ 64 = 0 := redc_digit P _
  have ht0l := (lk t₀ W₄).isLt
  rw [nv_cons, hB] at hTv
  rw [hB] at hSv hcert
  have hQ : (lk t₀ W₄).toNat + 2 ^ 64 * (nv W₄ Tt + 2 ^ (64 * n') *
      ((lk1 cA₂ W₄).toNat + (lk1 cB₂ W₄).toNat + (lk g₂ W₄).toNat))
      = nv W₂ (s₀ :: St) + M * P.p := by
    linear_combination hTv
  have ht0 : (lk t₀ W₄).toNat = 0 := by
    generalize nv W₄ Tt + 2 ^ (64 * n') *
      ((lk1 cA₂ W₄).toNat + (lk1 cB₂ W₄).toNat + (lk g₂ W₄).toNat) = Q at hQ
    generalize nv W₂ (s₀ :: St) + M * P.p = V at hQ hdig
    omega
  rw [ht0, Nat.zero_add] at hQ
  set c₁ := (lk1 cA₁ W₂).toNat + (lk1 cB₁ W₂).toNat + (lk g₁ W₂).toNat with hc₁
  set c₂ := (lk1 cA₂ W₄).toNat + (lk1 cB₂ W₄).toNat + (lk g₂ W₄).toNat with hc₂
  have e : (nv W₄ Tt + 2 ^ (64 * n') * (c₁ + c₂)) * 2 ^ 64
      = nv W acc + nv W ys * (lk x W).toNat + M * P.p := by
    linear_combination hQ + hSv
  obtain ⟨hA', hAB⟩ := nc_bound _ P.p _ _ _ _ _ hcert hA hY hxl hMlt e
  have hsum : c₁ + c₂ < 2 ^ 64 := by
    have h1 : 2 ^ (64 * n') * (c₁ + c₂) < 2 ^ (64 * n') * 2 ^ 64 := by omega
    exact Nat.lt_of_mul_lt_mul_left h1
  have eg₁ : lk (r₄ (r₃ g₁)) W₄ = lk g₁ W₂ := (h₄ _).trans (h₃ _)
  have ecA₁ : lk1 (r₄ (r₃ cA₁)) W₄ = lk1 cA₁ W₂ := (h₄ _).trans (h₃ _)
  have ecB₁ : lk1 (r₄ (r₃ cB₁)) W₄ = lk1 cB₁ W₂ := (h₄ _).trans (h₃ _)
  have ez4 : (lk (r₄ (r₃ (r₂ (r₁ z)))) W₄).toNat = 0 := by
    rw [show lk (r₄ (r₃ (r₂ (r₁ z)))) W₄ = lk z W from (h₄ _).trans ((h₃ _).trans (h12 z)), hz]
  refine topK_denote _ _ _ _ _ _ _ _ W₄ G ez4 (by rw [eg₁, ecA₁, ecB₁]; omega)
    fun r₅ t W₅ h₅ ht => ?_
  rw [eg₁, ecA₁, ecB₁] at ht
  have hout : nv W₅ ((t₀ :: Tt).tail.map (fun v => r₅ v) ++ [t])
      = nv W₄ Tt + 2 ^ (64 * n') * (c₁ + c₂) := by
    rw [List.tail_cons, nv_append, nv_map h₅, List.length_map, hTt, nv_cons, nv_nil, ht]
    ring
  refine hk _ _ W₅ (Pres.comp (Pres.comp (Pres.comp h12 h₃) h₄) h₅) (by simp [hTt])
    (by rw [hout]; exact hA') ⟨M, hMlt, by rw [hout]; exact e⟩

/-! ## 4. The rows -/

/-- The no-carry rows over the operand limbs `xs`, which live in the source context of
    the renaming `ren`, into the `n`-limb accumulator `acc`; `ys` are the limbs of the
    second operand, `ni` the word `nInv` and `z` a zero word. -/
def ncRowsK : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ →
    List (Var Δ w64) → Var Δ w64 → Var Δ w64 → List (Var Γ w64) →
    List (Var Δ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, _, _, _, _, [], acc, k => k (fun v => v) acc
  | _, _, _, ren, ys, ni, z, x :: xs, acc, k =>
      ncRowK P ys (ren x) ni z acc fun r₁ A =>
      ncRowsK (fun v => r₁ (ren v)) (ys.map fun v => r₁ v) (r₁ ni) (r₁ z) xs A fun r₂ out =>
        k (fun v => r₂ (r₁ v)) out

/-- The loop invariant of the no-carry rows: under the certificate, from an `n`-limb
    accumulator `A₀ < 2p` the rows over `xs` give an `n`-limb accumulator below `2p` with
    `acc · 2^(64s) = A₀ + X Y + M p`, `M < 2^(64s)`, for `s` the number of rows. -/
theorem ncRowsK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (W : Valuation Γ)
    (xs : List (Var Γ w64)) : ∀ {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom Γ Δ) (ys : List (Var Δ w64)) (ni z : Var Δ w64)
    (acc : List (Var Δ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W₀ : Valuation Δ) (G : ListDenote ts), noCarryOk P = true →
    Pres ren W W₀ → ys.length = n → nv W₀ ys < P.p →
    (lk ni W₀).toNat = P.nInv → (lk z W₀).toNat = 0 → acc.length = n →
    nv W₀ acc < 2 * P.p →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
      (W' : Valuation Δ'), Pres r W₀ W' → out.length = n → nv W' out < 2 * P.p →
      (∃ M, M < 2 ^ (64 * xs.length) ∧
        nv W' out * 2 ^ (64 * xs.length) = nv W₀ acc + nv W xs * nv W₀ ys + M * P.p) →
      (k r out).denote W' = G) →
    (ncRowsK P ren ys ni z xs acc k).denote W₀ = G := by
  induction xs with
  | nil =>
    intro Δ ren ys ni z acc k W₀ G _ _ _ _ _ _ hacc hA hk
    rw [ncRowsK]
    exact hk _ acc W₀ (Pres.id W₀) hacc hA ⟨0, by simp, by simp [nv_nil]⟩
  | cons x xs ih =>
    intro Δ ren ys ni z acc k W₀ G hc hren hys hY hni hz hacc hA hk
    rw [ncRowsK]
    have ex : (lk (ren x) W₀).toNat = (lk x W).toNat := by
      rw [show lk (ren x) W₀ = lk x W from hren x]
    refine ncRowK_denote P ys (ren x) ni z acc _ W₀ G hc hys hacc hY hA hni hz
      fun r₁ A W₁ h₁ hAl hA' ⟨m, hm, e₁⟩ => ?_
    rw [ex] at e₁
    refine ih (fun v => r₁ (ren v)) _ _ _ A _ W₁ G hc (Pres.comp hren h₁)
      (by simp [hys]) (by rw [nv_map h₁]; exact hY)
      (by rw [show lk (r₁ ni) W₁ = lk ni W₀ from h₁ ni, hni])
      (by rw [show lk (r₁ z) W₁ = lk z W₀ from h₁ z, hz]) hAl hA'
      fun r₂ out W₂ h₂ hout hlt ⟨M, hM, e₂⟩ => ?_
    refine hk _ out W₂ (Pres.comp h₁ h₂) hout hlt ⟨m + 2 ^ 64 * M, ?_, ?_⟩
    · simp only [List.length_cons]
      rw [two_pow_succ]
      omega
    · rw [nv_map h₁] at e₂
      simp only [List.length_cons]
      rw [two_pow_succ, nv_cons]
      linear_combination 2 ^ 64 * e₂ + e₁

/-! ## 5. The Montgomery product -/

/-- The no-carry Montgomery product on `n` limbs: the word `nInv` and a zero word; the
    rows (`ncRowsK`) from the zero accumulator of `n` limbs; one conditional subtraction
    on the accumulator widened by a zero limb. -/
def ncMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst P.nInv) fun r₁ ni =>
  bindK (eConst 0) fun r₂ z =>
  ncRowsK P (fun v => r₂ (r₁ v)) (ys.map fun v => r₂ (r₁ v)) (r₂ ni) z xs
    (List.replicate n z) fun r₃ B =>
  csubPCK P (B ++ [r₃ z]) fun r₄ out =>
  k (fun v => r₄ (r₃ (r₂ (r₁ v)))) out

theorem ncMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hc : noCarryOk P = true) (hxs : xs.length = n)
    (hys : ys.length = n) (hy : nv W ys < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out < P.p →
      nv W' out * 2 ^ (64 * n) ≡ nv W xs * nv W ys [MOD P.p] →
      (k r out).denote W' = G) :
    (ncMK P xs ys k).denote W = G := by
  have hp := P.p_lt
  have hcert := (noCarryOk_iff P).mp hc
  refine bindK_denote _ _ _ _ fun r₁ ni W₁ h₁ hni => ?_
  refine bindK_denote _ _ _ _ fun r₂ z W₂ h₂ hz => ?_
  have h12 : Pres (fun v => r₂ (r₁ v)) W W₂ := Pres.comp h₁ h₂
  have eni : (lk (r₂ ni) W₂).toNat = P.nInv := by
    rw [show lk (r₂ ni) W₂ = lk ni W₁ from h₂ ni, show lk ni W₁ = _ from hni, eConst_denote,
      BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt P.nInv_lt
  have ez : (lk z W₂).toNat = 0 := by rw [show lk z W₂ = _ from hz, eConst_denote]; rfl
  refine ncRowsK_denote P W xs (fun v => r₂ (r₁ v)) _ _ _ _ _ W₂ G hc h12 (by simp [hys])
    (by rw [nv_map h12]; exact hy) eni ez (by simp) (by rw [nv_replicate W₂ z ez]; omega)
    fun r₃ B W₃ h₃ hBl hB ⟨M, _, e₂⟩ => ?_
  rw [nv_map h12, nv_replicate W₂ z ez, hxs, Nat.zero_add] at e₂
  have ez3 : (lk (r₃ z) W₃).toNat = 0 := by rw [show lk (r₃ z) W₃ = lk z W₂ from h₃ z, ez]
  have hBz : nv W₃ (B ++ [r₃ z]) = nv W₃ B := by
    rw [nv_append, nv_cons, nv_nil, ez3]
    simp
  refine csubPCK_denote P _ _ W₃ G (by simp [hBl]) (by rw [hBz]; omega)
    fun r₄ out W₄ h₄ hout hv => ?_
  rw [hBz] at hv
  refine hk _ out W₄ (Pres.comp (Pres.comp h12 h₃) h₄) hout ?_ ?_
  · rw [hv, csub_eq_mod P _ hB]
    exact Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one P.one_lt)
  · rw [hv, csub_eq_mod P _ hB]
    unfold Nat.ModEq
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, e₂, Nat.add_mul_mod_self_right]

/-! ## 6. The blocks -/

section Blocks

variable {Γ : Ctxt jasminDialect}

/-- The no-carry Montgomery multiplication block. -/
def mulBlkNC (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  ncMK P xs ys fun _ out => retN n out

/-- The multiplication block selected by the certificate: `mulBlkNC` when
    `noCarryOk P`, `mulBlk` otherwise. -/
def mulBlkSel (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  if noCarryOk P then mulBlkNC P xs ys else mulBlk P xs ys

variable (W : Valuation Γ)

/-- Under the certificate the no-carry block denotes the Montgomery form of `x * y`, the
    statement of `mulBlk_denote` and `mulBlkI_denote`. -/
theorem mulBlkNC_spec (hc : noCarryOk P = true) (xs ys : List (Var Γ w64))
    (hxs : xs.length = n) (hys : ys.length = n) (x y : ZMod P.p)
    (hx : nv W xs = (x * R P).val) (hy : nv W ys = (y * R P).val) :
    (mulBlkNC P xs ys).denote W = enc P (x * y) := by
  refine ncMK_denote P _ _ _ W _ hc hxs hys (by rw [hy]; exact val_lt P _)
    fun r out W' _ hout hlt hmod => ?_
  rw [hx, hy] at hmod
  rw [retN_denote _ out W' hout, enc, mont_val_eq P x y _ hlt hmod]

/-- Under the certificate the no-carry block and `mulBlk` denote the same value. -/
theorem mulBlkNC_denote_eq_mulBlk (hc : noCarryOk P = true) (xs ys : List (Var Γ w64))
    (hxs : xs.length = n) (hys : ys.length = n) (x y : ZMod P.p)
    (hx : nv W xs = (x * R P).val) (hy : nv W ys = (y * R P).val) :
    (mulBlkNC P xs ys).denote W = (mulBlk P xs ys).denote W := by
  rw [mulBlkNC_spec P W hc xs ys hxs hys x y hx hy, mulBlk_denote P W xs ys hxs hys x y hx hy]

/-- The selected block denotes the Montgomery form of `x * y` at every modulus. -/
theorem mulBlkSel_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n)
    (hys : ys.length = n) (x y : ZMod P.p) (hx : nv W xs = (x * R P).val)
    (hy : nv W ys = (y * R P).val) :
    (mulBlkSel P xs ys).denote W = enc P (x * y) := by
  unfold mulBlkSel
  split
  · exact mulBlkNC_spec P W (by assumption) xs ys hxs hys x y hx hy
  · exact mulBlk_denote P W xs ys hxs hys x y hx hy

end Blocks

/-! ## 7. The certificates at the instances -/

theorem bn254_noCarryOk : noCarryOk Mont4Instances.bn254 = true := by decide

theorem p256_noCarryOk : noCarryOk Mont4Instances.p256 = false := by decide

theorem secp256k1_noCarryOk : noCarryOk Mont4Instances.secp256k1 = false := by decide

theorem sm2_noCarryOk : noCarryOk Mont4Instances.sm2 = false := by decide

theorem p256n_noCarryOk : noCarryOk Mont4Instances.p256n = false := by decide

theorem secp256k1n_noCarryOk : noCarryOk Mont4Instances.secp256k1n = false := by decide

set_option exponentiation.threshold 600 in
theorem bls12381_noCarryOk : noCarryOk MontInstances.bls12381 = true := by decide

set_option exponentiation.threshold 600 in
theorem p384_noCarryOk : noCarryOk MontInstances.p384 = false := by decide

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
