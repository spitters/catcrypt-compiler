/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

/-!
# Interleaved (CIOS) Montgomery multiplication over `n` 64-bit limbs

The coarsely integrated operand scanning schedule of the Montgomery product, the
schedule of fiat-crypto's word-by-word Montgomery backends: for each limb `x_i` of the
first operand, the row `x_i · y` is added into an `n + 1`-limb accumulator, widened to
`n + 2` limbs, and one word of Montgomery reduction follows,
`m := acc_0 · nInv mod 2^64; acc := (acc + m p) / 2^64`. After the `n` rows one
conditional subtraction of `p` on `n + 1` limbs gives the result. The limbs of `p`,
the constant `nInv` and a zero word are bound once and shared by all rows.

The accumulator stays below `2p` after every row (`cios_bound`), and after the rows
over `x_0, …, x_{s-1}` it satisfies `acc · 2^(64s) = acc₀ + X Y + M p` with
`M < 2^(64s)` (`ciosRowsK_denote`).

## Main definitions

* `ciosAddK`: the row `x · ys` added into an `n + 1`-limb accumulator.
* `ciosRedK`: one word of Montgomery reduction on `n + 2` limbs.
* `ciosRowsK`: the rows and reduction words over a list of operand limbs.
* `ciosMK`, `mulBlkI`: the interleaved Montgomery product and its block.

## Main results

* `ciosRowsK_denote`: the loop invariant of the rows.
* `ciosMK_denote`, `ciosMK_denote_enc`: the Montgomery product.
* `mulBlkI_denote`: the block denotes `enc P (x * y)`, the statement of
  `Mont.mulBlk_denote`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk lk1 eBin eConst eConst_denote eBin_denote Pres Pres.id Pres.comp bindK
    bindK_denote nv nv_nil nv_cons nv_map nv_append nv_lt constsK constsK_denote addK
    addK_denote mulRowK mulRowK_denote)

variable {n : Nat} (P : LimbParams n)

/-! ## 1. Arithmetic of one row -/

/-- One row and one reduction word keep the accumulator below `2p`: from `A < 2p`,
    `Y < p`, `x, m < 2^64` and `A' · 2^64 = A + Y x + m p` follows `A' < 2p`. -/
theorem cios_bound (p A Y x m A' : Nat) (hA : A < 2 * p) (hY : Y < p) (hx : x < 2 ^ 64)
    (hm : m < 2 ^ 64) (e : A' * 2 ^ 64 = A + Y * x + m * p) : A' < 2 * p := by
  have h1 : Y * x ≤ Y * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : m * p ≤ (2 ^ 64 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have h3 : Y * (2 ^ 64 - 1) ≤ (p - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The sum of an accumulator below `2p` and a row is below `2^65 p`. -/
theorem cios_row_lt (p A Y x : Nat) (hA : A < 2 * p) (hY : Y < p) (hx : x < 2 ^ 64) :
    A + Y * x < 2 ^ 64 * (2 * p) := by
  have h1 : Y * x ≤ Y * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : Y * (2 ^ 64 - 1) ≤ (p - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- `2^(64(n+2))` as `2^(64n) · 2^64 · 2^64`. -/
theorem two_pow_add_two (k : Nat) : 2 ^ (64 * (k + 2)) = 2 ^ (64 * k) * 2 ^ 64 * 2 ^ 64 := by
  rw [show 64 * (k + 2) = 64 * k + 64 + 64 by ring, Nat.pow_add, Nat.pow_add]

/-! ## 2. The row and the reduction word -/

/-- The row `x · ys` added into the `n + 1` limbs `acc`, as `n + 2` limbs; `z` is a
    zero word. -/
def ciosAddK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ys : List (Var Γ w64))
    (x z : Var Γ w64) (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  mulRowK ys x fun r₁ row =>
  addK (acc.map (fun v => r₁ v) ++ [r₁ z]) (row ++ [r₁ z]) fun r₂ S _ =>
  k (fun v => r₂ (r₁ v)) S

theorem ciosAddK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (ys : List (Var Γ w64)) (x z : Var Γ w64) (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hys : ys.length = n) (hacc : acc.length = n + 1)
    (hz : (lk z W).toNat = 0)
    (hb : nv W acc + nv W ys * (lk x W).toNat < 2 ^ (64 * (n + 2)))
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n + 2 →
      nv W' out = nv W acc + nv W ys * (lk x W).toNat → (k r out).denote W' = G) :
    (ciosAddK ys x z acc k).denote W = G := by
  refine mulRowK_denote ys x _ W G fun r₁ row W₁ h₁ hrow hrowv => ?_
  have ez : (lk (r₁ z) W₁).toNat = 0 := by rw [show lk (r₁ z) W₁ = lk z W from h₁ z, hz]
  refine addK_denote _ _ _ W₁ G (by simp [hacc, hrow, hys]) fun r₂ S c W₂ h₂ hS hSv => ?_
  rw [nv_append, nv_append, nv_map h₁, hrowv, nv_cons, nv_nil, ez] at hSv
  simp only [List.length_append, List.length_map, List.length_singleton, hacc,
    Nat.mul_zero, Nat.add_zero] at hSv hS
  refine hk _ S W₂ (Pres.comp h₁ h₂) hS ?_
  have hc := (lk1 c W₂).isLt
  rw [show n + 1 + 1 = n + 2 from rfl] at hSv
  have h0 : (lk1 c W₂).toNat = 0 := by
    by_contra hne
    have : 2 ^ (64 * (n + 2)) * 1 ≤ 2 ^ (64 * (n + 2)) * (lk1 c W₂).toNat :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  rw [h0] at hSv
  omega

/-- One word of Montgomery reduction on the `n + 2` limbs `S` of value `V`: the digit
    `m = (V mod 2^64) · nInv mod 2^64` from the word `ni = nInv`, the sum `V + m p`
    with the limbs `PL` of `p` (its low limb is zero), and its upper `n + 1` limbs. -/
def ciosRedK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (S PL : List (Var Γ w64))
    (ni z : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eBin .mul (S.headD z) ni) fun r₁ m =>
  mulRowK (PL.map fun v => r₁ v) m fun r₂ row =>
  addK (S.map fun v => r₂ (r₁ v)) (row ++ [r₂ (r₁ z)]) fun r₃ T _ =>
  k (fun v => r₃ (r₂ (r₁ v))) T.tail

theorem ciosRedK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (S PL : List (Var Γ w64)) (ni z : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : S.length = n + 2) (hPL : PL.length = n)
    (hPLv : nv W PL = P.p) (hni : (lk ni W).toNat = P.nInv) (hz : (lk z W).toNat = 0)
    (hV : nv W S < 2 ^ 64 * (2 * P.p))
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n + 1 →
      (∃ m, m < 2 ^ 64 ∧ nv W' out * 2 ^ 64 = nv W S + m * P.p) →
      (k r out).denote W' = G) :
    (ciosRedK S PL ni z k).denote W = G := by
  have hp := P.p_lt
  have hQ := two_pow_add_two n
  obtain ⟨x, rest, rfl⟩ : ∃ x rest, S = x :: rest := by
    cases S with
    | nil => simp at hlen
    | cons x rest => exact ⟨x, rest, rfl⟩
  refine bindK_denote _ _ _ _ fun r₁ m W₁ h₁ hm => ?_
  set M := nv W (x :: rest) % 2 ^ 64 * P.nInv % 2 ^ 64 with hM
  have em : (lk m W₁).toNat = M := by
    rw [show lk m W₁ = _ from hm, List.headD_cons, eBin_denote]
    show (lk x W * lk ni W).toNat = M
    rw [BitVec.toNat_mul, nv_cons_mod W x rest, hni]
  refine mulRowK_denote _ m _ W₁ G fun r₂ row W₂ h₂ hrow hrowv => ?_
  rw [nv_map h₁, hPLv, em] at hrowv
  rw [List.length_map, hPL] at hrow
  have h12 : Pres (fun v => r₂ (r₁ v)) W W₂ := Pres.comp h₁ h₂
  have ez : (lk (r₂ (r₁ z)) W₂).toNat = 0 := by
    rw [show lk (r₂ (r₁ z)) W₂ = lk z W from h12 z, hz]
  refine addK_denote _ _ _ W₂ G (by simp at hlen ⊢; omega) fun r₃ T c W₃ h₃ hT hTv => ?_
  rw [nv_map h12, nv_append, nv_cons W₂ _ [], nv_nil, ez, hrowv] at hTv
  rw [List.length_map, hlen] at hT hTv
  simp only [Nat.mul_zero, Nat.add_zero] at hTv
  have hMlt : M < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hMp : P.p * M ≤ P.p * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
  have hc := (lk1 c W₃).isLt
  have hT0 : nv W₃ T = nv W (x :: rest) + P.p * M := by
    have : (lk1 c W₃).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * (n + 2)) * 1 ≤ 2 ^ (64 * (n + 2)) * (lk1 c W₃).toNat :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this] at hTv
    omega
  obtain ⟨t₀, Tt, rfl⟩ : ∃ t₀ Tt, T = t₀ :: Tt := by
    cases T with
    | nil => simp at hT
    | cons t₀ Tt => exact ⟨t₀, Tt, rfl⟩
  have hdig : (nv W (x :: rest) + M * P.p) % 2 ^ 64 = 0 := redc_digit P _
  have ht₀ : (lk t₀ W₃).toNat = 0 := by
    rw [nv_cons_mod W₃ t₀ Tt, hT0, Nat.mul_comm P.p M, hdig]
  refine hk _ _ W₃ (Pres.comp h12 h₃) (by simp at hT ⊢; omega) ⟨M, hMlt, ?_⟩
  rw [List.tail_cons]
  rw [nv_cons, ht₀] at hT0
  rw [Nat.mul_comm M P.p]
  omega

/-! ## 3. The rows -/

/-- The rows and reduction words over the operand limbs `xs`, which live in the source
    context of the renaming `ren`, into the accumulator `acc`; `ys` are the limbs of
    the second operand, `PL` the limbs of `p`, `ni` the word `nInv` and `z` a zero
    word. -/
def ciosRowsK : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ →
    List (Var Δ w64) → List (Var Δ w64) → Var Δ w64 → Var Δ w64 → List (Var Γ w64) →
    List (Var Δ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, _, _, _, _, _, [], acc, k => k (fun v => v) acc
  | _, _, _, ren, ys, PL, ni, z, x :: xs, acc, k =>
      ciosAddK ys (ren x) z acc fun r₁ S =>
      ciosRedK S (PL.map fun v => r₁ v) (r₁ ni) (r₁ z) fun r₂ A =>
      ciosRowsK (fun v => r₂ (r₁ (ren v))) (ys.map fun v => r₂ (r₁ v))
        (PL.map fun v => r₂ (r₁ v)) (r₂ (r₁ ni)) (r₂ (r₁ z)) xs A fun r₃ out =>
        k (fun v => r₃ (r₂ (r₁ v))) out

/-- The loop invariant of the rows: from an accumulator `A₀ < 2p`, the rows over `xs`
    give an accumulator below `2p` with `acc · 2^(64s) = A₀ + X Y + M p`, `M < 2^(64s)`,
    for `s` the number of rows. -/
theorem ciosRowsK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (W : Valuation Γ)
    (xs : List (Var Γ w64)) : ∀ {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom Γ Δ) (ys PL : List (Var Δ w64)) (ni z : Var Δ w64)
    (acc : List (Var Δ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ → ys.length = n → nv W₀ ys < P.p → PL.length = n → nv W₀ PL = P.p →
    (lk ni W₀).toNat = P.nInv → (lk z W₀).toNat = 0 → acc.length = n + 1 →
    nv W₀ acc < 2 * P.p →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
      (W' : Valuation Δ'), Pres r W₀ W' → out.length = n + 1 → nv W' out < 2 * P.p →
      (∃ M, M < 2 ^ (64 * xs.length) ∧
        nv W' out * 2 ^ (64 * xs.length) = nv W₀ acc + nv W xs * nv W₀ ys + M * P.p) →
      (k r out).denote W' = G) →
    (ciosRowsK ren ys PL ni z xs acc k).denote W₀ = G := by
  induction xs with
  | nil =>
    intro Δ ren ys PL ni z acc k W₀ G _ _ _ _ _ _ _ hacc hA hk
    rw [ciosRowsK]
    exact hk _ acc W₀ (Pres.id W₀) hacc hA ⟨0, by simp, by simp [nv_nil]⟩
  | cons x xs ih =>
    intro Δ ren ys PL ni z acc k W₀ G hren hys hY hPL hPLv hni hz hacc hA hk
    rw [ciosRowsK]
    have hp := P.p_lt
    have hQ := two_pow_add_two n
    have ex : (lk (ren x) W₀).toNat = (lk x W).toNat := by
      rw [show lk (ren x) W₀ = lk x W from hren x]
    have hx := (lk x W).isLt
    have hrow := cios_row_lt P.p _ _ _ hA hY hx
    refine ciosAddK_denote ys (ren x) z acc _ W₀ G hys hacc hz (by rw [ex]; omega)
      fun r₁ S W₁ h₁ hS hSv => ?_
    rw [ex] at hSv
    refine ciosRedK_denote P S _ _ _ _ W₁ G hS (by simp [hPL]) (by rw [nv_map h₁, hPLv])
      (by rw [show lk (r₁ ni) W₁ = lk ni W₀ from h₁ ni, hni])
      (by rw [show lk (r₁ z) W₁ = lk z W₀ from h₁ z, hz]) (by rw [hSv]; exact hrow)
      fun r₂ A W₂ h₂ hAl ⟨m, hm, e₁⟩ => ?_
    rw [hSv] at e₁
    have hA' := cios_bound P.p _ _ _ _ _ hA hY hx hm e₁
    have h12 : Pres (fun v => r₂ (r₁ v)) W₀ W₂ := Pres.comp h₁ h₂
    refine ih (fun v => r₂ (r₁ (ren v))) _ _ _ _ A _ W₂ G (Pres.comp hren h12)
      (by simp [hys]) (by rw [nv_map h12]; exact hY) (by simp [hPL])
      (by rw [nv_map h12, hPLv])
      (by rw [show lk (r₂ (r₁ ni)) W₂ = lk ni W₀ from h12 ni, hni])
      (by rw [show lk (r₂ (r₁ z)) W₂ = lk z W₀ from h12 z, hz]) hAl hA'
      fun r₃ out W₃ h₃ hout hlt ⟨M, hM, e₂⟩ => ?_
    refine hk _ out W₃ (Pres.comp h12 h₃) hout hlt ⟨m + 2 ^ 64 * M, ?_, ?_⟩
    · simp only [List.length_cons]
      rw [two_pow_succ]
      omega
    · rw [nv_map h12] at e₂
      simp only [List.length_cons]
      rw [two_pow_succ, nv_cons]
      linear_combination 2 ^ 64 * e₂ + e₁

/-! ## 4. The Montgomery product -/

/-- The interleaved Montgomery product on `n` limbs: the limbs of `p`, the word `nInv`
    and a zero word; the first row `x_0 · ys` and its reduction word; the remaining rows
    (`ciosRowsK`); one conditional subtraction on the `n + 1` accumulator limbs. -/
def ciosMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  match xs with
  | [] => k (fun v => v) []
  | x :: xs' =>
    constsK (digits n P.p) fun r₁ PL =>
    bindK (eConst P.nInv) fun r₂ ni =>
    bindK (eConst 0) fun r₃ z =>
    mulRowK (ys.map fun v => r₃ (r₂ (r₁ v))) (r₃ (r₂ (r₁ x))) fun r₄ row =>
    ciosRedK (row ++ [r₄ z]) (PL.map fun v => r₄ (r₃ (r₂ v))) (r₄ (r₃ ni)) (r₄ z)
      fun r₅ A =>
    ciosRowsK (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) (ys.map fun v => r₅ (r₄ (r₃ (r₂ (r₁ v)))))
      (PL.map fun v => r₅ (r₄ (r₃ (r₂ v)))) (r₅ (r₄ (r₃ ni))) (r₅ (r₄ z)) xs' A
      fun r₆ B =>
    csubPCK P B fun r₇ out =>
    k (fun v => r₇ (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v))))))) out

theorem ciosMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hys : ys.length = n)
    (hx : nv W xs < P.p) (hy : nv W ys < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out < P.p →
      nv W' out * 2 ^ (64 * n) ≡ nv W xs * nv W ys [MOD P.p] →
      (k r out).denote W' = G) :
    (ciosMK P xs ys k).denote W = G := by
  have hp := P.p_lt
  have hn := n_pos P
  obtain ⟨x, xs', rfl⟩ := List.exists_cons_of_length_pos (show 0 < xs.length by omega)
  rw [ciosMK]
  refine constsK_denote _ _ W G (digits_lt _ _) fun r₁ PL W₁ h₁ hPL hPLv => ?_
  rw [limbsNat_digits _ _ hp] at hPLv
  rw [digits_length] at hPL
  refine bindK_denote _ _ _ _ fun r₂ ni W₂ h₂ hni => ?_
  refine bindK_denote _ _ _ _ fun r₃ z W₃ h₃ hz => ?_
  have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W W₃ := Pres.comp (Pres.comp h₁ h₂) h₃
  have h23 : Pres (fun v => r₃ (r₂ v)) W₁ W₃ := Pres.comp h₂ h₃
  have eni : (lk (r₃ ni) W₃).toNat = P.nInv := by
    rw [show lk (r₃ ni) W₃ = lk ni W₂ from h₃ ni, show lk ni W₂ = _ from hni, eConst_denote,
      BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt P.nInv_lt
  have ez : (lk z W₃).toNat = 0 := by rw [show lk z W₃ = _ from hz, eConst_denote]; rfl
  have hxl := (lk x W).isLt
  refine mulRowK_denote _ _ _ W₃ G fun r₄ row W₄ h₄ hrow hrowv => ?_
  rw [nv_map h123, show lk (r₃ (r₂ (r₁ x))) W₃ = lk x W from h123 x] at hrowv
  rw [List.length_map, hys] at hrow
  have ez4 : (lk (r₄ z) W₄).toNat = 0 := by rw [show lk (r₄ z) W₄ = lk z W₃ from h₄ z, ez]
  have hS : nv W₄ (row ++ [r₄ z]) = nv W ys * (lk x W).toNat := by
    rw [nv_append, nv_cons, nv_nil, ez4, hrowv]
    simp
  have hrow0 := cios_row_lt P.p 0 _ _ (by omega) hy hxl
  refine ciosRedK_denote P _ _ _ _ _ W₄ G (by simp [hrow]) (by simp [hPL])
    (by rw [nv_map (Pres.comp h23 h₄), hPLv])
    (by rw [show lk (r₄ (r₃ ni)) W₄ = lk (r₃ ni) W₃ from h₄ _, eni]) ez4
    (by rw [hS]; omega) fun r₅ A W₅ h₅ hAl ⟨m₀, hm₀, e₁⟩ => ?_
  rw [hS] at e₁
  have hA : nv W₅ A < 2 * P.p :=
    cios_bound P.p 0 _ _ _ _ (by omega) hy hxl hm₀ (by rw [e₁]; ring)
  have h45 : Pres (fun v => r₅ (r₄ v)) W₃ W₅ := Pres.comp h₄ h₅
  have hall : Pres (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) W W₅ := Pres.comp h123 h45
  refine ciosRowsK_denote P W xs' (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) _ _ _ _ A _ W₅ G hall
    (by simp [hys]) (by rw [nv_map hall]; exact hy) (by simp [hPL])
    (by rw [nv_map (Pres.comp h23 h45), hPLv])
    (by rw [show lk (r₅ (r₄ (r₃ ni))) W₅ = lk (r₃ ni) W₃ from h45 _, eni])
    (by rw [show lk (r₅ (r₄ z)) W₅ = lk z W₃ from h45 _, ez]) hAl hA
    fun r₆ B W₆ h₆ hBl hB ⟨M, hM, e₂⟩ => ?_
  rw [nv_map hall] at e₂
  have hxs' : xs'.length + 1 = n := by simpa using hxs
  have e : nv W₆ B * 2 ^ (64 * n) = nv W (x :: xs') * nv W ys + (m₀ + 2 ^ 64 * M) * P.p := by
    have h2n : 2 ^ (64 * n) = 2 ^ (64 * xs'.length) * 2 ^ 64 := by rw [← hxs', two_pow_succ]
    rw [h2n, nv_cons]
    linear_combination 2 ^ 64 * e₂ + e₁
  refine csubPCK_denote P B _ W₆ G hBl (by omega) fun r₇ out W₇ h₇ hout hv => ?_
  refine hk _ out W₇ (Pres.comp (Pres.comp hall h₆) h₇) hout ?_ ?_
  · rw [hv, csub_eq_mod P _ hB]
    exact Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one P.one_lt)
  · rw [hv, csub_eq_mod P _ hB]
    unfold Nat.ModEq
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, e, Nat.add_mul_mod_self_right]

/-- On the Montgomery forms of `x` and `y`, `ciosMK` gives the Montgomery form of
    `x * y`. -/
theorem ciosMK_denote_enc {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hys : ys.length = n)
    (x y : ZMod P.p) (hx : nv W xs = (x * R P).val) (hy : nv W ys = (y * R P).val)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out = (x * y * R P).val →
      (k r out).denote W' = G) :
    (ciosMK P xs ys k).denote W = G := by
  refine ciosMK_denote P xs ys k W G hxs hys (by rw [hx]; exact val_lt P _)
    (by rw [hy]; exact val_lt P _) fun r out W' hr hout hlt hmod => hk r out W' hr hout ?_
  rw [hx, hy] at hmod
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_val, ZMod.cast_id',
    id] at hc
  have hR : ((nv W' out : Nat) : ZMod P.p) = x * y * R P := by
    refine (isUnit_R P).mul_right_cancel ?_
    rw [show R P = 2 ^ (64 * n) from rfl] at hc ⊢
    rw [hc]
    ring
  rw [← hR, ZMod.val_natCast_of_lt hlt]

/-! ## 5. The block -/

section Blocks

variable {Γ : Ctxt jasminDialect}

/-- The interleaved Montgomery multiplication block. -/
def mulBlkI (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  ciosMK P xs ys fun _ out => retN n out

variable (W : Valuation Γ)

theorem mulBlkI_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n) (hys : ys.length = n)
    (x y : ZMod P.p) (hx : nv W xs = (x * R P).val) (hy : nv W ys = (y * R P).val) :
    (mulBlkI P xs ys).denote W = enc P (x * y) := by
  refine ciosMK_denote_enc P _ _ _ W _ hxs hys x y hx hy fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' hout, hv, enc]

end Blocks

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
