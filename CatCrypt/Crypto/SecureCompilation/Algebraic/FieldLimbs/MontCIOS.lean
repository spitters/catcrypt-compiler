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
conditional subtraction of `p` on `n + 1` limbs gives the result. The constant `nInv`
and a zero word are bound once and shared by all rows.

Both the operand row and the reduction row are fused multiply-add rows (`fmaR`): each
product `x · y_j` is formed as a low and a high word and added into the accumulator at
once, its low word by one carry chain and the previous high word by a second, so no
product row is materialised. The digits of `p` are bound inside each reduction row at
their use. During the rows the accumulator, the two words of the current product, the
previous high word, the reduction digit and the two shared constants are the live
words besides the operands: `n + 8` words.

The accumulator stays below `2p` after every row (`cios_bound`), and after the rows
over `x_0, …, x_{s-1}` it satisfies `acc · 2^(64s) = acc₀ + X Y + M p` with
`M < 2^(64s)` (`ciosRowsK_denote`).

## Main definitions

* `opK`: an operand word, a variable or a constant bound at its use.
* `fmaR`: the fused multiply-add row.
* `ciosAddK`: the row `x · ys` added into an `n + 1`-limb accumulator.
* `ciosRedK`: one word of Montgomery reduction on `n + 2` limbs.
* `ciosRowsK`: the rows and reduction words over a list of operand limbs.
* `ciosMK`, `mulBlkI`: the interleaved Montgomery product and its block.
* `mulBlkRoute`: the multiplication block of the field route, `mulBlkI` at six or more
  limbs and `Mont.mulBlk` below.

## Main results

* `fmaR_denote`: the fused row adds `Y · x` into the accumulator.
* `ciosRowsK_denote`: the loop invariant of the rows.
* `ciosMK_denote`, `ciosMK_denote_enc`: the Montgomery product.
* `mulBlkI_denote`, `mulBlkRoute_denote`: each block denotes `enc P (x * y)`, the
  statement of `Mont.mulBlk_denote`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk lk1 eBin eConst eBit eMulhi eAdc eCarry eConst_denote eBin_denote
    eBit_denote eMulhi_denote eAdc_denote eCarry_denote adc_toNat mulx_toNat Pres Pres.id
    Pres.comp bindK bindK_denote nv nv_nil nv_cons nv_map nv_append nv_lt limbsNat mulRowK
    mulRowK_denote)

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

/-- A sum `O + B e = V` with `V < B` has `O = V`. -/
theorem fma_low (O V B e : Nat) (h : O + B * e = V) (hV : V < B) : O = V := by
  rcases Nat.eq_zero_or_pos e with he | he
  · rw [he, Nat.mul_zero, Nat.add_zero] at h
    exact h
  · have : B ≤ B * e := Nat.le_mul_of_pos_right B he
    omega

/-! ## 2. The fused multiply-add row -/

/-- The value of an operand word of a fused row: a variable, or a constant reduced modulo
    `2^64`. -/
def sv {Γ : Ctxt jasminDialect} (W : Valuation Γ) : Var Γ w64 ⊕ Nat → Nat
  | .inl v => (lk v W).toNat
  | .inr d => d % 2 ^ 64

/-- The little-endian value of a list of operand words. -/
def svs {Γ : Ctxt jasminDialect} (W : Valuation Γ) : List (Var Γ w64 ⊕ Nat) → Nat
  | [] => 0
  | a :: as => sv W a + 2 ^ 64 * svs W as

theorem svs_inl {Γ : Ctxt jasminDialect} (W : Valuation Γ) :
    ∀ ys : List (Var Γ w64), svs W (ys.map Sum.inl) = nv W ys
  | [] => rfl
  | y :: ys => by simp only [List.map_cons, svs, sv, nv_cons, svs_inl W ys]

theorem svs_inr_digits {Γ : Ctxt jasminDialect} (W : Valuation Γ) :
    ∀ k v, svs W ((digits k v).map Sum.inr) = limbsNat (digits k v)
  | 0, _ => rfl
  | k + 1, v => by
      simp only [digits, List.map_cons, svs, sv, limbsNat, Nat.mod_mod, svs_inr_digits W k]

/-- The operand word `y` in the context of the renaming `ren`: a variable is renamed, a
    constant is bound by `regConst`. -/
def opK {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ) :
    Var Γ w64 ⊕ Nat →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Var Δ' w64 → MC Δ' ts) → MC Δ ts
  | .inl v, k => k (fun u => u) (ren v)
  | .inr d, k => bindK (eConst d) k

theorem opK_denote {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (y : Var Γ w64 ⊕ Nat)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Var Δ' w64 → MC Δ' ts)
    (W : Valuation Γ) (W₀ : Valuation Δ) (G : ListDenote ts) (hren : Pres ren W W₀)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (v : Var Δ' w64)
      (W' : Valuation Δ'), Pres r W₀ W' → (lk v W').toNat = sv W y → (k r v).denote W' = G) :
    (opK ren y k).denote W₀ = G := by
  cases y with
  | inl v =>
    exact hk _ (ren v) W₀ (Pres.id W₀) (by rw [show lk (ren v) W₀ = lk v W from hren v]; rfl)
  | inr d =>
    refine bindK_denote _ _ _ _ fun r v W' hr hv => hk r v W' hr ?_
    rw [show lk v W' = _ from hv, eConst_denote, BitVec.toNat_ofNat]
    rfl

/-- The fused multiply-add row: the operand words `ys` times the word `x` added into the
    limbs `acc`, with the word `h` and the carries `cA`, `cB` added at the lowest position.
    For each `y_j` the product `x · y_j` is formed as `(lo, hi)`; `lo` enters the carry
    chain `cA` at position `j` and the previous `hi` the carry chain `cB`, so each
    position is written once and no product row is materialised. The limbs of `acc` past
    `ys` take the carries; `k` receives the limbs, both carries and the last `hi`. `z` is
    a zero word. -/
def fmaR : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ →
    List (Var Γ w64 ⊕ Nat) → List (Var Γ w64) → Var Δ w64 → Var Δ w64 → Var Δ w64 →
    Var Δ w1 → Var Δ w1 →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 →
      Var Δ' w1 → Var Δ' w64 → MC Δ' ts) → MC Δ ts
  | _, _, _, ren, y :: ys, a :: acc, x, z, h, cA, cB, k =>
      opK ren y fun r₀ q =>
      bindK (eBin .mul q (r₀ x)) fun r₁ lo =>
      bindK (eMulhi (r₁ q) (r₁ (r₀ x))) fun r₂ hi =>
      bindK (eAdc (r₂ (r₁ (r₀ (ren a)))) (r₂ lo) (r₂ (r₁ (r₀ cA)))) fun r₃ s =>
      bindK (eCarry (r₃ (r₂ (r₁ (r₀ (ren a))))) (r₃ (r₂ lo)) (r₃ (r₂ (r₁ (r₀ cA)))))
        fun r₄ cA' =>
      bindK (eAdc (r₄ s) (r₄ (r₃ (r₂ (r₁ (r₀ h))))) (r₄ (r₃ (r₂ (r₁ (r₀ cB)))))) fun r₅ o =>
      bindK (eCarry (r₅ (r₄ s)) (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ h))))))
        (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ cB))))))) fun r₆ cB' =>
      fmaR (fun v => r₆ (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ (ren v)))))))) ys acc
        (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ x))))))) (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ z)))))))
        (r₆ (r₅ (r₄ (r₃ hi)))) (r₆ (r₅ cA')) cB' fun r₇ out cA'' cB'' h' =>
        k (fun v => r₇ (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ v)))))))) (r₇ (r₆ o) :: out) cA'' cB'' h'
  | _, _, _, ren, [], a :: acc, _, z, h, cA, cB, k =>
      bindK (eAdc (ren a) z cA) fun r₁ s =>
      bindK (eCarry (r₁ (ren a)) (r₁ z) (r₁ cA)) fun r₂ cA' =>
      bindK (eAdc (r₂ s) (r₂ (r₁ h)) (r₂ (r₁ cB))) fun r₃ o =>
      bindK (eCarry (r₃ (r₂ s)) (r₃ (r₂ (r₁ h))) (r₃ (r₂ (r₁ cB)))) fun r₄ cB' =>
      fmaR (fun v => r₄ (r₃ (r₂ (r₁ (ren v))))) [] acc (r₄ (r₃ (r₂ (r₁ z))))
        (r₄ (r₃ (r₂ (r₁ z)))) (r₄ (r₃ (r₂ (r₁ z)))) (r₄ (r₃ cA')) cB' fun r₅ out cA'' cB'' h' =>
        k (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) (r₅ (r₄ o) :: out) cA'' cB'' h'
  | _, _, _, _, _, [], _, _, h, cA, cB, k => k (fun v => v) [] cA cB h

/-- The fused row adds `Y · x + h + cA + cB` into `acc`: the limbs, the two carries and
    the last high word recombine to that sum. -/
theorem fmaR_denote : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (ys : List (Var Γ w64 ⊕ Nat)) (acc : List (Var Γ w64)) (x z h : Var Δ w64)
    (cA cB : Var Δ w1)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 →
      Var Δ' w1 → Var Δ' w64 → MC Δ' ts)
    (W : Valuation Γ) (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ → (lk z W₀).toNat = 0 → ys.length ≤ acc.length →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
        (cA' cB' : Var Δ' w1) (h' : Var Δ' w64) (W' : Valuation Δ'), Pres r W₀ W' →
        out.length = acc.length →
        nv W' out + 2 ^ (64 * acc.length) *
            ((lk1 cA' W').toNat + (lk1 cB' W').toNat + (lk h' W').toNat)
          = nv W acc + svs W ys * (lk x W₀).toNat + (lk h W₀).toNat + (lk1 cA W₀).toNat
            + (lk1 cB W₀).toNat →
        (k r out cA' cB' h').denote W' = G) →
    (fmaR ren ys acc x z h cA cB k).denote W₀ = G
  | _, _, _, ren, y :: ys, a :: acc, x, z, h, cA, cB, k, W, W₀, G, hren, hz, hlen, hk => by
      rw [fmaR]
      refine opK_denote ren y _ W W₀ G hren fun r₀ q W₀' h₀ hq => ?_
      refine bindK_denote _ _ _ _ fun r₁ lo W₁ h₁ hlo => ?_
      refine bindK_denote _ _ _ _ fun r₂ hi W₂ h₂ hhi => ?_
      refine bindK_denote _ _ _ _ fun r₃ s W₃ h₃ hs => ?_
      refine bindK_denote _ _ _ _ fun r₄ cA' W₄ h₄ hcA => ?_
      refine bindK_denote _ _ _ _ fun r₅ o W₅ h₅ ho => ?_
      refine bindK_denote _ _ _ _ fun r₆ cB' W₆ h₆ hcB => ?_
      have hx : lk (r₀ x) W₀' = lk x W₀ := h₀ x
      have elo : lk lo W₁ = lk q W₀' * lk x W₀ := by
        rw [show lk lo W₁ = _ from hlo, eBin_denote, hx]; rfl
      have ehi : lk hi W₂ = mulHiW (lk q W₀') (lk x W₀) := by
        rw [show lk hi W₂ = _ from hhi, eMulhi_denote, show lk (r₁ q) W₁ = lk q W₀' from h₁ q,
          show lk (r₁ (r₀ x)) W₁ = lk x W₀ from (h₁ _).trans hx]
      have ea : lk (r₂ (r₁ (r₀ (ren a)))) W₂ = lk a W :=
        (h₂ _).trans ((h₁ _).trans ((h₀ _).trans (hren a)))
      have el2 : lk (r₂ lo) W₂ = lk lo W₁ := h₂ lo
      have ecA : lk1 (r₂ (r₁ (r₀ cA))) W₂ = lk1 cA W₀ := (h₂ _).trans ((h₁ _).trans (h₀ cA))
      have es : lk s W₃ = addCarryWord (lk a W) (lk lo W₁) (lk1 cA W₀) := by
        rw [show lk s W₃ = _ from hs, eAdc_denote, ea, el2, ecA]
      have ecA' : lk1 cA' W₄ = carryOutBit (lk a W) (lk lo W₁) (lk1 cA W₀) := by
        rw [show lk1 cA' W₄ = _ from hcA, eCarry_denote,
          show lk (r₃ (r₂ (r₁ (r₀ (ren a))))) W₃ = lk a W from (h₃ _).trans ea,
          show lk (r₃ (r₂ lo)) W₃ = lk lo W₁ from (h₃ _).trans el2,
          show lk1 (r₃ (r₂ (r₁ (r₀ cA)))) W₃ = lk1 cA W₀ from (h₃ _).trans ecA]
      have eh : lk (r₄ (r₃ (r₂ (r₁ (r₀ h))))) W₄ = lk h W₀ :=
        (h₄ _).trans ((h₃ _).trans ((h₂ _).trans ((h₁ _).trans (h₀ h))))
      have ecB : lk1 (r₄ (r₃ (r₂ (r₁ (r₀ cB))))) W₄ = lk1 cB W₀ :=
        (h₄ _).trans ((h₃ _).trans ((h₂ _).trans ((h₁ _).trans (h₀ cB))))
      have es4 : lk (r₄ s) W₄ = lk s W₃ := h₄ s
      have eo : lk o W₅ = addCarryWord (lk s W₃) (lk h W₀) (lk1 cB W₀) := by
        rw [show lk o W₅ = _ from ho, eAdc_denote, es4, eh, ecB]
      have ecB' : lk1 cB' W₆ = carryOutBit (lk s W₃) (lk h W₀) (lk1 cB W₀) := by
        rw [show lk1 cB' W₆ = _ from hcB, eCarry_denote,
          show lk (r₅ (r₄ s)) W₅ = lk s W₃ from (h₅ _).trans es4,
          show lk (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ h)))))) W₅ = lk h W₀ from (h₅ _).trans eh,
          show lk1 (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ cB)))))) W₅ = lk1 cB W₀ from (h₅ _).trans ecB]
      have hmx := mulx_toNat (lk q W₀') (lk x W₀)
      rw [← elo, ← ehi, hq] at hmx
      have hA := adc_toNat (lk a W) (lk lo W₁) (lk1 cA W₀)
      rw [← es, ← ecA'] at hA
      have hB := adc_toNat (lk s W₃) (lk h W₀) (lk1 cB W₀)
      rw [← eo, ← ecB'] at hB
      have h06 : Pres (fun v => r₆ (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ v))))))) W₀ W₆ :=
        Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp h₀ h₁) h₂) h₃) h₄)
          h₅) h₆
      refine fmaR_denote _ ys acc _ _ _ _ cB' _ W W₆ G (Pres.comp hren h06)
        (by rw [show lk (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ z))))))) W₆ = lk z W₀ from h06 z, hz])
        (by simpa using hlen) fun r₇ out cA'' cB'' h' W₇ h₇ hout hv => ?_
      refine hk _ _ _ _ _ W₇ (Pres.comp h06 h₇) (by simp [hout]) ?_
      rw [show lk (r₆ (r₅ (r₄ (r₃ hi)))) W₆ = lk hi W₂ from
          (h₆ _).trans ((h₅ _).trans ((h₄ _).trans (h₃ hi))),
        show lk1 (r₆ (r₅ cA')) W₆ = lk1 cA' W₄ from (h₆ _).trans (h₅ cA'),
        show lk (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ x))))))) W₆ = lk x W₀ from h06 x] at hv
      have eo7 : lk (r₇ (r₆ o)) W₇ = lk o W₅ := (h₇ _).trans (h₆ o)
      simp only [nv_cons, svs, eo7, List.length_cons]
      rw [two_pow_succ]
      linear_combination hB + hA + hmx + 2 ^ 64 * hv
  | _, _, _, ren, [], a :: acc, x, z, h, cA, cB, k, W, W₀, G, hren, hz, _, hk => by
      rw [fmaR]
      refine bindK_denote _ _ _ _ fun r₁ s W₁ h₁ hs => ?_
      refine bindK_denote _ _ _ _ fun r₂ cA' W₂ h₂ hcA => ?_
      refine bindK_denote _ _ _ _ fun r₃ o W₃ h₃ ho => ?_
      refine bindK_denote _ _ _ _ fun r₄ cB' W₄ h₄ hcB => ?_
      have ea : lk (ren a) W₀ = lk a W := hren a
      have es : lk s W₁ = addCarryWord (lk a W) (lk z W₀) (lk1 cA W₀) := by
        rw [show lk s W₁ = _ from hs, eAdc_denote, ea]
      have ecA' : lk1 cA' W₂ = carryOutBit (lk a W) (lk z W₀) (lk1 cA W₀) := by
        rw [show lk1 cA' W₂ = _ from hcA, eCarry_denote,
          show lk (r₁ (ren a)) W₁ = lk a W from (h₁ _).trans ea,
          show lk (r₁ z) W₁ = lk z W₀ from h₁ z, show lk1 (r₁ cA) W₁ = lk1 cA W₀ from h₁ cA]
      have es2 : lk (r₂ s) W₂ = lk s W₁ := h₂ s
      have eh : lk (r₂ (r₁ h)) W₂ = lk h W₀ := (h₂ _).trans (h₁ h)
      have ecB : lk1 (r₂ (r₁ cB)) W₂ = lk1 cB W₀ := (h₂ _).trans (h₁ cB)
      have eo : lk o W₃ = addCarryWord (lk s W₁) (lk h W₀) (lk1 cB W₀) := by
        rw [show lk o W₃ = _ from ho, eAdc_denote, es2, eh, ecB]
      have ecB' : lk1 cB' W₄ = carryOutBit (lk s W₁) (lk h W₀) (lk1 cB W₀) := by
        rw [show lk1 cB' W₄ = _ from hcB, eCarry_denote,
          show lk (r₃ (r₂ s)) W₃ = lk s W₁ from (h₃ _).trans es2,
          show lk (r₃ (r₂ (r₁ h))) W₃ = lk h W₀ from (h₃ _).trans eh,
          show lk1 (r₃ (r₂ (r₁ cB))) W₃ = lk1 cB W₀ from (h₃ _).trans ecB]
      have hA := adc_toNat (lk a W) (lk z W₀) (lk1 cA W₀)
      rw [← es, ← ecA', hz] at hA
      have hB := adc_toNat (lk s W₁) (lk h W₀) (lk1 cB W₀)
      rw [← eo, ← ecB'] at hB
      have h04 : Pres (fun v => r₄ (r₃ (r₂ (r₁ v)))) W₀ W₄ :=
        Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄
      have ez4 : (lk (r₄ (r₃ (r₂ (r₁ z)))) W₄).toNat = 0 := by
        rw [show lk (r₄ (r₃ (r₂ (r₁ z)))) W₄ = lk z W₀ from h04 z, hz]
      refine fmaR_denote _ [] acc _ _ _ _ cB' _ W W₄ G (Pres.comp hren h04) ez4 (by simp)
        fun r₅ out cA'' cB'' h' W₅ h₅ hout hv => ?_
      refine hk _ _ _ _ _ W₅ (Pres.comp h04 h₅) (by simp [hout]) ?_
      rw [ez4, show lk1 (r₄ (r₃ cA')) W₄ = lk1 cA' W₂ from (h₄ _).trans (h₃ cA')] at hv
      have eo5 : lk (r₅ (r₄ o)) W₅ = lk o W₃ := (h₅ _).trans (h₄ o)
      simp only [nv_cons, svs, eo5, List.length_cons] at hv ⊢
      rw [two_pow_succ]
      linear_combination hB + hA + 2 ^ 64 * hv
  | _, _, _, _, [], [], x, z, h, cA, cB, k, W, W₀, G, _, _, _, hk => by
      rw [fmaR]
      exact hk _ [] cA cB h W₀ (Pres.id W₀) rfl (by simp [nv_nil, svs]; omega)
  | _, _, _, _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, hlen, _ => by simp at hlen

/-! ## 3. The row and the reduction word -/

/-- The row `x · ys` added into the `n + 1` limbs `acc`, as `n + 2` limbs, by the fused
    row; `z` is a zero word. -/
def ciosAddK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ys : List (Var Γ w64))
    (x z : Var Γ w64) (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eBit 0) fun r₁ c =>
  fmaR r₁ (ys.map Sum.inl) (acc ++ [z]) (r₁ x) (r₁ z) (r₁ z) c c fun r₂ S _ _ _ =>
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
  refine bindK_denote _ _ _ _ fun r₁ c W₁ h₁ hc => ?_
  have ec : (lk1 c W₁).toNat = 0 := by rw [show lk1 c W₁ = _ from hc, eBit_denote]; rfl
  have ez : (lk (r₁ z) W₁).toNat = 0 := by rw [show lk (r₁ z) W₁ = lk z W from h₁ z, hz]
  refine fmaR_denote r₁ _ _ _ _ _ c c _ W W₁ G h₁ ez
    (by simp only [List.length_map, List.length_append, List.length_singleton, hys, hacc]; omega)
    fun r₂ S cA cB h' W₂ h₂ hS hSv => ?_
  rw [nv_append, nv_cons, nv_nil, hz, svs_inl, ez, ec,
    show lk (r₁ x) W₁ = lk x W from h₁ x] at hSv
  simp only [List.length_append, List.length_singleton, hacc, Nat.mul_zero,
    Nat.add_zero] at hSv hS
  exact hk _ S W₂ (Pres.comp h₁ h₂) hS (fma_low _ _ _ _ hSv hb)

/-- One word of Montgomery reduction on the `n + 2` limbs `S` of value `V`: the digit
    `m = (V mod 2^64) · nInv mod 2^64` from the word `ni = nInv`, the sum `V + m p` by
    the fused row over the digits of `p`, each bound at its use (its low limb is zero),
    and its upper `n + 1` limbs. -/
def ciosRedK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (S : List (Var Γ w64))
    (ni z : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eBin .mul (S.headD z) ni) fun r₁ m =>
  bindK (eBit 0) fun r₂ c =>
  fmaR (fun v => r₂ (r₁ v)) ((digits n P.p).map Sum.inr) S (r₂ m) (r₂ (r₁ z)) (r₂ (r₁ z)) c c
    fun r₃ T _ _ _ =>
  k (fun v => r₃ (r₂ (r₁ v))) T.tail

theorem ciosRedK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (S : List (Var Γ w64)) (ni z : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : S.length = n + 2)
    (hni : (lk ni W).toNat = P.nInv) (hz : (lk z W).toNat = 0)
    (hV : nv W S < 2 ^ 64 * (2 * P.p))
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n + 1 →
      (∃ m, m < 2 ^ 64 ∧ nv W' out * 2 ^ 64 = nv W S + m * P.p) →
      (k r out).denote W' = G) :
    (ciosRedK P S ni z k).denote W = G := by
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
  refine bindK_denote _ _ _ _ fun r₂ c W₂ h₂ hc => ?_
  have ec : (lk1 c W₂).toNat = 0 := by rw [show lk1 c W₂ = _ from hc, eBit_denote]; rfl
  have h12 : Pres (fun v => r₂ (r₁ v)) W W₂ := Pres.comp h₁ h₂
  have ez : (lk (r₂ (r₁ z)) W₂).toNat = 0 := by
    rw [show lk (r₂ (r₁ z)) W₂ = lk z W from h12 z, hz]
  refine fmaR_denote _ _ _ _ _ _ c c _ W W₂ G h12 ez
    (by simp only [List.length_map, digits_length, hlen]; omega)
    fun r₃ T cA cB h' W₃ h₃ hT hTv => ?_
  rw [svs_inr_digits, limbsNat_digits _ _ hp, show lk (r₂ m) W₂ = lk m W₁ from h₂ m, em, ez,
    ec, hlen] at hTv
  rw [hlen] at hT
  simp only [Nat.add_zero] at hTv
  have hMlt : M < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hMp : P.p * M ≤ P.p * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
  have hT0 : nv W₃ T = nv W (x :: rest) + P.p * M :=
    fma_low _ _ _ _ hTv (by omega)
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

/-! ## 4. The rows -/

/-- The rows and reduction words over the operand limbs `xs`, which live in the source
    context of the renaming `ren`, into the accumulator `acc`; `ys` are the limbs of
    the second operand, `ni` the word `nInv` and `z` a zero word. -/
def ciosRowsK : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ →
    List (Var Δ w64) → Var Δ w64 → Var Δ w64 → List (Var Γ w64) →
    List (Var Δ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, _, _, _, _, [], acc, k => k (fun v => v) acc
  | _, _, _, ren, ys, ni, z, x :: xs, acc, k =>
      ciosAddK ys (ren x) z acc fun r₁ S =>
      ciosRedK P S (r₁ ni) (r₁ z) fun r₂ A =>
      ciosRowsK (fun v => r₂ (r₁ (ren v))) (ys.map fun v => r₂ (r₁ v))
        (r₂ (r₁ ni)) (r₂ (r₁ z)) xs A fun r₃ out =>
        k (fun v => r₃ (r₂ (r₁ v))) out

/-- The loop invariant of the rows: from an accumulator `A₀ < 2p`, the rows over `xs`
    give an accumulator below `2p` with `acc · 2^(64s) = A₀ + X Y + M p`, `M < 2^(64s)`,
    for `s` the number of rows. -/
theorem ciosRowsK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (W : Valuation Γ)
    (xs : List (Var Γ w64)) : ∀ {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom Γ Δ) (ys : List (Var Δ w64)) (ni z : Var Δ w64)
    (acc : List (Var Δ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ → ys.length = n → nv W₀ ys < P.p →
    (lk ni W₀).toNat = P.nInv → (lk z W₀).toNat = 0 → acc.length = n + 1 →
    nv W₀ acc < 2 * P.p →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
      (W' : Valuation Δ'), Pres r W₀ W' → out.length = n + 1 → nv W' out < 2 * P.p →
      (∃ M, M < 2 ^ (64 * xs.length) ∧
        nv W' out * 2 ^ (64 * xs.length) = nv W₀ acc + nv W xs * nv W₀ ys + M * P.p) →
      (k r out).denote W' = G) →
    (ciosRowsK P ren ys ni z xs acc k).denote W₀ = G := by
  induction xs with
  | nil =>
    intro Δ ren ys ni z acc k W₀ G _ _ _ _ _ hacc hA hk
    rw [ciosRowsK]
    exact hk _ acc W₀ (Pres.id W₀) hacc hA ⟨0, by simp, by simp [nv_nil]⟩
  | cons x xs ih =>
    intro Δ ren ys ni z acc k W₀ G hren hys hY hni hz hacc hA hk
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
    refine ciosRedK_denote P S _ _ _ W₁ G hS
      (by rw [show lk (r₁ ni) W₁ = lk ni W₀ from h₁ ni, hni])
      (by rw [show lk (r₁ z) W₁ = lk z W₀ from h₁ z, hz]) (by rw [hSv]; exact hrow)
      fun r₂ A W₂ h₂ hAl ⟨m, hm, e₁⟩ => ?_
    rw [hSv] at e₁
    have hA' := cios_bound P.p _ _ _ _ _ hA hY hx hm e₁
    have h12 : Pres (fun v => r₂ (r₁ v)) W₀ W₂ := Pres.comp h₁ h₂
    refine ih (fun v => r₂ (r₁ (ren v))) _ _ _ A _ W₂ G (Pres.comp hren h12)
      (by simp [hys]) (by rw [nv_map h12]; exact hY)
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

/-! ## 5. The Montgomery product -/

/-- The interleaved Montgomery product on `n` limbs: the word `nInv` and a zero word; the
    first row `x_0 · ys` and its reduction word; the remaining rows (`ciosRowsK`); one
    conditional subtraction on the `n + 1` accumulator limbs. -/
def ciosMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  match xs with
  | [] => k (fun v => v) []
  | x :: xs' =>
    bindK (eConst P.nInv) fun r₂ ni =>
    bindK (eConst 0) fun r₃ z =>
    mulRowK (ys.map fun v => r₃ (r₂ v)) (r₃ (r₂ x)) fun r₄ row =>
    ciosRedK P (row ++ [r₄ z]) (r₄ (r₃ ni)) (r₄ z) fun r₅ A =>
    ciosRowsK P (fun v => r₅ (r₄ (r₃ (r₂ v)))) (ys.map fun v => r₅ (r₄ (r₃ (r₂ v))))
      (r₅ (r₄ (r₃ ni))) (r₅ (r₄ z)) xs' A fun r₆ B =>
    csubPCK P B fun r₇ out =>
    k (fun v => r₇ (r₆ (r₅ (r₄ (r₃ (r₂ v)))))) out

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
  refine bindK_denote _ _ _ _ fun r₂ ni W₂ h₂ hni => ?_
  refine bindK_denote _ _ _ _ fun r₃ z W₃ h₃ hz => ?_
  have h123 : Pres (fun v => r₃ (r₂ v)) W W₃ := Pres.comp h₂ h₃
  have eni : (lk (r₃ ni) W₃).toNat = P.nInv := by
    rw [show lk (r₃ ni) W₃ = lk ni W₂ from h₃ ni, show lk ni W₂ = _ from hni, eConst_denote,
      BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt P.nInv_lt
  have ez : (lk z W₃).toNat = 0 := by rw [show lk z W₃ = _ from hz, eConst_denote]; rfl
  have hxl := (lk x W).isLt
  refine mulRowK_denote _ _ _ W₃ G fun r₄ row W₄ h₄ hrow hrowv => ?_
  rw [nv_map h123, show lk (r₃ (r₂ x)) W₃ = lk x W from h123 x] at hrowv
  rw [List.length_map, hys] at hrow
  have ez4 : (lk (r₄ z) W₄).toNat = 0 := by rw [show lk (r₄ z) W₄ = lk z W₃ from h₄ z, ez]
  have hS : nv W₄ (row ++ [r₄ z]) = nv W ys * (lk x W).toNat := by
    rw [nv_append, nv_cons, nv_nil, ez4, hrowv]
    simp
  have hrow0 := cios_row_lt P.p 0 _ _ (by omega) hy hxl
  refine ciosRedK_denote P _ _ _ _ W₄ G (by simp [hrow])
    (by rw [show lk (r₄ (r₃ ni)) W₄ = lk (r₃ ni) W₃ from h₄ _, eni]) ez4
    (by rw [hS]; omega) fun r₅ A W₅ h₅ hAl ⟨m₀, hm₀, e₁⟩ => ?_
  rw [hS] at e₁
  have hA : nv W₅ A < 2 * P.p :=
    cios_bound P.p 0 _ _ _ _ (by omega) hy hxl hm₀ (by rw [e₁]; ring)
  have h45 : Pres (fun v => r₅ (r₄ v)) W₃ W₅ := Pres.comp h₄ h₅
  have hall : Pres (fun v => r₅ (r₄ (r₃ (r₂ v)))) W W₅ := Pres.comp h123 h45
  refine ciosRowsK_denote P W xs' (fun v => r₅ (r₄ (r₃ (r₂ v)))) _ _ _ A _ W₅ G hall
    (by simp [hys]) (by rw [nv_map hall]; exact hy)
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

/-! ## 6. The block -/

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

/-- The multiplication block of the field route, selected by the limb count: the
    interleaved block `mulBlkI` at six or more limbs, the block `mulBlk` (the product, then
    the reduction) below six. -/
def mulBlkRoute (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  if 6 ≤ n then mulBlkI P xs ys else mulBlk P xs ys

/-- The route's multiplication block denotes the Montgomery form of `x * y` at every limb
    count, the statement of `mulBlk_denote`. -/
theorem mulBlkRoute_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n)
    (hys : ys.length = n) (x y : ZMod P.p) (hx : nv W xs = (x * R P).val)
    (hy : nv W ys = (y * R P).val) :
    (mulBlkRoute P xs ys).denote W = enc P (x * y) := by
  unfold mulBlkRoute
  split
  · exact mulBlkI_denote P W xs ys hxs hys x y hx hy
  · exact mulBlk_denote P W xs ys hxs hys x y hx hy

end Blocks

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
