/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
public import CatCrypt.Crypto.Optimizer.SolinasArith

/-!
# Solinas field blocks over `n` 64-bit limbs for `p = 2^k - c`

For a record `SolinasParams n` of a modulus `p = 2^k - c` with `64 ≤ k ≤ 64n`, odd
`c < 2^64` and `c · (c + 3) < 2^k`, an element `x` of `ZMod p` is represented by the
`n` little-endian 64-bit limbs of its canonical representative `x.val` (`enc`). The
module gives multi-result `jasminDialect` blocks for multiplication, squaring,
addition, subtraction, negation and constants, generic in `n`, `k` and `c`, and one
value theorem for each, proved once for every record.

Multiplication is the schoolbook product on `2n` limbs (`Mont.prodNK`), two Solinas
folds `v ↦ (v / 2^k) · c + v % 2^k` (`foldK`) and one carry-aware conditional
subtraction on `n + 1` limbs (`Mont.csubPCK`); its value is the residue by
`ModReduceSelect.solinasFold_mod` and the bounds of `ModReduceSelect.solinasFold_lt`.
A fold splits its operand at bit `k = 64q + s` (`splitK`): the low part is the first
`q` limbs and, when `s > 0`, the low `s` bits of limb `q`; the high part is the limbs
from `q` on shifted right by `s` (`shrR`, each output limb `(a >>> s) + (b <<< (64 - s))`).
Addition, subtraction and negation are the blocks of `FieldLimbs.Mont` at the record
`lp`, whose Montgomery constant those blocks do not read. None of the blocks branches
or indexes on data.

## Main definitions

* `SolinasParams n`, `p`, `lp`: the record, the modulus and its `Mont.LimbParams`.
* `shrR`, `splitK`, `foldK`, `mulSK`: the list-level operations.
* `enc`: the encoding.
* `mulBlk`, `sqrBlk`, `addBlk`, `subBlk`, `negBlk`, `constBlk`: the blocks.

## Main results

* `shrR_denote`: the limb list shifted right by `s` bits.
* `splitK_denote`: the split of a limb list at bit `k`.
* `foldK_denote`: one Solinas fold.
* `mulSK_denote`: the product modulo `p`.
* `mulBlk_denote`, `sqrBlk_denote`, `addBlk_denote`, `subBlk_denote`, `negBlk_denote`,
  `constBlk_denote`: the value theorems of the blocks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk lk1 eBin eConst eConst_denote eBin_denote Pres Pres.id Pres.comp bindK
    bindK_denote nv nv_nil nv_cons nv_map nv_append nv_lt addK addK_denote mulRowK
    mulRowK_denote)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
  (LimbParams Rn limbsN retN retN_denote nv_replicate nv_take csubPCK csubPCK_denote
    csub_eq_mod addMK addMK_denote)
open CatCrypt.Crypto.Optimizer.ModReduceSelect
  (SolinasPrime solinasFold solinasFold_mod solinasFold_lt)

/-! ## 1. Word and natural-number lemmas -/

/-- A funnel shift of two words by `s < 64` bits, as a sum of disjoint bit ranges. -/
theorem funnel_toNat (a b : BitVec 64) (s : Nat) (hs : s < 64) :
    ((a >>> s) + (b <<< (64 - s))).toNat
      = a.toNat / 2 ^ s + b.toNat % 2 ^ s * 2 ^ (64 - s) := by
  have hsplit : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h1 : (b <<< (64 - s)).toNat = b.toNat % 2 ^ s * 2 ^ (64 - s) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hsplit, Nat.mul_mod_mul_right]
  have h2 : (a >>> s).toNat = a.toNat / 2 ^ s := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  have hq : a.toNat / 2 ^ s < 2 ^ (64 - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)]
    rw [hsplit] at ha
    rwa [Nat.mul_comm] at ha
  have hr : b.toNat % 2 ^ s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
  have hlt : a.toNat / 2 ^ s + b.toNat % 2 ^ s * 2 ^ (64 - s) < 2 ^ 64 := by
    rw [hsplit]
    have : b.toNat % 2 ^ s * 2 ^ (64 - s) ≤ (2 ^ s - 1) * 2 ^ (64 - s) :=
      Nat.mul_le_mul_right _ (by omega)
    have e : (2 ^ s - 1) * 2 ^ (64 - s) + 2 ^ (64 - s) = 2 ^ s * 2 ^ (64 - s) := by
      have := Nat.two_pow_pos s
      rw [← Nat.succ_mul]; congr 1; omega
    omega
  rw [BitVec.toNat_add, h1, h2, Nat.mod_eq_of_lt hlt]

/-- The conjunction with `2^s - 1` keeps the low `s` bits. -/
theorem mask_toNat (a : BitVec 64) (s : Nat) (hs : s < 64) :
    (a &&& BitVec.ofNat 64 (2 ^ s - 1)).toNat = a.toNat % 2 ^ s := by
  have : (2 : Nat) ^ s - 1 < 2 ^ 64 := by
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) hs
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this,
    Nat.and_two_pow_sub_one_eq_mod]

/-- Shifting `x + 2^64 R` right by `s ≤ 64` bits. -/
theorem funnel_nat (x R s : Nat) (hs : s ≤ 64) :
    (x + 2 ^ 64 * R) / 2 ^ s
      = x / 2 ^ s + R % 2 ^ s * 2 ^ (64 - s) + 2 ^ 64 * (R / 2 ^ s) := by
  have hsplit : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s)]
  conv_lhs => rw [← Nat.mod_add_div R (2 ^ s)]
  ring

/-- The low `s ≤ 64` bits of `y + 2^64 R` are those of `y`. -/
theorem mod_two_pow_of_add (y R s : Nat) (hs : s ≤ 64) :
    (y + 2 ^ 64 * R) % 2 ^ s = y % 2 ^ s := by
  have hsplit : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- The remainder of `L + B D` modulo `B S` for `L < B`. -/
theorem add_mul_mod_mul (L B D S : Nat) (hL : L < B) :
    (L + B * D) % (B * S) = L + B * (D % S) := by
  have hB : 0 < B := by omega
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL,
    Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hL, Nat.zero_add]

/-- The quotient of `L + B D` by `B S` for `L < B`. -/
theorem add_mul_div_mul (L B D S : Nat) (hL : L < B) :
    (L + B * D) / (B * S) = D / S := by
  have hB : 0 < B := by omega
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hL,
    Nat.zero_add]

/-! ## 2. The right shift of a limb list -/

/-- The limbs `xs` shifted right by `s` bits, for registers `sa` holding `s` and `sb`
    holding `64 - s`: output limb `j` is `(xs[j] >>> s) + (xs[j+1] <<< (64 - s))`, the
    last one `xs[last] >>> s`. -/
def shrR : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ →
    Var Δ w64 → Var Δ w64 → List (Var Γ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, _, _, _, [], k => k (fun v => v) []
  | _, _, _, ren, sa, _, [x], k =>
      bindK (eBin .shr (ren x) sa) fun r₁ o => k r₁ [o]
  | _, _, _, ren, sa, sb, x :: y :: ys, k =>
      bindK (eBin .shr (ren x) sa) fun r₁ lo =>
      bindK (eBin .shl (r₁ (ren y)) (r₁ sb)) fun r₂ hi =>
      bindK (eBin .add (r₂ lo) hi) fun r₃ o =>
      shrR (fun v => r₃ (r₂ (r₁ (ren v)))) (r₃ (r₂ (r₁ sa))) (r₃ (r₂ (r₁ sb))) (y :: ys)
        fun r₄ out => k (fun v => r₄ (r₃ (r₂ (r₁ v)))) (r₄ o :: out)

/-- `shrR` at a shift `0 < s < 64` hands its continuation limbs denoting `xs / 2^s`. The
    bound `0 < s` keeps the left-shift count `64 - s` below the width, where the count
    mask `shiftMask 64` is the identity. -/
theorem shrR_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (W : Valuation Γ)
    (s : Nat) (hs0 : 0 < s) (hs : s < 64) : ∀ (xs : List (Var Γ w64)) {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom Γ Δ) (sa sb : Var Δ w64)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ → (lk sa W₀).toNat = s → (lk sb W₀).toNat = 64 - s →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
      (W' : Valuation Δ'), Pres r W₀ W' → out.length = xs.length →
      nv W' out = nv W xs / 2 ^ s → (k r out).denote W' = G) →
    (shrR ren sa sb xs k).denote W₀ = G := by
  intro xs
  induction xs with
  | nil =>
    intro Δ ren sa sb k W₀ G _ _ _ hk
    rw [shrR]
    exact hk _ [] W₀ (Pres.id W₀) rfl (by simp [nv_nil])
  | cons x rest ih =>
    intro Δ ren sa sb k W₀ G hren hsa hsb hk
    cases rest with
    | nil =>
      rw [shrR]
      refine bindK_denote _ _ _ _ fun r₁ o W₁ h₁ ho => hk r₁ [o] W₁ h₁ rfl ?_
      have eo : lk o W₁ = lk x W >>> s := by
        rw [show lk o W₁ = _ from ho, eBin_denote, show lk (ren x) W₀ = lk x W from hren x]
        show lk x W >>> shiftMask 64 (lk sa W₀).toNat = _
        rw [hsa, shiftMask_of_lt hs]
      simp only [nv_cons, nv_nil, Nat.mul_zero, Nat.add_zero, eo, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
    | cons y ys =>
      rw [shrR]
      refine bindK_denote _ _ _ _ fun r₁ lo W₁ h₁ hlo => ?_
      refine bindK_denote _ _ _ _ fun r₂ hi W₂ h₂ hhi => ?_
      refine bindK_denote _ _ _ _ fun r₃ o W₃ h₃ ho => ?_
      have eo : (lk o W₃).toNat = (lk x W).toNat / 2 ^ s
          + (lk y W).toNat % 2 ^ s * 2 ^ (64 - s) := by
        rw [show lk o W₃ = _ from ho, eBin_denote]
        show (lk (r₂ lo) W₂ + lk hi W₂).toNat = _
        rw [show lk (r₂ lo) W₂ = lk lo W₁ from h₂ lo, show lk lo W₁ = _ from hlo,
          show lk hi W₂ = _ from hhi, eBin_denote, eBin_denote]
        show (lk (ren x) W₀ >>> shiftMask 64 (lk sa W₀).toNat
          + lk (r₁ (ren y)) W₁ <<< shiftMask 64 (lk (r₁ sb) W₁).toNat).toNat = _
        rw [show lk (ren x) W₀ = lk x W from hren x,
          show lk (r₁ (ren y)) W₁ = lk y W from (h₁ _).trans (hren y),
          show lk (r₁ sb) W₁ = lk sb W₀ from h₁ sb, hsa, hsb, shiftMask_of_lt hs,
          shiftMask_of_lt (by omega : 64 - s < 64)]
        exact funnel_toNat _ _ s hs
      have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W₀ W₃ := Pres.comp (Pres.comp h₁ h₂) h₃
      refine ih _ _ _ _ W₃ G (Pres.comp hren h123)
        (by rw [show lk (r₃ (r₂ (r₁ sa))) W₃ = lk sa W₀ from h123 sa, hsa])
        (by rw [show lk (r₃ (r₂ (r₁ sb))) W₃ = lk sb W₀ from h123 sb, hsb])
        fun r₄ out W₄ h₄ hout hval => ?_
      refine hk _ _ W₄ (Pres.comp h123 h₄) (by simp [hout]) ?_
      rw [nv_cons, show lk (r₄ o) W₄ = lk o W₃ from h₄ o, eo, hval, nv_cons (W := W) x,
        funnel_nat _ _ s hs.le, nv_cons (W := W) y, mod_two_pow_of_add _ _ s hs.le]

/-! ## 3. The split at bit `k` -/

/-- The split of the limbs `xs` at bit `k = 64q + s`: the continuation receives the high
    part `xs / 2^k` (the limbs from `q` on, shifted right by `s`) and the low part
    `xs % 2^k` (the first `q` limbs and, when `s > 0`, the low `s` bits of limb `q`). -/
def splitK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (k : Nat) (xs : List (Var Γ w64))
    (K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → List (Var Δ w64) →
      MC Δ ts) : MC Γ ts :=
  if k % 64 = 0 then K (fun v => v) (xs.drop (k / 64)) (xs.take (k / 64)) else
  bindK (eConst (k % 64)) fun r₁ sa =>
  bindK (eConst (64 - k % 64)) fun r₂ sb =>
  bindK (eConst (2 ^ (k % 64) - 1)) fun r₃ mk =>
  bindK (eBin .and (((xs.drop (k / 64)).map (fun v => r₃ (r₂ (r₁ v)))).headD mk) mk)
    fun r₄ ml =>
  shrR (fun v => r₄ (r₃ (r₂ (r₁ v)))) (r₄ (r₃ (r₂ sa))) (r₄ (r₃ sb)) (xs.drop (k / 64))
    fun r₅ hi =>
  K (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) hi
    ((xs.take (k / 64)).map (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) ++ [r₅ ml])

theorem splitK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (k : Nat)
    (xs : List (Var Γ w64))
    (K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → List (Var Δ w64) →
      MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hq : k / 64 < xs.length)
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (hi lo : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → hi.length = xs.length - k / 64 →
      lo.length ≤ k / 64 + 1 → nv W' hi = nv W xs / 2 ^ k → nv W' lo = nv W xs % 2 ^ k →
      (K r hi lo).denote W' = G) :
    (splitK k xs K).denote W = G := by
  have hsplit := nv_append W (xs.take (k / 64)) (xs.drop (k / 64))
  have htl : (xs.take (k / 64)).length = k / 64 := by simp; omega
  rw [List.take_append_drop, htl] at hsplit
  have hL := nv_lt W (xs.take (k / 64))
  rw [htl] at hL
  have hk2 : (2 : Nat) ^ k = 2 ^ (64 * (k / 64)) * 2 ^ (k % 64) := by
    rw [← Nat.pow_add, Nat.div_add_mod]
  have hdiv : nv W xs / 2 ^ k = nv W (xs.drop (k / 64)) / 2 ^ (k % 64) := by
    rw [hsplit, hk2, add_mul_div_mul _ _ _ _ hL]
  have hmod : nv W xs % 2 ^ k = nv W (xs.take (k / 64))
      + 2 ^ (64 * (k / 64)) * (nv W (xs.drop (k / 64)) % 2 ^ (k % 64)) := by
    rw [hsplit, hk2, add_mul_mod_mul _ _ _ _ hL]
  unfold splitK
  by_cases hs : k % 64 = 0
  · rw [ite_eq_left hs]
    refine hK _ _ _ W (Pres.id W) (by simp) (by simp) ?_ ?_
    · rw [hdiv, hs, Nat.pow_zero, Nat.div_one]
    · rw [hmod, hs, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero]
  · rw [ite_eq_right hs]
    have hs64 : k % 64 < 64 := Nat.mod_lt _ (by norm_num)
    obtain ⟨d, rest, hd⟩ : ∃ d rest, xs.drop (k / 64) = d :: rest := by
      cases h : xs.drop (k / 64) with
      | nil => simp at h; omega
      | cons d rest => exact ⟨d, rest, rfl⟩
    refine bindK_denote _ _ _ _ fun r₁ sa W₁ h₁ hsa => ?_
    refine bindK_denote _ _ _ _ fun r₂ sb W₂ h₂ hsb => ?_
    refine bindK_denote _ _ _ _ fun r₃ mk W₃ h₃ hmk => ?_
    refine bindK_denote _ _ _ _ fun r₄ ml W₄ h₄ hml => ?_
    have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W W₃ := Pres.comp (Pres.comp h₁ h₂) h₃
    have h1234 : Pres (fun v => r₄ (r₃ (r₂ (r₁ v)))) W W₄ := Pres.comp h123 h₄
    have eml : (lk ml W₄).toNat = (lk d W).toNat % 2 ^ (k % 64) := by
      rw [show lk ml W₄ = _ from hml, eBin_denote, hd, List.map_cons, List.headD_cons]
      show (lk (r₃ (r₂ (r₁ d))) W₃ &&& lk mk W₃).toNat = _
      rw [show lk (r₃ (r₂ (r₁ d))) W₃ = lk d W from h123 d, show lk mk W₃ = _ from hmk,
        eConst_denote]
      exact mask_toNat _ _ hs64
    refine shrR_denote W (k % 64) (Nat.pos_of_ne_zero hs) hs64 _ _ _ _ _ W₄ G h1234 ?_ ?_
      fun r₅ hi W₅ h₅ hhi hhiv => ?_
    · rw [show lk (r₄ (r₃ (r₂ sa))) W₄ = lk sa W₁ from (h₄ _).trans ((h₃ _).trans (h₂ sa)),
        show lk sa W₁ = _ from hsa, eConst_denote, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [show lk (r₄ (r₃ sb)) W₄ = lk sb W₂ from (h₄ _).trans (h₃ sb),
        show lk sb W₂ = _ from hsb, eConst_denote, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    refine hK _ hi _ W₅ (Pres.comp h1234 h₅) (by rw [hhi]; simp) (by simp)
      (by rw [hhiv, hdiv]) ?_
    rw [hmod, nv_append, nv_map (Pres.comp h1234 h₅), List.length_map, htl, nv_cons, nv_nil,
      show lk (r₅ ml) W₅ = lk ml W₄ from h₅ ml, eml, hd, nv_cons,
      mod_two_pow_of_add _ _ _ (by omega)]
    simp

/-! ## 4. The Solinas fold -/

/-- The list `ys` padded with the register `z` to length `m`. -/
def padL {Δ : Ctxt jasminDialect} (z : Var Δ w64) (m : Nat) (ys : List (Var Δ w64)) :
    List (Var Δ w64) :=
  ys ++ List.replicate (m - ys.length) z

theorem padL_length {Δ : Ctxt jasminDialect} (z : Var Δ w64) (m : Nat)
    (ys : List (Var Δ w64)) (h : ys.length ≤ m) : (padL z m ys).length = m := by
  simp [padL]; omega

theorem nv_padL {Δ : Ctxt jasminDialect} (W : Valuation Δ) (z : Var Δ w64)
    (hz : (lk z W).toNat = 0) (m : Nat) (ys : List (Var Δ w64)) :
    nv W (padL z m ys) = nv W ys := by
  rw [padL, nv_append, nv_replicate W z hz, Nat.mul_zero, Nat.add_zero]

/-- One Solinas fold on `m` limbs: the split at bit `k`, the high part times the word
    `c`, and the sum with the low part, all padded to `m` limbs. -/
def foldK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (k c m : Nat)
    (xs : List (Var Γ w64))
    (K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  splitK k xs fun r₁ hi lo =>
  bindK (eConst c) fun r₂ cv =>
  mulRowK (hi.map (fun v => r₂ v)) cv fun r₃ H =>
  bindK (eConst 0) fun r₄ z =>
  addK (padL z m (H.map (fun v => r₄ v))) (padL z m (lo.map (fun v => r₄ (r₃ (r₂ v)))))
    fun r₅ S _ =>
  K (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) S

theorem foldK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (k c m : Nat)
    (xs : List (Var Γ w64))
    (K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = m) (hk : 64 ≤ k)
    (hq : k / 64 < m) (hc : c < 2 ^ 64)
    (hb : solinasFold ⟨k, c⟩ (nv W xs) < 2 ^ (64 * m))
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = m →
      nv W' out = solinasFold ⟨k, c⟩ (nv W xs) → (K r out).denote W' = G) :
    (foldK k c m xs K).denote W = G := by
  refine splitK_denote k xs _ W G (by omega) fun r₁ hi lo W₁ h₁ hhi hlo hhiv hlov => ?_
  refine bindK_denote _ _ _ _ fun r₂ cv W₂ h₂ hcv => ?_
  have ec : (lk cv W₂).toNat = c := by
    rw [show lk cv W₂ = _ from hcv, eConst_denote, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hc
  refine mulRowK_denote _ cv _ W₂ G fun r₃ H W₃ h₃ hH hHv => ?_
  rw [nv_map h₂, ec, hhiv] at hHv
  simp only [List.length_map, hhi] at hH
  refine bindK_denote _ _ _ _ fun r₄ z W₄ h₄ hz => ?_
  have ez : (lk z W₄).toNat = 0 := by rw [show lk z W₄ = _ from hz, eConst_denote]; rfl
  have hq1 : 1 ≤ k / 64 := by omega
  refine addK_denote _ _ _ W₄ G (by rw [padL_length _ _ _ (by simp; omega),
      padL_length _ _ _ (by simp; omega)]) fun r₅ S cy W₅ h₅ hS hSv => ?_
  rw [padL_length _ _ _ (by simp; omega)] at hS hSv
  rw [nv_padL W₄ z ez, nv_padL W₄ z ez, nv_map h₄, nv_map (Pres.comp (Pres.comp h₂ h₃) h₄),
    hHv, hlov] at hSv
  refine hK _ S W₅ (Pres.comp (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄) h₅) hS ?_
  have hcy := (lk1 cy W₅).isLt
  have hf : solinasFold ⟨k, c⟩ (nv W xs) = nv W xs / 2 ^ k * c + nv W xs % 2 ^ k := rfl
  rw [hf] at hb ⊢
  have h0 : (lk1 cy W₅).toNat = 0 := by
    by_contra hne
    have h1 : (lk1 cy W₅).toNat = 1 := by omega
    rw [h1] at hSv
    omega
  rw [h0] at hSv
  omega

/-! ## 5. The record and the product modulo `p` -/

/-- A Solinas modulus `p = 2^k - c` on `n` 64-bit limbs: `c` odd and below `2^64`,
    `64 ≤ k ≤ 64n`, and `c · (c + 3) < 2^k`. -/
structure SolinasParams (n : Nat) where
  /-- The bit position of the split. -/
  k : Nat
  /-- The subtrahend. -/
  c : Nat
  c_odd : c % 2 = 1
  c_lt : c < 2 ^ 64
  k_ge : 64 ≤ k
  k_le : k ≤ 64 * n
  cc_lt : c * (c + 3) < 2 ^ k

variable {n : Nat} (S : SolinasParams n)

/-- The modulus `2^k - c`. -/
abbrev p : Nat := 2 ^ S.k - S.c

theorem c_add_three_lt : S.c + 3 < 2 ^ S.k := by
  have h := S.cc_lt
  have h1 : 1 ≤ S.c := by have := S.c_odd; omega
  have : S.c + 3 ≤ S.c * (S.c + 3) := Nat.le_mul_of_pos_left _ h1
  omega

theorem two_pow_k_le : 2 ^ S.k ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by norm_num) S.k_le

theorem n_pos (S : SolinasParams n) : 1 ≤ n := by have := S.k_ge; have := S.k_le; omega

theorem p_lt : p S < 2 ^ (64 * n) := by
  have := two_pow_k_le S
  have := Nat.two_pow_pos (64 * n)
  have := S.c_odd
  simp only [p]
  omega

theorem p_odd : p S % 2 = 1 := by
  have h2 : (2 : Nat) ^ S.k = 2 * 2 ^ (S.k - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := S.k_ge; omega
  have := c_add_three_lt S
  have := S.c_odd
  simp only [p]
  omega

instance : NeZero (p S) := ⟨by have := c_add_three_lt S; simp only [p]; omega⟩

/-- The record of `FieldLimbs.Mont` at `p`, with `nInv = -p⁻¹ mod 2^64`. -/
def lp : LimbParams n where
  p := p S
  nInv := (-(((p S : Nat) : ZMod (2 ^ 64))⁻¹) : ZMod (2 ^ 64)).val
  one_lt := by have := c_add_three_lt S; simp only [p]; omega
  p_odd := p_odd S
  p_lt := p_lt S
  nInv_lt := ZMod.val_lt _
  nInv_spec := by
    have hcop : Nat.Coprime (p S) (2 ^ 64) :=
      (Nat.Coprime.pow_left 64 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (p_odd S)))).symm
    have hu := ZMod.coe_mul_inv_eq_one (p S) hcop
    refine Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp ?_)
    push_cast
    rw [ZMod.natCast_zmod_val, mul_neg, hu, neg_add_cancel]

/-- Multiplication modulo `p` on `n` limbs: the schoolbook product on `2n` limbs, two
    Solinas folds, and one conditional subtraction on the low `n + 1` limbs. -/
def mulSK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  Mont.prodNK xs ys fun r₁ T =>
  foldK S.k S.c (2 * n) T fun r₂ T₁ =>
  foldK S.k S.c (2 * n) T₁ fun r₃ T₂ =>
  csubPCK (lp S) (T₂.take (n + 1)) fun r₄ out =>
  K (fun v => r₄ (r₃ (r₂ (r₁ v)))) out

theorem mulSK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (xs ys : List (Var Γ w64))
    (K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hys : ys.length = n)
    (hx : nv W xs < p S) (hy : nv W ys < p S)
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n →
      nv W' out = nv W xs * nv W ys % p S → (K r out).denote W' = G) :
    (mulSK S xs ys K).denote W = G := by
  have hn := n_pos S
  have hkge := S.k_ge
  have hkle := S.k_le
  have hcl := S.c_lt
  have hc3 := c_add_three_lt S
  have hcc := S.cc_lt
  have hkB := two_pow_k_le S
  have hq : S.k / 64 < 2 * n := by omega
  have hB2 : 2 ^ (64 * n) * 2 ^ 64 ≤ 2 ^ (64 * (2 * n)) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc_le : S.c ≤ 2 ^ S.k := by omega
  have hpS : p S + S.c = 2 ^ S.k := by simp only [p]; omega
  have hpB := p_lt S
  refine Mont.prodNK_denote xs ys _ W G hxs (by omega) fun r₁ T W₁ h₁ hT hTv => ?_
  have hXY : nv W xs * nv W ys < 2 ^ S.k * 2 ^ S.k := Nat.mul_lt_mul'' (by omega) (by omega)
  -- the first fold
  have hf1 : solinasFold ⟨S.k, S.c⟩ (nv W₁ T) < 2 ^ S.k * (S.c + 1) := by
    have := solinasFold_lt ⟨S.k, S.c⟩ (v := nv W₁ T) (M := 2 ^ S.k) (by rw [hTv]; exact hXY)
    have e : 2 ^ S.k * S.c + 2 ^ S.k = 2 ^ S.k * (S.c + 1) := by ring
    rw [Nat.mul_comm (2 ^ S.k) S.c] at e
    omega
  have hf1' : solinasFold ⟨S.k, S.c⟩ (nv W₁ T) < 2 ^ (64 * (2 * n)) := by
    have : 2 ^ S.k * (S.c + 1) ≤ 2 ^ (64 * n) * 2 ^ 64 := Nat.mul_le_mul hkB (by omega)
    omega
  refine foldK_denote S.k S.c (2 * n) T _ W₁ G (by rw [hT, hys]; ring) hkge hq hcl hf1'
    fun r₂ T₁ W₂ h₂ hT₁ hT₁v => ?_
  -- the second fold
  have hf2 : solinasFold ⟨S.k, S.c⟩ (nv W₂ T₁) < (S.c + 1) * S.c + 2 ^ S.k :=
    solinasFold_lt ⟨S.k, S.c⟩ (by rw [hT₁v]; exact hf1)
  have h2p : solinasFold ⟨S.k, S.c⟩ (nv W₂ T₁) < 2 * p S := by
    have e : S.c * (S.c + 3) = (S.c + 1) * S.c + 2 * S.c := by ring
    omega
  have hf2' : solinasFold ⟨S.k, S.c⟩ (nv W₂ T₁) < 2 ^ (64 * (2 * n)) := by omega
  refine foldK_denote S.k S.c (2 * n) T₁ _ W₂ G hT₁ hkge hq hcl hf2'
    fun r₃ T₂ W₃ h₃ hT₂ hT₂v => ?_
  have hB1 := Mont.two_pow_succ n
  have htake : nv W₃ (T₂.take (n + 1)) = nv W₃ T₂ :=
    nv_take W₃ T₂ (n + 1) (by omega) (by rw [hT₂v, hB1]; omega)
  refine csubPCK_denote (lp S) _ _ W₃ G (by simp [hT₂]; omega)
    (by show _ < p S + _; rw [htake, hT₂v]; omega) fun r₄ out W₄ h₄ hout hv => ?_
  refine hK _ out W₄ (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄) hout ?_
  rw [hv, htake, hT₂v]
  have hmod := csub_eq_mod (lp S) (solinasFold ⟨S.k, S.c⟩ (nv W₂ T₁)) h2p
  refine hmod.trans ?_
  show solinasFold ⟨S.k, S.c⟩ (nv W₂ T₁) % p S = _
  rw [hT₁v, ← hTv]
  have m1 := solinasFold_mod ⟨S.k, S.c⟩ hc_le (solinasFold ⟨S.k, S.c⟩ (nv W₁ T))
  have m2 := solinasFold_mod ⟨S.k, S.c⟩ hc_le (nv W₁ T)
  exact m1.trans m2

/-! ## 6. The encoding and the blocks -/

/-- The encoding of `ZMod p`: the `n` limbs of the canonical representative. -/
def enc (x : ZMod (p S)) : ListDenote (Rn n) := limbsN n x.val

section Blocks

variable {Γ : Ctxt jasminDialect}

/-- The multiplication block over the limb lists `xs` and `ys`. -/
def mulBlk (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  mulSK S xs ys fun _ out => retN n out

/-- The squaring block: the multiplication block on one operand. -/
def sqrBlk (xs : List (Var Γ w64)) : MC Γ (Rn n) := mulBlk S xs xs

/-- The addition block: `Mont.addMK` at `lp`. -/
def addBlk (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  addMK (lp S) xs ys fun _ out => retN n out

/-- The subtraction block: `Mont.subBlk` at `lp`. -/
def subBlk (xs ys : List (Var Γ w64)) : MC Γ (Rn n) := Mont.subBlk (lp S) xs ys

/-- The negation block: `Mont.negBlk` at `lp`. -/
def negBlk (xs : List (Var Γ w64)) : MC Γ (Rn n) := Mont.negBlk (lp S) xs

/-- The constant block: the `n` digits of `x.val`. -/
def constBlk (x : ZMod (p S)) : MC Γ (Rn n) := Mont.constBlk n x.val

variable (W : Valuation Γ)

theorem mulBlk_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n) (hys : ys.length = n)
    (x y : ZMod (p S)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (mulBlk S xs ys).denote W = enc S (x * y) := by
  refine mulSK_denote S _ _ _ W _ hxs hys (by rw [hx]; exact ZMod.val_lt x)
    (by rw [hy]; exact ZMod.val_lt y) fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' hout, hv, hx, hy, enc, ZMod.val_mul]

theorem sqrBlk_denote (xs : List (Var Γ w64)) (hxs : xs.length = n) (x : ZMod (p S))
    (hx : nv W xs = x.val) :
    (sqrBlk S xs).denote W = enc S (x * x) :=
  mulBlk_denote S W xs xs hxs hxs x x hx hx

theorem addBlk_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n) (hys : ys.length = n)
    (x y : ZMod (p S)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (addBlk S xs ys).denote W = enc S (x + y) := by
  refine addMK_denote (lp S) _ _ _ W _ hxs hys (by rw [hx]; exact ZMod.val_lt x)
    (by rw [hy]; exact ZMod.val_lt y) fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' hout, hv, hx, hy, enc, ZMod.val_add]
  rfl

theorem subBlk_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n) (hys : ys.length = n)
    (x y : ZMod (p S)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (subBlk S xs ys).denote W = enc S (x - y) :=
  Mont.subBlk_denote (lp S) W xs ys hxs hys x y hx hy

theorem negBlk_denote (xs : List (Var Γ w64)) (hxs : xs.length = n) (x : ZMod (p S))
    (hx : nv W xs = x.val) :
    (negBlk S xs).denote W = enc S (-x) :=
  Mont.negBlk_denote (lp S) W xs hxs x hx

theorem constBlk_denote (x : ZMod (p S)) : (constBlk (Γ := Γ) S x).denote W = enc S x :=
  Mont.constBlk_denote W n x.val

end Blocks

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas
