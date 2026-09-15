/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Curve25519 field blocks over four 64-bit limbs

An element `x` of `ZMod (2^255 - 19)` is represented by the four little-endian
64-bit limbs of its canonical representative `x.val` (`enc`). For add, sub, neg,
mul, square, const and copy this module gives a multi-result
`MultiReturnCom jasminDialect Γ [reg 64, reg 64, reg 64, reg 64]` block over the
operand limb variables, and a value theorem: when the operand limbs have the
little-endian values `x.val` and `y.val`, the block denotes `enc (x ⋆ y)`.

The blocks are built by continuation-passing combinators (`bindK`, `adcR`, `rowR`,
`selR`, `xorR`, `constsK`). Each combinator has a specification over the
little-endian value `nv` of its limb lists, and the specifications compose through
renamings that preserve lookups (`Pres`).

The blocks bind `regArith`, `regConst`, `mulhi`, `addCarryLo`, `addCarryHi` and
`select`. None branches or indexes on data: every conditional correction is a
`select` on a carry bit.

* Addition: the carry chain, then one conditional subtraction of `p = 2^255 - 19`
  (`csubK`), which adds `2^256 - p` and selects the sum when its carry is set.
* Subtraction: `x + ¬y + 1` by the carry chain; when the carry is clear, `p` is
  added, selected by the carry. Negation is subtraction from zero.
* Multiplication: the 4×4 schoolbook product as rows of `mul`/`mulhi` carry chains
  (`rowR`, `accK`), then `reduceK`: the high half is folded by `2^256 ≡ 38`, the fifth
  limb of the sum is folded again, the carry of that fold adds `38` through a select,
  and two conditional subtractions give the canonical residue.

## Main definitions

* `p25519`, `limbsOf`, `enc`: the prime, the limbs of a natural and the encoding.
* `nv W xs`: the little-endian value of the limb variables `xs` under `W`.
* `addBlk`, `subBlk`, `negBlk`, `mulBlk`, `sqrBlk`, `constBlk`, `copyBlk`: the blocks.

## Main results

* `adcR_denote`, `rowR_denote`, `selR_denote`, `xorR_denote`, `constsK_denote`: the
  specifications of the list combinators.
* `csubK_denote`, `prodK_denote`, `reduceK_denote`: one conditional subtraction, the
  schoolbook product and the reduction of eight limbs below `2^510`.
* `addBlk_denote`, `subBlk_denote`, `negBlk_denote`, `mulBlk_denote`,
  `sqrBlk_denote`, `constBlk_denote`, `copyBlk_denote`: the value theorems of the
  blocks.
* `enc_injective`: the encoding is injective.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Expressions and the binding combinator -/

/-- The 64-bit register type. -/
abbrev w64 : JasminTy := .reg 64

/-- The 1-bit register type. -/
abbrev w1 : JasminTy := .reg 1

/-- Multi-result `jasminDialect` programs. -/
abbrev MC (Γ : Ctxt jasminDialect) (ts : List JasminTy) : Type :=
  MultiReturnCom jasminDialect Γ ts

/-- The value of a 64-bit variable. -/
abbrev lk {Γ : Ctxt jasminDialect} (x : Var Γ w64) (W : Valuation Γ) : BitVec 64 :=
  x.lookup W

/-- The value of a 1-bit variable. -/
abbrev lk1 {Γ : Ctxt jasminDialect} (x : Var Γ w1) (W : Valuation Γ) : BitVec 1 :=
  x.lookup W

section Exprs

variable {Γ : Ctxt jasminDialect}

/-- The expression `regArith op 64` on `a`, `b`. -/
def eBin (op : JasminBinOp) (a b : Var Γ w64) : Expr jasminDialect Γ w64 :=
  { op := .regArith op 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The expression `regConst 64 n`. -/
def eConst (n : Nat) : Expr jasminDialect Γ w64 :=
  { op := .regConst 64 n, retTy_eq := rfl, args := .nil }

/-- The expression `regConst 1 n`. -/
def eBit (n : Nat) : Expr jasminDialect Γ w1 :=
  { op := .regConst 1 n, retTy_eq := rfl, args := .nil }

/-- The expression `mulhi 64` on `a`, `b`. -/
def eMulhi (a b : Var Γ w64) : Expr jasminDialect Γ w64 :=
  { op := .mulhi 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The expression `addCarryLo 64` on `a`, `b`, `c`. -/
def eAdc (a b : Var Γ w64) (c : Var Γ w1) : Expr jasminDialect Γ w64 :=
  { op := .addCarryLo 64, retTy_eq := rfl, args := .cons a (.cons b (.cons c .nil)) }

/-- The expression `addCarryHi 64` on `a`, `b`, `c`. -/
def eCarry (a b : Var Γ w64) (c : Var Γ w1) : Expr jasminDialect Γ w1 :=
  { op := .addCarryHi 64, retTy_eq := rfl, args := .cons a (.cons b (.cons c .nil)) }

/-- The expression `select 64` on `c`, `a`, `b`. -/
def eSel (c : Var Γ w1) (a b : Var Γ w64) : Expr jasminDialect Γ w64 :=
  { op := .select 64, retTy_eq := rfl, args := .cons c (.cons a (.cons b .nil)) }

variable (W : Valuation Γ)

theorem eBin_denote (op : JasminBinOp) (a b : Var Γ w64) :
    (eBin op a b).denote W = op.apply (lk a W) (lk b W) := rfl

theorem eConst_denote (n : Nat) : (eConst (Γ := Γ) n).denote W = BitVec.ofNat 64 n := rfl

theorem eBit_denote (n : Nat) : (eBit (Γ := Γ) n).denote W = BitVec.ofNat 1 n := rfl

theorem eMulhi_denote (a b : Var Γ w64) :
    (eMulhi a b).denote W = mulHiW (lk a W) (lk b W) := rfl

theorem eAdc_denote (a b : Var Γ w64) (c : Var Γ w1) :
    (eAdc a b c).denote W = addCarryWord (lk a W) (lk b W) (lk1 c W) := rfl

theorem eCarry_denote (a b : Var Γ w64) (c : Var Γ w1) :
    (eCarry a b c).denote W = carryOutBit (lk a W) (lk b W) (lk1 c W) := rfl

theorem eSel_denote (c : Var Γ w1) (a b : Var Γ w64) :
    (eSel c a b).denote W = selectW (lk1 c W) (lk a W) (lk b W) := rfl

end Exprs

/-- A renaming `r` carries `W` to `W'` when every variable keeps its value. -/
def Pres {Γ Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (W : Valuation Γ)
    (W' : Valuation Δ) : Prop :=
  ∀ {s : JasminTy} (v : Var Γ s), (r v).lookup W' = v.lookup W

theorem Pres.id {Γ : Ctxt jasminDialect} (W : Valuation Γ) : Pres (fun v => v) W W :=
  fun _ => rfl

theorem Pres.comp {Γ₁ Γ₂ Γ₃ : Ctxt jasminDialect} {r₁ : Ctxt.Hom Γ₁ Γ₂}
    {r₂ : Ctxt.Hom Γ₂ Γ₃} {W₁ : Valuation Γ₁} {W₂ : Valuation Γ₂} {W₃ : Valuation Γ₃}
    (h₁ : Pres r₁ W₁ W₂) (h₂ : Pres r₂ W₂ W₃) : Pres (fun v => r₂ (r₁ v)) W₁ W₃ :=
  fun v => (h₂ (r₁ v)).trans (h₁ v)

/-- Bind an expression and pass the weakening and the bound variable to `k`. -/
def bindK {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ t → MC Δ ts) : MC Γ ts :=
  .var e (k (fun v => v.there) .here)

theorem bindK_denote {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ t → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (x : Var Δ t) (W' : Valuation Δ),
      Pres r W W' → x.lookup W' = e.denote W → (k r x).denote W' = G) :
    (bindK e k).denote W = G :=
  hk _ _ _ (fun _ => rfl) rfl

/-! ## 2. Word arithmetic -/

/-- The data word and carry of `addCarryLo`/`addCarryHi` recombine to the sum. -/
theorem adc_toNat (a b : BitVec 64) (c : BitVec 1) :
    (addCarryWord a b c).toNat + 2 ^ 64 * (carryOutBit a b c).toNat
      = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc : c.toNat < 2 := c.isLt
  unfold addCarryWord carryOutBit
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 by omega)]
  split <;> simp <;> omega

/-- `mul` and `mulhi` recombine to the full product. -/
theorem mulx_toNat (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (mulHiW a b).toNat = a.toNat * b.toNat := by
  have hlt : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_lt_mul'' a.isLt b.isLt
  have hq : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hlt
  simp only [mulHiW, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  exact Nat.mod_add_div _ _

/-- The high word of a 64-bit product is at most `2^64 - 2`. -/
theorem mulHiW_toNat_le (a b : BitVec 64) : (mulHiW a b).toNat ≤ 2 ^ 64 - 2 := by
  have ha : a.toNat ≤ 2 ^ 64 - 1 := by have := a.isLt; omega
  have hb : b.toNat ≤ 2 ^ 64 - 1 := by have := b.isLt; omega
  have h := mulx_toNat a b
  have hp : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul ha hb
  have hl := (a * b).isLt
  norm_num at hp
  omega

/-! ## 3. Little-endian values of variable lists -/

/-- The little-endian value of the 64-bit variables `xs` under `W`. -/
def nv {Δ : Ctxt jasminDialect} (W : Valuation Δ) : List (Var Δ w64) → Nat
  | [] => 0
  | x :: xs => (lk x W).toNat + 2 ^ 64 * nv W xs

theorem nv_nil {Δ : Ctxt jasminDialect} (W : Valuation Δ) : nv W [] = 0 := rfl

theorem nv_cons {Δ : Ctxt jasminDialect} (W : Valuation Δ) (x : Var Δ w64)
    (xs : List (Var Δ w64)) : nv W (x :: xs) = (lk x W).toNat + 2 ^ 64 * nv W xs := rfl

theorem nv_map {Γ Δ : Ctxt jasminDialect} {r : Ctxt.Hom Γ Δ} {W : Valuation Γ}
    {W' : Valuation Δ} (h : Pres r W W') :
    ∀ xs : List (Var Γ w64), nv W' (xs.map (fun v => r v)) = nv W xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, nv_cons, nv_map h xs]
      rw [show lk (r x) W' = lk x W from h x]

theorem nv_append {Δ : Ctxt jasminDialect} (W : Valuation Δ) :
    ∀ xs ys : List (Var Δ w64), nv W (xs ++ ys) = nv W xs + 2 ^ (64 * xs.length) * nv W ys
  | [], ys => by simp [nv_nil]
  | x :: xs, ys => by
      simp only [List.cons_append, nv_cons, nv_append W xs ys, List.length_cons]
      rw [Nat.mul_succ, Nat.pow_add]
      ring

theorem nv_lt {Δ : Ctxt jasminDialect} (W : Valuation Δ) :
    ∀ xs : List (Var Δ w64), nv W xs < 2 ^ (64 * xs.length)
  | [] => by simp [nv_nil]
  | x :: xs => by
      have h1 := nv_lt W xs
      have h2 := (lk x W).isLt
      simp only [nv_cons, List.length_cons]
      rw [Nat.mul_succ, Nat.pow_add]
      generalize 2 ^ (64 * xs.length) = B at h1 ⊢
      have : 2 ^ 64 * nv W xs + 2 ^ 64 ≤ 2 ^ 64 * B := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
      rw [Nat.mul_comm B]
      omega

/-! ## 4. List combinators -/

/-- The carry chain: `out[j] = xs[j] + ys[j] + c_j` with `c_0 = c`, passing the
    output words and the final carry to `k`. -/
def adcR : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ →
    List (Var Γ w64) → List (Var Γ w64) → Var Δ w1 →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 → MC Δ' ts) →
    MC Δ ts
  | _, _, _, ren, x :: xs, y :: ys, c, k =>
      bindK (eAdc (ren x) (ren y) c) fun r₁ s =>
      bindK (eCarry (r₁ (ren x)) (r₁ (ren y)) (r₁ c)) fun r₂ c' =>
      adcR (fun v => r₂ (r₁ (ren v))) xs ys c' fun r₃ out c'' =>
        k (fun v => r₃ (r₂ (r₁ v))) (r₃ (r₂ s) :: out) c''
  | _, _, _, _, [], _, c, k => k (fun v => v) [] c
  | _, _, _, _, _ :: _, [], c, k => k (fun v => v) [] c

theorem adcR_denote : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (xs ys : List (Var Γ w64)) (c : Var Δ w1)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 → MC Δ' ts)
    (W : Valuation Γ) (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ → xs.length = ys.length →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64)) (c' : Var Δ' w1)
        (W' : Valuation Δ'), Pres r W₀ W' → out.length = xs.length →
        nv W' out + 2 ^ (64 * xs.length) * (lk1 c' W').toNat
          = nv W xs + nv W ys + (lk1 c W₀).toNat →
        (k r out c').denote W' = G) →
    (adcR ren xs ys c k).denote W₀ = G
  | _, _, _, ren, x :: xs, y :: ys, c, k, W, W₀, G, hren, hlen, hk => by
      rw [adcR]
      refine bindK_denote _ _ _ _ fun r₁ s W₁ h₁ hs => ?_
      refine bindK_denote _ _ _ _ fun r₂ c' W₂ h₂ hc' => ?_
      refine adcR_denote _ xs ys c' _ W W₂ G (Pres.comp (Pres.comp hren h₁) h₂)
        (by simpa using hlen) fun r₃ out c'' W₃ h₃ hout hval => ?_
      refine hk _ _ _ W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) (by simp [hout]) ?_
      have e1 : lk (r₃ (r₂ s)) W₃ = addCarryWord (lk x W) (lk y W) (lk1 c W₀) := by
        rw [show lk (r₃ (r₂ s)) W₃ = lk s W₁ from (h₃ (r₂ s)).trans (h₂ s), show lk s W₁ = _ from hs,
          eAdc_denote]
        rw [show lk (ren x) W₀ = lk x W from hren x, show lk (ren y) W₀ = lk y W from hren y]
      have e2 : lk1 c' W₂ = carryOutBit (lk x W) (lk y W) (lk1 c W₀) := by
        rw [show lk1 c' W₂ = _ from hc', eCarry_denote]
        rw [show lk (r₁ (ren x)) W₁ = lk x W from (h₁ (ren x)).trans (hren x),
          show lk (r₁ (ren y)) W₁ = lk y W from (h₁ (ren y)).trans (hren y),
          show lk1 (r₁ c) W₁ = lk1 c W₀ from h₁ c]
      have ha := adc_toNat (lk x W) (lk y W) (lk1 c W₀)
      rw [← e1] at ha
      rw [e2] at hval
      simp only [nv_cons, List.length_cons]
      rw [Nat.mul_succ, Nat.pow_add]
      have hp : 2 ^ (64 * xs.length) * 2 ^ 64 * (lk1 c'' W₃).toNat
          = 2 ^ 64 * (2 ^ (64 * xs.length) * (lk1 c'' W₃).toNat) := by ring
      rw [hp]
      omega
  | _, _, _, _, [], [], c, k, W, W₀, G, _, _, hk => by
      rw [adcR]
      exact hk _ [] c W₀ (Pres.id W₀) rfl (by simp [nv_nil])
  | _, _, _, _, [], _ :: _, _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _, _, _, _, _ :: _, [], _, _, _, _, _, _, hlen, _ => by simp at hlen

/-- The product row: for `xs` and a word `w`, `out[j]` is the low word of
    `xs[j] · w` plus the high word of `xs[j-1] · w` and the carry, starting from the
    word `h` and the carry `c`; the last word is `h_last + c_last`. The register `z`
    holds `0`. -/
def rowR : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ →
    List (Var Γ w64) → Var Δ w64 → Var Δ w64 → Var Δ w64 → Var Δ w1 →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, _, [], _, z, h, c, k =>
      bindK (eAdc h z c) fun r₁ t => k r₁ [t]
  | _, _, _, ren, x :: xs, w, z, h, c, k =>
      bindK (eBin .mul (ren x) w) fun r₁ lo =>
      bindK (eMulhi (r₁ (ren x)) (r₁ w)) fun r₂ hi =>
      bindK (eAdc (r₂ lo) (r₂ (r₁ h)) (r₂ (r₁ c))) fun r₃ s =>
      bindK (eCarry (r₃ (r₂ lo)) (r₃ (r₂ (r₁ h))) (r₃ (r₂ (r₁ c)))) fun r₄ c' =>
      rowR (fun v => r₄ (r₃ (r₂ (r₁ (ren v))))) xs (r₄ (r₃ (r₂ (r₁ w))))
        (r₄ (r₃ (r₂ (r₁ z)))) (r₄ (r₃ hi)) c' fun r₅ out =>
        k (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) (r₅ (r₄ s) :: out)

theorem rowR_denote : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (xs : List (Var Γ w64)) (w z h : Var Δ w64) (c : Var Δ w1)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W : Valuation Γ) (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ → lk z W₀ = 0 → (lk h W₀).toNat + (lk1 c W₀).toNat < 2 ^ 64 →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
        (W' : Valuation Δ'), Pres r W₀ W' → out.length = xs.length + 1 →
        nv W' out = nv W xs * (lk w W₀).toNat + (lk h W₀).toNat + (lk1 c W₀).toNat →
        (k r out).denote W' = G) →
    (rowR ren xs w z h c k).denote W₀ = G
  | _, _, _, _, [], w, z, h, c, k, W, W₀, G, _, hz, hb, hk => by
      rw [rowR]
      refine bindK_denote _ _ _ _ fun r₁ t W₁ h₁ ht => hk r₁ [t] W₁ h₁ rfl ?_
      have ha := adc_toNat (lk h W₀) (lk z W₀) (lk1 c W₀)
      rw [show addCarryWord (lk h W₀) (lk z W₀) (lk1 c W₀) = lk t W₁ from ht.symm, hz] at ha
      simp only [nv_cons, nv_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod] at ha ⊢
      omega
  | _, _, _, ren, x :: xs, w, z, h, c, k, W, W₀, G, hren, hz, hb, hk => by
      rw [rowR]
      refine bindK_denote _ _ _ _ fun r₁ lo W₁ h₁ hlo => ?_
      refine bindK_denote _ _ _ _ fun r₂ hi W₂ h₂ hhi => ?_
      refine bindK_denote _ _ _ _ fun r₃ s W₃ h₃ hs => ?_
      refine bindK_denote _ _ _ _ fun r₄ c' W₄ h₄ hc' => ?_
      have ex : lk (ren x) W₀ = lk x W := hren x
      have elo : lk lo W₁ = lk x W * lk w W₀ := by rw [show lk lo W₁ = _ from hlo, eBin_denote, ex]; rfl
      have ehi : lk hi W₂ = mulHiW (lk x W) (lk w W₀) := by
        rw [show lk hi W₂ = _ from hhi, eMulhi_denote,
          show lk (r₁ (ren x)) W₁ = lk x W from (h₁ (ren x)).trans ex,
          show lk (r₁ w) W₁ = lk w W₀ from h₁ w]
      have el2 : lk (r₂ lo) W₂ = lk lo W₁ := h₂ lo
      have eh2 : lk (r₂ (r₁ h)) W₂ = lk h W₀ := (h₂ _).trans (h₁ h)
      have ec2 : lk1 (r₂ (r₁ c)) W₂ = lk1 c W₀ := (h₂ _).trans (h₁ c)
      have es : lk s W₃ = addCarryWord (lk lo W₁) (lk h W₀) (lk1 c W₀) := by
        rw [show lk s W₃ = _ from hs, eAdc_denote, el2, eh2, ec2]
      have ec' : lk1 c' W₄ = carryOutBit (lk lo W₁) (lk h W₀) (lk1 c W₀) := by
        rw [show lk1 c' W₄ = _ from hc', eCarry_denote,
          show lk (r₃ (r₂ lo)) W₃ = lk lo W₁ from (h₃ _).trans el2,
          show lk (r₃ (r₂ (r₁ h))) W₃ = lk h W₀ from (h₃ _).trans eh2,
          show lk1 (r₃ (r₂ (r₁ c))) W₃ = lk1 c W₀ from (h₃ _).trans ec2]
      have ew : lk (r₄ (r₃ (r₂ (r₁ w)))) W₄ = lk w W₀ := (h₄ _).trans ((h₃ _).trans ((h₂ _).trans (h₁ w)))
      have ez : lk (r₄ (r₃ (r₂ (r₁ z)))) W₄ = 0 :=
        ((h₄ _).trans ((h₃ _).trans ((h₂ _).trans (h₁ z)))).trans hz
      have ehi4 : lk (r₄ (r₃ hi)) W₄ = lk hi W₂ := (h₄ _).trans (h₃ hi)
      have hmx := mulx_toNat (lk x W) (lk w W₀)
      have hle := mulHiW_toNat_le (lk x W) (lk w W₀)
      have hadc := adc_toNat (lk lo W₁) (lk h W₀) (lk1 c W₀)
      rw [← es, ← ec'] at hadc
      rw [← elo, ← ehi] at hmx
      rw [← ehi] at hle
      have hc'2 : (lk1 c' W₄).toNat < 2 := (lk1 c' W₄).isLt
      refine rowR_denote _ xs _ _ _ c' _ W W₄ G
        (Pres.comp (Pres.comp (Pres.comp (Pres.comp hren h₁) h₂) h₃) h₄) ez
        (by rw [ehi4]; omega) fun r₅ out W₅ h₅ hout hval => ?_
      refine hk _ _ W₅ (Pres.comp (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄) h₅)
        (by simp [hout]) ?_
      rw [ew, ehi4] at hval
      have es5 : lk (r₅ (r₄ s)) W₅ = lk s W₃ := (h₅ _).trans (h₄ s)
      simp only [nv_cons, es5, Nat.add_mul, Nat.mul_assoc]
      rw [hval]
      omega

/-- The limb-wise select: `out[j] = if c = 1 then xs[j] else ys[j]`. -/
def selR : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ → Var Δ w1 →
    List (Var Γ w64) → List (Var Γ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, ren, c, x :: xs, y :: ys, k =>
      bindK (eSel c (ren x) (ren y)) fun r₁ s =>
      selR (fun v => r₁ (ren v)) (r₁ c) xs ys fun r₂ out =>
        k (fun v => r₂ (r₁ v)) (r₂ s :: out)
  | _, _, _, _, _, [], _, k => k (fun v => v) []
  | _, _, _, _, _, _ :: _, [], k => k (fun v => v) []

theorem selR_denote : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (c : Var Δ w1) (xs ys : List (Var Γ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W : Valuation Γ) (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ → xs.length = ys.length →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
        (W' : Valuation Δ'), Pres r W₀ W' → out.length = xs.length →
        nv W' out = (if lk1 c W₀ = 1#1 then nv W xs else nv W ys) →
        (k r out).denote W' = G) →
    (selR ren c xs ys k).denote W₀ = G
  | _, _, _, ren, c, x :: xs, y :: ys, k, W, W₀, G, hren, hlen, hk => by
      rw [selR]
      refine bindK_denote _ _ _ _ fun r₁ s W₁ h₁ hs => ?_
      refine selR_denote _ (r₁ c) xs ys _ W W₁ G (Pres.comp hren h₁) (by simpa using hlen)
        fun r₂ out W₂ h₂ hout hval => ?_
      refine hk _ _ W₂ (Pres.comp h₁ h₂) (by simp [hout]) ?_
      have es : lk (r₂ s) W₂ = selectW (lk1 c W₀) (lk x W) (lk y W) := by
        rw [show lk (r₂ s) W₂ = lk s W₁ from h₂ s, show lk s W₁ = _ from hs, eSel_denote,
          show lk (ren x) W₀ = lk x W from hren x, show lk (ren y) W₀ = lk y W from hren y]
      rw [show lk1 (r₁ c) W₁ = lk1 c W₀ from h₁ c] at hval
      simp only [nv_cons, es, hval, selectW]
      split <;> rfl
  | _, _, _, _, c, [], [], k, W, W₀, G, _, _, hk => by
      rw [selR]
      exact hk _ [] W₀ (Pres.id W₀) rfl (by simp [nv_nil])
  | _, _, _, _, _, [], _ :: _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _, _, _, _, _, _ :: _, [], _, _, _, _, _, hlen, _ => by simp at hlen

/-- The limb-wise exclusive or with the register `m`. -/
def xorR : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ → Var Δ w64 →
    List (Var Γ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, ren, m, x :: xs, k =>
      bindK (eBin .xor (ren x) m) fun r₁ s =>
      xorR (fun v => r₁ (ren v)) (r₁ m) xs fun r₂ out =>
        k (fun v => r₂ (r₁ v)) (r₂ s :: out)
  | _, _, _, _, _, [], k => k (fun v => v) []

theorem xor_allOnes_toNat (a : BitVec 64) :
    (a ^^^ BitVec.ofNat 64 (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 - a.toNat := by
  rw [show BitVec.ofNat 64 (2 ^ 64 - 1) = BitVec.allOnes 64 from
    BitVec.eq_of_toNat_eq (by simp), BitVec.xor_allOnes, BitVec.toNat_not]

theorem xorR_denote : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (m : Var Δ w64) (xs : List (Var Γ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W : Valuation Γ) (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ → lk m W₀ = BitVec.ofNat 64 (2 ^ 64 - 1) →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
        (W' : Valuation Δ'), Pres r W₀ W' → out.length = xs.length →
        nv W' out + nv W xs + 1 = 2 ^ (64 * xs.length) →
        (k r out).denote W' = G) →
    (xorR ren m xs k).denote W₀ = G
  | _, _, _, ren, m, x :: xs, k, W, W₀, G, hren, hm, hk => by
      rw [xorR]
      refine bindK_denote _ _ _ _ fun r₁ s W₁ h₁ hs => ?_
      refine xorR_denote _ (r₁ m) xs _ W W₁ G (Pres.comp hren h₁) ((h₁ m).trans hm)
        fun r₂ out W₂ h₂ hout hval => ?_
      refine hk _ _ W₂ (Pres.comp h₁ h₂) (by simp [hout]) ?_
      have es : (lk (r₂ s) W₂).toNat = 2 ^ 64 - 1 - (lk x W).toNat := by
        rw [show lk (r₂ s) W₂ = lk s W₁ from h₂ s, show lk s W₁ = _ from hs, eBin_denote,
          show lk (ren x) W₀ = lk x W from hren x, hm]
        exact xor_allOnes_toNat _
      have hx := (lk x W).isLt
      simp only [nv_cons, es, List.length_cons]
      rw [Nat.mul_succ, Nat.pow_add]
      have hB : 1 ≤ 2 ^ (64 * xs.length) := Nat.one_le_two_pow
      have hp : 2 ^ (64 * xs.length) * 2 ^ 64 = 2 ^ 64 * 2 ^ (64 * xs.length) := Nat.mul_comm _ _
      rw [hp]
      omega
  | _, _, _, _, _, [], k, W, W₀, G, _, _, hk => by
      rw [xorR]
      exact hk _ [] W₀ (Pres.id W₀) rfl (by simp [nv_nil])

/-- The little-endian value of a list of naturals in radix `2^64`. -/
def limbsNat : List Nat → Nat
  | [] => 0
  | n :: ns => n + 2 ^ 64 * limbsNat ns

/-- Bind `regConst 64 n` for each `n` in `ns`. -/
def constsK : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → List Nat →
    (∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) → MC Γ ts
  | _, _, [], k => k (fun v => v) []
  | _, _, n :: ns, k =>
      bindK (eConst n) fun r₁ v =>
      constsK ns fun r₂ out => k (fun u => r₂ (r₁ u)) (r₂ v :: out)

theorem constsK_denote : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ns : List Nat)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts),
    (∀ n ∈ ns, n < 2 ^ 64) →
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
        (W' : Valuation Δ), Pres r W W' → out.length = ns.length →
        nv W' out = limbsNat ns → (k r out).denote W' = G) →
    (constsK ns k).denote W = G
  | _, _, [], k, W, G, _, hk => by
      rw [constsK]
      exact hk _ [] W (Pres.id W) rfl rfl
  | _, _, n :: ns, k, W, G, hns, hk => by
      rw [constsK]
      refine bindK_denote _ _ _ _ fun r₁ v W₁ h₁ hv => ?_
      refine constsK_denote ns _ W₁ G (fun a ha => hns a (List.mem_cons_of_mem n ha))
        fun r₂ out W₂ h₂ hout hval => ?_
      refine hk _ _ W₂ (Pres.comp h₁ h₂) (by simp [hout]) ?_
      have ev : (lk (r₂ v) W₂).toNat = n := by
        rw [show lk (r₂ v) W₂ = lk v W₁ from h₂ v, show lk v W₁ = _ from hv, eConst_denote,
          BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (hns n (List.mem_cons_self))
      simp only [nv_cons, ev, hval, limbsNat]

/-! ## 5. Multi-limb arithmetic -/

/-- The carry chain with carry-in `0`. -/
def addK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → Var Δ w1 → MC Δ ts) :
    MC Γ ts :=
  bindK (eBit 0) fun r₁ c => adcR r₁ xs ys c fun r₂ out c' => k (fun v => r₂ (r₁ v)) out c'

theorem addK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → Var Δ w1 → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : xs.length = ys.length)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64)) (c : Var Δ w1)
      (W' : Valuation Δ), Pres r W W' → out.length = xs.length →
      nv W' out + 2 ^ (64 * xs.length) * (lk1 c W').toNat = nv W xs + nv W ys →
      (k r out c).denote W' = G) :
    (addK xs ys k).denote W = G := by
  refine bindK_denote _ _ _ _ fun r₁ c W₁ h₁ hc => ?_
  refine adcR_denote r₁ xs ys c _ W W₁ G h₁ hlen fun r₂ out c' W₂ h₂ hout hval => ?_
  refine hk _ out c' W₂ (Pres.comp h₁ h₂) hout ?_
  rw [hval, show lk1 c W₁ = _ from hc, eBit_denote]
  rfl

/-- The product of a limb list and a word, as `length + 1` limbs. -/
def mulRowK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64)) (w : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst 0) fun r₁ z =>
  bindK (eBit 0) fun r₂ c =>
  rowR (fun v => r₂ (r₁ v)) xs (r₂ (r₁ w)) (r₂ z) (r₂ z) c fun r₃ out =>
    k (fun v => r₃ (r₂ (r₁ v))) out

theorem mulRowK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (w : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = xs.length + 1 →
      nv W' out = nv W xs * (lk w W).toNat → (k r out).denote W' = G) :
    (mulRowK xs w k).denote W = G := by
  refine bindK_denote _ _ _ _ fun r₁ z W₁ h₁ hz => ?_
  refine bindK_denote _ _ _ _ fun r₂ c W₂ h₂ hc => ?_
  have ez : lk (r₂ z) W₂ = 0 := (h₂ z).trans hz
  have ec : (lk1 c W₂).toNat = 0 := by rw [show lk1 c W₂ = _ from hc, eBit_denote]; rfl
  refine rowR_denote _ xs _ _ _ c _ W W₂ G (Pres.comp h₁ h₂) ez (by rw [ez, ec]; simp)
    fun r₃ out W₃ h₃ hout hval => ?_
  refine hk _ out W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) hout ?_
  rw [hval, ez, ec, show lk (r₂ (r₁ w)) W₂ = lk w W from (h₂ _).trans (h₁ w)]
  simp

/-- One conditional subtraction of `2^255 - 19` from four limbs: the sum with
    `2^256 - (2^255 - 19)` is selected when its carry is set. -/
def csubK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  constsK [19, 0, 0, 2 ^ 63] fun r₁ K =>
  addK (xs.map (fun v => r₁ v)) K fun r₂ T c =>
  selR (fun v => v) c T (xs.map (fun v => r₂ (r₁ v))) fun r₃ out =>
    k (fun v => r₃ (r₂ (r₁ v))) out

theorem csubK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : xs.length = 4)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (if 2 ^ 255 - 19 ≤ nv W xs then nv W xs - (2 ^ 255 - 19) else nv W xs) →
      (k r out).denote W' = G) :
    (csubK xs k).denote W = G := by
  refine constsK_denote _ _ W G (by simp) fun r₁ K W₁ h₁ hK hKv => ?_
  refine addK_denote _ K _ W₁ G (by simp [hlen, hK]) fun r₂ T c W₂ h₂ hT hTv => ?_
  refine selR_denote (fun v => v) c T _ _ W₂ W₂ G (Pres.id W₂) (by simp [hT, hlen])
    fun r₃ out W₃ h₃ hout hval => ?_
  refine hk _ out W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) (by simp [hout, hT, hlen]) ?_
  rw [hval, nv_map (Pres.comp h₁ h₂) xs]
  rw [nv_map h₁ xs, hKv] at hTv
  simp only [List.length_map, hlen, limbsNat] at hTv hT
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

/-- One accumulation step of the schoolbook product: the row `xs · y` is added to
    the limbs of `acc` from position `i` on. -/
def accK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (i : Nat) (xs : List (Var Γ w64))
    (y : Var Γ w64) (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  mulRowK xs y fun r₁ row =>
  bindK (eConst 0) fun r₂ z =>
  addK ((acc.drop i).map (fun v => r₂ (r₁ v)) ++ [z]) (row.map (fun v => r₂ v)) fun r₃ s _ =>
  k (fun v => r₃ (r₂ (r₁ v))) ((acc.take i).map (fun v => r₃ (r₂ (r₁ v))) ++ s)

theorem accK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (i : Nat)
    (xs : List (Var Γ w64)) (y : Var Γ w64) (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4) (hacc : acc.length = i + 4)
    (hbound : nv W acc + 2 ^ (64 * i) * (nv W xs * (lk y W).toNat) < 2 ^ (64 * i) * 2 ^ 320)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = i + 5 →
      nv W' out = nv W acc + 2 ^ (64 * i) * (nv W xs * (lk y W).toNat) →
      (k r out).denote W' = G) :
    (accK i xs y acc k).denote W = G := by
  refine mulRowK_denote xs y _ W G fun r₁ row W₁ h₁ hrow hrowv => ?_
  refine bindK_denote _ _ _ _ fun r₂ z W₂ h₂ hz => ?_
  have hdl : (acc.drop i).length = 4 := by simp [hacc]
  have htl : (acc.take i).length = i := by simp [hacc]
  refine addK_denote _ _ _ W₂ G (by simp [hrow, hxs, hacc]) fun r₃ s c W₃ h₃ hs hsv => ?_
  refine hk _ _ W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) (by simp [hs, hacc]) ?_
  have hzv : (lk z W₂).toNat = 0 := by rw [show lk z W₂ = _ from hz, eConst_denote]; rfl
  rw [nv_append, nv_map (Pres.comp h₁ h₂), nv_map h₂, hrowv] at hsv
  simp only [nv_cons, nv_nil, hzv, List.length_append, List.length_map, hdl,
    List.length_singleton] at hsv hs
  rw [nv_append, nv_map (Pres.comp (Pres.comp h₁ h₂) h₃), List.length_map, htl]
  have hsplit := nv_append W (acc.take i) (acc.drop i)
  rw [List.take_append_drop, htl] at hsplit
  rw [hsplit] at hbound ⊢
  generalize 2 ^ (64 * i) = B at hbound ⊢
  have hpow : (2 : Nat) ^ (64 * (4 + 1)) = 2 ^ 320 := by norm_num
  rw [hpow] at hsv
  have hlt : B * (nv W₃ s + 2 ^ 320 * (lk1 c W₃).toNat) < B * 2 ^ 320 := by
    have : nv W₃ s + 2 ^ 320 * (lk1 c W₃).toNat = nv W (acc.drop i) + nv W xs * (lk y W).toNat := by
      omega
    rw [this, Nat.mul_add]
    omega
  have hlt' := Nat.lt_of_mul_lt_mul_left hlt
  have hs' : nv W₃ s = nv W (acc.drop i) + nv W xs * (lk y W).toNat := by omega
  rw [hs', Nat.mul_add]
  omega

/-- The schoolbook product of four limbs and the words `y₀, y₁, y₂, y₃`, as eight
    limbs. -/
def prodK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (y₀ y₁ y₂ y₃ : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  mulRowK xs y₀ fun r₁ a₁ =>
  accK 1 (xs.map (fun v => r₁ v)) (r₁ y₁) a₁ fun r₂ a₂ =>
  accK 2 (xs.map (fun v => r₂ (r₁ v))) (r₂ (r₁ y₂)) a₂ fun r₃ a₃ =>
  accK 3 (xs.map (fun v => r₃ (r₂ (r₁ v)))) (r₃ (r₂ (r₁ y₃))) a₃ fun r₄ a₄ =>
  k (fun v => r₄ (r₃ (r₂ (r₁ v)))) a₄

set_option exponentiation.threshold 512 in
theorem prodK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (y₀ y₁ y₂ y₃ : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 8 →
      nv W' out = nv W xs * nv W [y₀, y₁, y₂, y₃] → (k r out).denote W' = G) :
    (prodK xs y₀ y₁ y₂ y₃ k).denote W = G := by
  have hX := nv_lt W xs
  rw [hxs] at hX
  have b0 := (lk y₀ W).isLt
  have b1 := (lk y₁ W).isLt
  have b2 := (lk y₂ W).isLt
  have b3 := (lk y₃ W).isLt
  refine mulRowK_denote xs y₀ _ W G fun r₁ a₁ W₁ h₁ ha₁ ha₁v => ?_
  have e1 : nv W₁ (xs.map (fun v => r₁ v)) = nv W xs := nv_map h₁ xs
  have ey1 : lk (r₁ y₁) W₁ = lk y₁ W := h₁ y₁
  refine accK_denote 1 _ _ a₁ _ W₁ G (by simp [hxs]) (by simp [ha₁, hxs]) ?_
    fun r₂ a₂ W₂ h₂ ha₂ ha₂v => ?_
  · simp only [e1, ey1, ha₁v]
    calc nv W xs * (lk y₀ W).toNat + 2 ^ (64 * 1) * (nv W xs * (lk y₁ W).toNat)
        = nv W xs * ((lk y₀ W).toNat + 2 ^ 64 * (lk y₁ W).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 128 := Nat.mul_lt_mul'' hX (by omega)
      _ = 2 ^ (64 * 1) * 2 ^ 320 :=
          (Nat.pow_add 2 256 128).symm.trans (Nat.pow_add 2 (64 * 1) 320)
  have h12 : Pres (fun v => r₂ (r₁ v)) W W₂ := Pres.comp h₁ h₂
  have e2 : nv W₂ (xs.map (fun v => r₂ (r₁ v))) = nv W xs := nv_map h12 xs
  have ey2 : lk (r₂ (r₁ y₂)) W₂ = lk y₂ W := h12 y₂
  simp only [e1, ey1, ha₁v] at ha₂v
  refine accK_denote 2 _ _ a₂ _ W₂ G (by simp [hxs]) (by simp [ha₂]) ?_
    fun r₃ a₃ W₃ h₃ ha₃ ha₃v => ?_
  · simp only [e2, ey2, ha₂v]
    calc nv W xs * (lk y₀ W).toNat + 2 ^ (64 * 1) * (nv W xs * (lk y₁ W).toNat)
          + 2 ^ (64 * 2) * (nv W xs * (lk y₂ W).toNat)
        = nv W xs * ((lk y₀ W).toNat + 2 ^ 64 * (lk y₁ W).toNat
            + 2 ^ 128 * (lk y₂ W).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 192 := Nat.mul_lt_mul'' hX (by omega)
      _ = 2 ^ (64 * 2) * 2 ^ 320 := by rw [← Nat.pow_add, ← Nat.pow_add]
  have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W W₃ := Pres.comp h12 h₃
  have e3 : nv W₃ (xs.map (fun v => r₃ (r₂ (r₁ v)))) = nv W xs := nv_map h123 xs
  have ey3 : lk (r₃ (r₂ (r₁ y₃))) W₃ = lk y₃ W := h123 y₃
  simp only [e2, ey2, ha₂v] at ha₃v
  refine accK_denote 3 _ _ a₃ _ W₃ G (by simp [hxs]) (by simp [ha₃]) ?_
    fun r₄ a₄ W₄ h₄ ha₄ ha₄v => ?_
  · simp only [e3, ey3, ha₃v]
    calc nv W xs * (lk y₀ W).toNat + 2 ^ (64 * 1) * (nv W xs * (lk y₁ W).toNat)
          + 2 ^ (64 * 2) * (nv W xs * (lk y₂ W).toNat)
          + 2 ^ (64 * 3) * (nv W xs * (lk y₃ W).toNat)
        = nv W xs * ((lk y₀ W).toNat + 2 ^ 64 * (lk y₁ W).toNat
            + 2 ^ 128 * (lk y₂ W).toNat + 2 ^ 192 * (lk y₃ W).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul'' hX (by omega)
      _ = 2 ^ (64 * 3) * 2 ^ 320 := by rw [← Nat.pow_add, ← Nat.pow_add]
  refine hk _ _ W₄ (Pres.comp h123 h₄) ha₄ ?_
  simp only [ha₄v, e3, ey3, ha₃v]
  simp only [nv_cons, nv_nil]
  ring

/-- Two conditional subtractions of `2^255 - 19` reduce every value below `2^256`. -/
theorem csub_twice_eq_mod (V : Nat) (hV : V < 2 ^ 256) :
    (if 2 ^ 255 - 19 ≤ (if 2 ^ 255 - 19 ≤ V then V - (2 ^ 255 - 19) else V)
      then (if 2 ^ 255 - 19 ≤ V then V - (2 ^ 255 - 19) else V) - (2 ^ 255 - 19)
      else (if 2 ^ 255 - 19 ≤ V then V - (2 ^ 255 - 19) else V)) = V % (2 ^ 255 - 19) := by
  split_ifs <;> omega

/-- The reduction of eight limbs below `2^510` modulo `2^255 - 19`: the high half is
    folded with `2^256 ≡ 38`, the fifth limb of the result is folded again, the carry
    of that fold is folded by a select, and two conditional subtractions follow. -/
def reduceK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ps : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst 38) fun r₁ c38 =>
  mulRowK ((ps.drop 4).map (fun v => r₁ v)) c38 fun r₂ R =>
  bindK (eConst 0) fun r₃ z =>
  addK ((ps.take 4).map (fun v => r₃ (r₂ (r₁ v))) ++ [z]) (R.map (fun v => r₃ v)) fun r₄ S _ =>
  mulRowK (S.drop 4) (r₄ (r₃ (r₂ c38))) fun r₅ M =>
  addK ((S.take 4).map (fun v => r₅ v)) (M ++ [r₅ (r₄ z), r₅ (r₄ z)]) fun r₆ U cu =>
  bindK (eSel cu (r₆ (r₅ (r₄ (r₃ (r₂ c38))))) (r₆ (r₅ (r₄ z)))) fun r₇ m =>
  addK (U.map (fun v => r₇ v))
    [m, r₇ (r₆ (r₅ (r₄ z))), r₇ (r₆ (r₅ (r₄ z))), r₇ (r₆ (r₅ (r₄ z)))] fun r₈ V _ =>
  csubK V fun r₉ V₁ =>
  csubK V₁ fun r₁₀ V₂ =>
  k (fun v => r₁₀ (r₉ (r₈ (r₇ (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v)))))))))) V₂

theorem reduceK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ps : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hps : ps.length = 8) (hN : nv W ps < 2 ^ 510)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = nv W ps % (2 ^ 255 - 19) → (k r out).denote W' = G) :
    (reduceK ps k).denote W = G := by
  have hsplit := nv_append W (ps.take 4) (ps.drop 4)
  have htl : (ps.take 4).length = 4 := by simp [hps]
  have hdl : (ps.drop 4).length = 4 := by simp [hps]
  rw [List.take_append_drop, htl] at hsplit
  have hL := nv_lt W (ps.take 4)
  rw [htl] at hL
  refine bindK_denote _ _ _ _ fun r₁ c38 W₁ h₁ hc38 => ?_
  have e38 : (lk c38 W₁).toNat = 38 := by rw [show lk c38 W₁ = _ from hc38, eConst_denote]; rfl
  refine mulRowK_denote _ c38 _ W₁ G fun r₂ R W₂ h₂ hR hRv => ?_
  rw [nv_map h₁, e38] at hRv
  simp only [List.length_map, hdl] at hR
  refine bindK_denote _ _ _ _ fun r₃ z W₃ h₃ hz => ?_
  have ez : (lk z W₃).toNat = 0 := by rw [show lk z W₃ = _ from hz, eConst_denote]; rfl
  have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W W₃ := Pres.comp (Pres.comp h₁ h₂) h₃
  refine addK_denote _ _ _ W₃ G (by simp [hps, hR]) fun r₄ S cs W₄ h₄ hS hSv => ?_
  rw [nv_append, nv_map h123, nv_map h₃, hRv] at hSv
  simp only [nv_cons, nv_nil, ez, List.length_append, List.length_map, htl,
    List.length_singleton] at hSv hS
  have hS8 : (S.take 4).length = 4 := by simp [hS]
  have hS1 : (S.drop 4).length = 1 := by simp [hS]
  have hSsplit := nv_append W₄ (S.take 4) (S.drop 4)
  rw [List.take_append_drop, hS8] at hSsplit
  have hSlo := nv_lt W₄ (S.take 4)
  rw [hS8] at hSlo
  have ec38 : (lk (r₄ (r₃ (r₂ c38))) W₄).toNat = 38 := by
    rw [show lk (r₄ (r₃ (r₂ c38))) W₄ = lk c38 W₁ from (h₄ _).trans ((h₃ _).trans (h₂ c38)), e38]
  refine mulRowK_denote _ _ _ W₄ G fun r₅ M W₅ h₅ hM hMv => ?_
  rw [ec38] at hMv
  rw [hS1] at hM
  have ez5 : (lk (r₅ (r₄ z)) W₅).toNat = 0 := by
    rw [show lk (r₅ (r₄ z)) W₅ = lk z W₃ from (h₅ _).trans (h₄ z), ez]
  refine addK_denote _ _ _ W₅ G (by simp [hS, hM]) fun r₆ U cu W₆ h₆ hU hUv => ?_
  rw [nv_append, nv_map h₅, hMv] at hUv
  simp only [nv_cons, nv_nil, ez5, List.length_map, hS8, hM] at hUv hU
  have hUl := nv_lt W₆ U
  rw [hU] at hUl
  refine bindK_denote _ _ _ _ fun r₇ m W₇ h₇ hm => ?_
  have hcu := (lk1 cu W₆).isLt
  have em : (lk m W₇).toNat = if lk1 cu W₆ = 1#1 then 38 else 0 := by
    rw [show lk m W₇ = _ from hm, eSel_denote, selectW,
      show lk (r₆ (r₅ (r₄ (r₃ (r₂ c38))))) W₆ = lk (r₄ (r₃ (r₂ c38))) W₄ from
        (h₆ _).trans (h₅ _),
      show lk (r₆ (r₅ (r₄ z))) W₆ = lk (r₅ (r₄ z)) W₅ from h₆ _]
    split
    · exact ec38
    · exact ez5
  have ez7 : (lk (r₇ (r₆ (r₅ (r₄ z)))) W₇).toNat = 0 := by
    rw [show lk (r₇ (r₆ (r₅ (r₄ z)))) W₇ = lk (r₅ (r₄ z)) W₅ from (h₇ _).trans (h₆ _), ez5]
  refine addK_denote _ _ _ W₇ G (by simp [hU]) fun r₈ V cv W₈ h₈ hV hVv => ?_
  rw [nv_map h₇] at hVv
  simp only [nv_cons, nv_nil, em, ez7, List.length_map, hU] at hVv hV
  have hVl := nv_lt W₈ V
  rw [hV] at hVl
  refine csubK_denote V _ W₈ G hV fun r₉ V₁ W₉ h₉ hV₁ hV₁v => ?_
  refine csubK_denote V₁ _ W₉ G hV₁ fun r₁₀ V₂ W₁₀ h₁₀ hV₂ hV₂v => ?_
  refine hk _ V₂ W₁₀ (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp
    (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉) h₁₀) hV₂ ?_
  rw [hV₂v, hV₁v]
  have hcs := (lk1 cs W₄).isLt
  have hcv := (lk1 cv W₈).isLt
  have hH : nv W (ps.drop 4) < 2 ^ 254 := by omega
  have hcs0 : (lk1 cs W₄).toNat = 0 := by omega
  rw [hcs0] at hSv
  have hS4 : nv W₄ (S.drop 4) < 64 := by omega
  have hEq : nv W ps = nv W₈ V
      + (2 ^ 255 - 19) * (2 * (nv W (ps.drop 4) + nv W₄ (S.drop 4) + (lk1 cu W₆).toNat)) := by
    by_cases hc : lk1 cu W₆ = 1#1
    · have h1 : (lk1 cu W₆).toNat = 1 := by rw [hc]; rfl
      rw [if_pos hc] at hVv
      rw [h1] at hUv
      have hU0 : nv W₆ U < 2 ^ 12 := by omega
      have hcv0 : (lk1 cv W₈).toNat = 0 := by omega
      rw [hcv0] at hVv
      omega
    · have h0 : (lk1 cu W₆).toNat = 0 := by
        have : (lk1 cu W₆).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      rw [if_neg hc] at hVv
      rw [h0] at hUv
      have hcv0 : (lk1 cv W₈).toNat = 0 := by omega
      rw [hcv0] at hVv
      omega
  rw [hEq, Nat.add_mul_mod_self_left]
  exact csub_twice_eq_mod _ hVl

/-- Field addition on four limbs: the carry chain, then one conditional subtraction. -/
def addFK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  addK xs ys fun r₁ S _ => csubK S fun r₂ out => k (fun v => r₂ (r₁ v)) out

theorem addFK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4) (hys : ys.length = 4)
    (hx : nv W xs < 2 ^ 255 - 19) (hy : nv W ys < 2 ^ 255 - 19)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (nv W xs + nv W ys) % (2 ^ 255 - 19) → (k r out).denote W' = G) :
    (addFK xs ys k).denote W = G := by
  refine addK_denote xs ys _ W G (by rw [hxs, hys]) fun r₁ S c W₁ h₁ hS hSv => ?_
  refine csubK_denote S _ W₁ G (by rw [hS, hxs]) fun r₂ out W₂ h₂ hout hv => ?_
  refine hk _ out W₂ (Pres.comp h₁ h₂) hout ?_
  rw [hv]
  rw [hxs] at hSv
  have hc := (lk1 c W₁).isLt
  have hSl := nv_lt W₁ S
  rw [hS, hxs] at hSl
  split_ifs <;> omega

/-- Field subtraction on four limbs: `xs + ¬ys + 1` by the carry chain; when the carry
    is clear, `2^255 - 19` is added, selected by the carry. -/
def subK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst (2 ^ 64 - 1)) fun r₁ m =>
  xorR r₁ m ys fun r₂ ny =>
  bindK (eBit 1) fun r₃ one =>
  adcR (fun v => v) (xs.map (fun v => r₃ (r₂ (r₁ v)))) (ny.map (fun v => r₃ v)) one
    fun r₄ D c =>
  constsK [2 ^ 64 - 19, 2 ^ 64 - 1, 2 ^ 64 - 1, 2 ^ 63 - 1] fun r₅ PL =>
  addK (D.map (fun v => r₅ v)) PL fun r₆ E _ =>
  selR (fun v => v) (r₆ (r₅ c)) (D.map (fun v => r₆ (r₅ v))) E fun r₇ out =>
  k (fun v => r₇ (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v))))))) out

theorem subK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4) (hys : ys.length = 4)
    (hx : nv W xs < 2 ^ 255 - 19) (hy : nv W ys < 2 ^ 255 - 19)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = (nv W xs + (2 ^ 255 - 19 - nv W ys)) % (2 ^ 255 - 19) →
      (k r out).denote W' = G) :
    (subK xs ys k).denote W = G := by
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
  refine constsK_denote _ _ W₄ G (by simp) fun r₅ PL W₅ h₅ hPL hPLv => ?_
  refine addK_denote _ PL _ W₅ G (by simp [hD, hPL]) fun r₆ E e W₆ h₆ hE hEv => ?_
  rw [nv_map h₅, hPLv] at hEv
  simp only [List.length_map, hD, limbsNat] at hEv hE
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
    omega
  · have h0 : (lk1 c W₄).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    rw [if_neg hc]
    omega

/-- Field multiplication on four limbs: the schoolbook product, then `reduceK`. -/
def mulFK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (y₀ y₁ y₂ y₃ : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  prodK xs y₀ y₁ y₂ y₃ fun r₁ ps => reduceK ps fun r₂ out => k (fun v => r₂ (r₁ v)) out

set_option exponentiation.threshold 512 in
theorem mulFK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (y₀ y₁ y₂ y₃ : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = 4)
    (hx : nv W xs < 2 ^ 255 - 19) (hy : nv W [y₀, y₁, y₂, y₃] < 2 ^ 255 - 19)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 4 →
      nv W' out = nv W xs * nv W [y₀, y₁, y₂, y₃] % (2 ^ 255 - 19) →
      (k r out).denote W' = G) :
    (mulFK xs y₀ y₁ y₂ y₃ k).denote W = G := by
  refine prodK_denote xs y₀ y₁ y₂ y₃ _ W G hxs fun r₁ ps W₁ h₁ hps hpsv => ?_
  have hlt : nv W₁ ps < 2 ^ 510 := by
    rw [hpsv]
    calc nv W xs * nv W [y₀, y₁, y₂, y₃] < 2 ^ 255 * 2 ^ 255 :=
          Nat.mul_lt_mul'' (by omega) (by omega)
      _ = 2 ^ 510 := (Nat.pow_add 2 255 255).symm
  refine reduceK_denote ps _ W₁ G hps hlt fun r₂ out W₂ h₂ hout hv => ?_
  exact hk _ out W₂ (Pres.comp h₁ h₂) hout (by rw [hv, hpsv])

/-! ## 6. The encoding and the blocks -/

/-- The prime `2^255 - 19`. -/
abbrev p25519 : Nat := 2 ^ 255 - 19

instance : NeZero p25519 := ⟨by norm_num⟩

/-- The register types of a field element: four 64-bit limbs. -/
abbrev R4 : List JasminTy := [w64, w64, w64, w64]

/-- The four little-endian 64-bit limbs of `n`. -/
def limbsOf (n : Nat) : ListDenote R4 :=
  .cons (BitVec.ofNat 64 n) (.cons (BitVec.ofNat 64 (n / 2 ^ 64))
    (.cons (BitVec.ofNat 64 (n / 2 ^ 128)) (.cons (BitVec.ofNat 64 (n / 2 ^ 192)) .nil)))

/-- The encoding of `ZMod (2^255 - 19)`: the four limbs of the canonical
    representative. -/
def enc (x : ZMod p25519) : ListDenote R4 := limbsOf x.val

/-- A 64-bit word is unchanged when its natural argument is truncated to 64
    bits. -/
theorem ofNat_mod_two_pow (n : Nat) :
    BitVec.ofNat 64 (n % 2 ^ 64) = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat, Nat.mod_mod])

theorem limbsOf_injective {m n : Nat} (hm : m < 2 ^ 256) (hn : n < 2 ^ 256)
    (h : limbsOf m = limbsOf n) : m = n := by
  simp only [limbsOf, HVector.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, -⟩ := h
  have e0 := congrArg BitVec.toNat h0
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  have e3 := congrArg BitVec.toNat h3
  simp only [BitVec.toNat_ofNat] at e0 e1 e2 e3
  omega

theorem enc_injective : Function.Injective enc := fun x y h =>
  ZMod.val_injective _ (limbsOf_injective
    (by have : x.val < 2 ^ 255 - 19 := ZMod.val_lt x; omega)
    (by have : y.val < 2 ^ 255 - 19 := ZMod.val_lt y; omega) h)

/-- The return of the four variables of a list of length four, and of `fb` four
    times on other lists. -/
def ret4 {Δ : Ctxt jasminDialect} (fb : Var Δ w64) : List (Var Δ w64) → MC Δ R4
  | [a, b, c, d] => .ret (.cons a (.cons b (.cons c (.cons d .nil))))
  | _ => .ret (.cons fb (.cons fb (.cons fb (.cons fb .nil))))

theorem ret4_denote {Δ : Ctxt jasminDialect} (fb : Var Δ w64) (out : List (Var Δ w64))
    (W : Valuation Δ) (hlen : out.length = 4) :
    (ret4 fb out).denote W = limbsOf (nv W out) := by
  match out, hlen with
  | [a, b, c, d], _ =>
    have ha := (lk a W).isLt
    have hb := (lk b W).isLt
    have hc := (lk c W).isLt
    have hd := (lk d W).isLt
    have e0 : Var.lookup a W = BitVec.ofNat 64 (nv W [a, b, c, d]) :=
      BitVec.eq_of_toNat_eq (by
        show (lk a W).toNat = _
        simp only [nv_cons, nv_nil, BitVec.toNat_ofNat]; omega)
    have e1 : Var.lookup b W = BitVec.ofNat 64 (nv W [a, b, c, d] / 2 ^ 64) :=
      BitVec.eq_of_toNat_eq (by
        show (lk b W).toNat = _
        simp only [nv_cons, nv_nil, BitVec.toNat_ofNat]; omega)
    have e2 : Var.lookup c W = BitVec.ofNat 64 (nv W [a, b, c, d] / 2 ^ 128) :=
      BitVec.eq_of_toNat_eq (by
        show (lk c W).toNat = _
        simp only [nv_cons, nv_nil, BitVec.toNat_ofNat]; omega)
    have e3 : Var.lookup d W = BitVec.ofNat 64 (nv W [a, b, c, d] / 2 ^ 192) :=
      BitVec.eq_of_toNat_eq (by
        show (lk d W).toNat = _
        simp only [nv_cons, nv_nil, BitVec.toNat_ofNat]; omega)
    show HVector.cons (Var.lookup a W) (HVector.cons (Var.lookup b W)
      (HVector.cons (Var.lookup c W) (HVector.cons (Var.lookup d W) HVector.nil))) = _
    rw [e0, e1, e2, e3]
    rfl

theorem val_sub_eq (x y : ZMod p25519) :
    (x - y).val = (x.val + (2 ^ 255 - 19 - y.val)) % (2 ^ 255 - 19) := by
  have hy : y.val < p25519 := ZMod.val_lt y
  have hcast : x - y = (((x.val + (p25519 - y.val)) : Nat) : ZMod p25519) := by
    rw [Nat.cast_add, Nat.cast_sub hy.le, ZMod.natCast_self]
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [hcast, ZMod.val_natCast]

theorem val_neg_eq (x : ZMod p25519) :
    (-x).val = (0 + (2 ^ 255 - 19 - x.val)) % (2 ^ 255 - 19) := by
  rw [← zero_sub, val_sub_eq, ZMod.val_zero]

section Blocks

variable {Γ : Ctxt jasminDialect}

/-- The field addition block over the limbs `x₀ … x₃` and `y₀ … y₃`. -/
def addBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  addFK [x₀, x₁, x₂, x₃] [y₀, y₁, y₂, y₃] fun r out => ret4 (r x₀) out

/-- The field subtraction block. -/
def subBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  subK [x₀, x₁, x₂, x₃] [y₀, y₁, y₂, y₃] fun r out => ret4 (r x₀) out

/-- The field negation block: subtraction from the zero limbs. -/
def negBlk (x₀ x₁ x₂ x₃ : Var Γ w64) : MC Γ R4 :=
  constsK [0, 0, 0, 0] fun r₁ zs =>
  subK zs [r₁ x₀, r₁ x₁, r₁ x₂, r₁ x₃] fun r₂ out => ret4 (r₂ (r₁ x₀)) out

/-- The field multiplication block. -/
def mulBlk (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) : MC Γ R4 :=
  mulFK [x₀, x₁, x₂, x₃] y₀ y₁ y₂ y₃ fun r out => ret4 (r x₀) out

/-- The field squaring block: the multiplication block on one operand. -/
def sqrBlk (x₀ x₁ x₂ x₃ : Var Γ w64) : MC Γ R4 :=
  mulBlk x₀ x₁ x₂ x₃ x₀ x₁ x₂ x₃

/-- The constant block: the four limbs of `x.val` as `regConst` bindings. Each
    bound natural is the 64-bit remainder of its digit, so it is the limb itself
    and fits a 64-bit immediate. -/
def constBlk (x : ZMod p25519) : MC Γ R4 :=
  .var (eConst (x.val % 2 ^ 64)) <| .var (eConst (x.val / 2 ^ 64 % 2 ^ 64)) <|
  .var (eConst (x.val / 2 ^ 128 % 2 ^ 64)) <|
  .var (eConst (x.val / 2 ^ 192 % 2 ^ 64)) <|
  .ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here))
    (.cons (.there .here) (.cons .here .nil))))

/-- The copy block: one `regArith or` binding `a ||| a` per limb. -/
def copyBlk (x₀ x₁ x₂ x₃ : Var Γ w64) : MC Γ R4 :=
  bindK (eBin .or x₀ x₀) fun r₁ c₀ =>
  bindK (eBin .or (r₁ x₁) (r₁ x₁)) fun r₂ c₁ =>
  bindK (eBin .or (r₂ (r₁ x₂)) (r₂ (r₁ x₂))) fun r₃ c₂ =>
  bindK (eBin .or (r₃ (r₂ (r₁ x₃))) (r₃ (r₂ (r₁ x₃)))) fun r₄ c₃ =>
  ret4 c₃ [r₄ (r₃ (r₂ c₀)), r₄ (r₃ c₁), r₄ c₂, c₃]

variable (W : Valuation Γ)

theorem addBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod p25519)
    (hx : nv W [x₀, x₁, x₂, x₃] = x.val) (hy : nv W [y₀, y₁, y₂, y₃] = y.val) :
    (addBlk x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc (x + y) := by
  have hxl : x.val < 2 ^ 255 - 19 := ZMod.val_lt x
  have hyl : y.val < 2 ^ 255 - 19 := ZMod.val_lt y
  refine addFK_denote _ _ _ W _ rfl rfl (by rw [hx]; exact hxl) (by rw [hy]; exact hyl)
    fun r out W' _ hout hv => ?_
  rw [ret4_denote _ out W' hout, hv, hx, hy, enc, ZMod.val_add]

theorem subBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod p25519)
    (hx : nv W [x₀, x₁, x₂, x₃] = x.val) (hy : nv W [y₀, y₁, y₂, y₃] = y.val) :
    (subBlk x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc (x - y) := by
  have hxl : x.val < 2 ^ 255 - 19 := ZMod.val_lt x
  have hyl : y.val < 2 ^ 255 - 19 := ZMod.val_lt y
  refine subK_denote _ _ _ W _ rfl rfl (by rw [hx]; exact hxl) (by rw [hy]; exact hyl)
    fun r out W' _ hout hv => ?_
  rw [ret4_denote _ out W' hout, hv, hx, hy, enc, val_sub_eq]

theorem negBlk_denote (x₀ x₁ x₂ x₃ : Var Γ w64) (x : ZMod p25519)
    (hx : nv W [x₀, x₁, x₂, x₃] = x.val) :
    (negBlk x₀ x₁ x₂ x₃).denote W = enc (-x) := by
  have hxl : x.val < 2 ^ 255 - 19 := ZMod.val_lt x
  refine constsK_denote _ _ W _ (by simp) fun r₁ zs W₁ h₁ hzs hzsv => ?_
  have hx₁ : nv W₁ [r₁ x₀, r₁ x₁, r₁ x₂, r₁ x₃] = x.val :=
    (nv_map h₁ [x₀, x₁, x₂, x₃]).trans hx
  simp only [limbsNat, Nat.mul_zero, Nat.add_zero] at hzsv
  refine subK_denote zs _ _ W₁ _ hzs rfl (by rw [hzsv]; omega) (by rw [hx₁]; exact hxl)
    fun r₂ out W₂ _ hout hv => ?_
  rw [ret4_denote _ out W₂ hout, hv, hzsv, hx₁, enc, val_neg_eq]

theorem mulBlk_denote (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64) (x y : ZMod p25519)
    (hx : nv W [x₀, x₁, x₂, x₃] = x.val) (hy : nv W [y₀, y₁, y₂, y₃] = y.val) :
    (mulBlk x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc (x * y) := by
  have hxl : x.val < 2 ^ 255 - 19 := ZMod.val_lt x
  have hyl : y.val < 2 ^ 255 - 19 := ZMod.val_lt y
  refine mulFK_denote _ _ _ _ _ _ W _ rfl (by rw [hx]; exact hxl) (by rw [hy]; exact hyl)
    fun r out W' _ hout hv => ?_
  rw [ret4_denote _ out W' hout, hv, hx, hy, enc, ZMod.val_mul]

theorem sqrBlk_denote (x₀ x₁ x₂ x₃ : Var Γ w64) (x : ZMod p25519)
    (hx : nv W [x₀, x₁, x₂, x₃] = x.val) :
    (sqrBlk x₀ x₁ x₂ x₃).denote W = enc (x * x) :=
  mulBlk_denote W x₀ x₁ x₂ x₃ x₀ x₁ x₂ x₃ x x hx hx

theorem constBlk_denote (x : ZMod p25519) : (constBlk (Γ := Γ) x).denote W = enc x := by
  rw [enc, limbsOf, ← ofNat_mod_two_pow x.val, ← ofNat_mod_two_pow (x.val / 2 ^ 64),
    ← ofNat_mod_two_pow (x.val / 2 ^ 128), ← ofNat_mod_two_pow (x.val / 2 ^ 192)]
  rfl

theorem copyBlk_denote (x₀ x₁ x₂ x₃ : Var Γ w64) (x : ZMod p25519)
    (hx : nv W [x₀, x₁, x₂, x₃] = x.val) :
    (copyBlk x₀ x₁ x₂ x₃).denote W = enc x := by
  refine bindK_denote _ _ _ _ fun r₁ c₀ W₁ h₁ hc₀ => ?_
  refine bindK_denote _ _ _ _ fun r₂ c₁ W₂ h₂ hc₁ => ?_
  refine bindK_denote _ _ _ _ fun r₃ c₂ W₃ h₃ hc₂ => ?_
  refine bindK_denote _ _ _ _ fun r₄ c₃ W₄ h₄ hc₃ => ?_
  rw [ret4_denote _ _ W₄ rfl, enc, ← hx]
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

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
