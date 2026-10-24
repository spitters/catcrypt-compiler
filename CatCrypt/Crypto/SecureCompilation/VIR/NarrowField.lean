/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact

/-!
# Single-word modular multiplication blocks

Three `jasminDialect` blocks for `a · b mod p` on `w`-bit words, read unsigned: the
Montgomery multiply at radix `2 ^ w` with products at `2 w` bits, the Barrett multiply with
products at `2 w` bits, and the Plantard multiply with its low product at `4 w` bits and
its high step at `2 w` bits. Each block lies in the exact fragment of `ComRangeExact`: the
residues modulo `2 ^ w` and `2 ^ (2 w)` are `and` masks, so no binding wraps.

Each block has an algebraic theorem over its integer semantics `Com.denoteZ`, proved once
for every `w` and `p`, and a word theorem that combines it with
`denote_eq_denoteZ_of_boundsOk`. The parameters of one modulus form a `WordField w p`; its
side conditions `montOk`, `barOk`, `plantOk` are booleans holding the arithmetic
conditions and the bounds certificate `boundsOk` of the block, so an instance discharges
them by `decide +kernel`. The representation is relational: a word represents a field
element under a bound (`Rep`), and the output bound need not be canonical.

The signed Montgomery multiply `smontW` of `NegacyclicNttWordSigned` sign-extends by
`castW` of a possibly negative word and forms its quotient by a wrapping `w`-bit product,
so it lies outside the exact fragment; the Montgomery block here is the unsigned form.

## Main definitions

* `montBlk`, `barBlk`, `plantBlk`: the three blocks.
* `montZ`, `barZ`, `plantZ`: their integer semantics.
* `WordField`, `Rep`: the parameter record of a modulus and the representation relation.
* `WordField.montOk`, `WordField.barOk`, `WordField.plantOk`: the decidable side
  conditions.
* `mlkemField`, `mldsaField`, `babyBearField`: the instances at `q = 3329` (16-bit),
  `q = 8380417` (32-bit) and `p = 2 ^ 31 − 2 ^ 27 + 1` (32-bit).

## Main results

* `montZ_mul`, `barZ_cast`, `plantZ_mul`: the algebraic theorems.
* `run2_eq_denoteZ`: a two-input block under its bounds check computes its integer
  semantics.
* `WordField.mulMont_rep`: the Montgomery output `z` satisfies `z · 2 ^ w = u · v`.
* `WordField.mulBar_rep`: the Barrett output represents `u · v`.
* `WordField.mulPlant_rep`: the Plantard output `z` satisfies `z · 2 ^ (2 w) = −(u · v)`,
  with bound `p`.
* `mlkemField_montOk`, …, `babyBearField_plantOk`: the nine instance certificates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate (constE binE castE shrE Rw)

/-- The two-input context of `w`-bit words; `.here` is the first operand. -/
abbrev C2 (w : ℕ) : JCtxt := [Rw w, Rw w]

/-- The unsigned Montgomery multiply at radix `2 ^ w`, products at `2 w` bits:
`t = a · b`, `m = ((t mod 2 ^ w) · nq) mod 2 ^ w`, result `(t + m · p) / 2 ^ w`. -/
def montBlk (w p nq : ℕ) : Com jasminDialect (C2 w) (.reg w) :=
  .var (castE w (2 * w) .here) <|
  .var (castE w (2 * w) (.there (.there .here))) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (constE (2 * w) (2 ^ w - 1)) <|
  .var (binE .and (2 * w) (.there .here) .here) <|
  .var (constE (2 * w) nq) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (binE .and (2 * w) .here (.there (.there (.there .here)))) <|
  .var (constE (2 * w) p) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (binE .add (2 * w)
    (.there (.there (.there (.there (.there (.there (.there .here))))))) .here) <|
  .var (shrE (2 * w) w .here) <|
  .var (castE (2 * w) w .here) <|
  .ret .here

/-- The Barrett multiply, products at `2 w` bits: `t = a · b`, result
`t − ⌊⌊t / 2 ^ s⌋ · m / 2 ^ k⌋ · p`. -/
def barBlk (w p s k m : ℕ) : Com jasminDialect (C2 w) (.reg w) :=
  .var (castE w (2 * w) .here) <|
  .var (castE w (2 * w) (.there (.there .here))) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (shrE (2 * w) s .here) <|
  .var (constE (2 * w) m) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (shrE (2 * w) k .here) <|
  .var (constE (2 * w) p) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (binE .sub (2 * w) (.there (.there (.there (.there (.there (.there .here)))))) .here) <|
  .var (castE (2 * w) w .here) <|
  .ret .here

/-- The Plantard multiply, the low product at `4 w` bits and the high step at `2 w` bits:
`c = (a · b · pinv) mod 2 ^ (2 w)`, result `(⌊c / 2 ^ w⌋ + 1) · p / 2 ^ w`. -/
def plantBlk (w p pinv : ℕ) : Com jasminDialect (C2 w) (.reg w) :=
  .var (castE w (4 * w) .here) <|
  .var (castE w (4 * w) (.there (.there .here))) <|
  .var (binE .mul (4 * w) (.there .here) .here) <|
  .var (constE (4 * w) pinv) <|
  .var (binE .mul (4 * w) (.there .here) .here) <|
  .var (constE (4 * w) (2 ^ (2 * w) - 1)) <|
  .var (binE .and (4 * w) (.there .here) .here) <|
  .var (shrE (4 * w) w .here) <|
  .var (castE (4 * w) (2 * w) .here) <|
  .var (constE (2 * w) 1) <|
  .var (binE .add (2 * w) (.there .here) .here) <|
  .var (constE (2 * w) p) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (shrE (2 * w) w .here) <|
  .var (castE (2 * w) w .here) <|
  .ret .here

/-! ## 2. Integer semantics and the algebraic theorems -/

/-- The integer value of the constant `n` in a `W`-bit word. -/
def cW (W n : ℕ) : ℤ := ((n % 2 ^ W : ℕ) : ℤ)

theorem cW_of_lt {W n : ℕ} (h : n < 2 ^ W) : cW W n = n := by
  rw [cW, Nat.mod_eq_of_lt h]

theorem cW_mask {W k : ℕ} (h : 2 ^ k - 1 < 2 ^ W) : cW W (2 ^ k - 1) = 2 ^ k - 1 := by
  rw [cW_of_lt h]
  have := Nat.one_le_two_pow (n := k)
  push_cast [Nat.cast_sub this]
  rfl

/-- The integer semantics of `montBlk`. -/
def montZ (w p nq : ℕ) (a b : ℤ) : ℤ :=
  (a * b + andZ (andZ (a * b) (cW (2 * w) (2 ^ w - 1)) * cW (2 * w) nq)
    (cW (2 * w) (2 ^ w - 1)) * cW (2 * w) p) / 2 ^ w

theorem montBlk_denoteZ (w p nq : ℕ) (a b : ℤ) :
    (montBlk w p nq).denoteZ (.cons a (.cons b .nil)) = montZ w p nq a b := rfl

/-- The integer semantics of `barBlk`. -/
def barZ (w p s k m : ℕ) (a b : ℤ) : ℤ :=
  a * b - a * b / 2 ^ s * cW (2 * w) m / 2 ^ k * cW (2 * w) p

theorem barBlk_denoteZ (w p s k m : ℕ) (a b : ℤ) :
    (barBlk w p s k m).denoteZ (.cons a (.cons b .nil)) = barZ w p s k m a b := rfl

/-- The integer semantics of `plantBlk`. -/
def plantZ (w p pinv : ℕ) (a b : ℤ) : ℤ :=
  (andZ (a * b * cW (4 * w) pinv) (cW (4 * w) (2 ^ (2 * w) - 1)) / 2 ^ w + cW (2 * w) 1)
    * cW (2 * w) p / 2 ^ w

theorem plantBlk_denoteZ (w p pinv : ℕ) (a b : ℤ) :
    (plantBlk w p pinv).denoteZ (.cons a (.cons b .nil)) = plantZ w p pinv a b := rfl

/-- **Montgomery.** With `p · nq ≡ −1 (mod 2 ^ w)` the Montgomery multiply of nonnegative
operands times `2 ^ w` is `a · b + m · p`. -/
theorem montZ_mul (w p nq : ℕ) (hnq : (p * nq + 1) % 2 ^ w = 0) (hnl : nq < 2 ^ (2 * w))
    (hp : p < 2 ^ (2 * w)) {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    montZ w p nq a b * 2 ^ w = a * b + a * b % 2 ^ w * nq % 2 ^ w * p := by
  have hR : (0 : ℤ) < 2 ^ w := by positivity
  have hmask : 2 ^ w - 1 < 2 ^ (2 * w) := by
    have : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  unfold montZ
  rw [cW_mask hmask, cW_of_lt hnl, cW_of_lt hp, andZ_mask hab,
    andZ_mask (mul_nonneg (Int.emod_nonneg _ hR.ne') (Int.natCast_nonneg _))]
  apply Int.ediv_mul_cancel
  have h1 : a * b % 2 ^ w * nq % 2 ^ w ≡ a * b * nq [ZMOD 2 ^ w] :=
    (Int.mod_modEq _ _).trans ((Int.mod_modEq _ _).mul_right _)
  have h2 : (2 : ℤ) ^ w ∣ (p * nq + 1 : ℕ) := by
    have := Nat.dvd_of_mod_eq_zero hnq
    exact_mod_cast this
  have h3 : a * b + a * b % 2 ^ w * nq % 2 ^ w * p ≡ a * b * ((p * nq + 1 : ℕ) : ℤ)
      [ZMOD 2 ^ w] := by
    have := (Int.ModEq.refl (a * b)).add (h1.mul_right (p : ℤ))
    have e : a * b + a * b * nq * p = a * b * ((p * nq + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [e] at this
  have := dvd_add (Int.ModEq.dvd h3.symm) (dvd_mul_of_dvd_right h2 (a * b))
  simpa using this

/-- **Barrett.** The Barrett multiply is congruent to `a · b` modulo `p`. -/
theorem barZ_cast (w p s k m : ℕ) (hp : p < 2 ^ (2 * w)) (a b : ℤ) :
    ((barZ w p s k m a b : ℤ) : ZMod p) = (a : ZMod p) * b := by
  unfold barZ
  rw [cW_of_lt hp]
  push_cast
  simp

/-- **Plantard.** With `p · pinv ≡ 1 (mod 2 ^ (2 w))` and `0 ≤ a · b`,
`a · b + 2 ^ w · p < 2 ^ (2 w)`, the Plantard multiply times `2 ^ (2 w)` is `c · p − a · b`
for `c = (a · b · pinv) mod 2 ^ (2 w)`. -/
theorem plantZ_mul (w p pinv : ℕ) (hpi : (p * pinv) % 2 ^ (2 * w) = 1)
    (hpl : pinv < 2 ^ (4 * w)) (hp : p < 2 ^ (2 * w)) (hw : 0 < w) {a b : ℤ}
    (hab : 0 ≤ a * b) (hlt : a * b + 2 ^ w * p < 2 ^ (2 * w)) :
    plantZ w p pinv a b * 2 ^ (2 * w) = a * b * pinv % 2 ^ (2 * w) * p - a * b := by
  have hmask : 2 ^ (2 * w) - 1 < 2 ^ (4 * w) := by
    have : 2 ^ (2 * w) ≤ 2 ^ (4 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : 1 < 2 ^ (2 * w) := Nat.one_lt_two_pow (by omega)
  have hR : (0 : ℤ) < 2 ^ w := by positivity
  have hRR : (2 : ℤ) ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  unfold plantZ
  rw [cW_mask hmask, cW_of_lt hpl, cW_of_lt hp, cW_of_lt h1,
    andZ_mask (mul_nonneg hab (Int.natCast_nonneg _))]
  set X := a * b
  set c := X * pinv % 2 ^ (2 * w) with hc
  -- `c · p = X + j · 2 ^ (2 w)`
  have hcong : c * p ≡ X [ZMOD 2 ^ (2 * w)] := by
    have e1 : c * p ≡ X * pinv * p [ZMOD 2 ^ (2 * w)] := (Int.mod_modEq _ _).mul_right _
    refine e1.trans ?_
    have e2 : ((p : ℤ) * pinv) ≡ 1 [ZMOD 2 ^ (2 * w)] := by
      unfold Int.ModEq
      rw [Int.emod_eq_of_lt zero_le_one (by exact_mod_cast h1)]
      exact_mod_cast hpi
    have e3 := (Int.ModEq.refl X).mul e2
    rw [mul_one] at e3
    rw [show X * pinv * p = X * (p * pinv) by ring]
    exact e3
  obtain ⟨j, hj⟩ := (Int.ModEq.dvd hcong.symm)
  -- `c = h · 2 ^ w + l`
  have hl0 : 0 ≤ c % 2 ^ w := Int.emod_nonneg _ hR.ne'
  have hl1 : c % 2 ^ w < 2 ^ w := Int.emod_lt_of_pos _ hR
  have hdec : c = c / 2 ^ w * 2 ^ w + c % 2 ^ w := (Int.ediv_mul_add_emod c (2 ^ w)).symm
  have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  have key : (c / 2 ^ w + 1) * p * 2 ^ w
      = X + j * 2 ^ (2 * w) + (2 ^ w - c % 2 ^ w) * p := by
    linear_combination (-(p : ℤ)) * hdec + hj
  have hq : (c / 2 ^ w + 1) * (p : ℤ) / 2 ^ w = j := by
    rw [hRR] at key hlt
    have hA := mul_nonneg (show (0 : ℤ) ≤ 2 ^ w - c % 2 ^ w by linarith) hp0
    have hB := mul_nonneg hl0 hp0
    rw [Int.ediv_eq_iff_of_pos hR]
    constructor
    · exact le_of_mul_le_mul_right (by linarith) hR
    · exact lt_of_mul_lt_mul_right (by linarith) hR.le
  rw [Nat.cast_one, hq]
  linear_combination -hj

/-! ## 3. The parameter record and the word theorems -/

/-- The parameters of single-word multiplication modulo `p` in `w`-bit words: the input
bound, and for each method its constants and output bound. The arithmetic side conditions
and the bounds certificates are the decidable conditions `montOk`, `barOk`, `plantOk`. -/
structure WordField (w p : ℕ) where
  /-- Every input word is at most `inMax`. -/
  inMax : ℕ
  /-- The Montgomery constant `−p⁻¹ mod 2 ^ w`. -/
  montInv : ℕ
  /-- The bound of a Montgomery output. -/
  montOut : ℕ
  /-- The first Barrett shift. -/
  barS : ℕ
  /-- The second Barrett shift. -/
  barT : ℕ
  /-- The Barrett multiplier, `⌊2 ^ (barS + barT) / p⌋`. -/
  barM : ℕ
  /-- The bound of a Barrett output. -/
  barOut : ℕ
  /-- The Plantard constant `p⁻¹ mod 2 ^ (2 w)`. -/
  plantInv : ℕ

/-- A word represents the field element `v` with bound `B`: its value is at most `B` and
is congruent to `v` modulo `p`. -/
def Rep (p : ℕ) {w : ℕ} (B : ℕ) (x : BitVec w) (v : ZMod p) : Prop :=
  x.toNat ≤ B ∧ (x.toNat : ZMod p) = v

/-- The two input intervals `[0, n]`. -/
def ivs2 (w n : ℕ) : HVector (fun _ => Iv) (C2 w) := .cons (0, n) (.cons (0, n) .nil)

/-- The output of a two-input block on the words `x`, `y`. -/
def run2 {w : ℕ} (c : Com jasminDialect (C2 w) (.reg w)) (x y : BitVec w) : BitVec w :=
  c.denote (.cons x (.cons y .nil))

/-- Under the bounds check from `[0, B]` to `[0, out]`, the output of a two-input block on
words at most `B` is its integer semantics and is at most `out`. -/
theorem run2_eq_denoteZ {w B out : ℕ} {c : Com jasminDialect (C2 w) (.reg w)}
    (hb : boundsOk false (ivs2 w B) c (0, out) = true) (x y : BitVec w) (hx : x.toNat ≤ B)
    (hy : y.toNat ≤ B) :
    ((run2 c x y).toNat : ℤ) = c.denoteZ (.cons (x.toNat : ℤ) (.cons (y.toNat : ℤ) .nil)) ∧
      (run2 c x y).toNat ≤ out := by
  have hV : ValsIn false (ivs2 w B) (.cons x (.cons y .nil) : Valuation (C2 w)) :=
    ⟨⟨by simp [rd], by simp [rd]; omega⟩, ⟨by simp [rd], by simp [rd]; omega⟩, trivial⟩
  obtain ⟨h1, -, h3⟩ := denote_eq_denoteZ_of_boundsOk false _ c _ hb _ hV
  refine ⟨h1, ?_⟩
  simp only [rd, Bool.false_eq_true, ite_false] at h3
  exact_mod_cast h3

/-- The side condition of the Montgomery block: `p · montInv ≡ −1 (mod 2 ^ w)`, the
constants fit `2 w` bits, and the bounds check from `[0, inMax]` to `[0, montOut]`. -/
def WordField.montOk {w p : ℕ} (F : WordField w p) : Bool :=
  decide ((p * F.montInv + 1) % 2 ^ w = 0 ∧ F.montInv < 2 ^ (2 * w) ∧ p < 2 ^ (2 * w)) &&
    boundsOk false (ivs2 w F.inMax) (montBlk w p F.montInv) (0, F.montOut)

/-- The side condition of the Barrett block: `p` fits `2 w` bits, and the bounds check from
`[0, inMax]` to `[0, barOut]`. -/
def WordField.barOk {w p : ℕ} (F : WordField w p) : Bool :=
  decide (p < 2 ^ (2 * w)) &&
    boundsOk false (ivs2 w F.inMax) (barBlk w p F.barS F.barT F.barM) (0, F.barOut)

/-- The side condition of the Plantard block: `p · plantInv ≡ 1 (mod 2 ^ (2 w))`, the
constants fit, `inMax ^ 2 + 2 ^ w · p < 2 ^ (2 w)`, and the bounds check from `[0, inMax]`
to `[0, p]`. -/
def WordField.plantOk {w p : ℕ} (F : WordField w p) : Bool :=
  decide ((p * F.plantInv) % 2 ^ (2 * w) = 1 ∧ F.plantInv < 2 ^ (4 * w) ∧ p < 2 ^ (2 * w) ∧
      0 < w ∧ F.inMax * F.inMax + 2 ^ w * p < 2 ^ (2 * w)) &&
    boundsOk false (ivs2 w F.inMax) (plantBlk w p F.plantInv) (0, p)

/-- The Montgomery multiply of `F` on words. -/
def WordField.mulMont {w p : ℕ} (F : WordField w p) (x y : BitVec w) : BitVec w :=
  run2 (montBlk w p F.montInv) x y

/-- The Barrett multiply of `F` on words. -/
def WordField.mulBar {w p : ℕ} (F : WordField w p) (x y : BitVec w) : BitVec w :=
  run2 (barBlk w p F.barS F.barT F.barM) x y

/-- The Plantard multiply of `F` on words. -/
def WordField.mulPlant {w p : ℕ} (F : WordField w p) (x y : BitVec w) : BitVec w :=
  run2 (plantBlk w p F.plantInv) x y

/-- **The Montgomery block.** On words representing `u`, `v` with bound `inMax`, the
output represents an element `z` with `z · 2 ^ w = u · v`, with bound `montOut`. -/
theorem WordField.mulMont_rep {w p : ℕ} (F : WordField w p) (h : F.montOk = true)
    {x y : BitVec w} {u v : ZMod p} (hx : Rep p F.inMax x u) (hy : Rep p F.inMax y v) :
    Rep p F.montOut (F.mulMont x y) ((F.mulMont x y).toNat : ZMod p) ∧
      ((F.mulMont x y).toNat : ZMod p) * 2 ^ w = u * v := by
  simp only [montOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2, h3⟩, hb⟩ := h
  obtain ⟨e, hle⟩ := run2_eq_denoteZ hb x y hx.1 hy.1
  refine ⟨⟨hle, rfl⟩, ?_⟩
  rw [← hx.2, ← hy.2]
  have key := montZ_mul w p F.montInv h1 h2 h3 (Int.natCast_nonneg x.toNat)
    (Int.natCast_nonneg y.toNat)
  rw [montBlk_denoteZ] at e
  rw [← e] at key
  have := congrArg (fun z : ℤ => (z : ZMod p)) key
  push_cast at this
  simpa [WordField.mulMont] using this

/-- **The Barrett block.** On words representing `u`, `v` with bound `inMax`, the output
represents `u · v` with bound `barOut`. -/
theorem WordField.mulBar_rep {w p : ℕ} (F : WordField w p) (h : F.barOk = true)
    {x y : BitVec w} {u v : ZMod p} (hx : Rep p F.inMax x u) (hy : Rep p F.inMax y v) :
    Rep p F.barOut (F.mulBar x y) (u * v) := by
  simp only [barOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, hb⟩ := h
  obtain ⟨e, hle⟩ := run2_eq_denoteZ hb x y hx.1 hy.1
  refine ⟨hle, ?_⟩
  rw [← hx.2, ← hy.2]
  rw [barBlk_denoteZ] at e
  have := barZ_cast w p F.barS F.barT F.barM h1 x.toNat y.toNat
  rw [← e] at this
  exact_mod_cast this

/-- **The Plantard block.** On words representing `u`, `v` with bound `inMax`, the output
represents an element `z` with `z · 2 ^ (2 w) = −(u · v)`, with bound `p`. -/
theorem WordField.mulPlant_rep {w p : ℕ} (F : WordField w p) (h : F.plantOk = true)
    {x y : BitVec w} {u v : ZMod p} (hx : Rep p F.inMax x u) (hy : Rep p F.inMax y v) :
    Rep p p (F.mulPlant x y) ((F.mulPlant x y).toNat : ZMod p) ∧
      ((F.mulPlant x y).toNat : ZMod p) * 2 ^ (2 * w) = -(u * v) := by
  simp only [plantOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, hb⟩ := h
  obtain ⟨e, hle⟩ := run2_eq_denoteZ hb x y hx.1 hy.1
  refine ⟨⟨hle, rfl⟩, ?_⟩
  rw [← hx.2, ← hy.2]
  have hxy : x.toNat * y.toNat + 2 ^ w * p < 2 ^ (2 * w) :=
    lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul hx.1 hy.1) _) h5
  have key := plantZ_mul w p F.plantInv h1 h2 h3 h4
    (mul_nonneg (Int.natCast_nonneg x.toNat) (Int.natCast_nonneg y.toNat))
    (by exact_mod_cast hxy)
  rw [plantBlk_denoteZ] at e
  rw [← e] at key
  have := congrArg (fun z : ℤ => (z : ZMod p)) key
  push_cast at this
  simpa [WordField.mulPlant] using this

/-! ## 4. Instances

The constants of each instance: `montInv = −p⁻¹ mod 2 ^ w`, `plantInv = p⁻¹ mod 2 ^ (2 w)`,
and the Barrett shifts with the least Barrett output bound over inputs below `p`. Each
output bound is the one the range analysis computes. -/

/-- ML-KEM, `q = 3329` in 16-bit words. -/
def mlkemField : WordField 16 3329 :=
  ⟨3328, 3327, 3497, 8, 20, 80635, 3648, 1806234369⟩

/-- ML-DSA, `q = 8380417` in 32-bit words. -/
def mldsaField : WordField 32 8380417 :=
  ⟨8380416, 4236238847, 8396769, 14, 41, 4299165187, 8396841, 1732267787797143553⟩

/-- BabyBear, `p = 2 ^ 31 − 2 ^ 27 + 1` in 32-bit words. -/
def babyBearField : WordField 32 2013265921 :=
  ⟨2013265920, 2013265919, 2956984320, 29, 33, 2290649223, 3250061314,
    4053239662620180481⟩

theorem mlkemField_montOk : mlkemField.montOk = true := by decide +kernel
theorem mlkemField_barOk : mlkemField.barOk = true := by decide +kernel
theorem mlkemField_plantOk : mlkemField.plantOk = true := by decide +kernel
theorem mldsaField_montOk : mldsaField.montOk = true := by decide +kernel
theorem mldsaField_barOk : mldsaField.barOk = true := by decide +kernel
theorem mldsaField_plantOk : mldsaField.plantOk = true := by decide +kernel
theorem babyBearField_montOk : babyBearField.montOk = true := by decide +kernel
theorem babyBearField_barOk : babyBearField.barOk = true := by decide +kernel
theorem babyBearField_plantOk : babyBearField.plantOk = true := by decide +kernel

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowField
