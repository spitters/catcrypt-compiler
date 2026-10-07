/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
public import CatCrypt.Crypto.SecureCompilation.VIR.RoundCodecDefs

/-!
# Rounding and codec functions of ML-KEM and ML-DSA as bounded word templates

Straight-line `Com jasminDialect` templates for ML-KEM `Compress_d`/`Decompress_d` and
ML-DSA `Power2Round`, `Decompose`, `MakeHint` and `UseHint`, each stated over the exact
integer semantics `MultiReturnCom.denoteZ` of `ComRangeExact` and packaged as a
`BoundedBlock` whose side condition `boundsOkMR` is decided by the kernel.

A division by a constant `q` is a multiply by a constant and a shift. Its exactness is one
generic statement, `mulShift_eq_div`: `⌊(n·m + b)/2^k⌋ = ⌊(n + c)/q⌋` for `n ≤ N` under the
decidable condition `MulShiftOk q m k b c N`, which bounds an affine function of the
quotient at its two end points. Each instance discharges it by `decide`. A comparison
`[x ≥ c]` is the arithmetic shift `(x + 2^j - c) >> j`, and a selection is a multiply by
that bit, so every template is branch-free and stays in the exact fragment.

The FIPS 203 functions are restated here as `compressSpec` and `decompressSpec`, with the
formulas of the specification module. The FIPS 204 functions are the definitions of
`Fips204` in `VIR.RoundCodecDefs`, which the specification module `MLDSA.Spec.Rounding`
uses as well.

## Main definitions

* `MulShiftOk`: the side condition of the multiply-shift.
* `compressProg`, `decompressProg`: the ML-KEM templates; `mlkemCompressMagic` gives the
  constants at `q = 3329`.
* `power2RoundProg`, `decomposeProg`, `makeHintProg`, `useHintProg`: the ML-DSA templates
  over the constants `DecomposeMagic`; `mldsa88` and `mldsa32` are the two instances.
* `mlkemCompressBlock`, `mlkemDecompressBlock`, `mldsaPower2RoundBlock`,
  `mldsaDecomposeBlock`, `mldsaMakeHintBlock`, `mldsaUseHintBlock`: the bounded blocks.

## Main results

* `mulShift_eq_div`: exactness of the multiply-shift under `MulShiftOk`.
* `compressZ_eq`, `decompressZ_eq`: the integer semantics of the ML-KEM templates is
  `Compress_d` and `Decompress_d`, for every `q`, `d` and admissible constants.
* `compress_denote`, `decompress_denote`: the same for the word programs under the bounds
  check; `mlkemCompress_ok` discharges the side conditions at `d ∈ {1, 4, 5, 10, 11}`.
* `power2Round_denote`, `decompose_denote`, `makeHint_denote`, `useHint_denote`: the word
  programs compute FIPS 204 `Power2Round`, `(HighBits, LowBits)`, `MakeHint` and
  `UseHint` under the bounds check, at `q = 8380417` and `γ₂ ∈ {(q-1)/88, (q-1)/32}`.
* `mlkemCompressBlock_ok`, `mlkemDecompressBlock_ok`, `mldsaPower2RoundBlock_ok`,
  `mldsaDecomposeBlock_ok`, `mldsaMakeHintBlock_mldsa88_ok` and the other `MakeHint`,
  `UseHint` instances: every instance passes its bounds check, by `decide +kernel`.
* `decomposeProg_Q`, `makeHintProg_Q`, `useHintProg_Q`: the integer semantics of the
  ML-DSA programs, evaluated one combinator at a time through `hbK_Q` and `decK_Q`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (hget JCtxt)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact

/-! ## 1. Exactness of a multiply-shift -/

/-- The side condition of `mulShift_eq_div`, decided on `ℕ`. With `A = ⌊(N + c) / q⌋` it
    states, at `a = 0` and at `a = A`, the bounds `c·m + a·2^k ≤ b + a·m·q` and
    `q·m + b + a·m·q < 2^k + c·m + m + a·2^k`. -/
def MulShiftOk (q m k b c N : ℕ) : Bool :=
  decide (c * m ≤ b) &&
    decide (c * m + (N + c) / q * 2 ^ k ≤ b + (N + c) / q * m * q) &&
    decide (q * m + b < 2 ^ k + c * m + m) &&
    decide (q * m + b + (N + c) / q * m * q < 2 ^ k + c * m + m + (N + c) / q * 2 ^ k)

/-- An affine function nonnegative at `0` and at `A` is nonnegative on `[0, A]`. -/
theorem affine_nonneg {α β a A : ℤ} (h0 : 0 ≤ α) (hA : 0 ≤ α + β * A) (ha : 0 ≤ a)
    (haA : a ≤ A) : 0 ≤ α + β * a := by
  have key : A * (α + β * a) = (A - a) * α + a * (α + β * A) := by ring
  have hnn : 0 ≤ A * (α + β * a) := by
    rw [key]
    exact add_nonneg (mul_nonneg (by linarith) h0) (mul_nonneg ha hA)
  rcases eq_or_lt_of_le (ha.trans haA) with hA0 | hA0
  · have : a = 0 := by omega
    subst this
    simpa using h0
  · exact nonneg_of_mul_nonneg_right (by linarith) hA0

/-- **Exactness of a multiply-shift.** Under the decidable side condition `MulShiftOk`,
    `⌊(n·m + b) / 2^k⌋ = ⌊(n + c) / q⌋` for every `n ≤ N`. -/
theorem mulShift_eq_div {q m k b c N : ℕ} (h : MulShiftOk q m k b c N = true) (hq : 0 < q)
    {n : ℕ} (hn : n ≤ N) : (n * m + b) / 2 ^ k = (n + c) / q := by
  simp only [MulShiftOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hdm := Nat.div_add_mod (n + c) q
  have hr := Nat.mod_lt (n + c) hq
  have haA : (n + c) / q ≤ (N + c) / q := Nat.div_le_div_right (by omega)
  generalize (N + c) / q = A at h2 h4 haA
  generalize (n + c) / q = a at hdm haA ⊢
  generalize (n + c) % q = r at hdm hr
  generalize hP : 2 ^ k = P at h2 h3 h4 ⊢
  apply Nat.div_eq_of_lt_le
  · zify at h1 h2 hdm haA ⊢
    have hL := affine_nonneg (α := (b : ℤ) - c * m) (β := (m : ℤ) * q - P) (a := a) (A := A)
      (by linarith) (by linarith) (by positivity) haA
    have e : ((n : ℤ) + c) * m = (q * a + r) * m := by rw [hdm]
    nlinarith [mul_nonneg (Int.natCast_nonneg r) (Int.natCast_nonneg m)]
  · zify at h3 h4 hdm haA hr ⊢
    have hU := affine_nonneg (α := (P : ℤ) + c * m + m - q * m - b - 1)
      (β := (P : ℤ) - m * q) (a := a) (A := A) (by linarith) (by linarith) (by positivity) haA
    have e : ((n : ℤ) + c) * m = (q * a + r) * m := by rw [hdm]
    have hrm : (r : ℤ) * m ≤ (q - 1) * m :=
      mul_le_mul_of_nonneg_right (by linarith) (Int.natCast_nonneg m)
    nlinarith

/-- `mulShift_eq_div` over `ℤ`, for `0 ≤ n ≤ N`. -/
theorem mulShift_eq_divZ {q m k b c N : ℕ} (h : MulShiftOk q m k b c N = true) (hq : 0 < q)
    {n : ℤ} (h0 : 0 ≤ n) (hn : n ≤ N) :
    (n * m + b) / 2 ^ k = (n + c) / (q : ℤ) := by
  lift n to ℕ using h0
  have := mulShift_eq_div h hq (n := n) (by exact_mod_cast hn)
  exact_mod_cast this

/-! ## 2. Expressions and continuation-passing combinators -/

section Combinators

variable {Γ : JCtxt} {ts : List JasminTy}

/-- The expression `regArith op w` on `a`, `b`. -/
def eAr (op : JasminBinOp) (w : ℕ) (a b : Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w) :=
  { op := .regArith op w, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The expression `regConst w n`. -/
def eK (w n : ℕ) : Expr jasminDialect Γ (.reg w) :=
  { op := .regConst w n, retTy_eq := rfl, args := .nil }

/-- The expression `shrImm w n` on `a`. -/
def eShr (w n : ℕ) (a : Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w) :=
  { op := .shrImm w n, retTy_eq := rfl, args := .cons a .nil }

/-- The expression `shlImm w n` on `a`. -/
def eShl (w n : ℕ) (a : Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w) :=
  { op := .shlImm w n, retTy_eq := rfl, args := .cons a .nil }

/-- The expression `sarImm w n` on `a`. -/
def eSar (w n : ℕ) (a : Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w) :=
  { op := .sarImm w n, retTy_eq := rfl, args := .cons a .nil }

/-- A multi-return `jasminDialect` program. -/
abbrev MC (Γ : JCtxt) (ts : List JasminTy) : Type := MultiReturnCom jasminDialect Γ ts

/-- A continuation receiving a weakening of `Γ` and a `w`-bit variable. -/
abbrev Kont (Γ : JCtxt) (w : ℕ) (ts : List JasminTy) : Type :=
  ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ (.reg w) → MC Δ ts

/-- A continuation receiving a weakening of `Γ` and two `w`-bit variables. -/
abbrev Kont2 (Γ : JCtxt) (w : ℕ) (ts : List JasminTy) : Type :=
  ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ (.reg w) → Var Δ (.reg w) → MC Δ ts

/-- Bind `e` and pass the weakening and the bound variable to `k`. -/
def bindE {w : ℕ} (e : Expr jasminDialect Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts :=
  .var e (k (fun v => v.there) .here)

/-- `a op b`. -/
def arK (op : JasminBinOp) (w : ℕ) (a b : Var Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts :=
  bindE (eAr op w a b) k

/-- `a op n` for the constant `n`. -/
def arCK (op : JasminBinOp) (w : ℕ) (a : Var Γ (.reg w)) (n : ℕ) (k : Kont Γ w ts) :
    MC Γ ts :=
  bindE (eK w n) fun r c => arK op w (r a) c fun r' y => k (fun v => r' (r v)) y

/-- `a >> n`. -/
def shrK (w n : ℕ) (a : Var Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts := bindE (eShr w n a) k

/-- `a << n`. -/
def shlK (w n : ℕ) (a : Var Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts := bindE (eShl w n a) k

/-- `a >> n`, arithmetic. -/
def sarK (w n : ℕ) (a : Var Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts := bindE (eSar w n a) k

/-- The comparison bit `[x ≥ c]` as `(x + (2^j - c)) >> j`, arithmetic. -/
def geK (w c j : ℕ) (x : Var Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts :=
  arCK .add w x (2 ^ j - c) fun r y => sarK w j y fun r' z => k (fun v => r' (r v)) z

/-- `⌊(x·m + b) / 2^s⌋`, by a logical shift. -/
def mulAddShrK (w m b s : ℕ) (x : Var Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts :=
  arCK .mul w x m fun r1 y => arCK .add w y b fun r2 u => shrK w s u fun r3 z =>
    k (fun v => r3 (r2 (r1 v))) z

/-- `⌊(x·m + b) / 2^s⌋`, by an arithmetic shift. -/
def mulAddSarK (w m b s : ℕ) (x : Var Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts :=
  arCK .mul w x m fun r1 y => arCK .add w y b fun r2 u => sarK w s u fun r3 z =>
    k (fun v => r3 (r2 (r1 v))) z

/-- `a - bit·M`. -/
def subMulK (w M : ℕ) (a bit : Var Γ (.reg w)) (k : Kont Γ w ts) : MC Γ ts :=
  arCK .mul w bit M fun r1 t => arK .sub w (r1 a) t fun r2 z => k (fun v => r2 (r1 v)) z

end Combinators

/-- The integer value of the `w`-bit constant `n`. -/
def cZ (w n : ℕ) : ℤ := ((n % 2 ^ w : ℕ) : ℤ)

theorem cZ_of_lt {w n : ℕ} (h : n < 2 ^ w) : cZ w n = n := by
  simp [cZ, Nat.mod_eq_of_lt h]

/-- The integer semantics of `geK`. -/
def geZ (w c j : ℕ) (x : ℤ) : ℤ := (x + cZ w (2 ^ j - c)) / 2 ^ j

/-- The integer semantics of `mulAddShrK`. -/
def mulAddShrZ (w m b s : ℕ) (x : ℤ) : ℤ := (x * cZ w m + cZ w b) / 2 ^ s

/-- The integer semantics of `subMulK`. -/
def subMulZ (w M : ℕ) (a bit : ℤ) : ℤ := a - bit * cZ w M

/-! ### Integer semantics of the combinators

A combinator's lemma states that its program satisfies `Q` whenever its continuation does
at the value of the bound variable (`KQ`), under a renaming that keeps every value
(`PresZ`). A program is then evaluated one combinator at a time. -/

section CombinatorZ

variable {Γ : JCtxt} {ts : List JasminTy}

/-- The renaming `r` carries the integer values `Z` to `Z'`. -/
abbrev PresZ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (Z : ZVec Γ) (Z' : ZVec Δ) : Prop :=
  ∀ {t : JasminTy} (v : Var Γ t), hget Z' (r v) = hget Z v

/-- The continuation `k` satisfies `Q` whenever its variable has the value `val`. -/
abbrev KQ {w : ℕ} (Z : ZVec Γ) (val : ℤ) (Q : ZVec ts → Prop) (k : Kont Γ w ts) : Prop :=
  ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (y : Var Δ (.reg w)) (Z' : ZVec Δ), PresZ r Z Z' →
    hget Z' y = val → Q ((k r y).denoteZ Z')

/-- The continuation `k` satisfies `Q` whenever its variables have the values `v1`, `v2`. -/
abbrev KQ2 {w : ℕ} (Z : ZVec Γ) (v1 v2 : ℤ) (Q : ZVec ts → Prop) (k : Kont2 Γ w ts) : Prop :=
  ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (y1 y2 : Var Δ (.reg w)) (Z' : ZVec Δ), PresZ r Z Z' →
    hget Z' y1 = v1 → hget Z' y2 = v2 → Q ((k r y1 y2).denoteZ Z')

theorem bindE_Q {w : ℕ} {e : Expr jasminDialect Γ (.reg w)} {k : Kont Γ w ts} {Z : ZVec Γ}
    (Q : ZVec ts → Prop) (hk : KQ Z (opZ e.op e.args Z) Q k) : Q ((bindE e k).denoteZ Z) :=
  hk _ _ _ (fun _ => rfl) rfl

theorem arK_Q {op : JasminBinOp} {w : ℕ} {a b : Var Γ (.reg w)} {k : Kont Γ w ts}
    {Z : ZVec Γ} (Q : ZVec ts → Prop) (hk : KQ Z (binZ op (hget Z a) (hget Z b)) Q k) :
    Q ((arK op w a b k).denoteZ Z) :=
  bindE_Q Q hk

theorem arCK_Q {op : JasminBinOp} {w : ℕ} {a : Var Γ (.reg w)} {n : ℕ} {k : Kont Γ w ts}
    {Z : ZVec Γ} (Q : ZVec ts → Prop) (hk : KQ Z (binZ op (hget Z a) (cZ w n)) Q k) :
    Q ((arCK op w a n k).denoteZ Z) :=
  bindE_Q Q fun _ c _ h1 hc => arK_Q Q fun _ y Z2 h2 hy =>
    hk _ y Z2 (fun v => (h2 _).trans (h1 v)) (by rw [hy, h1, hc]; rfl)

theorem shrK_Q {w n : ℕ} {a : Var Γ (.reg w)} {k : Kont Γ w ts} {Z : ZVec Γ}
    (Q : ZVec ts → Prop) (hk : KQ Z (hget Z a / 2 ^ n) Q k) : Q ((shrK w n a k).denoteZ Z) :=
  bindE_Q Q hk

theorem sarK_Q {w n : ℕ} {a : Var Γ (.reg w)} {k : Kont Γ w ts} {Z : ZVec Γ}
    (Q : ZVec ts → Prop) (hk : KQ Z (hget Z a / 2 ^ n) Q k) : Q ((sarK w n a k).denoteZ Z) :=
  bindE_Q Q hk

theorem geK_Q {w c j : ℕ} {x : Var Γ (.reg w)} {k : Kont Γ w ts} {Z : ZVec Γ}
    (Q : ZVec ts → Prop) (hk : KQ Z (geZ w c j (hget Z x)) Q k) :
    Q ((geK w c j x k).denoteZ Z) :=
  arCK_Q Q fun _ y _ h1 hy => sarK_Q Q fun _ z Z2 h2 hz =>
    hk _ z Z2 (fun v => (h2 _).trans (h1 v)) (by rw [hz, hy]; rfl)

theorem mulAddSarK_Q {w m b s : ℕ} {x : Var Γ (.reg w)} {k : Kont Γ w ts} {Z : ZVec Γ}
    (Q : ZVec ts → Prop) (hk : KQ Z (mulAddShrZ w m b s (hget Z x)) Q k) :
    Q ((mulAddSarK w m b s x k).denoteZ Z) :=
  arCK_Q Q fun _ y _ h1 hy => arCK_Q Q fun _ u _ h2 hu => sarK_Q Q fun _ z Z3 h3 hz =>
    hk _ z Z3 (fun v => (h3 _).trans ((h2 _).trans (h1 v)))
      (by rw [hz, hu, hy]; rfl)

theorem subMulK_Q {w M : ℕ} {a bit : Var Γ (.reg w)} {k : Kont Γ w ts} {Z : ZVec Γ}
    (Q : ZVec ts → Prop) (hk : KQ Z (subMulZ w M (hget Z a) (hget Z bit)) Q k) :
    Q ((subMulK w M a bit k).denoteZ Z) :=
  arCK_Q Q fun _ t _ h1 ht => arK_Q Q fun _ z Z2 h2 hz =>
    hk _ z Z2 (fun v => (h2 _).trans (h1 v)) (by rw [hz, h1, ht]; rfl)

end CombinatorZ

/-! ## 3. ML-KEM compression and decompression -/

/-- FIPS 203 `Compress_d` on `ℕ`: `⌊(2^d·x + ⌊q/2⌋) / q⌋ mod 2^d`. -/
def compressSpec (q d x : ℕ) : ℕ := (2 ^ d * x + q / 2) / q % 2 ^ d

/-- FIPS 203 `Decompress_d` on `ℕ`: `⌊(q·y + ⌊2^d/2⌋) / 2^d⌋`. -/
def decompressSpec (q d y : ℕ) : ℕ := (q * y + 2 ^ d / 2) / 2 ^ d

/-- The constants of a compression template: the word width `w`, the multiplier `m`, the
    addend `b` and the shift `s` of `⌊(2^d·x·m + b) / 2^s⌋`. -/
structure CompressMagic where
  /-- The word width. -/
  w : ℕ
  /-- The multiplier of `2^d·x`. -/
  m : ℕ
  /-- The addend. -/
  b : ℕ
  /-- The shift. -/
  s : ℕ

/-- The one-input context of `w`-bit words. -/
abbrev C1 (w : ℕ) : JCtxt := [.reg w]

/-- The two-input context of `w`-bit words. -/
abbrev C2 (w : ℕ) : JCtxt := [.reg w, .reg w]

/-- The compression template: `⌊(x·(2^d·m) + b) / 2^s⌋ and (2^d - 1)`. -/
def compressProg (d : ℕ) (P : CompressMagic) : MC (C1 P.w) [.reg P.w] :=
  mulAddShrK P.w (2 ^ d * P.m) P.b P.s .here fun _ t =>
    arCK .and P.w t (2 ^ d - 1) fun _ y => .ret (.cons y .nil)

/-- The integer semantics of `compressProg`. -/
def compressZ (d : ℕ) (P : CompressMagic) (x : ℤ) : ℤ :=
  andZ (mulAddShrZ P.w (2 ^ d * P.m) P.b P.s x) (cZ P.w (2 ^ d - 1))

theorem compressProg_denoteZ (d : ℕ) (P : CompressMagic) (x : ℤ) :
    (compressProg d P).denoteZ (.cons x .nil) = .cons (compressZ d P x) .nil := rfl

/-- The side condition of a compression template at `q`, `d`: the multiply-shift is exact
    on `[0, 2^d·(q - 1)]` with offset `⌊q/2⌋`, and the constants fit the word. -/
def CompressOk (q d : ℕ) (P : CompressMagic) : Bool :=
  MulShiftOk q P.m P.s P.b (q / 2) (2 ^ d * (q - 1)) && decide (0 < q) &&
    decide (2 ^ d * P.m < 2 ^ P.w) && decide (P.b < 2 ^ P.w) && decide (2 ^ d ≤ 2 ^ P.w)

/-- **The compression template computes `Compress_d`** on the integers, for `x < q`. -/
theorem compressZ_eq (q d : ℕ) (P : CompressMagic) (h : CompressOk q d P = true) (x : ℕ)
    (hx : x < q) : compressZ d P x = compressSpec q d x := by
  simp only [CompressOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hm, hq⟩, hM⟩, hb⟩, hd⟩ := h
  have hd1 : 2 ^ d - 1 < 2 ^ P.w := by have := Nat.one_le_two_pow (n := d); omega
  have key := mulShift_eq_div hm hq (n := 2 ^ d * x) (Nat.mul_le_mul_left _ (by omega))
  unfold compressZ mulAddShrZ
  rw [cZ_of_lt hM, cZ_of_lt hb, cZ_of_lt hd1]
  have e1 : (x : ℤ) * ((2 ^ d * P.m : ℕ) : ℤ) + (P.b : ℤ) = ((2 ^ d * x * P.m + P.b : ℕ) : ℤ) := by
    push_cast; ring
  rw [e1, show (2 : ℤ) ^ P.s = ((2 ^ P.s : ℕ) : ℤ) by push_cast; rfl, ← Int.natCast_ediv, key,
    show ((2 ^ d - 1 : ℕ) : ℤ) = 2 ^ d - 1 by
      have := Nat.one_le_two_pow (n := d); push_cast [Nat.cast_sub this]; rfl,
    andZ_mask (Int.natCast_nonneg _)]
  unfold compressSpec
  push_cast
  rfl

/-- The decompression template: `⌊(y·q + ⌊2^d/2⌋) / 2^d⌋`. -/
def decompressProg (w q d : ℕ) : MC (C1 w) [.reg w] :=
  mulAddShrK w q (2 ^ d / 2) d .here fun _ y => .ret (.cons y .nil)

theorem decompressProg_denoteZ (w q d : ℕ) (y : ℤ) :
    (decompressProg w q d).denoteZ (.cons y .nil)
      = .cons (mulAddShrZ w q (2 ^ d / 2) d y) .nil := rfl

/-- **The decompression template computes `Decompress_d`** on the integers, when `q` and
    `⌊2^d/2⌋` fit the word. -/
theorem decompressZ_eq (w q d : ℕ) (hq : q < 2 ^ w) (hd : 2 ^ d / 2 < 2 ^ w) (y : ℕ) :
    mulAddShrZ w q (2 ^ d / 2) d y = decompressSpec q d y := by
  unfold mulAddShrZ decompressSpec
  rw [cZ_of_lt hq, cZ_of_lt hd]
  push_cast
  rw [mul_comm (y : ℤ)]

/-- The one-entry interval vector. -/
abbrev iv1 {w : ℕ} (i : Iv) : HVector (fun _ => Iv) (C1 w) := .cons i .nil

theorem valsIn_iv1 {w : ℕ} (s : Bool) (i : Iv) (x : BitVec w) (h1 : i.1 ≤ rd s x)
    (h2 : rd s x ≤ i.2) : ValsIn s (iv1 i) (HVector.cons x .nil : Valuation (C1 w)) :=
  ⟨⟨h1, h2⟩, trivial⟩

/-- **The compression template computes `Compress_d` on words.** Under `CompressOk` and the
    bounds check from `[0, q - 1]` to `[0, 2^d - 1]`, the unsigned reading of the output on
    a word `x < q` is `Compress_d (x)`. -/
theorem compress_denote (q d : ℕ) (P : CompressMagic) (h : CompressOk q d P = true)
    (hb : boundsOkMR false (iv1 (0, (q : ℤ) - 1)) (compressProg d P)
      (iv1 (0, 2 ^ d - 1)) = true) (x : BitVec P.w) (hx : x.toNat < q) :
    zvals false ((compressProg d P).denote (.cons x .nil))
      = .cons (compressSpec q d x.toNat : ℤ) .nil := by
  have hV := valsIn_iv1 false (0, (q : ℤ) - 1) x (by simp [rd]) (by simp [rd]; omega)
  rw [(denoteMR_eq_denoteZ_of_boundsOk false _ _ _ hb _ hV).1]
  exact congrArg (HVector.cons · _) (compressZ_eq q d P h x.toNat hx)

/-- **The decompression template computes `Decompress_d` on words.** Under the bounds check
    from `[0, 2^d - 1]` to `[0, q - 1]`, the unsigned reading of the output is
    `Decompress_d (y)`. -/
theorem decompress_denote (w q d : ℕ) (hq : q < 2 ^ w) (hd : 2 ^ d / 2 < 2 ^ w)
    (hb : boundsOkMR false (iv1 (0, 2 ^ d - 1)) (decompressProg w q d)
      (iv1 (0, (q : ℤ) - 1)) = true) (y : BitVec w) (hy : y.toNat < 2 ^ d) :
    zvals false ((decompressProg w q d).denote (.cons y .nil))
      = .cons (decompressSpec q d y.toNat : ℤ) .nil := by
  have hV := valsIn_iv1 false (0, 2 ^ d - 1) y (by simp [rd]) (by
    simp only [rd, Bool.false_eq_true, if_false]
    have : ((y.toNat : ℕ) : ℤ) < ((2 ^ d : ℕ) : ℤ) := by exact_mod_cast hy
    push_cast at this; omega)
  rw [(denoteMR_eq_denoteZ_of_boundsOk false _ _ _ hb _ hV).1]
  exact congrArg (HVector.cons · _) (decompressZ_eq w q d hq hd y.toNat)

/-! ### ML-KEM instances at `q = 3329`

The multiplier `m`, addend `b` and shift `s` of each compression template are the least
shift at which `MulShiftOk` holds over `[0, 2^d·(q - 1)]`, with `m = ⌊2^s/q⌋` or
`⌈2^s/q⌉` and `b` the least admissible addend. -/

/-- The compression constants at `q = 3329` for `d ∈ {1, 4, 5, 10, 11}`: 32-bit words for
    `d ≤ 5`, 64-bit words for `d ∈ {10, 11}`. -/
def mlkemCompressMagic : ℕ → CompressMagic
  | 1 => ⟨32, 315, 524160, 20⟩
  | 4 => ⟨32, 20159, 33544576, 26⟩
  | 5 => ⟨32, 20159, 33544576, 26⟩
  | _ => ⟨64, 2580335, 4293677440, 33⟩

/-- The side conditions of the ML-KEM compression templates hold. -/
theorem mlkemCompress_ok : ∀ d ∈ [1, 4, 5, 10, 11],
    CompressOk 3329 d (mlkemCompressMagic d) = true := by
  decide

/-- The ML-KEM compression template at `d` as a bounded block: unsigned readings, input in
    `[0, 3328]`, output in `[0, 2^d - 1]`. -/
def mlkemCompressBlock (d : ℕ) : BoundedBlock :=
  BoundedBlock.ofBoundsOk false (iv1 (0, 3328)) (compressProg d (mlkemCompressMagic d))
    (iv1 (0, 2 ^ d - 1))

/-- The ML-KEM decompression template at `d` as a bounded block: 32-bit unsigned readings,
    input in `[0, 2^d - 1]`, output in `[0, 3328]`. -/
def mlkemDecompressBlock (d : ℕ) : BoundedBlock :=
  BoundedBlock.ofBoundsOk false (iv1 (0, 2 ^ d - 1)) (decompressProg 32 3329 d)
    (iv1 (0, 3328))

/-- The compression templates pass the bounds check from `[0, 3328]`. -/
theorem mlkemCompressBlock_ok : ∀ d ∈ [1, 4, 5, 10, 11], (mlkemCompressBlock d).ok = true := by
  decide +kernel

/-- The decompression templates pass the bounds check from `[0, 2^d - 1]`. -/
theorem mlkemDecompressBlock_ok :
    ∀ d ∈ [1, 4, 5, 10, 11], (mlkemDecompressBlock d).ok = true := by
  decide +kernel

/-! ## 4. ML-DSA rounding

The FIPS 204 functions `Fips204.power2Round`, `Fips204.decompose`, `Fips204.highBits`,
`Fips204.lowBits`, `Fips204.makeHint` and `Fips204.useHint` are defined in
`VIR.RoundCodecDefs`.

### Power2Round -/

/-- The `Power2Round` template on `w`-bit words: `r1 = (r + 2^(d-1) - 1) >> d` and
    `r0 = r - (r1 << d)`. -/
def power2RoundProg (w d : ℕ) : MC (C1 w) [.reg w, .reg w] :=
  arCK .add w .here (2 ^ (d - 1) - 1) fun r1 u => shrK w d u fun r2 h => shlK w d h fun r3 t =>
    arK .sub w (r3 (r2 (r1 .here))) t fun r4 l => .ret (.cons (r4 (r3 h)) (.cons l .nil))

/-- The integer semantics of `power2RoundProg`. -/
def power2RoundZ (w d : ℕ) (r : ℤ) : ℤ × ℤ :=
  let r1 := (r + cZ w (2 ^ (d - 1) - 1)) / 2 ^ d
  (r1, r - r1 * 2 ^ d)

theorem power2RoundProg_denoteZ (w d : ℕ) (r : ℤ) :
    (power2RoundProg w d).denoteZ (.cons r .nil)
      = .cons (power2RoundZ w d r).1 (.cons (power2RoundZ w d r).2 .nil) := rfl

/-- **The `Power2Round` template computes FIPS 204 `Power2Round`** at 32 bits, `d = 13`, for
    `0 ≤ r < q`. -/
theorem power2RoundZ_eq (r : ℤ) (h0 : 0 ≤ r) (h1 : r < Fips204.q) :
    power2RoundZ 32 13 r = Fips204.power2Round r := by
  simp only [power2RoundZ, Fips204.power2Round, Fips204.modPm, Fips204.q, Fips204.twoPowD,
    cZ] at h1 ⊢
  norm_num
  split_ifs <;> omega

/-! ### Decompose, MakeHint, UseHint -/

/-- The constants of the ML-DSA rounding templates. `Decompose` computes
    `a' = (a + 2^p - 1) >> p`, `t = (a'·m + b) >> s`, `a1 = t - M·[t ≥ M]`,
    `a0 = a - α·a1` and `a0 - q·[a0 ≥ (q + 1)/2]`; each bit `[x ≥ c]` is
    `(x + 2^j - c) >> j` with the width `j` named by a field. -/
structure DecomposeMagic where
  /-- The word width. -/
  w : ℕ
  /-- The modulus. -/
  q : ℕ
  /-- `2·γ₂`. -/
  alpha : ℕ
  /-- `(q - 1) / (2·γ₂)`. -/
  M : ℕ
  /-- The pre-shift. -/
  p : ℕ
  /-- The multiplier. -/
  m : ℕ
  /-- The addend. -/
  b : ℕ
  /-- The shift. -/
  s : ℕ
  /-- The width of the bit `[t ≥ M]`. -/
  jt : ℕ
  /-- The width of the bit `[a0 ≥ (q + 1)/2]`. -/
  j0 : ℕ
  /-- The width of the bits `[u ≥ q]`, `[u ≥ 2q]` and `[a0 ≥ 1]`. -/
  jq : ℕ
  /-- The width of the bit `[δ² ≥ 1]`. -/
  jd : ℕ
  /-- The width of the bits `[u ≥ M]`, `[u ≥ 2M]`. -/
  ju : ℕ

section DecomposeProgs

variable (P : DecomposeMagic) {Γ : JCtxt} {ts : List JasminTy}

/-- The high part `a1` of `Decompose`. -/
def hbK (x : Var Γ (.reg P.w)) (k : Kont Γ P.w ts) : MC Γ ts :=
  arCK .add P.w x (2 ^ P.p - 1) fun r1 u => sarK P.w P.p u fun r2 a' =>
    mulAddSarK P.w P.m P.b P.s a' fun r3 t => geK P.w P.M P.jt t fun r4 hi =>
      subMulK P.w P.M (r4 t) hi fun r5 a1 => k (fun v => r5 (r4 (r3 (r2 (r1 v))))) a1

/-- `Decompose`: the high part `a1` and the low part. -/
def decK (x : Var Γ (.reg P.w)) (k : Kont2 Γ P.w ts) : MC Γ ts :=
  hbK P x fun r1 a1 => subMulK P.w P.alpha (r1 x) a1 fun r2 a0 =>
    geK P.w ((P.q + 1) / 2) P.j0 a0 fun r3 g => subMulK P.w P.q (r3 a0) g fun r4 l =>
      k (fun v => r4 (r3 (r2 (r1 v)))) (r4 (r3 (r2 a1))) l

/-- The `Decompose` template: outputs `(a1, a0)`. -/
def decomposeProg : MC (C1 P.w) [.reg P.w, .reg P.w] :=
  decK P .here fun _ a1 a0 => .ret (.cons a1 (.cons a0 .nil))

/-- The `MakeHint` template on the inputs `r` (`.here`) and `z`: reduce `u = r + z + q`
    modulo `q` by `u - q·([u ≥ q] + [u ≥ 2q])`, take the high parts of `r` and of the
    reduced sum, and return `[δ² ≥ 1]` for their difference `δ`. -/
def makeHintProg : MC (C2 P.w) [.reg P.w] :=
  arK .add P.w .here (.there .here) fun r1 u0 => arCK .add P.w u0 P.q fun r2 u =>
    geK P.w P.q P.jq u fun r3 b1 => geK P.w (2 * P.q) P.jq (r3 u) fun r4 b2 =>
      arK .add P.w (r4 b1) b2 fun r5 bs => subMulK P.w P.q (r5 (r4 (r3 u))) bs fun r6 sr =>
        hbK P (r6 (r5 (r4 (r3 (r2 (r1 .here)))))) fun r7 h1 => hbK P (r7 sr) fun r8 h2 =>
          arK .sub P.w (r8 h1) h2 fun _ δ => arK .mul P.w δ δ fun _ δ2 =>
            geK P.w 1 P.jd δ2 fun _ y => .ret (.cons y .nil)

/-- The `UseHint` template on the inputs `r` (`.here`) and the hint bit `h`: with `(a1, a0)`
    the `Decompose` of `r` and `p = [a0 ≥ 1]`, `t = a1 + 2·h·p - h` and `u = t + M`, return
    `u - M·([u ≥ M] + [u ≥ 2M])`. -/
def useHintProg : MC (C2 P.w) [.reg P.w] :=
  decK P .here fun r1 a1 a0 => geK P.w 1 P.jq a0 fun r2 pb =>
    arK .mul P.w (r2 (r1 (.there .here))) pb fun r3 hp => arK .add P.w hp hp fun r4 hp2 =>
      arK .add P.w (r4 (r3 (r2 a1))) hp2 fun r5 t1 =>
        arK .sub P.w t1 (r5 (r4 (r3 (r2 (r1 (.there .here)))))) fun _ t =>
          arCK .add P.w t P.M fun _ u => geK P.w P.M P.ju u fun r8 c1 =>
            geK P.w (2 * P.M) P.ju (r8 u) fun r9 c2 => arK .add P.w (r9 c1) c2 fun r10 cs =>
              subMulK P.w P.M (r10 (r9 (r8 u))) cs fun _ y => .ret (.cons y .nil)

/-- The integer semantics of `hbK`. -/
def hbZ (a : ℤ) : ℤ :=
  let t := mulAddShrZ P.w P.m P.b P.s ((a + cZ P.w (2 ^ P.p - 1)) / 2 ^ P.p)
  subMulZ P.w P.M t (geZ P.w P.M P.jt t)

/-- The integer semantics of `decK`. -/
def decZ (a : ℤ) : ℤ × ℤ :=
  let a0 := subMulZ P.w P.alpha a (hbZ P a)
  (hbZ P a, subMulZ P.w P.q a0 (geZ P.w ((P.q + 1) / 2) P.j0 a0))

/-- The integer semantics of `makeHintProg`. -/
def makeHintZ (z r : ℤ) : ℤ :=
  let u := r + z + cZ P.w P.q
  let sr := subMulZ P.w P.q u (geZ P.w P.q P.jq u + geZ P.w (2 * P.q) P.jq u)
  let δ := hbZ P r - hbZ P sr
  geZ P.w 1 P.jd (δ * δ)

/-- The integer semantics of `useHintProg`. -/
def useHintZ (h r : ℤ) : ℤ :=
  let pb := geZ P.w 1 P.jq (decZ P r).2
  let u := (decZ P r).1 + (h * pb + h * pb) - h + cZ P.w P.M
  subMulZ P.w P.M u (geZ P.w P.M P.ju u + geZ P.w (2 * P.M) P.ju u)

theorem hbK_Q {x : Var Γ (.reg P.w)} {k : Kont Γ P.w ts} {Z : ZVec Γ}
    (Q : ZVec ts → Prop) (hk : KQ Z (hbZ P (hget Z x)) Q k) : Q ((hbK P x k).denoteZ Z) :=
  arCK_Q Q fun _ u _ h1 hu => sarK_Q Q fun _ a' _ h2 ha' => mulAddSarK_Q Q fun _ t _ h3 ht =>
    geK_Q Q fun _ hi _ h4 hhi => subMulK_Q Q fun _ a1 Z5 h5 ha1 =>
      hk _ a1 Z5 (fun v => (h5 _).trans ((h4 _).trans ((h3 _).trans ((h2 _).trans (h1 v)))))
        (by rw [ha1, h4, hhi, ht, ha', hu]; rfl)

theorem decK_Q {x : Var Γ (.reg P.w)} {k : Kont2 Γ P.w ts} {Z : ZVec Γ}
    (Q : ZVec ts → Prop) (hk : KQ2 Z (decZ P (hget Z x)).1 (decZ P (hget Z x)).2 Q k) :
    Q ((decK P x k).denoteZ Z) :=
  hbK_Q P Q fun _ a1 _ h1 ha1 => subMulK_Q Q fun _ a0 _ h2 ha0 => geK_Q Q fun _ g _ h3 hg =>
    subMulK_Q Q fun _ l Z4 h4 hl =>
      hk _ _ l Z4 (fun v => (h4 _).trans ((h3 _).trans ((h2 _).trans (h1 v))))
        (by rw [h4, h3, h2, ha1]; rfl) (by rw [hl, h3, hg, ha0, h1, ha1]; rfl)

theorem decomposeProg_Q (Z : ZVec (C1 P.w)) (Q : ZVec [.reg P.w, .reg P.w] → Prop)
    (hk : Q (.cons (decZ P (hget Z .here)).1 (.cons (decZ P (hget Z .here)).2 .nil))) :
    Q ((decomposeProg P).denoteZ Z) :=
  decK_Q P Q fun _ y1 y2 Zf _ h1 h2 => by
    show Q (HVector.cons (hget Zf y1) (.cons (hget Zf y2) .nil))
    rw [h1, h2]; exact hk

theorem decomposeProg_denoteZ (a : ℤ) :
    (decomposeProg P).denoteZ (.cons a .nil)
      = .cons (decZ P a).1 (.cons (decZ P a).2 .nil) :=
  decomposeProg_Q P _ (fun v => v = _) rfl

theorem makeHintProg_Q (Z : ZVec (C2 P.w)) (Q : ZVec (C1 P.w) → Prop)
    (hk : Q (.cons (makeHintZ P (hget Z (.there .here)) (hget Z .here)) .nil)) :
    Q ((makeHintProg P).denoteZ Z) :=
  arK_Q Q fun _ _ _ h1 hu0 => arCK_Q Q fun _ _ _ h2 hu =>
    geK_Q Q fun _ _ _ h3 hb1 => geK_Q Q fun _ _ _ h4 hb2 => arK_Q Q fun _ _ _ h5 hbs =>
      subMulK_Q Q fun _ _ _ h6 hsr => hbK_Q P Q fun _ _ _ h7 hh1 => hbK_Q P Q fun _ _ _ h8 hh2 =>
        arK_Q Q fun _ _ _ _ hδ => arK_Q Q fun _ _ _ _ hδ2 => geK_Q Q fun _ y Zf _ hy => by
          show Q (HVector.cons (hget Zf y) .nil)
          have e : hget Zf y = makeHintZ P (hget Z (.there .here)) (hget Z .here) := by
            simp only [hy, hδ2, hδ, hh2, h8, hh1, h7, h6, hsr, h5, h4, h3, hbs, hb1, hb2, hu,
              h2, h1, hu0]
            rfl
          rw [e]; exact hk

theorem makeHintProg_denoteZ (z r : ℤ) :
    (makeHintProg P).denoteZ (.cons r (.cons z .nil)) = .cons (makeHintZ P z r) .nil :=
  makeHintProg_Q P _ (fun v => v = _) rfl

theorem useHintProg_Q (Z : ZVec (C2 P.w)) (Q : ZVec (C1 P.w) → Prop)
    (hk : Q (.cons (useHintZ P (hget Z (.there .here)) (hget Z .here)) .nil)) :
    Q ((useHintProg P).denoteZ Z) :=
  decK_Q P Q fun _ _ _ _ h1 ha1 ha0 => geK_Q Q fun _ _ _ h2 hpb =>
    arK_Q Q fun _ _ _ h3 hhp => arK_Q Q fun _ _ _ h4 hhp2 => arK_Q Q fun _ _ _ h5 ht1 =>
      arK_Q Q fun _ _ _ _ ht => arCK_Q Q fun _ _ _ _ hu => geK_Q Q fun _ _ _ h8 hc1 =>
        geK_Q Q fun _ _ _ h9 hc2 => arK_Q Q fun _ _ _ h10 hcs =>
          subMulK_Q Q fun _ y Zf _ hy => by
            show Q (HVector.cons (hget Zf y) .nil)
            have e : hget Zf y = useHintZ P (hget Z (.there .here)) (hget Z .here) := by
              simp only [hy, h10, h9, h8, hcs, hc1, hc2, hu, ht, h5, h4, h3, h2, ht1,
                hhp2, hhp, hpb, h1, ha1, ha0]
              rfl
            rw [e]; exact hk

theorem useHintProg_denoteZ (h r : ℤ) :
    (useHintProg P).denoteZ (.cons r (.cons h .nil)) = .cons (useHintZ P h r) .nil :=
  useHintProg_Q P _ (fun v => v = _) rfl

end DecomposeProgs

/-- The ML-DSA-44 constants, `γ₂ = (q - 1)/88`: the high part is
    `⌊(⌊(a + 127)/128⌋·11275 + 2^23) / 2^24⌋`, the reference implementation's multiplier. -/
def mldsa88 : DecomposeMagic :=
  ⟨32, 8380417, 190464, 44, 7, 11275, 8388608, 24, 6, 24, 25, 13, 8⟩

/-- The ML-DSA-65/87 constants, `γ₂ = (q - 1)/32`: the high part is
    `⌊(⌊(a + 127)/128⌋·1025 + 2^21) / 2^22⌋`, the reference implementation's multiplier. -/
def mldsa32 : DecomposeMagic :=
  ⟨32, 8380417, 523776, 16, 7, 1025, 2097152, 22, 6, 24, 25, 13, 8⟩

/-! ### The ML-DSA bounded blocks and their bounds checks -/

/-- The output interval of the ML-DSA blocks: the 25-bit signed range. -/
def mldsaOut : Iv := (-2 ^ 24, 2 ^ 24)

/-- The two-entry interval vector. -/
abbrev iv2 {w : ℕ} (i j : Iv) : HVector (fun _ => Iv) (C2 w) := .cons i (.cons j .nil)

/-- The ML-DSA `Power2Round` template as a bounded block: 32-bit signed readings, input in
    `[0, q - 1]`. -/
def mldsaPower2RoundBlock : BoundedBlock :=
  BoundedBlock.ofBoundsOk true (iv1 (0, 8380416)) (power2RoundProg 32 13) (iv2 mldsaOut mldsaOut)

/-- The ML-DSA `Decompose` template at `P` as a bounded block: signed readings, input in
    `[0, q - 1]`. -/
def mldsaDecomposeBlock (P : DecomposeMagic) : BoundedBlock :=
  BoundedBlock.ofBoundsOk true (iv1 (0, 8380416)) (decomposeProg P) (iv2 mldsaOut mldsaOut)

/-- The ML-DSA `MakeHint` template at `P` as a bounded block: signed readings, `r` in
    `[0, q - 1]` and `z` in `[-α/2, α/2]`. -/
def mldsaMakeHintBlock (P : DecomposeMagic) : BoundedBlock :=
  BoundedBlock.ofBoundsOk true (iv2 (0, 8380416) (-((P.alpha / 2 : ℕ) : ℤ), (P.alpha / 2 : ℕ)))
    (makeHintProg P) (iv1 mldsaOut)

/-- The ML-DSA `UseHint` template at `P` as a bounded block: signed readings, `r` in
    `[0, q - 1]` and `h` in `[0, 1]`. -/
def mldsaUseHintBlock (P : DecomposeMagic) : BoundedBlock :=
  BoundedBlock.ofBoundsOk true (iv2 (0, 8380416) (0, 1)) (useHintProg P) (iv1 mldsaOut)

/-- The `Power2Round` template passes the bounds check from `[0, q - 1]` at 32 bits. -/
theorem mldsaPower2RoundBlock_ok : mldsaPower2RoundBlock.ok = true := by decide +kernel

/-- The `Decompose` templates pass the bounds check from `[0, q - 1]`. -/
theorem mldsaDecomposeBlock_ok :
    (mldsaDecomposeBlock mldsa88).ok = true ∧ (mldsaDecomposeBlock mldsa32).ok = true := by
  decide +kernel

/-- The `MakeHint` template at `γ₂ = (q - 1)/88` passes the bounds check from
    `r ∈ [0, q - 1]`, `|z| ≤ γ₂`. -/
theorem mldsaMakeHintBlock_mldsa88_ok : (mldsaMakeHintBlock mldsa88).ok = true := by
  decide +kernel

/-- The `MakeHint` template at `γ₂ = (q - 1)/32` passes the bounds check from
    `r ∈ [0, q - 1]`, `|z| ≤ γ₂`. -/
theorem mldsaMakeHintBlock_mldsa32_ok : (mldsaMakeHintBlock mldsa32).ok = true := by
  decide +kernel

/-- The `UseHint` template at `γ₂ = (q - 1)/88` passes the bounds check from
    `r ∈ [0, q - 1]`, `h ∈ [0, 1]`. -/
theorem mldsaUseHintBlock_mldsa88_ok : (mldsaUseHintBlock mldsa88).ok = true := by
  decide +kernel

/-- The `UseHint` template at `γ₂ = (q - 1)/32` passes the bounds check from
    `r ∈ [0, q - 1]`, `h ∈ [0, 1]`. -/
theorem mldsaUseHintBlock_mldsa32_ok : (mldsaUseHintBlock mldsa32).ok = true := by
  decide +kernel

/-! ### The ML-DSA templates compute the FIPS 204 functions -/

theorem decZ_mldsa88 (a : ℤ) (h0 : 0 ≤ a) (h1 : a < Fips204.q) :
    decZ mldsa88 a = Fips204.decompose 95232 a := by
  simp only [Fips204.q] at h1
  have ht := mulShift_eq_divZ (q := 1488) (m := 11275) (k := 24) (b := 8388608) (c := 743)
    (N := 65473) (by decide) (by norm_num) (n := (a + 127) / 128) (by omega) (by push_cast; omega)
  simp only [decZ, hbZ, mulAddShrZ, geZ, subMulZ, cZ, mldsa88, Fips204.decompose, Fips204.modPm,
    Fips204.q, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceDiv,
    Nat.cast_ofNat, Int.reducePow, Int.reduceMul, Int.reduceDiv, Int.reduceSub, gt_iff_lt] at ht ⊢
  have hT : ((a + 127) / 128 + 743) / 1488 = (a + 95231) / 190464 := by omega
  have hb : 190464 * ((a + 95231) / 190464) ≤ a + 95231 ∧
      a + 95231 < 190464 * ((a + 95231) / 190464) + 190464 := by omega
  rw [ht, hT, Int.emod_eq_of_lt h0 h1]
  generalize (a + 95231) / 190464 = T at hb ⊢
  clear ht hT
  have key : (if 95232 < a % 190464 then a % 190464 - 190464 else a % 190464)
      = a - 190464 * T := by split_ifs <;> omega
  rw [key]
  rcases (show T ≤ 43 ∨ T = 44 by omega) with hT | hT
  · rw [show (T + 20) / 64 = 0 by omega, if_neg (by omega),
      show (a - (T - 0 * 44) * 190464 + 12587007) / 16777216 = 0 by omega]
    simp only [Prod.mk.injEq]
    omega
  · subst hT
    rw [if_pos (by omega)]
    norm_num
    omega

theorem decZ_mldsa32 (a : ℤ) (h0 : 0 ≤ a) (h1 : a < Fips204.q) :
    decZ mldsa32 a = Fips204.decompose 261888 a := by
  simp only [Fips204.q] at h1
  have ht := mulShift_eq_divZ (q := 4092) (m := 1025) (k := 22) (b := 2097152) (c := 2045)
    (N := 65473) (by decide) (by norm_num) (n := (a + 127) / 128) (by omega) (by push_cast; omega)
  simp only [decZ, hbZ, mulAddShrZ, geZ, subMulZ, cZ, mldsa32, Fips204.decompose, Fips204.modPm,
    Fips204.q, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceDiv,
    Nat.cast_ofNat, Int.reducePow, Int.reduceMul, Int.reduceDiv, Int.reduceSub, gt_iff_lt] at ht ⊢
  have hT : ((a + 127) / 128 + 2045) / 4092 = (a + 261887) / 523776 := by omega
  have hb : 523776 * ((a + 261887) / 523776) ≤ a + 261887 ∧
      a + 261887 < 523776 * ((a + 261887) / 523776) + 523776 := by omega
  rw [ht, hT, Int.emod_eq_of_lt h0 h1]
  generalize (a + 261887) / 523776 = T at hb ⊢
  clear ht hT
  have key : (if 261888 < a % 523776 then a % 523776 - 523776 else a % 523776)
      = a - 523776 * T := by split_ifs <;> omega
  rw [key]
  rcases (show T ≤ 15 ∨ T = 16 by omega) with hT | hT
  · rw [show (T + 48) / 64 = 0 by omega, if_neg (by omega),
      show (a - (T - 0 * 16) * 523776 + 12587007) / 16777216 = 0 by omega]
    simp only [Prod.mk.injEq]
    omega
  · subst hT
    rw [if_pos (by omega)]
    norm_num
    omega

/-- The ranges of FIPS 204 `Decompose` on `[0, q)`: `0 ≤ r1 < (q - 1)/(2γ₂)` and
    `|r0| ≤ γ₂`. -/
theorem decompose_range (γ2 : ℤ) (hγ : γ2 = 95232 ∨ γ2 = 261888) (a : ℤ) (h0 : 0 ≤ a)
    (h1 : a < Fips204.q) :
    0 ≤ (Fips204.decompose γ2 a).1 ∧ (Fips204.decompose γ2 a).1 < (Fips204.q - 1) / (2 * γ2) ∧
      -γ2 ≤ (Fips204.decompose γ2 a).2 ∧ (Fips204.decompose γ2 a).2 ≤ γ2 := by
  simp only [Fips204.q] at h1
  rcases hγ with rfl | rfl <;>
  · simp only [Fips204.decompose, Fips204.modPm, Fips204.q, Int.emod_eq_of_lt h0 h1]
    norm_num
    split_ifs <;> omega

/-- `HighBits` depends on its argument only modulo `q`. -/
theorem highBits_emod (γ2 r : ℤ) :
    Fips204.highBits γ2 (r % Fips204.q) = Fips204.highBits γ2 r := by
  simp only [Fips204.highBits, Fips204.decompose, Int.emod_emod_of_dvd r (Int.dvd_refl _)]

/-- The reduction step of `makeHintProg`: `u - q·([u ≥ q] + [u ≥ 2q])` for
    `u = r + z + q` is `(r + z) mod q` when `-q < r + z < 2q`. -/
theorem makeHint_reduce (r z : ℤ) (h0 : -8380417 < r + z) (h1 : r + z < 2 * 8380417) :
    subMulZ 32 8380417 (r + z + cZ 32 8380417)
        (geZ 32 8380417 25 (r + z + cZ 32 8380417) +
          geZ 32 (2 * 8380417) 25 (r + z + cZ 32 8380417)) = (r + z) % 8380417 := by
  simp only [subMulZ, geZ, cZ]
  norm_num
  rcases (show r + z < 0 ∨ (0 ≤ r + z ∧ r + z < 8380417) ∨ 8380417 ≤ r + z by omega) with
    h | h | h
  · rw [show (r + z) % 8380417 = r + z + 8380417 by omega]; omega
  · rw [show (r + z) % 8380417 = r + z by omega]; omega
  · rw [show (r + z) % 8380417 = r + z - 8380417 by omega]; omega

/-- The hint bit of `makeHintProg`: `[δ² ≥ 1] = [δ ≠ 0]` for `|δ| ≤ 43`. -/
theorem hintBit (h1 h2 : ℤ) (ha : 0 ≤ h1 ∧ h1 ≤ 43) (hb : 0 ≤ h2 ∧ h2 ≤ 43) :
    geZ 32 1 13 ((h1 - h2) * (h1 - h2)) = if decide (h1 ≠ h2) = true then 1 else 0 := by
  simp only [geZ, cZ]
  norm_num
  by_cases e : h1 = h2
  · subst e; simp
  · have hl : 1 ≤ (h1 - h2) * (h1 - h2) := by
      rcases lt_or_gt_of_ne (sub_ne_zero.mpr e) with h | h <;> nlinarith
    have hu : (h1 - h2) * (h1 - h2) ≤ 1849 := by nlinarith
    simp only [e, if_false]
    omega

/-- **The `MakeHint` template computes FIPS 204 `MakeHint`** on the integers, for
    `0 ≤ r < q` and `-q < z < q`, given that its high part computes `HighBits`. -/
theorem makeHintZ_eq (P : DecomposeMagic) (γ2 : ℤ) (hw : P.w = 32) (hq : P.q = 8380417)
    (hjq : P.jq = 25) (hjd : P.jd = 13)
    (hdec : ∀ a, 0 ≤ a → a < Fips204.q → hbZ P a = Fips204.highBits γ2 a)
    (hrange : ∀ a, 0 ≤ a → a < Fips204.q →
      0 ≤ Fips204.highBits γ2 a ∧ Fips204.highBits γ2 a ≤ 43)
    (z r : ℤ) (h0 : 0 ≤ r) (h1 : r < Fips204.q) (hz0 : -Fips204.q < z) (hz1 : z < Fips204.q) :
    makeHintZ P z r = if Fips204.makeHint γ2 z r then 1 else 0 := by
  have hq' : (0 : ℤ) < Fips204.q := by simp [Fips204.q]
  have hs0 := Int.emod_nonneg (r + z) hq'.ne'
  have hs1 := Int.emod_lt_of_pos (r + z) hq'
  obtain ⟨w, q, alpha, M, p, m, b, s, jt, j0, jq, jd, ju⟩ := P
  simp only at hw hq hjq hjd
  subst hw hq hjq hjd
  simp only [Fips204.q] at h1 hz0 hz1 hs0 hs1
  simp only [makeHintZ]
  rw [makeHint_reduce r z (by omega) (by omega), hdec r h0 (by simp [Fips204.q]; omega),
    hdec _ hs0 (by simpa [Fips204.q] using hs1)]
  have e := highBits_emod γ2 (r + z)
  simp only [Fips204.q] at e
  rw [e, Fips204.makeHint]
  exact hintBit _ _ (hrange r h0 (by simp [Fips204.q]; omega))
    (by rw [← e]; exact hrange _ hs0 (by simpa [Fips204.q] using hs1))

/-- The bit `p = [r0 ≥ 1]` of `useHintProg` for `|r0| ≤ 2^24`. -/
theorem useHint_pbit (r0 : ℤ) (h0 : -2 ^ 24 ≤ r0) (h1 : r0 ≤ 2 ^ 24) :
    geZ 32 1 25 r0 = if 0 < r0 then 1 else 0 := by
  simp only [geZ, cZ, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat]
  split_ifs <;> omega

/-- The reduction step of `useHintProg`: `u - M·([u ≥ M] + [u ≥ 2M])` for `u = t + M` is
    `t mod M` when `-1 ≤ t ≤ M`. -/
theorem useHint_mod (M : ℕ) (hM : M = 44 ∨ M = 16) (t : ℤ) (h0 : -1 ≤ t) (h1 : t ≤ M) :
    subMulZ 32 M (t + cZ 32 M) (geZ 32 M 8 (t + cZ 32 M) + geZ 32 (2 * M) 8 (t + cZ 32 M))
      = t % M := by
  rcases hM with rfl | rfl <;>
  · simp only [subMulZ, geZ, cZ, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceMul,
      Nat.cast_ofNat] at h1 ⊢
    rcases (show t = -1 ∨ (0 ≤ t ∧ t < 44) ∨ t = 44 ∨ (44 < t) by omega) with h | h | h | h <;>
    omega

/-- **The `UseHint` template computes FIPS 204 `UseHint`** on the integers, for
    `0 ≤ r < q` and the hint bit read as `0` or `1`, given that its `Decompose` part
    computes `Decompose`. -/
theorem useHintZ_eq (P : DecomposeMagic) (γ2 : ℤ) (hw : P.w = 32) (hjq : P.jq = 25)
    (hju : P.ju = 8) (hM : (P.M = 44 ∧ γ2 = 95232) ∨ (P.M = 16 ∧ γ2 = 261888))
    (hdec : ∀ a, 0 ≤ a → a < Fips204.q → decZ P a = Fips204.decompose γ2 a)
    (hb : Bool) (r : ℤ) (h0 : 0 ≤ r) (h1 : r < Fips204.q) :
    useHintZ P (if hb then 1 else 0) r = Fips204.useHint γ2 hb r := by
  have hr := decompose_range γ2 (by rcases hM with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]) r h0 h1
  have hγ : γ2 ≤ 261888 := by rcases hM with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  obtain ⟨w, q, alpha, M, p, m, b, s, jt, j0, jq, jd, ju⟩ := P
  simp only at hw hjq hju hM hdec
  subst hw hjq hju
  have hM' : M = 44 ∨ M = 16 := by rcases hM with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hm : (Fips204.q - 1) / (2 * γ2) = (M : ℤ) := by
    rcases hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  simp only [useHintZ, Fips204.useHint, hm]
  rw [hdec r h0 h1]
  generalize Fips204.decompose γ2 r = d at hr ⊢
  obtain ⟨r1, r0⟩ := d
  simp only [hm] at hr ⊢
  have hM1 : (1 : ℤ) ≤ M := by rcases hM' with rfl | rfl <;> norm_num
  cases hb
  · simp only [Bool.false_eq_true, if_false, zero_mul, add_zero, sub_zero, false_and]
    rw [useHint_mod M hM' r1 (by omega) (by omega)]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · simp only [if_true, one_mul, true_and]
    rw [useHint_pbit r0 (by omega) (by omega)]
    split_ifs
    · rw [useHint_mod M hM' _ (by omega) (by omega)]
      congr 1; ring
    · rw [useHint_mod M hM' _ (by omega) (by omega)]
      congr 1; ring

/-- The two ML-DSA instances: `mldsa88` with `γ₂ = (q - 1)/88` and `mldsa32` with
    `γ₂ = (q - 1)/32`. -/
def MldsaInst (P : DecomposeMagic) (γ2 : ℤ) : Prop :=
  (P = mldsa88 ∧ γ2 = 95232) ∨ (P = mldsa32 ∧ γ2 = 261888)

theorem decZ_mldsa {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2) (a : ℤ) (h0 : 0 ≤ a)
    (h1 : a < Fips204.q) : decZ P a = Fips204.decompose γ2 a := by
  rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact decZ_mldsa88 a h0 h1
  · exact decZ_mldsa32 a h0 h1


/-- **The `Power2Round` template computes FIPS 204 `Power2Round` on words.** Under the
    bounds check from `[0, q - 1]`, the signed readings of the outputs on a 32-bit word in
    `[0, q)` are the two parts of `Power2Round`. -/
theorem power2Round_denote (outs : HVector (fun _ => Iv) (C2 32))
    (hb : boundsOkMR true (iv1 (0, Fips204.q - 1)) (power2RoundProg 32 13) outs = true)
    (x : BitVec 32) (h0 : 0 ≤ rd true x) (h1 : rd true x < Fips204.q) :
    zvals true ((power2RoundProg 32 13).denote (.cons x .nil))
      = .cons (Fips204.power2Round (rd true x)).1
          (.cons (Fips204.power2Round (rd true x)).2 .nil) := by
  have hV := valsIn_iv1 true (0, Fips204.q - 1) x h0 (by simp only; omega)
  rw [(denoteMR_eq_denoteZ_of_boundsOk true _ _ _ hb _ hV).1]
  exact (power2RoundProg_denoteZ 32 13 (rd true x)).trans (by rw [power2RoundZ_eq _ h0 h1])

/-- **The `Decompose` template computes FIPS 204 `Decompose` on words**, at both ML-DSA
    instances. Under the bounds check from `[0, q - 1]`, the signed readings of the outputs
    on a word in `[0, q)` are `(HighBits, LowBits)`. -/
theorem decompose_denote {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (outs : HVector (fun _ => Iv) (C2 P.w))
    (hb : boundsOkMR true (iv1 (0, Fips204.q - 1)) (decomposeProg P) outs = true)
    (x : BitVec P.w) (h0 : 0 ≤ rd true x) (h1 : rd true x < Fips204.q) :
    zvals true ((decomposeProg P).denote (.cons x .nil))
      = .cons (Fips204.highBits γ2 (rd true x)) (.cons (Fips204.lowBits γ2 (rd true x)) .nil) := by
  have hV := valsIn_iv1 true (0, Fips204.q - 1) x h0 (by simp only; omega)
  rw [(denoteMR_eq_denoteZ_of_boundsOk true _ _ _ hb _ hV).1]
  exact (decomposeProg_denoteZ P (rd true x)).trans (by rw [decZ_mldsa hP _ h0 h1]; rfl)

/-- **The `MakeHint` template computes FIPS 204 `MakeHint` on words**, at both ML-DSA
    instances. Under the bounds check from `r ∈ [0, q - 1]`, `z ∈ [-γ₂, γ₂]`, the signed
    reading of the output is `1` when `MakeHint (z, r)` holds and `0` otherwise. -/
theorem makeHint_denote {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (out : HVector (fun _ => Iv) (C1 P.w))
    (hb : boundsOkMR true (iv2 (0, Fips204.q - 1) (-γ2, γ2)) (makeHintProg P) out = true)
    (r z : BitVec P.w) (h0 : 0 ≤ rd true r) (h1 : rd true r < Fips204.q)
    (hz0 : -γ2 ≤ rd true z) (hz1 : rd true z ≤ γ2) :
    zvals true ((makeHintProg P).denote (.cons r (.cons z .nil)))
      = .cons (if Fips204.makeHint γ2 (rd true z) (rd true r) then 1 else 0) .nil := by
  have hV : ValsIn true (iv2 (0, Fips204.q - 1) (-γ2, γ2))
      (HVector.cons r (.cons z .nil) : Valuation (C2 P.w)) :=
    ⟨⟨h0, by simp only; omega⟩, ⟨hz0, hz1⟩, trivial⟩
  rw [(denoteMR_eq_denoteZ_of_boundsOk true _ _ _ hb _ hV).1]
  have hγ : γ2 ≤ 261888 := by rcases hP with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  have hrng : ∀ a, 0 ≤ a → a < Fips204.q →
      0 ≤ Fips204.highBits γ2 a ∧ Fips204.highBits γ2 a ≤ 43 := fun a ha0 ha1 => by
    have h := decompose_range γ2 (by rcases hP with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]) a ha0 ha1
    have hm : (Fips204.q - 1) / (2 * γ2) ≤ 44 := by
      rcases hP with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [Fips204.q]
    exact ⟨h.1, by unfold Fips204.highBits; omega⟩
  have hfix : P.w = 32 ∧ P.q = 8380417 ∧ P.jq = 25 ∧ P.jd = 13 := by
    rcases hP with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩
  refine (makeHintProg_denoteZ P (rd true z) (rd true r)).trans ?_
  rw [makeHintZ_eq P γ2 hfix.1 hfix.2.1 hfix.2.2.1 hfix.2.2.2
    (fun a ha0 ha1 => by rw [show hbZ P a = (decZ P a).1 from rfl, decZ_mldsa hP a ha0 ha1]; rfl)
    hrng _ _ h0 h1 (by simp only [Fips204.q] at *; omega) (by simp only [Fips204.q] at *; omega)]

/-- **The `UseHint` template computes FIPS 204 `UseHint` on words**, at both ML-DSA
    instances. Under the bounds check from `r ∈ [0, q - 1]`, `h ∈ [0, 1]`, the signed
    reading of the output is `UseHint (h = 1, r)`. -/
theorem useHint_denote {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (out : HVector (fun _ => Iv) (C1 P.w))
    (hb : boundsOkMR true (iv2 (0, Fips204.q - 1) (0, 1)) (useHintProg P) out = true)
    (r h : BitVec P.w) (h0 : 0 ≤ rd true r) (h1 : rd true r < Fips204.q)
    (hh0 : 0 ≤ rd true h) (hh1 : rd true h ≤ 1) :
    zvals true ((useHintProg P).denote (.cons r (.cons h .nil)))
      = .cons (Fips204.useHint γ2 (decide (rd true h = 1)) (rd true r)) .nil := by
  have hV : ValsIn true (iv2 (0, Fips204.q - 1) (0, 1))
      (HVector.cons r (.cons h .nil) : Valuation (C2 P.w)) :=
    ⟨⟨h0, by simp only; omega⟩, ⟨hh0, hh1⟩, trivial⟩
  rw [(denoteMR_eq_denoteZ_of_boundsOk true _ _ _ hb _ hV).1]
  have hfix : P.w = 32 ∧ P.jq = 25 ∧ P.ju = 8 ∧
      ((P.M = 44 ∧ γ2 = 95232) ∨ (P.M = 16 ∧ γ2 = 261888)) := by
    rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, rfl, rfl, .inr ⟨rfl, rfl⟩⟩
  have e : rd true h = if decide (rd true h = 1) then 1 else 0 := by
    by_cases hc : rd true h = 1
    · simp [hc]
    · simp only [hc, decide_false, Bool.false_eq_true, if_false]
      omega
  refine (useHintProg_denoteZ P (rd true h) (rd true r)).trans ?_
  rw [e, useHintZ_eq P γ2 hfix.1 hfix.2.1 hfix.2.2.1 hfix.2.2.2 (decZ_mldsa hP) _ _ h0 h1, ← e]

end CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec
