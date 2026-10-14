/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord
public import CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric
public import CatCrypt.Crypto.Jasmin.LowCTSyntax
public import Mathlib.Tactic.NormNum

/-!
# Single-multiply Barrett reduction for small NTT primes

The modular reduction used by the scalar `q = 3329` field kernels, parameterised by
the modulus `q`, the Barrett multiplier `μ` and the shift `k`, on 64-bit words:

    q̂ = (r · μ) >>> k,   t = r − q̂ · q,   result = csubW q t

where `csubW q` is the branch-free conditional subtract of
`Algebraic.FieldWord.SingleWord`. The block is given at two levels: the word
function `barrettW q μ k`, and the `LowCT` statement lists `csubStmts` and
`mulModStmtsE` / `mulModStmts` that the front-compiled emitters feed to
`translateDialectControl`.

## Main definitions

* `barrettW q μ k r`: the Barrett reduce of a 64-bit word.
* `csubStmts q dst src`: the conditional subtract of `q` as two `RScalarSetExpr`
  statements.
* `mulModStmtsE q μ k dst a b`, `mulModStmts q μ k dst a b`: the product `a · b`
  followed by the Barrett reduce, as `RScalarSetExpr` statements.
* `scalarRunBV`: the straight-line reading of a list of `RScalarSetExpr` statements
  under the wrapping evaluator `SExpr.evalBV`.

## Main results

* `barrettW_toNat`: for `0 < q ≤ 2^k`, `2q ≤ 2^63`, `μ = ⌊2^k / q⌋`,
  `2^k · μ < 2^64` and `r < 2^k`, `(barrettW q μ k r).toNat = r.toNat % q`. The
  quotient bounds are `BarrettReduceGeneric.barrettQuot_le` and `barrett_bounds`.
* `csubStmts_run`, `mulModStmtsE_run`, `mulModStmts_run`: the statement lists
  compute `csubW q` and `barrettW q μ k` of the product under `scalarRunBV`.
* `barrettW_mlkem_toNat`, `csubW_mlkem_toNat`, `csubW_mldsa_toNat`: the instances at
  `q = 3329` (`μ = 5039`, `k = 24`) and `q = 8380417`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SmallPrimeBarrett

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (csubW csubW_toNat)
open CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric
  (mu barrettQuot barrett barrettQuot_le barrett_bounds)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The word function -/

/-- The single-multiply Barrett reduce of a 64-bit word: quotient estimate
    `(r · μ) >>> k`, remainder `r − q̂ · q`, then one conditional subtract of `q`. -/
def barrettW (q μ k : Nat) (r : BitVec 64) : BitVec 64 :=
  csubW q (r - ((r * BitVec.ofNat 64 μ) >>> k) * BitVec.ofNat 64 q)

/-- The Barrett reduce is reduction modulo `q` on inputs below `2^k`, when `μ` is the
    Barrett multiplier `⌊2^k / q⌋`, the product `r · μ` does not wrap
    (`2^k · μ < 2^64`) and the conditional subtract applies (`2q ≤ 2^63`). -/
theorem barrettW_toNat (q μ k : Nat) (hq : 0 < q) (hqk : q ≤ 2 ^ k)
    (hq63 : 2 * q ≤ 2 ^ 63) (hμ : μ = mu q k) (hov : 2 ^ k * μ < 2 ^ 64)
    (r : BitVec 64) (hr : r.toNat < 2 ^ k) :
    (barrettW q μ k r).toNat = r.toNat % q := by
  have h64 : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := by norm_num
  have hμlt : μ < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left μ (Nat.two_pow_pos k)) hov
  have hμt : (BitVec.ofNat 64 μ).toNat = μ := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hμlt
  have hqt : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hprod : r.toNat * μ < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right μ hr.le) hov
  have hm : (r * BitVec.ofNat 64 μ).toNat = r.toNat * μ := by
    rw [BitVec.toNat_mul, hμt, Nat.mod_eq_of_lt hprod]
  have hqhat : ((r * BitVec.ofNat 64 μ) >>> k).toNat = barrettQuot q k r.toNat := by
    rw [BitVec.toNat_ushiftRight, hm, Nat.shiftRight_eq_div_pow, barrettQuot, ← hμ]
  have hqq : barrettQuot q k r.toNat * q ≤ r.toNat :=
    le_trans (Nat.mul_le_mul_right q (barrettQuot_le q k hq hqk r.toNat))
      (Nat.div_mul_le_self r.toNat q)
  have hmul : (((r * BitVec.ofNat 64 μ) >>> k) * BitVec.ofNat 64 q).toNat
      = barrettQuot q k r.toNat * q := by
    rw [BitVec.toNat_mul, hqhat, hqt, Nat.mod_eq_of_lt (lt_of_le_of_lt hqq r.isLt)]
  have hsub : (r - ((r * BitVec.ofNat 64 μ) >>> k) * BitVec.ofNat 64 q).toNat
      = barrett q k r.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hmul]; exact hqq), hmul]; rfl
  obtain ⟨_, hb2⟩ := barrett_bounds q k hq hqk r.toNat hr
  have hmodlt := Nat.mod_lt r.toNat hq
  have hrec : barrett q k r.toNat + barrettQuot q k r.toNat * q = r.toNat := by
    simp only [barrett]; omega
  unfold barrettW
  rw [csubW_toNat q hq63 _ (by rw [hsub]; omega), hsub]
  calc barrett q k r.toNat % q
      = (barrett q k r.toNat + barrettQuot q k r.toNat * q) % q := by
        rw [Nat.add_mul_mod_self_right]
    _ = r.toNat % q := by rw [hrec]

/-! ## 2. The `LowCT` statement lists -/

/-- The conditional subtract of `q` into `dst` (correct for `src < 2q`):
    `dst_s := src − q;  dst := dst_s + (q & (0 − (dst_s >>> 63)))`. -/
def csubStmts (q : Nat) (dst src : String) : List LowCT := [
  .RScalarSetExpr (dst ++ "_s") (.SSub (.SVar src) (.SLit q)),
  .RScalarSetExpr dst
    (.SAdd (.SVar (dst ++ "_s"))
      (.SAnd (.SLit q)
        (.SSub (.SLit 0) (.SShr (.SVar (dst ++ "_s")) (.SLit 63))))) ]

/-- `dst := (a · b) mod q` for an expression `a` and a slot `b`: the product into
    `dst_x`, the quotient estimate `dst_q := (dst_x · μ) >>> k`, the remainder
    `dst_r := dst_x − dst_q · q`, then `csubStmts q dst dst_r`. -/
def mulModStmtsE (q μ k : Nat) (dst : String) (a : SExpr) (b : String) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "_x") (.SMul a (.SVar b)),
    .RScalarSetExpr (dst ++ "_q")
      (.SShr (.SMul (.SVar (dst ++ "_x")) (.SLit μ)) (.SLit k)),
    .RScalarSetExpr (dst ++ "_r")
      (.SSub (.SVar (dst ++ "_x"))
        (.SMul (.SVar (dst ++ "_q")) (.SLit q))) ]
  ++ csubStmts q dst (dst ++ "_r")

/-- `mulModStmtsE` with a slot as the first factor. -/
def mulModStmts (q μ k : Nat) (dst a b : String) : List LowCT :=
  mulModStmtsE q μ k dst (.SVar a) b

/-- The straight-line reading of a list of `RScalarSetExpr` statements: each
    statement writes the `SExpr.evalBV` value of its right-hand side to its slot.
    Any other statement makes the result `none`. -/
def scalarRunBV : List LowCT → (String → BitVec 64) → Option (String → BitVec 64)
  | [], β => some β
  | .RScalarSetExpr x e :: cs, β => scalarRunBV cs (Function.update β x (e.evalBV β))
  | _ :: _, _ => none

/-- The conditional-subtract statements leave `csubW q (β src)` in `dst`. -/
theorem csubStmts_run (q : Nat) (dst src : String) (β : String → BitVec 64) :
    (scalarRunBV (csubStmts q dst src) β).map (· dst) = some (csubW q (β src)) := by
  simp [scalarRunBV, csubStmts, SExpr.evalBV, csubW]

/-- The Barrett multiply statements leave `barrettW q μ k (a · β b)` in `dst`, for a
    shift amount `k < 64`. -/
theorem mulModStmtsE_run (q μ k : Nat) (hk : k < 64) (dst : String) (a : SExpr)
    (b : String) (β : String → BitVec 64) :
    (scalarRunBV (mulModStmtsE q μ k dst a b) β).map (· dst)
      = some (barrettW q μ k (a.evalBV β * β b)) := by
  have hk' : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
  have hk64 : k % 64 = k := Nat.mod_eq_of_lt hk
  simp [scalarRunBV, mulModStmtsE, csubStmts, SExpr.evalBV, barrettW, csubW, hk', hk64]

/-- `mulModStmts` leaves `barrettW q μ k (β a · β b)` in `dst`, for a shift amount
    `k < 64`. -/
theorem mulModStmts_run (q μ k : Nat) (hk : k < 64) (dst a b : String)
    (β : String → BitVec 64) :
    (scalarRunBV (mulModStmts q μ k dst a b) β).map (· dst)
      = some (barrettW q μ k (β a * β b)) :=
  mulModStmtsE_run q μ k hk dst (.SVar a) b β

/-! ## 3. Instances -/

/-- `5039 = ⌊2^24 / 3329⌋`, the ML-KEM Barrett multiplier. -/
theorem mu_mlkem : mu 3329 24 = 5039 := by decide

/-- The ML-KEM (`q = 3329`, `μ = 5039`, `k = 24`) Barrett reduce is reduction modulo
    `3329` on every input below `3329²`. -/
theorem barrettW_mlkem_toNat (r : BitVec 64) (hr : r.toNat < 3329 * 3329) :
    (barrettW 3329 5039 24 r).toNat = r.toNat % 3329 :=
  barrettW_toNat 3329 5039 24 (by norm_num) (by norm_num) (by norm_num) mu_mlkem.symm
    (by norm_num) r (lt_of_lt_of_le hr (by norm_num))

/-- The conditional subtract of `3329` is reduction modulo `3329` below `2 · 3329`. -/
theorem csubW_mlkem_toNat (r : BitVec 64) (hr : r.toNat < 2 * 3329) :
    (csubW 3329 r).toNat = r.toNat % 3329 :=
  csubW_toNat 3329 (by norm_num) r hr

/-- The conditional subtract of `8380417` is reduction modulo `8380417` below
    `2 · 8380417`. -/
theorem csubW_mldsa_toNat (r : BitVec 64) (hr : r.toNat < 2 * 8380417) :
    (csubW 8380417 r).toNat = r.toNat % 8380417 :=
  csubW_toNat 8380417 (by norm_num) r hr

end CatCrypt.Crypto.SecureCompilation.SmallPrimeBarrett
