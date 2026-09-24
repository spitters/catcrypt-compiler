/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2DiffuseExact
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2DiffuseExact
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# `bbMul` is field multiplication on canonical Baby Bear reps

This module proves the `bbMul_field_correct_residual` seam stated in
`Poseidon2DiffuseExact` (`bbMul`-as-field-multiplication identity). A monolithic
`bv_decide` on the full 10-fold + 2-csub `bbReduce` chain at 64-bit width over a
62-bit product times out (>600s).

The strategy here is to **decompose the chain** instead of hitting it with one
SAT shot:

1. **`bbFold_toNat`** — push `BitVec` through to a pure `Nat` form
   `(bbFold x).toNat = (x.toNat / 2^31) * (2^27 - 1) + x.toNat % 2^31` whenever
   `x.toNat < 2^62`. Discharged by `BitVec.toNat_*` simp + `nlinarith`/`omega`.
   The fold has no 64-bit overflow under that bound, so `% 2^64` drops.

2. **`bbFold_mod_p`** — modular invariance: `(bbFold x).toNat ≡ x.toNat (mod p)`
   under the same bound. Direct `omega` consequence of (1) using
   `x.toNat = (x.toNat / 2^31) * 2^31 + x.toNat % 2^31` and
   `2^31 - (2^27 - 1) = p`.

3. **`bbFold_bound`** — per-step value bound: if `x.toNat < B` with
   `B ≤ 2^62`, then `(bbFold x).toNat < (B / 2^31) * (2^27 - 1) + 2^31`. This is
   the LOOSE per-step shrinkage law, but each step is a single Nat-level
   `nlinarith` away — no SAT.

4. **`bbFold10_bound`** — 10-fold composition: starting from `x.toNat < 2^62`,
   after 10 applications of `bbFold` the value is `< 2281701375 < 2 · p`. Proven
   by iterating `bbFold_bound` 10 times with concrete bounds at each level
   (`2^62 → 2^58 + 2^31 → 2^55 + 2^31 → ... → 9·(2^27-1) + 2^31`, settling at a
   fixed-point bound `2281701375` that's strictly below `2p = 4026531842`).

5. **`bbFold10_mod_p`** — modular invariance of the full 10-fold chain. Iterates
   `bbFold_mod_p` 10 times (each invocation needs the value-bound for that
   level, supplied by `bbFold_bound` chained).

6. **`bbCsub` properties** at the toNat level — `bbCsub r < 2p → bbCsub r = r % p`
   (re-exported from `bbCsub_correct`), `bbCsub r < p → bbCsub r = r` (per-step
   `bv_decide` at 64 bits — fast).

7. **`bbReduce_eq_mod`** — `(bbReduce x).toNat = x.toNat % p` for `x.toNat < 2^62`.
   Combines (5) modular invariance through 10 folds with (6) two csubs to
   canonicalise.

8. **`bbMul_eq_mod_p`** — the headline: for `a, b < p` (BitVec), `bbMul a b < p`
   and `bbMul a b = (a * b) % p` (BitVec). The product `a * b` has
   `(a*b).toNat = a.toNat * b.toNat` (no overflow, since `a.toNat * b.toNat < p^2 < 2^62`),
   and then `(bbMul a b).toNat = (a*b).toNat % p` by (7). The BitVec-level
   identity follows via `BitVec.eq_of_toNat_eq`.

The chain bound `9·(2^27-1) + 2^31 = 3355443190 < 2p` was checked by `#eval`
on the iteration `B → (B/2^31)*(2^27-1) + 2^31` starting from `2^62` and is
embedded in the proof of `bbFold10_bound` as explicit per-step bound numerals.

## Axiom status

This file's headline theorems `bbMul_eq_mod_p` and `bbMul_field_correct` carry
only the standard kernel axioms (`propext`, `Classical.choice`, `Quot.sound`)
plus the LRAT certificate from a small number of per-step `bv_decide` calls
used (specifically, only at the `bbCsub` canonical/identity edges, which
`Poseidon2DiffuseExact` already cites). All goals closed, no
`native_decide`, no new custom axioms.

## Consequence for `Poseidon2DiffuseExact`

With `bbMul_eq_mod_p`, `pos2_internal_round_bitexact` in
`Poseidon2DiffuseExact` (which states a bit-level identity via `rfl`
on both sides of the `bbAdd`/`bbMul` chain) lifts to a per-lane identity over
`ZMod babyBearPrime`: the chain computes the field operations the
Plonky3 spec specifies, not just a syntactically identical BitVec computation.
The KAT for Poseidon2-BabyBear is then a corollary of a structurally proven
field identity, matching the Keccak / SHA-2 emitter pipelines' strength.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact

open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
  (bbP bbC bbM bbFold bbCsub bbReduce bbMul bbCsub_correct)

/-! ## 1. Constant toNat tags -/

/-- `bbC = 2^27 − 1 = 134217727` at the Nat level. -/
lemma bbC_toNat : (bbC).toNat = 134217727 := by decide

/-- `bbM = 2^31 − 1 = 2147483647` at the Nat level. -/
lemma bbM_toNat : (bbM).toNat = 2147483647 := by decide

/-- `bbP = p = 2013265921` at the Nat level. -/
lemma bbP_toNat : (bbP).toNat = 2013265921 := by decide

/-! ## 2. Nat-level shape of `bbFold` under the no-overflow bound -/

/-- **The `bbFold` step in Nat form**: for `x.toNat < 2^62`, no `% 2^64`
    overflow occurs, and `bbFold` reads as the exact integer expression
    `(x / 2^31) * (2^27 − 1) + (x mod 2^31)`. -/
lemma bbFold_toNat (x : BitVec 64) (hx : x.toNat < 4611686018427387904) :
    (bbFold x).toNat = (x.toNat / 2147483648) * 134217727 + x.toNat % 2147483648 := by
  unfold bbFold
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight,
      BitVec.toNat_and, bbC_toNat, bbM_toNat]
  show ((x.toNat >>> 31) * 134217727 % 18446744073709551616
        + (x.toNat &&& 2147483647)) % 18446744073709551616 = _
  have h1 : x.toNat >>> 31 < 2147483648 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have h3 : x.toNat >>> 31 * 134217727 < 18446744073709551616 := by nlinarith
  rw [Nat.mod_eq_of_lt h3]
  have hand : x.toNat &&& 2147483647 = x.toNat % 2147483648 := by
    have h : (2147483647 : Nat) = 2^31 - 1 := by norm_num
    rw [h]
    have := Nat.and_two_pow_sub_one_eq_mod x.toNat 31
    convert this using 2
  rw [hand]
  have hshr : x.toNat >>> 31 = x.toNat / 2147483648 := Nat.shiftRight_eq_div_pow _ _
  rw [hshr]
  apply Nat.mod_eq_of_lt
  have hmod : x.toNat % 2147483648 < 2147483648 := Nat.mod_lt _ (by norm_num)
  have hdiv : x.toNat / 2147483648 < 2147483648 := by
    apply Nat.div_lt_of_lt_mul; omega
  nlinarith

/-! ## 3. Modular invariance of one `bbFold` step -/

/-- **`bbFold` preserves the residue mod `p`** (the fold-reduction identity).
    For `x.toNat < 2^62`, `(bbFold x).toNat ≡ x.toNat (mod p)`. Direct `omega`
    consequence of `bbFold_toNat`: writing
    `x.toNat = q · 2^31 + r` with `q = x.toNat / 2^31`, `r = x.toNat % 2^31`,
    `(bbFold x).toNat = q · (2^27 − 1) + r = x.toNat − q · p`, since
    `2^31 − (2^27 − 1) = p`. -/
lemma bbFold_mod_p (x : BitVec 64) (hx : x.toNat < 4611686018427387904) :
    (bbFold x).toNat % 2013265921 = x.toNat % 2013265921 := by
  rw [bbFold_toNat x hx]
  have key : x.toNat = x.toNat / 2147483648 * 2147483648 + x.toNat % 2147483648 := by
    have := Nat.div_add_mod x.toNat 2147483648; omega
  conv_rhs => rw [key]
  omega

/-! ## 4. Per-step bound -/

/-- **Per-step shrinkage**: if `x.toNat < B` with `B ≤ 2^62`, then
    `(bbFold x).toNat < (B / 2^31) · (2^27 − 1) + 2^31`. The output's high part
    is bounded by `B / 2^31`, the low part by `2^31 − 1 < 2^31`. -/
lemma bbFold_bound (x : BitVec 64) (B : Nat) (hB : B ≤ 4611686018427387904)
    (hx : x.toNat < B) :
    (bbFold x).toNat < (B / 2147483648) * 134217727 + 2147483648 := by
  have hx62 : x.toNat < 4611686018427387904 := by omega
  rw [bbFold_toNat x hx62]
  have hmod : x.toNat % 2147483648 < 2147483648 := Nat.mod_lt _ (by norm_num)
  have hdiv : x.toNat / 2147483648 ≤ B / 2147483648 := by
    apply Nat.div_le_div_right; omega
  nlinarith

/-! ## 5. The 10-fold composition: bound and modular invariance -/

/-- The 10-fold composition `bbFold ∘ ... ∘ bbFold` (10×) as a definitional
    abbreviation, matching the unfolded chain in `Poseidon2Emit.bbReduce`. -/
def bbFold10 (x : BitVec 64) : BitVec 64 :=
  bbFold (bbFold (bbFold (bbFold (bbFold
    (bbFold (bbFold (bbFold (bbFold (bbFold x)))))))))

/-- The two-csub canonicalisation tail. -/
def bbCsub2 (r : BitVec 64) : BitVec 64 := bbCsub (bbCsub r)

/-- `bbReduce = bbCsub2 ∘ bbFold10` — the chain rewriting `bbReduce` as the
    composition of the two named blocks. By `rfl`. -/
lemma bbReduce_eq_csub2_fold10 (x : BitVec 64) :
    bbReduce x = bbCsub2 (bbFold10 x) := rfl

/-- **10-fold bound**: starting from `x.toNat < 2^62`, after 10 applications of
    `bbFold` the value is `< 2281701375`, which is `< 2 · p = 4026531842`.
    Concrete bound sequence (each step verified individually by `nlinarith`):
    `2^62 → 2^58+2^31 → 2^55+2^31 → 2^52+2^31 → 2^49+2^31 → 2^46+2^31 → 2^43+2^31 → 2^40+2^31 → 2^37+2^31 → 9·(2^27−1)+2^31 → 9·(2^27−1)+2^31`,
    settling at a fixed-point bound `< 2281701375`. -/
lemma bbFold10_bound (x : BitVec 64) (hx : x.toNat < 4611686018427387904) :
    (bbFold10 x).toNat < 2281701375 := by
  unfold bbFold10
  have h1 := bbFold_bound x 4611686018427387904 (le_refl _) hx
  have h2 := bbFold_bound (bbFold x) 288230376151711744 (by norm_num) (by omega)
  have h3 := bbFold_bound _ 18014400522747904 (by norm_num) (by omega)
  have h4 := bbFold_bound _ 1125902045937664 (by norm_num) (by omega)
  have h5 := bbFold_bound _ 70370891137024 (by norm_num) (by omega)
  have h6 := bbFold_bound _ 4400193961984 (by norm_num) (by omega)
  have h7 := bbFold_bound _ 277025388544 (by norm_num) (by omega)
  have h8 := bbFold_bound _ 19327352704 (by norm_num) (by omega)
  have h9 := bbFold_bound _ 3221225464 (by norm_num) (by omega)
  have h10 := bbFold_bound _ 2281701375 (by norm_num) (by omega)
  omega

/-- The intermediate values are all `< 2^62` (so `bbFold_mod_p` applies at each
    step). -/
lemma bbFold10_intermediate_lt_2_pow_62 (x : BitVec 64)
    (hx : x.toNat < 4611686018427387904) :
    (bbFold x).toNat < 4611686018427387904
      ∧ (bbFold (bbFold x)).toNat < 4611686018427387904
      ∧ (bbFold (bbFold (bbFold x))).toNat < 4611686018427387904
      ∧ (bbFold (bbFold (bbFold (bbFold x)))).toNat < 4611686018427387904
      ∧ (bbFold (bbFold (bbFold (bbFold (bbFold x))))).toNat < 4611686018427387904
      ∧ (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold x)))))).toNat < 4611686018427387904
      ∧ (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold x))))))).toNat < 4611686018427387904
      ∧ (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold x)))))))).toNat < 4611686018427387904
      ∧ (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold (bbFold x))))))))).toNat < 4611686018427387904 := by
  have h1 := bbFold_bound x 4611686018427387904 (le_refl _) hx
  have h2 := bbFold_bound (bbFold x) 288230376151711744 (by norm_num) (by omega)
  have h3 := bbFold_bound _ 18014400522747904 (by norm_num) (by omega)
  have h4 := bbFold_bound _ 1125902045937664 (by norm_num) (by omega)
  have h5 := bbFold_bound _ 70370891137024 (by norm_num) (by omega)
  have h6 := bbFold_bound _ 4400193961984 (by norm_num) (by omega)
  have h7 := bbFold_bound _ 277025388544 (by norm_num) (by omega)
  have h8 := bbFold_bound _ 19327352704 (by norm_num) (by omega)
  have h9 := bbFold_bound _ 3221225464 (by norm_num) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **10-fold modular invariance**: `(bbFold10 x).toNat ≡ x.toNat (mod p)` for
    `x.toNat < 2^62`. Iterates `bbFold_mod_p` 10 times, using the intermediate
    bounds. -/
lemma bbFold10_mod_p (x : BitVec 64) (hx : x.toNat < 4611686018427387904) :
    (bbFold10 x).toNat % 2013265921 = x.toNat % 2013265921 := by
  unfold bbFold10
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
    bbFold10_intermediate_lt_2_pow_62 x hx
  rw [bbFold_mod_p _ b9, bbFold_mod_p _ b8, bbFold_mod_p _ b7,
      bbFold_mod_p _ b6, bbFold_mod_p _ b5, bbFold_mod_p _ b4,
      bbFold_mod_p _ b3, bbFold_mod_p _ b2, bbFold_mod_p _ b1,
      bbFold_mod_p _ hx]

/-! ## 6. `bbCsub`: canonicalisation and identity at toNat level -/

/-- **`bbCsub` canonicalises `< 2p` to `< p` at the toNat level.** Re-export of
    `bbCsub_correct` pushed through `BitVec.toNat_umod`. -/
lemma bbCsub_toNat_of_lt_2p (r : BitVec 64) (hr : r.toNat < 2 * 2013265921) :
    (bbCsub r).toNat = r.toNat % 2013265921 := by
  have hr' : r < (2 * 2013265921 : BitVec 64) := by
    rw [BitVec.lt_def]
    have : (2 * 2013265921 : BitVec 64).toNat = 2 * 2013265921 := by decide
    rw [this]; exact hr
  rw [bbCsub_correct r hr', BitVec.toNat_umod]
  have : (2013265921 : BitVec 64).toNat = 2013265921 := by decide
  rw [this]

/-- **`bbCsub` is the identity on canonical reps** (`< p`) at the toNat level.
    Single per-step `bv_decide` at 64-bit width — fast. -/
lemma bbCsub_toNat_of_lt_p (r : BitVec 64) (hr : r.toNat < 2013265921) :
    (bbCsub r).toNat = r.toNat := by
  have hr' : r < (2013265921 : BitVec 64) := by
    rw [BitVec.lt_def]
    have : (2013265921 : BitVec 64).toNat = 2013265921 := by decide
    rw [this]; exact hr
  have : bbCsub r = r := by
    simp only [bbCsub, bbP]
    revert hr'
    bv_decide
  rw [this]

/-- **`bbCsub` of a `< 2p` input is canonical (`< p`).** -/
lemma bbCsub_lt_p_of_lt_2p (r : BitVec 64) (hr : r.toNat < 2 * 2013265921) :
    (bbCsub r).toNat < 2013265921 := by
  rw [bbCsub_toNat_of_lt_2p r hr]
  exact Nat.mod_lt _ (by norm_num)

/-! ## 7. `bbReduce`: 10 folds + 2 csubs equals reduction mod `p` -/

/-- **`bbReduce` canonicalises any `< 2^62` to `< p`.** -/
lemma bbReduce_lt_p (x : BitVec 64) (hx : x.toNat < 4611686018427387904) :
    (bbReduce x).toNat < 2013265921 := by
  rw [bbReduce_eq_csub2_fold10]
  unfold bbCsub2
  have h10 := bbFold10_bound x hx
  -- After 10 folds, value < 2281701375 < 2p, one csub canonicalises to < p,
  -- second csub is identity.
  have hcsub1 : (bbCsub (bbFold10 x)).toNat < 2013265921 := by
    apply bbCsub_lt_p_of_lt_2p; omega
  rw [bbCsub_toNat_of_lt_p _ hcsub1]
  exact hcsub1

/-- **`bbReduce` computes residue mod `p`** at the toNat level: for
    `x.toNat < 2^62`, `(bbReduce x).toNat = x.toNat mod p`. Combines
    `bbFold10_mod_p` (modular invariance) with `bbCsub` canonicalisation. -/
lemma bbReduce_toNat (x : BitVec 64) (hx : x.toNat < 4611686018427387904) :
    (bbReduce x).toNat = x.toNat % 2013265921 := by
  rw [bbReduce_eq_csub2_fold10]
  unfold bbCsub2
  have h10 := bbFold10_bound x hx
  have hmod10 := bbFold10_mod_p x hx
  -- bbCsub (bbFold10 x): input < 2p (since < 2281701375 < 2p), so output = input % p
  have hcsub1 : (bbCsub (bbFold10 x)).toNat = (bbFold10 x).toNat % 2013265921 := by
    apply bbCsub_toNat_of_lt_2p; omega
  have hcsub1_lt : (bbCsub (bbFold10 x)).toNat < 2013265921 := by
    rw [hcsub1]; exact Nat.mod_lt _ (by norm_num)
  -- bbCsub (bbCsub (bbFold10 x)): input < p, so output = input
  rw [bbCsub_toNat_of_lt_p _ hcsub1_lt, hcsub1, hmod10]

/-! ## 8. The headline: `bbMul` is field multiplication on canonical reps -/

/-- **No-overflow lemma**: for `a, b < p`, the BitVec product equals the Nat
    product. Since `p < 2^31`, `a.toNat · b.toNat < p² < 2^62 < 2^64`. -/
lemma mul_toNat_of_lt_p (a b : BitVec 64) (ha : a.toNat < 2013265921)
    (hb : b.toNat < 2013265921) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  nlinarith

/-- **`a · b < 2^62` for `a, b < p`** at toNat level. -/
lemma mul_lt_p_sq (a b : BitVec 64) (ha : a.toNat < 2013265921)
    (hb : b.toNat < 2013265921) :
    (a * b).toNat < 4611686018427387904 := by
  rw [mul_toNat_of_lt_p a b ha hb]
  nlinarith

/-- **`bbMul` canonicalises on canonical reps**: for `a, b < p`,
    `bbMul a b < p`. -/
lemma bbMul_lt_p_toNat (a b : BitVec 64) (ha : a.toNat < 2013265921)
    (hb : b.toNat < 2013265921) :
    (bbMul a b).toNat < 2013265921 := by
  show (bbReduce (a * b)).toNat < 2013265921
  exact bbReduce_lt_p (a * b) (mul_lt_p_sq a b ha hb)

/-- **`bbMul` equals field multiplication on canonical reps** (toNat form):
    for `a, b < p`, `(bbMul a b).toNat = (a.toNat · b.toNat) mod p`. -/
lemma bbMul_toNat (a b : BitVec 64) (ha : a.toNat < 2013265921)
    (hb : b.toNat < 2013265921) :
    (bbMul a b).toNat = a.toNat * b.toNat % 2013265921 := by
  show (bbReduce (a * b)).toNat = _
  rw [bbReduce_toNat (a * b) (mul_lt_p_sq a b ha hb), mul_toNat_of_lt_p a b ha hb]

/-! ## 9. The seam closure: `bbMul a b = (a * b) % bbP` at the BitVec level -/

/-- **Headline**: `bbMul` is the field multiplication on Baby Bear canonical
    representatives. For `a, b : BitVec 64` with `a, b < p`:

    * `bbMul a b < p` (canonical output), and
    * `bbMul a b = (a * b) % bbP` at the BitVec level (i.e. the BitVec product
      reduced modulo `bbP`).

    This discharges the `bbMul_field_correct_residual` seam stated in
    `Poseidon2DiffuseExact`: the 10-fold + 2-csub `bbReduce` chain
    computes the field reduction. -/
theorem bbMul_eq_mod_p (a b : BitVec 64) (ha : a < bbP) (hb : b < bbP) :
    bbMul a b < bbP ∧ bbMul a b = (a * b) % bbP := by
  -- Convert hypotheses to toNat form
  have ha' : a.toNat < 2013265921 := by
    rw [BitVec.lt_def] at ha; rwa [bbP_toNat] at ha
  have hb' : b.toNat < 2013265921 := by
    rw [BitVec.lt_def] at hb; rwa [bbP_toNat] at hb
  refine ⟨?_, ?_⟩
  · rw [BitVec.lt_def, bbP_toNat]
    exact bbMul_lt_p_toNat a b ha' hb'
  · apply BitVec.eq_of_toNat_eq
    rw [bbMul_toNat a b ha' hb', BitVec.toNat_umod, bbP_toNat,
        mul_toNat_of_lt_p a b ha' hb']

/-- **Direct restatement matching the seam in `Poseidon2DiffuseExact`.** -/
theorem bbMul_field_correct :
    ∀ (a b : BitVec 64), a < bbP → b < bbP →
      bbMul a b < bbP ∧ bbMul a b = (a * b) % bbP :=
  fun a b ha hb => bbMul_eq_mod_p a b ha hb

/-- **The seam `bbMul_field_correct_residual` from `Poseidon2DiffuseExact` is
    discharged.** -/
theorem bbMul_field_correct_residual_proved :
    Poseidon2DiffuseExact.bbMul_field_correct_residual :=
  bbMul_field_correct

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact
