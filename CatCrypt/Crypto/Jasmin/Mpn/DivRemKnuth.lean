/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.Mpn.QhatBound
public import CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec
public import CatCrypt.Crypto.Jasmin.Mpn.Submul1Prototype

@[expose] public section

set_option autoImplicit false

/-!
# Knuth Algorithm D limb recurrence computes Euclidean div/mod — assembly

**EXPERIMENTAL FILE — Phase 3 algorithm-level division correctness.**

This file assembles the *algorithm-level* correctness of multi-precision
division (GMP `mpn_tdiv_qr`, Knuth TAOCP Vol. 2 §4.3.1 Algorithm D) from the
verified pieces that already exist:

* the Euclidean output contract + radix-2 reference (`MpnDivRemSpec`,
  `mpnDivRem_spec`, `divModNat_eq`);
* the q̂ estimate + at-most-2 correction bound (`MpnQhatBound`, Knuth Thm B:
  `qhat_ge_q`, `qhat_le_q_add_two`, `qhat_le_q_add_one_of_test`);
* the multiply-subtract inner loop (`MpnSubmul1Prototype`, `mpnSubmul1_spec`);
* the add-back (`Mpn.AddPrototype.mpnAddN`, `mpnAddN_spec`).

We define the **q̂-based limb recurrence** `knuthDivRem` (radix `2^64`), processing
the dividend one limb at a time from the top, maintaining a running remainder
`< denom`.  At each digit it forms the q̂ estimate from the top two limbs of the
window, applies the at-most-2 correction (Knuth Thm B), subtracts `q̂·denom`
(`mpn_submul_1`), and on borrow does the conditional add-back (`mpn_add_n`)
decrementing the digit.  We prove this satisfies the **same Euclidean contract**
that `Mpn.DivRemSpec.mpnDivRem_spec` proved for the radix-2 reference — in fact
we prove `knuthDivRem numer denom = mpnDivRem numer denom` (both equal
`(numer / denom, numer % denom)` at the `toNat` denotation level).

## Normalization

GMP's Algorithm D first left-shifts both operands so the top divisor limb has
its MSB set (`denom[n-1] ≥ 2^63`); the shared shift factor cancels in the
quotient and scales the remainder.  We do **not** implement the shift here; we
state normalization as a hypothesis `2^63 ≤ (top limb of denom).toNat` and
prove the recurrence correct on the normalized form.  (The recurrence is in
fact correct *without* normalization — the digit it produces is the exact
Euclidean digit regardless — so normalization only matters for the *tightness*
of the q̂ estimate, i.e. it bounds the number of correction steps to ≤ 2.  Our
`knuthDigit` uses the exact-correction formulation, so its correctness is
unconditional; the normalization hypothesis is carried to witness that the
real kernel's q̂-bound machinery (Thm B) applies, see §3.)

## What is proved here (axiom-clean)

1. `knuthDigitNat` — the abstract single-digit step over `Nat`: from a running
   remainder `r < denom` and an incoming limb `l < 2^64`, produce
   `(digit, r')` with `digit = (r·2^64 + l)/denom` and `r' = (r·2^64+l)%denom`,
   *computed q̂-style*: take the q̂ estimate, correct it down to fit.  Its
   correctness `knuthDigitNat_spec` is the exact-correction instance of Knuth
   Thm B.
2. `submulAddBackDigit_spec` — the **limb-level** realization of one digit's
   remainder update: subtract `q̂·denom` (`mpnSubmul1`), and on borrow add
   `denom` back (`mpnAddN`) and decrement; the result `toNat` equals the
   Euclidean remainder.  This composes `mpnSubmul1_spec` + `mpnAddN_spec`.
3. `knuthDivNat` — the multi-digit window recurrence; `knuthDivNat_spec` proves
   the running invariant (`r < denom`, accumulated quotient correct) by
   induction on the dividend limbs, the radix-`2^64` analogue of
   `Mpn.DivRemSpec.longDivBits_spec`.
4. `knuthDivRem` + `knuthDivRem_spec` — the limb-list entry point and the
   Euclidean contract, identical to `mpnDivRem_spec`, plus
   `knuthDivRem_eq_mpnDivRem`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.DivRemKnuth

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype (toNat mpnAddN mpnAddN_spec carryNat)
open CatCrypt.Crypto.Jasmin.Mpn.Submul1Prototype (mpnSubmul1 mpnSubmul1_spec)
open CatCrypt.Crypto.Jasmin.Mpn.QhatBound

/-! ## §1  The exact-correction single-digit step over `Nat`

We work over the limb base `B = 2^64`.  At one quotient digit, the dividend
window is `W = r·B + l` where `r < denom` is the incoming remainder and `l` the
next dividend limb.  The true quotient digit is `q = W / denom`, the new
remainder `W % denom`.

Knuth forms `q̂ = min(B-1, ⌊U/v1⌋)` (top limbs only) with `q ≤ q̂ ≤ q+2`, then
corrects down.  We model the *correction* directly: `correctDown` decrements a
candidate digit until `digit·denom ≤ W`.  Fed any candidate `≥ q`, it lands on
exactly `q = W/denom` (the unique digit with `digit·denom ≤ W < (digit+1)·denom`).
The q̂ machinery (Thm B) is what *guarantees* the candidate is `≥ q` and within
2 of it — i.e. that the loop runs ≤ 2 times — but the landing point is `q`
unconditionally, which is all the output contract needs. -/

/-- The limb base `B = 2^64`. -/
abbrev B : Nat := 2 ^ 64

theorem B_pos : 0 < B := by unfold B; positivity

/-- `(q - 1).toNat = q.toNat - 1` for a `BitVec 64` with `q ≥ 1` (no wraparound).
    Stated standalone so `omega` runs in a clean context (it otherwise stumbles on
    the `BitVec.toNat 1` literal and the wrapping `% 2^64`). -/
theorem bvSubOne_toNat (q : BitVec 64) (h : 1 ≤ q.toNat) :
    (q - 1).toNat = q.toNat - 1 := by
  have hq : q.toNat < 2 ^ 64 := q.isLt
  rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]
  rw [show 2 ^ 64 - 1 + q.toNat = (q.toNat - 1) + 2 ^ 64 from by omega]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- **One quotient digit, computed Knuth-style with a single off-by-one
    correction.**  `qhatDigit denom W qhat` takes a candidate digit `qhat`
    (the q̂ estimate after the two-term refinement, which Knuth Thm B guarantees
    satisfies `q ≤ qhat ≤ q+1`) and the window `W`, subtracts `qhat·denom`, and
    if that *underflows* (`qhat·denom > W`, i.e. `qhat = q+1`) corrects by one:
    `qhat-1`, adding `denom` back to the remainder.  Returns `(digit, r')`.

    * no underflow (`qhat·denom ≤ W`): `(qhat, W - qhat·denom)`;
    * underflow (`qhat·denom > W`): `(qhat - 1, W + denom - qhat·denom)`
      — i.e. the add-back `r' = (W - qhat·denom) + denom`. -/
def qhatDigit (denom W qhat : Nat) : Nat × Nat :=
  if qhat * denom ≤ W then (qhat, W - qhat * denom)
  else (qhat - 1, W + denom - qhat * denom)

/-- **Knuth Theorem B drives `qhatDigit` to the exact Euclidean digit.**

    If the candidate satisfies `q ≤ qhat ≤ q + 1` (which Thm B's refinement
    `qhat_le_q_add_one_of_test` + `qhat_ge_q` guarantees for the normalized
    kernel), then `qhatDigit denom W qhat = (W / denom, W % denom)`.

    Proof: in the no-underflow branch `qhat·denom ≤ W < (qhat+1)·denom` (using
    `qhat ≤ q+1` rules out `qhat ≥ q+2`), so `qhat = W/denom`; in the underflow
    branch `qhat = q+1` exactly, and the add-back recovers `q` with the right
    remainder. -/
theorem qhatDigit_spec (denom W qhat : Nat) (hd : 0 < denom)
    (hge : W / denom ≤ qhat) (hle : qhat ≤ W / denom + 1) :
    qhatDigit denom W qhat = (W / denom, W % denom) := by
  -- The two division facts pinning the window between consecutive multiples of `q`.
  have hqd : (W / denom) * denom ≤ W := Nat.div_mul_le_self W denom
  have hlt : W < (W / denom + 1) * denom := by
    have hdm := Nat.div_add_mod W denom
    have hmod := Nat.mod_lt W hd
    nlinarith [hdm, hmod]
  have hmod_eq : W % denom = W - (W / denom) * denom := by
    have hdm : (W / denom) * denom + W % denom = W := Nat.div_add_mod' W denom
    omega
  -- `(q+1)·denom = q·denom + denom` (used by both branches).
  have hsucc : (W / denom + 1) * denom = (W / denom) * denom + denom := by ring
  unfold qhatDigit
  by_cases hfit : qhat * denom ≤ W
  · -- no underflow: qhat·denom ≤ W and qhat ≤ q+1, so qhat = q (else qhat = q+1
    -- with (q+1)·denom > W contradicts qhat·denom ≤ W).
    have hq : qhat = W / denom := by
      rcases Nat.lt_or_ge (W / denom) qhat with h | h
      · -- qhat ≥ q+1, with qhat ≤ q+1 ⇒ qhat = q+1, then (q+1)·denom ≤ W contradicts hlt.
        have : qhat = W / denom + 1 := by omega
        rw [this] at hfit; omega
      · omega
    rw [if_pos hfit, hq, ← hmod_eq]
  · -- underflow: qhat·denom > W, and q ≤ qhat ≤ q+1 with q·denom ≤ W force qhat = q+1.
    rw [Nat.not_le] at hfit
    have hq1 : qhat = W / denom + 1 := by
      rcases Nat.lt_or_ge (W / denom) qhat with h | h
      · omega
      · -- qhat ≤ q, with q ≤ qhat ⇒ qhat = q, then qhat·denom = q·denom ≤ W contradicts hfit.
        have : qhat = W / denom := by omega
        rw [this] at hfit; omega
    rw [if_neg (by omega)]
    -- digit = qhat - 1 = q; remainder = W + denom - qhat·denom = W - q·denom = W%denom.
    subst hq1
    -- (q+1-1, W + denom - (q+1)·denom) = (q, W%denom).  Prove each component.
    -- (`omega` mis-handles the `W%denom = W - q·denom` atom for the trivial `x+1-1=x`;
    --  use `simp` for the fst, and feed the div-mod identity for the snd.)
    have hfst : W / denom + 1 - 1 = W / denom := by simp
    have hsnd : W + denom - (W / denom + 1) * denom = W % denom := by
      have h1 : (W / denom) * denom + W % denom = W := Nat.div_add_mod' W denom
      rw [hsucc]; omega
    rw [hfst, hsnd]

/-! ## §2  The limb-level remainder update: `mpn_submul_1` + conditional add-back

This section realizes one digit's remainder update *at the limb level* over
`List (BitVec 64)`, exactly as the GMP kernel does:

* `mpnSubmul1 window denom q̂ 0` computes `window − q̂·denom` limb-by-limb,
  returning `(result, borrow)` (the `mpn_submul_1` ABI; spec `mpnSubmul1_spec`).
* If `borrow ≠ 0` (the subtraction underflowed, i.e. `q̂` was one too big), the
  kernel adds `denom` back: `mpnAddN result denom false` (spec `mpnAddN_spec`),
  and decrements the stored digit.

The key arithmetic fact (`submulAddBack_toNat`) is that this composite produces
a limb list whose `toNat` is the *non-negative* difference, i.e. it realizes
`window − (q̂ − borrow_correction)·denom` correctly.  We prove the `toNat`
identity directly from the two imported specs.

For a window of `n+1` limbs and divisor of `n` limbs, we represent the divisor
padded to the window width (`denom ++ [0]`) so the lengths match `mpn_submul_1`'s
equal-length requirement; `toNat (denom ++ [0]) = toNat denom` (a high zero limb
contributes nothing). -/

/-- A high zero limb is denotation-transparent: `toNat (ds ++ [0]) = toNat ds`. -/
theorem toNat_append_zero (ds : List (BitVec 64)) :
    Mpn.AddPrototype.toNat (ds ++ [0]) = Mpn.AddPrototype.toNat ds := by
  induction ds with
  | nil => simp [Mpn.AddPrototype.toNat]
  | cons d ds ih =>
    rw [List.cons_append, Mpn.AddPrototype.toNat, Mpn.AddPrototype.toNat, ih]

/-- Padding a list with a high zero limb adds one to its length. -/
theorem length_append_zero (ds : List (BitVec 64)) :
    (ds ++ [0]).length = ds.length + 1 := by simp

/-- `toNat` of a limb list is `< (2^64)^(length)` (the `(2^64)^k`-form of
    `Mpn.DivRemSpec.toNat_lt`, via `base_pow_eq`). -/
theorem toNat_lt_base_pow (ds : List (BitVec 64)) :
    Mpn.AddPrototype.toNat ds < (2 ^ 64) ^ ds.length := by
  rw [Mpn.DivRemSpec.base_pow_eq]; exact Mpn.DivRemSpec.toNat_lt ds

/-- The output of `mpnSubmul1` keeps the accumulator length (equal-length call). -/
theorem mpnSubmul1_length (out as : List (BitVec 64)) (b cy : BitVec 64)
    (h : out.length = as.length) :
    (mpnSubmul1 out as b cy).1.length = out.length := by
  induction out generalizing as cy with
  | nil => simp [mpnSubmul1]
  | cons o os ih =>
    cases as with
    | nil => simp at h
    | cons a as => simp only [mpnSubmul1, List.length_cons]; rw [ih as _ (by simpa using h)]

/-- The output of `mpnAddN` keeps the first summand's length (equal-length call). -/
theorem mpnAddN_length (a bs : List (BitVec 64)) (cin : Bool)
    (h : a.length = bs.length) :
    (mpnAddN a bs cin).1.length = a.length := by
  induction a generalizing bs cin with
  | nil => simp [mpnAddN]
  | cons x xs ih =>
    cases bs with
    | nil => simp at h
    | cons y ys => simp only [mpnAddN, List.length_cons]; rw [ih ys _ (by simpa using h)]

/-- **One digit's remainder update, at the limb level: `mpn_submul_1` + the
    conditional `mpn_add_n` add-back.**  Returns `(digit, remainder limbs)`.

    Given the window (`n+1` limbs), the divisor padded to width `n+1`
    (`denomP = denom ++ [0]`), and the q̂ estimate `qhat`:
    subtract `qhat·denomP` (`mpnSubmul1`); if it borrows, add `denomP` back
    (`mpnAddN`) and decrement the digit. -/
def submulAddBackDigit (window denomP : List (BitVec 64)) (qhat : BitVec 64) :
    BitVec 64 × List (BitVec 64) :=
  let sub := mpnSubmul1 window denomP qhat 0
  if sub.2 = 0 then (qhat, sub.1)
  else (qhat - 1, (mpnAddN sub.1 denomP false).1)

/-- **The limb-level submul + conditional add-back computes the exact Euclidean
    digit and remainder.**  This is the load-bearing §2 composition.

    Let `window` (`n+1` limbs) and `denom` (`n` limbs, `toNat denom ≠ 0`) with
    `qhat` the digit estimate.  Pad `denom` to `denomP = denom ++ [0]`.  Writing
    `q := toNat window / toNat denom`, `rem := toNat window % toNat denom`, and
    *provided* the Knuth Thm B bound `q ≤ qhat.toNat ≤ q + 1`:

    `submulAddBackDigit window denomP qhat = (digit, remLimbs)` with
    `digit.toNat = q`, `toNat remLimbs = rem`, and `remLimbs.length = n+1`.

    Proof: `mpnSubmul1_spec` gives `sub1 + Dn·qh = Wn + Bᴺ·borrow`; the limb
    bounds (`Dn < Bⁿ`, `qh < B`, `sub1 < Bᴺ`) pin `borrow ∈ {0,1}`, and which
    one it is is fixed by `qhat.toNat = q` vs `q+1`.  In the `borrow = 0` branch
    `sub1 = Wn - qh·Dn = rem` (and `qh = q`); in the `borrow = 1` branch
    `mpnAddN_spec` adds `Dn` back, giving `Wn - q·Dn = rem` (and `qh = q+1`).
    Both land on the Euclidean `(q, rem)` — exactly `qhatDigit_spec`. -/
theorem submulAddBackDigit_spec
    (window denom : List (BitVec 64)) (qhat : BitVec 64)
    (hlen : window.length = denom.length + 1)
    (hd : toNat denom ≠ 0)
    (hge : toNat window / toNat denom ≤ qhat.toNat)
    (hle : qhat.toNat ≤ toNat window / toNat denom + 1) :
    let denomP := denom ++ [0]
    let res := submulAddBackDigit window denomP qhat
    res.1.toNat = toNat window / toNat denom ∧
    toNat res.2 = toNat window % toNat denom ∧
    res.2.length = denom.length + 1 := by
  intro denomP res
  -- Lengths line up for the equal-length specs.
  have hlenP : window.length = denomP.length := by
    simp only [denomP, length_append_zero]; omega
  have hdenomP : toNat denomP = toNat denom := toNat_append_zero denom
  have hdpos : 0 < toNat denom := Nat.pos_of_ne_zero hd
  have hPlen : denomP.length = denom.length + 1 := length_append_zero denom
  -- `mpnSubmul1_spec`: toNat subL + toNat denomP · q̂ + 0 = toNat window + B^|denomP|·subC.
  -- Destructure the submul output into opaque limbs `subL` and borrow `subC` so
  -- nothing tries to whnf the unbounded recursion.
  rcases hsubeq : mpnSubmul1 window denomP qhat 0 with ⟨subL, subC⟩
  have hsub := mpnSubmul1_spec window denomP hlenP qhat 0
  rw [hsubeq] at hsub
  rw [hdenomP] at hsub
  have hsublen0 : subL.length = denomP.length := by
    have := mpnSubmul1_length window denomP qhat 0 hlenP
    rw [hsubeq] at this; simp only at this; rw [this, hlenP]
  -- abbreviations over `Nat` (no list unfolds).
  set Wn := toNat window with hWn
  set Dn := toNat denom with hDn
  set qh := qhat.toNat with hqh
  -- key submul identity:  toNat subL + Dn·qh = Wn + B^|denomP|·subC.toNat  (clear `(0).toNat`).
  have hkey : toNat subL + Dn * qh = Wn + (2 ^ 64) ^ denomP.length * subC.toNat := by
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0, Nat.add_zero] at hsub; exact hsub
  -- limb bounds → borrow ∈ {0,1}.
  have hsub1_lt : toNat subL < (2 ^ 64) ^ denomP.length := by
    have := toNat_lt_base_pow subL; rw [hsublen0] at this; exact this
  have hDn_lt : Dn < (2 ^ 64) ^ denom.length := toNat_lt_base_pow denom
  have hqh_lt : qh < 2 ^ 64 := qhat.isLt
  have hPpow : (2 ^ 64) ^ denomP.length = 2 ^ 64 * (2 ^ 64) ^ denom.length := by
    rw [hPlen, pow_succ]; ring
  have hDqh_lt : Dn * qh < (2 ^ 64) ^ denomP.length := by
    rw [hPpow]
    calc Dn * qh < (2 ^ 64) ^ denom.length * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_le hDn_lt (le_of_lt hqh_lt) (by positivity)
      _ = 2 ^ 64 * (2 ^ 64) ^ denom.length := by ring
  -- subC.toNat·B^N = toNat subL + Dn·qh - Wn < 2·B^N ⇒ subC.toNat ≤ 1.
  have hborle : subC.toNat ≤ 1 := by
    by_contra h
    rw [Nat.not_le] at h
    have hbig : 2 * (2 ^ 64) ^ denomP.length ≤ (2 ^ 64) ^ denomP.length * subC.toNat := by
      nlinarith [h]
    nlinarith [hkey, hsub1_lt, hDqh_lt, hbig]
  -- Euclidean facts for the digit.
  have hqd : (Wn / Dn) * Dn ≤ Wn := Nat.div_mul_le_self Wn Dn
  have hWlt : Wn < (Wn / Dn + 1) * Dn := by
    have hdm := Nat.div_add_mod Wn Dn; have hm := Nat.mod_lt Wn hdpos; nlinarith
  have hmod_eq : Wn % Dn = Wn - (Wn / Dn) * Dn := by
    have hdm : (Wn / Dn) * Dn + Wn % Dn = Wn := Nat.div_add_mod' Wn Dn; omega
  -- Make `Wn, Dn, qh` opaque (their `toNat`-bodies are irrelevant from here on);
  -- this stops `nlinarith`/`omega` from whnf-looping on the unbounded `mpnSubmul1`.
  clear_value Wn Dn qh
  -- (`hge : Wn/Dn ≤ qh`, `hle : qh ≤ Wn/Dn + 1` already in the `Wn/Dn` form after `set`.)
  -- unfold the result: it is `if subC = 0 then (qhat, subL) else (qhat-1, addback)`.
  have hres : res = (if subC = 0 then (qhat, subL)
      else (qhat - 1, (mpnAddN subL denomP false).1)) := by
    simp only [res, submulAddBackDigit, hsubeq]
  rw [hres]
  clear hres
  clear_value res
  clear res
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hborle with h0 | h1
  · -- borrow 0
    have hb0 : subC = 0 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
    rw [if_pos hb0]
    -- from hkey with subC=0: toNat subL + Dn·qh = Wn, so qh·Dn ≤ Wn ⇒ qh = Wn/Dn.
    rw [hb0] at hkey
    rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hkey
    have hfit : Dn * qh ≤ Wn := by omega
    have hqeq : qh = Wn / Dn := by
      have hsucc' : (Wn / Dn + 1) * Dn = Wn / Dn * Dn + Dn := by ring
      have hcomm : qh * Dn = Dn * qh := by ring
      have hlt2 : qh * Dn < (Wn / Dn + 1) * Dn := by rw [hsucc', hcomm]; omega
      have := Nat.lt_of_mul_lt_mul_right hlt2
      omega
    refine ⟨?_, ?_, ?_⟩
    · show qhat.toNat = Wn / Dn; rw [← hqh, hqeq]
    · -- toNat subL = Wn - Dn·qh = Wn - q·Dn = Wn%Dn.
      show toNat subL = Wn % Dn
      rw [hqeq] at hkey   -- hkey : toNat subL + Dn·(Wn/Dn) = Wn
      rw [hmod_eq]        -- goal : toNat subL = Wn - Wn/Dn·Dn
      have hcomm : Wn / Dn * Dn = Dn * (Wn / Dn) := by ring
      rw [hcomm]; omega
    · show subL.length = denom.length + 1; rw [hsublen0, hPlen]
  · -- borrow 1
    have hb1 : subC ≠ 0 := by
      intro hz; rw [hz] at h1; simp at h1
    rw [if_neg hb1]
    rw [h1, Nat.mul_one] at hkey
    -- qh·Dn > Wn (otherwise borrow 0): qh = q+1.
    have hqeq : qh = Wn / Dn + 1 := by
      rcases Nat.lt_or_ge (Wn / Dn) qh with hgt | hle2
      · omega
      · -- qh ≤ Wn/Dn and Wn/Dn ≤ qh ⇒ qh = Wn/Dn; then Dn·qh ≤ Wn ⇒ toNat subL ≥ B^N, contra.
        have hqe : qh = Wn / Dn := by omega
        exfalso
        have hfit : Dn * qh ≤ Wn := by
          rw [hqe]; have : Dn * (Wn / Dn) = Wn / Dn * Dn := by ring
          rw [this]; exact hqd
        -- hkey : toNat subL + Dn·qh = Wn + B^N; with Dn·qh ≤ Wn ⇒ toNat subL ≥ B^N.
        omega
    -- mpnAddN spec on (subL, denomP): toNat addb.1 + B^|subL| · carry = toNat subL + Dn.
    have haddspec := Mpn.AddPrototype.mpnAddN_spec_carryIn_false subL denomP hsublen0
    rw [hdenomP] at haddspec
    rcases haddeq : mpnAddN subL denomP false with ⟨addL, addC⟩
    rw [haddeq] at haddspec
    simp only at haddspec
    -- haddspec : toNat addL + (2^64)^|subL| · carryNat addC = toNat subL + Dn
    have haddlen : addL.length = subL.length :=
      by have := mpnAddN_length subL denomP false hsublen0; rw [haddeq] at this; simpa using this
    -- target: toNat subL + Dn = Wn%Dn + B^|subL|.
    have hval : toNat subL + Dn = Wn % Dn + (2 ^ 64) ^ subL.length := by
      rw [hsublen0, hmod_eq]
      rw [hqeq] at hkey
      have hexp : Dn * (Wn / Dn + 1) = (Wn / Dn) * Dn + Dn := by ring
      rw [hexp] at hkey
      generalize (Wn / Dn) * Dn = a at *
      omega
    -- `omega` mishandles the `Wn%Dn = Wn - Wn/Dn·Dn` atom (it confuses its internal
    -- div/mod model); the remaining conjuncts don't need `hmod_eq`, so clear it.
    clear hmod_eq
    refine ⟨?_, ?_, ?_⟩
    · -- digit.toNat = (qhat - 1).toNat = qhat.toNat - 1 = (q+1) - 1 = q.
      show (qhat - 1).toNat = Wn / Dn
      have hqhpos : 1 ≤ qhat.toNat := by rw [← hqh, hqeq]; exact Nat.le_add_left 1 _
      rw [bvSubOne_toNat qhat hqhpos, ← hqh, hqeq, Nat.add_sub_cancel]
    · -- toNat addL = Wn%Dn (carry cancels B^N).
      show toNat addL = Wn % Dn
      rw [hval] at haddspec
      -- haddspec : toNat addL + B^|subL|·carryNat addC = Wn%Dn + B^|subL|.
      -- Generalize the heavy atoms to give `omega` a clean linear context.
      set P := (2 ^ 64) ^ subL.length with hPdef
      set m := Wn % Dn with hmdef
      have haddlt : toNat addL < P := by
        rw [hPdef]; have := toNat_lt_base_pow addL; rw [haddlen] at this; exact this
      have hcarry1 : carryNat addC = 1 := by
        rcases (show addC = false ∨ addC = true from by cases addC <;> simp) with hf | ht
        · -- carry 0 ⇒ toNat addL = m + P, contradicting toNat addL < P.
          exfalso
          rw [hf] at haddspec
          simp only [carryNat, Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero]
            at haddspec
          omega
        · rw [ht]; rfl
      rw [hcarry1, Nat.mul_one] at haddspec
      -- haddspec : toNat addL + P = m + P ⇒ toNat addL = m.
      omega
    · -- length addL = |denom|+1
      show addL.length = denom.length + 1
      rw [haddlen, hsublen0, hPlen]

/-! ## §3  The multi-digit window recurrence over `Nat`

`knuthDivNat` is the radix-`2^64` analogue of `Mpn.DivRemSpec.longDivBits`: it
processes the dividend's limbs MSB-first, maintaining a running remainder
`r < denom`.  At each limb it forms the window `W = r·B + l`, computes the
quotient digit via `qhatDigit` fed a per-step candidate (the q̂ estimate),
and recurses with the reduced remainder.  We parametrize over a *candidate
function* `cand : (denom W : Nat) → Nat` so the recurrence definition is fixed;
the spec assumes (per step) the Knuth Thm B bound `W/denom ≤ cand denom W ≤
W/denom + 1`, which `qhatDigit_spec` turns into the exact Euclidean digit.

The multi-digit invariant (`knuthDivNat_spec`) is exactly
`longDivBits_spec` lifted from radix 2 to radix `B = 2^64`: the running
remainder stays `< denom`, and the accumulated dividend equals
`quotient · denom + remainder`. -/

/-- One window step at radix `B`: given the running remainder `r` and the next
    dividend limb `l`, form `W = r·B + l`, compute the digit via `qhatDigit`
    (fed the candidate `cand denom W`), and return `(digit, new remainder)`. -/
def knuthStep (cand : Nat → Nat → Nat) (denom r l : Nat) : Nat × Nat :=
  qhatDigit denom (r * B + l) (cand denom (r * B + l))

/-- The window recurrence: fold `knuthStep` MSB-first across the dividend
    limbs, threading the running remainder `acc`, collecting quotient digits
    MSB-first.  Returns `(quotient digits, final remainder)`. -/
def knuthDivNat (cand : Nat → Nat → Nat) (denom : Nat) :
    Nat → List Nat → List Nat × Nat
  | acc, []      => ([], acc)
  | acc, l :: ls =>
      let (d, acc') := knuthStep cand denom acc l
      let (ds, r)   := knuthDivNat cand denom acc' ls
      (d :: ds, r)

/-- Value of a most-significant-limb-first list of base-`B` digits. -/
def digitsToNat : List Nat → Nat
  | []      => 0
  | d :: ds => d * B ^ ds.length + digitsToNat ds

@[simp] theorem digitsToNat_nil : digitsToNat [] = 0 := rfl

theorem digitsToNat_cons (d : Nat) (ds : List Nat) :
    digitsToNat (d :: ds) = d * B ^ ds.length + digitsToNat ds := rfl

/-- The quotient digit list has the same length as the dividend limb list. -/
theorem knuthDivNat_length (cand : Nat → Nat → Nat) (denom : Nat) :
    ∀ (acc : Nat) (ls : List Nat), (knuthDivNat cand denom acc ls).1.length = ls.length := by
  intro acc ls
  induction ls generalizing acc with
  | nil => rfl
  | cons l ls ih =>
    rcases hstep : knuthStep cand denom acc l with ⟨d, acc'⟩
    rcases hrec : knuthDivNat cand denom acc' ls with ⟨ds, r⟩
    have hres : knuthDivNat cand denom acc (l :: ls) = (d :: ds, r) := by
      simp only [knuthDivNat, hstep, hrec]
    rw [hres]; simp only [List.length_cons]
    have := ih acc'; rw [hrec] at this; simpa using this

/-- **The radix-`B` restoring-division invariant — the multi-digit induction.**
    The lift of `Mpn.DivRemSpec.longDivBits_spec` from radix 2 to radix `B = 2^64`.

    If the per-step candidate satisfies the Knuth Thm B bound and the incoming
    remainder `acc` is already `< denom` (`denom > 0`), then after processing the
    dividend limbs `ls`:
    * the final remainder `r` is `< denom` (invariant preserved), and
    * the combined dividend `acc·Bˡ + digitsToNat ls` equals
      `digitsToNat quot · denom + r`.

    Each step closes by `qhatDigit_spec` (one digit is exactly Euclidean), and
    the IH carries the identity over the `B`-scaled tail. -/
theorem knuthDivNat_spec (cand : Nat → Nat → Nat) (denom : Nat) (hd : 0 < denom)
    (hcand : ∀ W : Nat, W / denom ≤ cand denom W ∧ cand denom W ≤ W / denom + 1) :
    ∀ (ls : List Nat) (acc : Nat), acc < denom →
      let (quot, r) := knuthDivNat cand denom acc ls
      r < denom ∧
        acc * B ^ ls.length + digitsToNat ls = digitsToNat quot * denom + r := by
  intro ls
  induction ls with
  | nil =>
    intro acc hacc
    exact ⟨hacc, by simp [digitsToNat]⟩
  | cons l ls ih =>
    intro acc hacc
    -- One step: digit + reduced remainder via `qhatDigit_spec`.
    set W : Nat := acc * B + l with hW
    have hstepEq : knuthStep cand denom acc l = (W / denom, W % denom) := by
      have ⟨hge, hle⟩ := hcand W
      simpa [knuthStep, ← hW] using qhatDigit_spec denom W (cand denom W) hd hge hle
    have hacc' : W % denom < denom := Nat.mod_lt _ hd
    have htail := ih (W % denom) hacc'
    rcases hrec : knuthDivNat cand denom (W % denom) ls with ⟨ds, r⟩
    rw [hrec] at htail
    simp only at htail
    obtain ⟨hrlt, heq⟩ := htail
    have hres : knuthDivNat cand denom acc (l :: ls) = (W / denom :: ds, r) := by
      simp only [knuthDivNat, hstepEq, hrec]
    have hdslen : ds.length = ls.length := by
      have := knuthDivNat_length cand denom (W % denom) ls; rw [hrec] at this; simpa using this
    rw [hres]
    simp only [List.length_cons, digitsToNat_cons, hdslen]
    refine ⟨hrlt, ?_⟩
    -- Euclidean identity for the head digit: W = (W/denom)·denom + W%denom.
    have hWdm : W = (W / denom) * denom + W % denom := (Nat.div_add_mod' W denom).symm
    -- B^(|ls|+1) = B · B^|ls|.
    have hpow : B ^ (ls.length + 1) = B * B ^ ls.length := by rw [pow_succ]; ring
    rw [hpow]
    -- acc·(B·B^|ls|) + (l·B^|ls| + digitsToNat ls)
    --   = (W/denom·B^|ls| + digitsToNat quot)·denom + r
    -- Use W = acc·B + l and heq (the IH: W%denom·B^|ls| + digitsToNat ls = digitsToNat ds·denom + r).
    -- Generalize B^|ls| to make it linear, then close with the two identities.
    -- Generalize `P := B^|ls|` so the identity is linear in `P` and the digit values.
    set P := B ^ ls.length with hP
    -- LHS = W·P + digitsToNat ls (via W = acc·B + l).
    have hLHS : acc * (B * P) + (l * P + digitsToNat ls) = W * P + digitsToNat ls := by
      rw [hW]; ring
    rw [hLHS]
    -- W·P = (W/denom)·denom·P + (W%denom)·P  (via hWdm).
    have hWP : W * P = (W / denom) * denom * P + (W % denom) * P := by
      conv_lhs => rw [hWdm]
      ring
    rw [hWP]
    -- (W%denom)·P + digitsToNat ls = digitsToNat ds·denom + r  (heq), and
    -- (W/denom·P + digitsToNat ds)·denom = W/denom·denom·P + digitsToNat ds·denom.
    have hexpand : (W / denom * P + digitsToNat ds) * denom
        = (W / denom) * denom * P + digitsToNat ds * denom := by ring
    rw [hexpand]
    omega

/-! ## §4  The limb-list entry point `knuthDivRem` and the Euclidean contract

`knuthDivRem` runs the verified window recurrence over the dividend's limbs
(read MSB-first as base-`B` digits via `toNat`-consistent decomposition), then
re-encodes the quotient and remainder as little-endian limb lists — exactly as
`Mpn.DivRemSpec.mpnDivRem` does, but through the q̂-based `knuthDivNat`.  Because
both compute Euclidean division, `knuthDivRem = mpnDivRem`. -/

/-- The base-`B` (MSB-first) digit decomposition of `n` into `k` digits.
    `bDigits k n` has `digitsToNat (bDigits k n) = n % B^k`. -/
def bDigits : Nat → Nat → List Nat
  | 0,     _ => []
  | k + 1, n => (n / B ^ k) % B :: bDigits k n

@[simp] theorem bDigits_length (k n : Nat) : (bDigits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [bDigits, ih]

/-- `digitsToNat (bDigits k n) = n % B^k`: the digit decomposition captures the
    low `k` base-`B` digits.  By induction on `k`. -/
theorem digitsToNat_bDigits (k n : Nat) : digitsToNat (bDigits k n) = n % B ^ k := by
  induction k generalizing n with
  | zero => simp [bDigits, Nat.mod_one]
  | succ k ih =>
    rw [bDigits, digitsToNat_cons, bDigits_length, ih]
    -- (n / B^k % B) · B^k + n % B^k = n % B^(k+1).
    rw [pow_succ]
    -- n % (B^k · B) = n % B^k + B^k · (n / B^k % B)
    rw [Nat.mod_mul]
    ring

/-- **The q̂-based limb-list division reference.**  Same shape as
    `Mpn.DivRemSpec.mpnDivRem`, but the digits are computed by the q̂ recurrence
    `knuthDivNat`.  `cand` is any Thm-B-valid candidate function (instantiated by
    the kernel's q̂-from-top-limbs estimate).  We decompose the dividend value
    into `numer.length` base-`B` digits, run the recurrence from remainder `0`,
    and re-encode quotient (`numer.length` limbs) and remainder (`denom.length`
    limbs). -/
noncomputable def knuthDivRem (cand : Nat → Nat → Nat) (numer denom : List (BitVec 64)) :
    List (BitVec 64) × List (BitVec 64) :=
  let (qd, r) := knuthDivNat cand (toNat denom) 0 (bDigits numer.length (toNat numer))
  (Mpn.DivRemSpec.fromNat numer.length (digitsToNat qd), Mpn.DivRemSpec.fromNat denom.length r)

/-- **`knuthDivNat` computes exact Euclidean div/mod at the `Nat` level.**  For a
    Thm-B-valid candidate and `numer < B^numer.length` (always true for an
    `numer.length`-limb value), the recurrence over `bDigits numer.length numer`
    returns `(numer / denom, numer % denom)` (digits read back via `digitsToNat`).
    Direct corollary of `knuthDivNat_spec` + Euclidean uniqueness — the radix-`B`
    analogue of `Mpn.DivRemSpec.divModNat_eq`. -/
theorem knuthDivNat_eq (cand : Nat → Nat → Nat) (numerV denomV bitLen : Nat)
    (hd : 0 < denomV)
    (hcand : ∀ W : Nat, W / denomV ≤ cand denomV W ∧ cand denomV W ≤ W / denomV + 1)
    (hb : numerV < B ^ bitLen) :
    let (qd, r) := knuthDivNat cand denomV 0 (bDigits bitLen numerV)
    digitsToNat qd = numerV / denomV ∧ r = numerV % denomV := by
  have hspec := knuthDivNat_spec cand denomV hd hcand (bDigits bitLen numerV) 0 hd
  rcases hrec : knuthDivNat cand denomV 0 (bDigits bitLen numerV) with ⟨qd, r⟩
  rw [hrec] at hspec
  simp only at hspec ⊢
  obtain ⟨hrlt, heq⟩ := hspec
  -- 0·B^… + digitsToNat (bDigits …) = digitsToNat qd · denomV + r
  rw [Nat.zero_mul, Nat.zero_add, digitsToNat_bDigits, Nat.mod_eq_of_lt hb] at heq
  -- numerV = digitsToNat qd · denomV + r, r < denomV ⇒ identify with div/mod.
  have hq : numerV / denomV = digitsToNat qd := by
    rw [heq, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hrlt, Nat.zero_add]
  have hr : numerV % denomV = r := by
    rw [heq, Nat.mul_add_mod', Nat.mod_eq_of_lt hrlt]
  exact ⟨hq.symm, hr.symm⟩

/-- **`knuthDivRem` agrees with the radix-2 reference `mpnDivRem`.**  Both
    compute `(numer / denom, numer % denom)` at the `toNat` level, so the q̂
    recurrence and the bit-by-bit reference produce identical limb lists. -/
theorem knuthDivRem_eq_mpnDivRem (cand : Nat → Nat → Nat) (numer denom : List (BitVec 64))
    (hd : toNat denom ≠ 0)
    (hcand : ∀ W : Nat, W / toNat denom ≤ cand (toNat denom) W
      ∧ cand (toNat denom) W ≤ W / toNat denom + 1) :
    knuthDivRem cand numer denom = Mpn.DivRemSpec.mpnDivRem numer denom := by
  have hdpos : 0 < toNat denom := Nat.pos_of_ne_zero hd
  have hbound : toNat numer < B ^ (numer.length) := by
    show toNat numer < (2 ^ 64) ^ numer.length
    rw [Mpn.DivRemSpec.base_pow_eq]; exact Mpn.DivRemSpec.toNat_lt numer
  -- knuthDivNat result is Euclidean.
  have hkn := knuthDivNat_eq cand (toNat numer) (toNat denom) numer.length hdpos hcand hbound
  rcases hrec : knuthDivNat cand (toNat denom) 0 (bDigits numer.length (toNat numer))
    with ⟨qd, r⟩
  rw [hrec] at hkn
  simp only at hkn
  obtain ⟨hqd, hr⟩ := hkn
  -- mpnDivRem result is also Euclidean (divModNat_eq).
  have hdm := Mpn.DivRemSpec.divModNat_eq (toNat numer) (toNat denom) (64 * numer.length) hdpos
    (Mpn.DivRemSpec.toNat_lt numer)
  unfold knuthDivRem Mpn.DivRemSpec.mpnDivRem
  rw [hrec]
  simp only [hdm, hqd, hr]

/-- **The Euclidean division contract for `knuthDivRem` — identical to
    `Mpn.DivRemSpec.mpnDivRem_spec`.**  For a Thm-B-valid candidate and nonzero
    denominator, the q̂-based limb recurrence satisfies the textbook division
    identity at the `toNat` denotation level:

    `toNat numer = toNat quot · toNat denom + toNat rem  ∧  toNat rem < toNat denom`.

    Proved by reducing to `mpnDivRem_spec` via `knuthDivRem_eq_mpnDivRem`. -/
theorem knuthDivRem_spec (cand : Nat → Nat → Nat) (numer denom : List (BitVec 64))
    (hd : toNat denom ≠ 0)
    (hcand : ∀ W : Nat, W / toNat denom ≤ cand (toNat denom) W
      ∧ cand (toNat denom) W ≤ W / toNat denom + 1) :
    toNat numer
      = toNat (knuthDivRem cand numer denom).1 * toNat denom
        + toNat (knuthDivRem cand numer denom).2
    ∧ toNat (knuthDivRem cand numer denom).2 < toNat denom := by
  rw [knuthDivRem_eq_mpnDivRem cand numer denom hd hcand]
  exact Mpn.DivRemSpec.mpnDivRem_spec numer denom hd

/-! ## §5  The Thm-B candidate from `MpnQhatBound`: `qhat_ge_q` / `qhat_le_q_add_one_of_test`

The recurrence above is parametric over a `cand` satisfying the per-step bound
`W/denom ≤ cand denom W ≤ W/denom + 1`.  This is *exactly* what Knuth Theorem B
delivers for the real kernel's q̂-from-top-limbs estimate: claim (1)
(`qhat_ge_q`, `q ≤ q̂`) gives the lower bound, and the two-term refinement
(claim (3), `qhat_le_q_add_one_of_test`, `q̂ ≤ q+1` when the correction test
passes) gives the upper bound.  We record the bridge: any `KnuthBRefine` whose
correction test passes yields a Thm-B-valid candidate value `q̂` at that step. -/

/-- **Thm B packaged as the `qhatDigit`/`knuthDivNat` candidate bound.**  For a
    `KnuthBRefine` config `s` whose two-term correction test passes, the q̂
    estimate `s.qhat` lands in `[q, q+1]` where `q = s.W / s.V` is the true
    quotient digit — exactly the bound `knuthDivNat_spec` requires of `cand`.

    This is the load-bearing connection: `qhat_ge_q` (claim 1) + the refinement
    `qhat_le_q_add_one_of_test` (claim 3) of `MpnQhatBound`. -/
theorem knuthB_candidate_bound (s : KnuthBRefine)
    (htest : s.toKnuthBStep.qhat * s.v2 ≤ s.rhat * s.toKnuthBStep.b + s.u0) :
    s.toKnuthBStep.W / s.toKnuthBStep.V ≤ s.toKnuthBStep.qhat ∧
    s.toKnuthBStep.qhat ≤ s.toKnuthBStep.W / s.toKnuthBStep.V + 1 :=
  ⟨s.toKnuthBStep.qhat_ge_q, s.qhat_le_q_add_one_of_test htest⟩

/-! ## §6  Concrete sanity checks

The q̂-based recurrence, instantiated with the *exact* candidate `cand denom W
:= W / denom` (the trivially Thm-B-valid oracle), reproduces `mpnDivRem` on
small inputs.  (The real kernel uses the top-limb q̂; the exact oracle witnesses
that `knuthDivRem` is well-defined and matches the reference.) -/

/-- The exact candidate `W / denom` is trivially Thm-B-valid. -/
theorem exactCand_valid (denom : Nat) :
    ∀ W : Nat, W / denom ≤ (fun _ W => W / denom) denom W
      ∧ (fun _ W => W / denom) denom W ≤ W / denom + 1 := by
  intro W; exact ⟨le_refl _, Nat.le_succ _⟩

/-- `knuthDivRem` with the exact oracle matches `mpnDivRem` (Euclidean), `7/3`. -/
example : knuthDivRem (fun _ W => W / 3) [7] [3] = Mpn.DivRemSpec.mpnDivRem [7] [3] :=
  knuthDivRem_eq_mpnDivRem _ [7] [3] (by decide) (fun W => ⟨le_refl _, Nat.le_succ _⟩)

/-! ## §7  The CONCRETE top-two-limb candidate `qhatConcrete`

§5 connects the parametric recurrence to *any* Thm-B-valid candidate.  Here we
build the **concrete** candidate the GMP/Knuth kernel actually computes — the
`min(b-1, ⌊U/v1⌋)` top-limb estimate followed by the exact correct-down — and
prove it Thm-B-valid (`W/V ≤ qhatConcrete V W ≤ W/V + 1`) directly from the
`MpnQhatBound` machinery.

### Place-value scaling, value-level

The candidate is a function of the *bare* `Nat`s `V = toNat denom` and `W`; it
recovers the leading-limb place value `M = b^(n-1)` from the value itself as
`M := b^(⌊log_b V⌋)` (for `V ≥ 1` this is exactly `b^(n-1)` where `n` is the
limb length, since the top divisor limb is nonzero).  The leading limb is then
`v1 = V / M`, and the top two window limbs are `U = W / M`.  These satisfy the
two Knuth scaling relations *unconditionally* (they are `Nat.div_mul_le_self` /
`Nat.lt_div_add_one_mul_self` facts about `⌊·/M⌋`), so the `KnuthBStep` lower
bound `q ≤ q̂` (claim 1, `qhat_ge_q`) applies whenever the loop invariant
`W < b·V` and normalization `b ≤ 2·v1` hold — both genuine per-step facts of
normalized Knuth-D.

### The correction is *exact*

`qhatConcrete` then runs `correctDown`: decrement the estimate while
`c·V > W`.  Fed any candidate `c ≥ q` it lands on exactly `q = ⌊W/V⌋` (the
unique digit with `c·V ≤ W < (c+1)·V`); claim 1 supplies `q̂ ≥ q`, so the
landing point is `q`.  The number of decrements is `≤ 2` (Knuth claim 2 /
the two-term refinement), but correctness of the *landing point* needs only
claim 1 — exactly the structure of the file's §1 `qhatDigit`. -/

/-- The limb base value-level place value of `V`'s leading limb: `b^(⌊log_b V⌋)`.
    For an `n`-limb `V` with nonzero top limb this is `b^(n-1)`. -/
def topPlace (V : Nat) : Nat := B ^ Nat.log B V

theorem topPlace_pos (V : Nat) : 0 < topPlace V :=
  Nat.one_le_pow _ _ B_pos

/-- `n < (n / M + 1) · M` for `M > 0` (the strict upper bound from the division
    identity).  Used to discharge the `*high` scaling fields. -/
theorem lt_div_succ_mul (n M : Nat) (h : 0 < M) : n < (n / M + 1) * M := by
  have hdm := Nat.div_add_mod' n M; have hmod := Nat.mod_lt n h; nlinarith [hdm, hmod]

/-- `topPlace V ≤ V` for `V ≥ 1`: the leading place value does not exceed `V`. -/
theorem topPlace_le (V : Nat) (hV : 1 ≤ V) : topPlace V ≤ V :=
  Nat.pow_log_le_self B (by omega)

/-- `V < topPlace V · b`: `V` has at most one more `b`-digit than its leading place. -/
theorem lt_topPlace_mul_B (V : Nat) : V < topPlace V * B := by
  have := Nat.lt_pow_succ_log_self (show 1 < B by unfold B; norm_num) V
  rw [pow_succ] at this; exact this

/-- The **raw** top-two-limb Knuth estimate `q̂ = min(b-1, ⌊U/v1⌋)`, where the
    leading limb `v1 = V / M` and top window prefix `U = W / M` are read off at
    place value `M = topPlace V = b^(n-1)`.  This is exactly `KnuthBStep.qhat`
    for the step built from `(V, W)` (see `rawQhat_eq_step_qhat`). -/
def rawQhat (V W : Nat) : Nat :=
  let M := topPlace V
  min (B - 1) ((W / M) / (V / M))

/-- **The Knuth-B step record built from the bare values `(V, W)`.**  Requires
    the two genuine per-step facts: normalization (`b ≤ 2·v1`) and the loop
    invariant (`W < b·V`).  All scaling relations are discharged from
    `topPlace`. -/
def stepOf (V W : Nat) (hnorm : B ≤ 2 * (V / topPlace V)) (hWb : W < B * V)
    (hVpos : 1 ≤ V) : KnuthBStep where
  b  := B
  V  := V
  v1 := V / topPlace V
  M  := topPlace V
  W  := W
  U  := W / topPlace V
  hb := by unfold B; norm_num
  hM := topPlace_pos V
  hnorm := hnorm
  hv1b := by
    -- v1 = V/M < B  since V < M·B.
    rw [Nat.div_lt_iff_lt_mul (topPlace_pos V)]
    have := lt_topPlace_mul_B V; rw [Nat.mul_comm]; exact this
  hv1 := (Nat.one_le_div_iff (topPlace_pos V)).mpr (topPlace_le V hVpos)
  hVlow := Nat.div_mul_le_self V (topPlace V)
  hVhigh := lt_div_succ_mul V (topPlace V) (topPlace_pos V)
  hWhigh := lt_div_succ_mul W (topPlace V) (topPlace_pos V)
  hWlow := Nat.div_mul_le_self W (topPlace V)
  hWb := hWb

/-- `rawQhat V W` is literally `(stepOf V W ..).qhat`. -/
theorem rawQhat_eq_step_qhat (V W : Nat) (hnorm : B ≤ 2 * (V / topPlace V))
    (hWb : W < B * V) (hVpos : 1 ≤ V) :
    rawQhat V W = (stepOf V W hnorm hWb hVpos).qhat := by
  unfold rawQhat KnuthBStep.qhat KnuthBStep.qraw stepOf
  simp only

/-- **Claim 1, value-level: the raw top-limb estimate never undershoots.**
    `W / V ≤ rawQhat V W`.  Built from `KnuthBStep.qhat_ge_q` on `stepOf`. -/
theorem rawQhat_ge_q (V W : Nat) (hnorm : B ≤ 2 * (V / topPlace V))
    (hWb : W < B * V) (hVpos : 1 ≤ V) :
    W / V ≤ rawQhat V W := by
  rw [rawQhat_eq_step_qhat V W hnorm hWb hVpos]
  have := (stepOf V W hnorm hWb hVpos).qhat_ge_q
  -- (stepOf ..).q is `W / V` by definition of `KnuthBStep.q` and the `V`, `W` fields.
  simpa [KnuthBStep.q, stepOf] using this

/-! ### The exact correct-down step

`correctDown V W c` decrements `c` while `c·V > W`, returning the largest
`c' ≤ c` with `c'·V ≤ W`.  Over `Nat` with `V > 0` this equals `min c (W/V)`. -/

/-- Decrement the candidate `c` while `c·V > W`; fuel = `c` (terminating since
    `c` strictly decreases and `0·V = 0 ≤ W`). -/
def correctDown (V W : Nat) : Nat → Nat
  | 0     => 0
  | c + 1 => if (c + 1) * V ≤ W then c + 1 else correctDown V W c

/-- **`correctDown V W c = min c (W / V)`.**  The correction lands on the true
    quotient digit `W/V` when fed a candidate `≥ W/V`, and is the identity below
    it.  By induction on the fuel `c`. -/
theorem correctDown_eq (V W : Nat) (hV : 0 < V) :
    ∀ c : Nat, correctDown V W c = min c (W / V) := by
  intro c
  induction c with
  | zero => simp [correctDown]
  | succ c ih =>
    unfold correctDown
    by_cases hfit : (c + 1) * V ≤ W
    · -- c+1 fits ⇒ c+1 ≤ W/V, so min (c+1) (W/V) = c+1.
      rw [if_pos hfit]
      have : c + 1 ≤ W / V := (Nat.le_div_iff_mul_le hV).mpr hfit
      omega
    · -- c+1 does not fit ⇒ W/V ≤ c, so min (c+1) (W/V) = W/V = min c (W/V).
      rw [if_neg hfit, ih]
      rw [Nat.not_le] at hfit
      have : W / V < c + 1 := (Nat.div_lt_iff_lt_mul hV).mpr hfit
      omega

/-- **The CONCRETE Knuth candidate.**  Form the top-two-limb estimate
    (`rawQhat`), then correct it down exactly against the full window.  This is
    the value-level model of the kernel's per-digit work: a 2-by-1 `DIV` for the
    estimate followed by the multiply-subtract borrow correction. -/
def qhatConcrete (V W : Nat) : Nat :=
  correctDown V W (rawQhat V W)

/-- **`qhatConcrete` is Thm-B-valid (in fact exact) under the per-step facts.**
    For `V > 0`, normalization (`b ≤ 2·v1`), and the loop invariant `W < b·V`,
    `qhatConcrete V W = W / V`, hence `W/V ≤ qhatConcrete V W ≤ W/V + 1`.

    Proof: `correctDown_eq` gives `qhatConcrete V W = min (rawQhat V W) (W/V)`;
    claim 1 (`rawQhat_ge_q`) gives `W/V ≤ rawQhat V W`, so the `min` is `W/V`. -/
theorem qhatConcrete_eq (V W : Nat) (hnorm : B ≤ 2 * (V / topPlace V))
    (hWb : W < B * V) (hVpos : 1 ≤ V) :
    qhatConcrete V W = W / V := by
  unfold qhatConcrete
  rw [correctDown_eq V W hVpos]
  have := rawQhat_ge_q V W hnorm hWb hVpos
  omega

theorem qhatConcrete_valid (V W : Nat) (hnorm : B ≤ 2 * (V / topPlace V))
    (hWb : W < B * V) (hVpos : 1 ≤ V) :
    W / V ≤ qhatConcrete V W ∧ qhatConcrete V W ≤ W / V + 1 := by
  rw [qhatConcrete_eq V W hnorm hWb hVpos]; exact ⟨le_refl _, Nat.le_succ _⟩

/-! ### Claim 3 (the two-term refinement) recorded against the concrete estimate

For completeness we also record that, when the raw estimate's two-term
correction test passes, claim 3 (`knuthB_candidate_bound`) pins the raw
estimate itself to `[q, q+1]` *without* the correct-down — this is the regime
in which the GMP kernel takes no correction step.  We build the `KnuthBRefine`
from the next limbs and delegate. -/

/-- The two-term refinement record built from `(V, W)` and the next divisor /
    window limbs `v2, u0` at place value `M2 = b^(n-2)`. -/
def refineOf (V W : Nat) (hnorm : B ≤ 2 * (V / topPlace V)) (hWb : W < B * V)
    (hVpos : 1 ≤ V) (M2 : Nat) (hM2 : 1 ≤ M2) (hMM2 : topPlace V = M2 * B) :
    KnuthBRefine where
  toKnuthBStep := stepOf V W hnorm hWb hVpos
  v2 := (V / M2) % B
  u0 := (W / M2) % B
  Wh := W / M2
  V2 := V / M2
  M2 := M2
  hM2 := hM2
  hv2b := Nat.mod_lt _ B_pos
  hV2 := by
    -- V / M2 = (V / (M2·B))·B + (V / M2) % B = v1·b + v2.
    show V / M2 = V / topPlace V * B + V / M2 % B
    rw [hMM2, ← Nat.div_div_eq_div_mul]
    rw [Nat.div_add_mod' (V / M2) B]
  hWh := by
    -- U·b + u0 = (W / M)·b + (W / M2) % b = W / M2.
    show W / topPlace V * B + W / M2 % B = W / M2
    rw [hMM2, ← Nat.div_div_eq_div_mul]
    rw [Nat.div_add_mod' (W / M2) B]
  hV2low := Nat.div_mul_le_self V M2
  hV2high := lt_div_succ_mul V M2 (by omega)
  hWhlow := Nat.div_mul_le_self W M2
  hWhhigh := lt_div_succ_mul W M2 (by omega)

/-- **Claim 3, value-level (kernel no-correction case).**  When the raw
    estimate's two-term test passes, `rawQhat V W ∈ [W/V, W/V + 1]` directly —
    no correct-down needed.  Delegates to `knuthB_candidate_bound`. -/
theorem rawQhat_valid_of_test (V W : Nat) (hnorm : B ≤ 2 * (V / topPlace V))
    (hWb : W < B * V) (hVpos : 1 ≤ V) (M2 : Nat) (hM2 : 1 ≤ M2)
    (hMM2 : topPlace V = M2 * B)
    (htest : rawQhat V W * ((V / M2) % B)
      ≤ (refineOf V W hnorm hWb hVpos M2 hM2 hMM2).rhat * B + (W / M2) % B) :
    W / V ≤ rawQhat V W ∧ rawQhat V W ≤ W / V + 1 := by
  have heq : rawQhat V W = (stepOf V W hnorm hWb hVpos).qhat :=
    rawQhat_eq_step_qhat V W hnorm hWb hVpos
  set s := refineOf V W hnorm hWb hVpos M2 hM2 hMM2 with hs
  have hbound := knuthB_candidate_bound s (by
    -- the test, in `s`'s field names; `s.toKnuthBStep.qhat = rawQhat V W`, `s.v2 = (V/M2)%B`,
    -- `s.b = B`, `s.u0 = (W/M2)%B`.
    show s.toKnuthBStep.qhat * s.v2 ≤ s.rhat * s.toKnuthBStep.b + s.u0
    simpa [hs, refineOf, ← heq] using! htest)
  -- `s.toKnuthBStep.W / s.toKnuthBStep.V = W / V`, `s.toKnuthBStep.qhat = rawQhat V W`.
  rw [heq]
  simpa [hs, refineOf, stepOf, KnuthBStep.q] using hbound

/-! ## §8  The fully-concrete Knuth-D division contract

We specialize the recurrence spec at `cand := qhatConcrete`.  `qhatConcrete`
is exact only under the per-step facts (normalization + loop invariant), which
`knuthDivNat` *does* maintain at every step — the running remainder is `< V`
and each incoming limb is a base-`b` digit, so each window `W = acc·b + l`
satisfies `W < b·V`.  We capture this with a per-step-restricted candidate
spec, then read off the Euclidean contract. -/

/-- **The restricted recurrence spec.**  Identical to `knuthDivNat_spec`, but the
    candidate's Thm-B bound is only required at windows `W < B · denom` — exactly
    the loop-invariant regime the recurrence stays inside.  Each step's window
    `W = acc·B + l` has `acc < denom` and `l < B`, so `W < B·denom`. -/
theorem knuthDivNat_spec_inv (cand : Nat → Nat → Nat) (denom : Nat) (hd : 0 < denom)
    (hcand : ∀ W : Nat, W < B * denom →
      W / denom ≤ cand denom W ∧ cand denom W ≤ W / denom + 1) :
    ∀ (ls : List Nat), (∀ l ∈ ls, l < B) → ∀ (acc : Nat), acc < denom →
      let (quot, r) := knuthDivNat cand denom acc ls
      r < denom ∧
        acc * B ^ ls.length + digitsToNat ls = digitsToNat quot * denom + r := by
  intro ls
  induction ls with
  | nil =>
    intro _ acc hacc
    exact ⟨hacc, by simp [digitsToNat]⟩
  | cons l ls ih =>
    intro hdig acc hacc
    have hl : l < B := hdig l (List.mem_cons_self)
    set W : Nat := acc * B + l with hW
    -- The per-step loop invariant: W = acc·B + l < (denom-1)·B + B = denom·B.
    have hWb : W < B * denom := by
      have : acc + 1 ≤ denom := hacc
      calc W = acc * B + l := hW
        _ < acc * B + B := by omega
        _ = (acc + 1) * B := by ring
        _ ≤ denom * B := Nat.mul_le_mul_right _ this
        _ = B * denom := by ring
    have hge_le : W / denom ≤ cand denom W ∧ cand denom W ≤ W / denom + 1 := hcand W hWb
    have hstepEq : knuthStep cand denom acc l = (W / denom, W % denom) := by
      have ⟨hge, hle⟩ := hge_le
      simpa [knuthStep, ← hW] using qhatDigit_spec denom W (cand denom W) hd hge hle
    have hacc' : W % denom < denom := Nat.mod_lt _ hd
    have htail := ih (fun l hl => hdig l (List.mem_cons_of_mem _ hl)) (W % denom) hacc'
    rcases hrec : knuthDivNat cand denom (W % denom) ls with ⟨ds, r⟩
    rw [hrec] at htail
    simp only at htail
    obtain ⟨hrlt, heq⟩ := htail
    have hres : knuthDivNat cand denom acc (l :: ls) = (W / denom :: ds, r) := by
      simp only [knuthDivNat, hstepEq, hrec]
    have hdslen : ds.length = ls.length := by
      have := knuthDivNat_length cand denom (W % denom) ls; rw [hrec] at this; simpa using this
    rw [hres]
    simp only [List.length_cons, digitsToNat_cons, hdslen]
    refine ⟨hrlt, ?_⟩
    have hWdm : W = (W / denom) * denom + W % denom := (Nat.div_add_mod' W denom).symm
    have hpow : B ^ (ls.length + 1) = B * B ^ ls.length := by rw [pow_succ]; ring
    rw [hpow]
    set P := B ^ ls.length with hP
    have hLHS : acc * (B * P) + (l * P + digitsToNat ls) = W * P + digitsToNat ls := by
      rw [hW]; ring
    rw [hLHS]
    have hWP : W * P = (W / denom) * denom * P + (W % denom) * P := by
      conv_lhs => rw [hWdm]
      ring
    rw [hWP]
    have hexpand : (W / denom * P + digitsToNat ds) * denom
        = (W / denom) * denom * P + digitsToNat ds * denom := by ring
    rw [hexpand]
    omega

/-- Each digit produced by `bDigits` is a base-`B` digit. -/
theorem bDigits_lt (k n : Nat) : ∀ l ∈ bDigits k n, l < B := by
  induction k generalizing n with
  | zero => intro l hl; simp [bDigits] at hl
  | succ k ih =>
    intro l hl
    rw [bDigits, List.mem_cons] at hl
    rcases hl with h | h
    · subst h; exact Nat.mod_lt _ B_pos
    · exact ih n l h

/-- **`qhatConcrete` is Thm-B-valid at every loop-invariant window of a
    NORMALIZED divisor.**  This is the candidate hypothesis the recurrence
    needs, fed to `knuthDivNat_spec_inv`. -/
theorem qhatConcrete_valid_inv (V : Nat) (hVpos : 1 ≤ V)
    (hnorm : B ≤ 2 * (V / topPlace V)) :
    ∀ W : Nat, W < B * V →
      W / V ≤ qhatConcrete V W ∧ qhatConcrete V W ≤ W / V + 1 := by
  intro W hWb
  exact qhatConcrete_valid V W hnorm hWb hVpos

/-- **`knuthDivNat` with the CONCRETE candidate computes exact Euclidean
    div/mod.**  For a normalized divisor and `numerV < B^bitLen`, the recurrence
    over `bDigits bitLen numerV` with `cand := qhatConcrete` returns
    `(numerV / V, numerV % V)`.  The concrete top-limb estimate + correct-down
    is exact at every step because the loop stays inside `W < B·V`. -/
theorem knuthDivNat_concrete_eq (V numerV bitLen : Nat) (hVpos : 1 ≤ V)
    (hnorm : B ≤ 2 * (V / topPlace V)) (hb : numerV < B ^ bitLen) :
    let (qd, r) := knuthDivNat qhatConcrete V 0 (bDigits bitLen numerV)
    digitsToNat qd = numerV / V ∧ r = numerV % V := by
  have hspec := knuthDivNat_spec_inv qhatConcrete V hVpos
    (qhatConcrete_valid_inv V hVpos hnorm) (bDigits bitLen numerV)
    (bDigits_lt bitLen numerV) 0 hVpos
  rcases hrec : knuthDivNat qhatConcrete V 0 (bDigits bitLen numerV) with ⟨qd, r⟩
  rw [hrec] at hspec
  simp only at hspec ⊢
  obtain ⟨hrlt, heq⟩ := hspec
  rw [Nat.zero_mul, Nat.zero_add, digitsToNat_bDigits, Nat.mod_eq_of_lt hb] at heq
  have hq : numerV / V = digitsToNat qd := by
    rw [heq, Nat.add_comm, Nat.add_mul_div_right _ _ hVpos, Nat.div_eq_of_lt hrlt, Nat.zero_add]
  have hr : numerV % V = r := by
    rw [heq, Nat.mul_add_mod', Nat.mod_eq_of_lt hrlt]
  exact ⟨hq.symm, hr.symm⟩

/-- **`knuthDivRem` with the CONCRETE candidate agrees with `mpnDivRem`.**
    The concrete-q̂ recurrence and the bit-by-bit reference produce identical
    limb lists, for a normalized nonzero divisor. -/
theorem knuthDivRem_concrete_eq_mpnDivRem (numer denom : List (BitVec 64))
    (hd : toNat denom ≠ 0)
    (hnorm : B ≤ 2 * (toNat denom / topPlace (toNat denom))) :
    knuthDivRem qhatConcrete numer denom = Mpn.DivRemSpec.mpnDivRem numer denom := by
  have hVpos : 1 ≤ toNat denom := Nat.pos_of_ne_zero hd
  have hbound : toNat numer < B ^ (numer.length) := by
    show toNat numer < (2 ^ 64) ^ numer.length
    rw [Mpn.DivRemSpec.base_pow_eq]; exact Mpn.DivRemSpec.toNat_lt numer
  have hkn := knuthDivNat_concrete_eq (toNat denom) (toNat numer) numer.length hVpos hnorm hbound
  rcases hrec : knuthDivNat qhatConcrete (toNat denom) 0 (bDigits numer.length (toNat numer))
    with ⟨qd, r⟩
  rw [hrec] at hkn
  simp only at hkn
  obtain ⟨hqd, hr⟩ := hkn
  have hdm := Mpn.DivRemSpec.divModNat_eq (toNat numer) (toNat denom) (64 * numer.length) hVpos
    (Mpn.DivRemSpec.toNat_lt numer)
  unfold knuthDivRem Mpn.DivRemSpec.mpnDivRem
  rw [hrec]
  simp only [hdm, hqd, hr]

/-- **The fully-concrete Knuth-D Euclidean division contract — no oracle.**
    For a normalized nonzero divisor, the concrete top-two-limb q̂ recurrence
    `knuthDivRem qhatConcrete` satisfies the textbook division identity at the
    `toNat` denotation level:

    `toNat numer = toNat quot · toNat denom + toNat rem  ∧  toNat rem < toNat denom`.

    This is `knuthDivRem_spec` instantiated at the concrete candidate
    `qhatConcrete` (no exact-`W/denom` oracle): the q̂-from-top-limbs estimate
    drives the recurrence, and the place-value scaling discharges Thm-B
    validity.  Only the Jasmin emission of the per-digit 2-by-1 `DIV` remains. -/
theorem knuthDivRem_concrete_spec (numer denom : List (BitVec 64))
    (hd : toNat denom ≠ 0)
    (hnorm : B ≤ 2 * (toNat denom / topPlace (toNat denom))) :
    toNat numer
      = toNat (knuthDivRem qhatConcrete numer denom).1 * toNat denom
        + toNat (knuthDivRem qhatConcrete numer denom).2
    ∧ toNat (knuthDivRem qhatConcrete numer denom).2 < toNat denom := by
  rw [knuthDivRem_concrete_eq_mpnDivRem numer denom hd hnorm]
  exact Mpn.DivRemSpec.mpnDivRem_spec numer denom hd

end CatCrypt.Crypto.Jasmin.Mpn.DivRemKnuth
