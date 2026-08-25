/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.BigNat

/-!
# Single-limb short division over the BigNat limb carrier

Schoolbook long division of a multi-limb `bignumVal`-carrier by a single
`BitVec 64` limb. Each step is a `128 / 64 → 64` division on the running
`(remainder, limb)` window, expressed as `BitVec 128` `udiv`/`umod` — the
hardware `div r/m64` instruction — so the kernel is limb-native and does not
delegate to a `Nat`-level big-integer division.

The recursion divides the higher-order limbs first: for `l :: ls` (with `l` the
least-significant limb) it divides `ls`, then folds the returned remainder back
into the window with `l` to produce the next quotient digit. The value spec is
proved directly against the little-endian `bignumVal`, hypothesising a nonzero
divisor.

## Main results

* `divmodLE` — the core recursion returning (little-endian quotient limbs,
  single-limb remainder), with `divmodLE_spec`:
  `bignumVal a = d.toNat * bignumVal (divmodLE a d).1 + (divmodLE a d).2.toNat`
  and `(divmodLE a d).2.toNat < d.toNat` for `0 < d.toNat`.
* `shortDivMod` — the (quotient limbs, remainder limbs) wrapper, with
  `shortDivMod_val`: `bignumVal (shortDivMod a d).1 = bignumVal a / d.toNat`
  and `bignumVal (shortDivMod a d).2 = bignumVal a % d.toNat`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatShortDivMod

open CatCrypt.Crypto.SecureCompilation

local notation "bignumVal" => MultiLimbKernel.bignumVal

/-- Core recursion: divide a little-endian limb list by a single limb `d`,
    returning the little-endian quotient limbs together with the single-limb
    remainder. The higher limbs are divided first; the returned remainder is
    folded with the current limb `l` into a `128 / 64 → 64` window. For `d = 0`
    the `BitVec` division convention applies (`x.udiv 0 = 2^64 - 1`,
    `x.umod 0 = x`); the value spec hypothesises `0 < d.toNat`. -/
def divmodLE : List (BitVec 64) → BitVec 64 → List (BitVec 64) × BitVec 64
  | [], _ => ([], 0)
  | l :: ls, d =>
      let (qhi, rhi) := divmodLE ls d
      let w : BitVec 128 := (BitVec.setWidth 128 rhi <<< (64 : Nat)) + BitVec.setWidth 128 l
      let d128 : BitVec 128 := BitVec.setWidth 128 d
      (BitVec.setWidth 64 (w / d128) :: qhi, BitVec.setWidth 64 (w % d128))

/-- **Value correctness of the core recursion.** For a nonzero divisor, the
    quotient limbs and single-limb remainder satisfy the division identity with
    a remainder below the divisor. -/
theorem divmodLE_spec (d : BitVec 64) (hd : 0 < d.toNat) :
    ∀ a : List (BitVec 64),
      bignumVal a = d.toNat * bignumVal (divmodLE a d).1 + (divmodLE a d).2.toNat ∧
      (divmodLE a d).2.toNat < d.toNat
  | [] => by
      refine ⟨?_, ?_⟩
      · simp [divmodLE, MultiLimbKernel.bignumVal]
      · simpa [divmodLE] using hd
  | l :: ls => by
      obtain ⟨ihv, ihr⟩ := divmodLE_spec d hd ls
      -- destructure the recursive result
      set qr := divmodLE ls d with hqr
      set qhi := qr.1 with hqhi
      set rhi := qr.2 with hrhi
      have hd64 : d.toNat < 2 ^ 64 := d.isLt
      have hl64 : l.toNat < 2 ^ 64 := l.isLt
      have hrhi64 : rhi.toNat < 2 ^ 64 := by omega
      have hpow : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by
        rw [show (128 : Nat) = 64 + 64 from rfl, pow_add]
      have hpos64 : 0 < (2 : Nat) ^ 64 := by positivity
      -- the 128-bit window value
      set wNat := rhi.toNat * 2 ^ 64 + l.toNat with hwNat
      have hw_lt : wNat < d.toNat * 2 ^ 64 := by
        have hstep : rhi.toNat * 2 ^ 64 + 2 ^ 64 ≤ d.toNat * 2 ^ 64 := by
          have : (rhi.toNat + 1) * 2 ^ 64 ≤ d.toNat * 2 ^ 64 :=
            Nat.mul_le_mul_right _ (by omega)
          simpa [Nat.add_mul] using this
        omega
      have hw_lt128 : wNat < 2 ^ 128 := by
        have hle : d.toNat * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 :=
          Nat.mul_le_mul_right _ (by omega)
        rw [hpow]; exact Nat.lt_of_lt_of_le hw_lt hle
      -- unfold BitVec window arithmetic to Nat
      have hd128 : (BitVec.setWidth 128 d).toNat = d.toNat := by
        rw [BitVec.toNat_setWidth, hpow]
        exact Nat.mod_eq_of_lt (by nlinarith [hpos64])
      have hwtoNat : ((BitVec.setWidth 128 rhi <<< (64 : Nat)) +
          BitVec.setWidth 128 l).toNat = wNat := by
        rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
          BitVec.toNat_setWidth, Nat.shiftLeft_eq]
        have e1 : rhi.toNat % 2 ^ 128 = rhi.toNat :=
          Nat.mod_eq_of_lt (by rw [hpow]; nlinarith [hpos64])
        have e2 : l.toNat % 2 ^ 128 = l.toNat :=
          Nat.mod_eq_of_lt (by rw [hpow]; nlinarith [hpos64])
        rw [e1, e2]
        have e3 : rhi.toNat * 2 ^ 64 % 2 ^ 128 = rhi.toNat * 2 ^ 64 :=
          Nat.mod_eq_of_lt (by rw [hpow]; nlinarith [hpos64, hrhi64])
        rw [e3, hwNat]
        exact Nat.mod_eq_of_lt hw_lt128
      -- quotient digit and remainder as Nat
      have hqdig : (BitVec.setWidth 64 ((BitVec.setWidth 128 rhi <<< (64 : Nat) +
          BitVec.setWidth 128 l) / BitVec.setWidth 128 d)).toNat = wNat / d.toNat := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_udiv, hwtoNat, hd128]
        exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hw_lt)
      have hrdig : (BitVec.setWidth 64 ((BitVec.setWidth 128 rhi <<< (64 : Nat) +
          BitVec.setWidth 128 l) % BitVec.setWidth 128 d)).toNat = wNat % d.toNat := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_umod, hwtoNat, hd128]
        exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt wNat hd) hd64)
      -- assemble
      have hdivmod : wNat = d.toNat * (wNat / d.toNat) + wNat % d.toNat :=
        (Nat.div_add_mod wNat d.toNat).symm
      refine ⟨?_, ?_⟩
      · simp only [divmodLE, ← hqr, ← hqhi, ← hrhi]
        rw [show bignumVal (l :: ls) = l.toNat + 2 ^ 64 * bignumVal ls from rfl]
        simp only [MultiLimbKernel.bignumVal]
        rw [hqdig, ihv]
        -- goal: l + 2^64*(d*bignumVal qhi + rhi) = d*(wNat/d + 2^64*bignumVal qhi) + (wNat % d)
        nlinarith [hdivmod, hwNat, Nat.zero_le (bignumVal qhi)]
      · simp only [divmodLE, ← hqr, ← hqhi, ← hrhi]
        rw [hrdig]
        exact Nat.mod_lt wNat hd

/-- Divide a multi-limb little-endian limb list `a` by a single limb `d`,
    returning `(quotient limbs, remainder limbs)`. The remainder is the
    single-limb list `[r]` with `r < d`. -/
def shortDivMod (a : List (BitVec 64)) (d : BitVec 64) :
    List (BitVec 64) × List (BitVec 64) :=
  let (q, r) := divmodLE a d
  (q, [r])

/-- **Value correctness.** For a nonzero single-limb divisor, `shortDivMod`
    computes the `Nat` quotient and remainder of `bignumVal a` by `d.toNat`. -/
theorem shortDivMod_val (a : List (BitVec 64)) (d : BitVec 64) (hd : 0 < d.toNat) :
    bignumVal (shortDivMod a d).1 = bignumVal a / d.toNat ∧
    bignumVal (shortDivMod a d).2 = bignumVal a % d.toNat := by
  obtain ⟨hv, hr⟩ := divmodLE_spec d hd a
  set q := (divmodLE a d).1 with hq
  set r := (divmodLE a d).2 with hr'
  have hval : bignumVal a = d.toNat * bignumVal q + r.toNat := hv
  have hrlt : r.toNat < d.toNat := hr
  have hrem : bignumVal (shortDivMod a d).2 = r.toNat := by
    simp [shortDivMod, ← hq, ← hr', MultiLimbKernel.bignumVal]
  have hquo : (shortDivMod a d).1 = q := by simp [shortDivMod, ← hq, ← hr']
  refine ⟨?_, ?_⟩
  · rw [hquo, hval, Nat.mul_add_div hd, Nat.div_eq_of_lt hrlt, Nat.add_zero]
  · rw [hrem, hval, Nat.mul_add_mod, Nat.mod_eq_of_lt hrlt]

end CatCrypt.Crypto.SecureCompilation.BigNatShortDivMod
