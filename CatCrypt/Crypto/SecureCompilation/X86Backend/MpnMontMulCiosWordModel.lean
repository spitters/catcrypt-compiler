/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public import Mathlib.Data.Nat.ModEq

/-!
# CIOS Montgomery multiplication: the integer word model

The pure-arithmetic value specification of Coarsely-Integrated Operand-Scanning
(CIOS) Montgomery multiplication (Koc-Acar-Kaliski, §5), stated over
little-endian `BitVec 64` limb lists with `bignumVal` as the represented value.

One outer pass at digit `j` performs two sweeps:

* **Phase A** (`phaseA` / `phaseADone`) multiply-accumulates the scalar `x = b[j]`
  into the accumulator: word by word `(S, C) := t[i] + x·a[i] + C`, carrying `C`
  to the next word and the final carry into the top limb. The value identity is
  `bignumVal t' = bignumVal t + x · bignumVal a`.

* **Phase B** (`phaseB`) reduces one Montgomery digit `m`: it multiply-accumulates
  `m·N` into the accumulator and shifts right by one word. Because `m` is latched
  so the low word of `t + m·N` vanishes, the shift is exact and
  `2^64 · bignumVal t' = bignumVal t + m · bignumVal N`.

`ciosStep` is the per-trip word step `(S, C) := t + a·b + C`; `ciosStep_val` is
its split identity. `ciosPass` composes one outer pass and `ciosPass_val` gives
`2^64 · bignumVal t' = bignumVal t + x · bignumVal a + m · bignumVal N`. The final
conditional subtract is omitted; the model is the pre-subtract accumulator.

## Main results

* `ciosStep_val`: the per-trip split identity
  `low + 2^64 · carry = t + a · b + c`.
* `phaseA_val`: the multiply-accumulate running-carry invariant over any prefix.
* `phaseADone_val`: the whole Phase A sweep,
  `bignumVal t' = bignumVal t + x · bignumVal a`.
* `phaseB_val`: the reduction sweep's one-word right-shift split identity.
* `phaseB_done`: the whole Phase B sweep,
  `2^64 · bignumVal t' = bignumVal t + m · bignumVal N`.
* `ciosPass_val`: one outer CIOS pass,
  `2^64 · bignumVal t' = bignumVal t + x · bignumVal a + m · bignumVal N`.
* `ciosFold`: the accumulated fold of `ciosPass` over the digits of the
  multiplier, keeping the accumulator at a fixed width by truncating each pass's
  flushed carry.
* `ciosFold_val`: the fold's value law,
  `(2^64)^n · bignumVal t_n = bignumVal t + bignumVal a · bignumVal b + M · bignumVal N`
  for the multiplier `M` the fold accumulates.
* `ciosFold_congr`: the Montgomery congruence
  `bignumVal t_n · (2^64)^n ≡ bignumVal a · bignumVal b  (mod bignumVal N)`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMontMulCiosWordModel

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms

/-! ## 1. The per-trip word step -/

/-- One CIOS inner-loop position on words: form the wide product `a·b`, add the
    running carry `c` and the destination word `t`, and split into
    `(low word, carry-out)`. Both carry-out bits are the branch-free `bSltu` of a
    sum against its first summand; the high half of the product is `mulhi a b`. -/
def ciosStep (t a b c : BitVec 64) : BitVec 64 × BitVec 64 :=
  let lo := a * b
  let s1 := lo + c
  let s2 := s1 + t
  (s2, mulhi a b + bSltu s1 lo + bSltu s2 s1)

/-- **The single-position addmul identity.** `ciosStep t a b c` splits
    `t + a·b + c` into a low word and a carry-out word:
    `low + 2^64 · carry-out = t + a·b + c`. -/
theorem ciosStep_val (t a b c : BitVec 64) :
    (ciosStep t a b c).1.toNat + 2 ^ 64 * (ciosStep t a b c).2.toNat
      = t.toNat + a.toNat * b.toNat + c.toNat := by
  have hmul := mulWide_lo_hi a b
  have hc1 := addCarry_toNat (a * b) c
  have hc2 := addCarry_toNat (a * b + c) t
  have hb1 : (bSltu (a * b + c) (a * b)).toNat ≤ 1 := by rw [bSltu_eq]; split <;> simp
  have hb2 : (bSltu (a * b + c + t) (a * b + c)).toNat ≤ 1 := by rw [bSltu_eq]; split <;> simp
  have hlo := (a * b).isLt
  have hprod : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)
  have hsum : (mulhi a b).toNat + (bSltu (a * b + c) (a * b)).toNat
      + (bSltu (a * b + c + t) (a * b + c)).toNat < 2 ^ 64 := by
    obtain ⟨P, hP⟩ : ∃ P, a.toNat * b.toNat = P := ⟨_, rfl⟩
    rw [hP] at hmul hprod
    norm_num at hprod
    omega
  have hno1 : (mulhi a b + bSltu (a * b + c) (a * b)).toNat
      = (mulhi a b).toNat + (bSltu (a * b + c) (a * b)).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hno2 : (mulhi a b + bSltu (a * b + c) (a * b)
        + bSltu (a * b + c + t) (a * b + c)).toNat
      = (mulhi a b).toNat + (bSltu (a * b + c) (a * b)).toNat
        + (bSltu (a * b + c + t) (a * b + c)).toNat := by
    rw [BitVec.toNat_add, hno1, Nat.mod_eq_of_lt (by omega)]
  simp only [ciosStep, hno2]
  omega

/-! ## 2. Phase A: the multiply-accumulate sweep -/

/-- The multiply-accumulate sweep of one outer pass: fold `ciosStep` across the
    accumulator `t` and the multiplicand `b` in lockstep, threading the carry.
    Returns the updated accumulator (same length as `t`) and the final carry. -/
def phaseA (x : BitVec 64) :
    List (BitVec 64) → List (BitVec 64) → BitVec 64 → List (BitVec 64) × BitVec 64
  | t0 :: ts, b0 :: bs, c =>
      ((ciosStep t0 x b0 c).1 :: (phaseA x ts bs (ciosStep t0 x b0 c).2).1,
       (phaseA x ts bs (ciosStep t0 x b0 c).2).2)
  | t, [], c => (t, c)
  | [], _ :: _, c => ([], c)

/-- The multiply-accumulate sweep preserves the accumulator length. -/
theorem phaseA_length (x : BitVec 64) :
    ∀ (t b : List (BitVec 64)) (c : BitVec 64), (phaseA x t b c).1.length = t.length
  | t0 :: ts, b0 :: bs, c => by
      simp only [phaseA, List.length_cons]
      rw [phaseA_length x ts bs (ciosStep t0 x b0 c).2]
  | _, [], _ => by simp [phaseA]
  | [], _ :: _, _ => by simp [phaseA]

/-- **Phase A running-carry invariant.** After the sweep over `b` (with the carry
    out at weight `2^(64·|b|)`), the updated accumulator plus the carried-out high
    part equals `t + x · b`. -/
theorem phaseA_val (x : BitVec 64) :
    ∀ (t b : List (BitVec 64)) (c : BitVec 64), b.length ≤ t.length →
      bignumVal (phaseA x t b c).1 + (2 ^ 64) ^ b.length * (phaseA x t b c).2.toNat
        = bignumVal t + x.toNat * bignumVal b + c.toNat
  | t, [], c, _ => by simp [phaseA, bignumVal]
  | [], _ :: _, _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | t0 :: ts, b0 :: bs, c, h => by
      have hlen : bs.length ≤ ts.length := by simp only [List.length_cons] at h; omega
      have hstep := ciosStep_val t0 x b0 c
      have ih := phaseA_val x ts bs (ciosStep t0 x b0 c).2 hlen
      have hpow2 : (2 ^ 64 : ℕ) ^ (bs.length + 1)
            * (phaseA x ts bs (ciosStep t0 x b0 c).2).2.toNat
          = 2 ^ 64 * ((2 ^ 64) ^ bs.length
            * (phaseA x ts bs (ciosStep t0 x b0 c).2).2.toNat) := by
        rw [pow_succ]; ring
      have hgd : x.toNat * (b0.toNat + 2 ^ 64 * bignumVal bs)
          = x.toNat * b0.toNat + 2 ^ 64 * (x.toNat * bignumVal bs) := by ring
      simp only [phaseA, bignumVal, List.length_cons]
      rw [hpow2, hgd]
      generalize (2 ^ 64) ^ bs.length * (phaseA x ts bs (ciosStep t0 x b0 c).2).2.toNat = D
        at ih ⊢
      generalize bignumVal (phaseA x ts bs (ciosStep t0 x b0 c).2).1 = R1 at ih ⊢
      generalize x.toNat * bignumVal bs = B at ih ⊢
      generalize x.toNat * b0.toNat = A at hstep ⊢
      generalize (ciosStep t0 x b0 c).1.toNat = Sn at hstep ⊢
      generalize (ciosStep t0 x b0 c).2.toNat = Cn at hstep ih ⊢
      omega

/-- The full multiply-accumulate sweep with the final carry appended as the new
    top limb: `t + x · b` with no truncation. -/
def phaseADone (x : BitVec 64) (t b : List (BitVec 64)) : List (BitVec 64) :=
  (phaseA x t b 0).1 ++ [(phaseA x t b 0).2]

/-- `phaseADone` produces one more limb than the accumulator. -/
theorem phaseADone_length (x : BitVec 64) (t b : List (BitVec 64)) :
    (phaseADone x t b).length = t.length + 1 := by
  simp only [phaseADone, List.length_append, List.length_cons, List.length_nil,
    phaseA_length]

/-- **Phase A value-correctness (carry absorbed).** For equal-length operands the
    completed multiply-accumulate sweep represents exactly `t + x · b`. -/
theorem phaseADone_val (x : BitVec 64) (t b : List (BitVec 64)) (hlen : b.length = t.length) :
    bignumVal (phaseADone x t b) = bignumVal t + x.toNat * bignumVal b := by
  have hval := phaseA_val x t b 0 (by omega)
  have hlen1 := phaseA_length x t b 0
  simp only [phaseADone]
  rw [bignumVal_snoc, hlen1, ← hlen, Nat.mul_comm ((phaseA x t b 0).2.toNat)]
  simpa using hval

/-! ## 3. Phase B: the reduction sweep (one-word right shift) -/

/-- The reduction sweep of one outer pass: multiply-accumulate the Montgomery
    digit `m` against the modulus `N`, then shift right by one word. When `m` is
    latched so the low word of `t + m · N` vanishes, this is `(t + m · N) / 2^64`. -/
def phaseB (m : BitVec 64) (t N : List (BitVec 64)) : List (BitVec 64) :=
  (phaseADone m t N).drop 1

/-- **Phase B shift split.** The pre-shift accumulator decomposes into its low
    word plus `2^64` times the shifted result. -/
theorem phaseB_val (m : BitVec 64) (t N : List (BitVec 64)) :
    bignumVal (phaseADone m t N)
      = bignumVal ((phaseADone m t N).take 1) + 2 ^ 64 * bignumVal (phaseB m t N) := by
  have h := bignumVal_take_drop 1 (phaseADone m t N)
  rw [pow_one] at h
  simpa [phaseB] using h

/-- **Phase B value-correctness (one-word shift invariant).** For equal-length
    `t` and `N`, when the Montgomery digit latch makes the low word of `t + m · N`
    vanish, the shifted accumulator satisfies `2^64 · t' = t + m · N`. -/
theorem phaseB_done (m : BitVec 64) (t N : List (BitVec 64)) (hlen : N.length = t.length)
    (hmont : bignumVal (phaseADone m t N) % 2 ^ 64 = 0) :
    2 ^ 64 * bignumVal (phaseB m t N) = bignumVal t + m.toNat * bignumVal N := by
  have hsplit := bignumVal_take_drop 1 (phaseADone m t N)
  have hdv := phaseADone_val m t N hlen
  have htlen : ((phaseADone m t N).take 1).length = 1 := by
    rw [List.length_take, phaseADone_length]; omega
  have hlow : bignumVal ((phaseADone m t N).take 1) < 2 ^ 64 := by
    have h := bignumVal_lt ((phaseADone m t N).take 1)
    rw [htlen, pow_one] at h; exact h
  have hmod : bignumVal (phaseADone m t N) % 2 ^ 64
      = bignumVal ((phaseADone m t N).take 1) := by
    conv_lhs => rw [hsplit]
    simp only [pow_one, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hlow
  have hlow0 : bignumVal ((phaseADone m t N).take 1) = 0 := by rw [← hmod]; exact hmont
  have hfin : 2 ^ 64 * bignumVal (phaseB m t N) = bignumVal (phaseADone m t N) := by
    rw [phaseB, hsplit, pow_one, hlow0, Nat.zero_add]
  rw [hfin]; exact hdv

/-! ## 4. One outer pass -/

/-- One outer CIOS pass at digit scalar `x` with Montgomery digit `m`:
    multiply-accumulate `x · a` into `t`, then reduce one word by `m · N`. -/
def ciosPass (x m : BitVec 64) (t a N : List (BitVec 64)) : List (BitVec 64) :=
  phaseB m (phaseADone x t a) N

/-- **One-pass value-correctness.** Composing the multiply-accumulate and the
    reduction sweep, one outer pass gives
    `2^64 · t' = t + x · a + m · N`. -/
theorem ciosPass_val (x m : BitVec 64) (t a N : List (BitVec 64))
    (halen : a.length = t.length) (hNlen : N.length = t.length + 1)
    (hmont : bignumVal (phaseADone m (phaseADone x t a) N) % 2 ^ 64 = 0) :
    2 ^ 64 * bignumVal (ciosPass x m t a N)
      = bignumVal t + x.toNat * bignumVal a + m.toNat * bignumVal N := by
  have hA := phaseADone_val x t a halen
  have hAlen := phaseADone_length x t a
  have hNeq : N.length = (phaseADone x t a).length := by rw [hAlen, hNlen]
  have hB := phaseB_done m (phaseADone x t a) N hNeq hmont
  rw [ciosPass, hB, hA]

/-! ## 5. The accumulated fold and the Montgomery congruence -/

/-- The reduction sweep preserves the accumulator length. -/
theorem phaseB_length (m : BitVec 64) (t N : List (BitVec 64)) :
    (phaseB m t N).length = t.length := by
  simp only [phaseB, List.length_drop, phaseADone_length, Nat.add_sub_cancel]

/-- The accumulated CIOS fold: run one outer pass per digit `x` of the multiplier,
    latching the Montgomery digit `lat u` from the post-multiply accumulator
    `u = phaseADone x t b`, then truncate the flushed carry so the accumulator
    keeps its width. The second component accumulates the Montgomery multiplier
    `M = m₀ + 2^64 · (m₁ + 2^64 · (…))`. -/
def ciosFold (lat : List (BitVec 64) → BitVec 64) (b N : List (BitVec 64)) :
    List (BitVec 64) → List (BitVec 64) → List (BitVec 64) × ℕ
  | [], t => (t, 0)
  | x :: xs, t =>
      ((ciosFold lat b N xs
          ((phaseB (lat (phaseADone x t b)) (phaseADone x t b) N).take t.length)).1,
       (lat (phaseADone x t b)).toNat
         + 2 ^ 64 * (ciosFold lat b N xs
             ((phaseB (lat (phaseADone x t b)) (phaseADone x t b) N).take t.length)).2)

/-- **Accumulated-fold value law.** With the accumulator kept at width `b.length`,
    the modulus one word wider, the Montgomery latch making each pass's low word
    vanish (`hmont`), and each flushed carry fitting the width (`hflush`), the fold
    over the multiplier digits `a` satisfies
    `(2^64)^|a| · bignumVal t_n = bignumVal t + bignumVal a · bignumVal b + M · bignumVal N`. -/
theorem ciosFold_val (lat : List (BitVec 64) → BitVec 64) (b N : List (BitVec 64))
    (hmont : ∀ (y : BitVec 64) (s : List (BitVec 64)), s.length = b.length →
      bignumVal (phaseADone (lat (phaseADone y s b)) (phaseADone y s b) N) % 2 ^ 64 = 0)
    (hflush : ∀ (y : BitVec 64) (s : List (BitVec 64)), s.length = b.length →
      bignumVal (phaseB (lat (phaseADone y s b)) (phaseADone y s b) N) < (2 ^ 64) ^ b.length) :
    ∀ (a t : List (BitVec 64)), t.length = b.length → N.length = b.length + 1 →
      (2 ^ 64) ^ a.length * bignumVal (ciosFold lat b N a t).1
        = bignumVal t + bignumVal a * bignumVal b + (ciosFold lat b N a t).2 * bignumVal N
  | [], t, _, _ => by simp [ciosFold, bignumVal]
  | x :: xs, t, ht, hN => by
      have hpass : 2 ^ 64 * bignumVal (phaseB (lat (phaseADone x t b)) (phaseADone x t b) N)
          = bignumVal t + x.toNat * bignumVal b
            + (lat (phaseADone x t b)).toNat * bignumVal N := by
        have h := ciosPass_val x (lat (phaseADone x t b)) t b N ht.symm (by rw [hN, ht])
          (hmont x t ht)
        simpa [ciosPass] using h
      have hflushx : bignumVal (phaseB (lat (phaseADone x t b)) (phaseADone x t b) N)
          < (2 ^ 64) ^ t.length := by
        have h := hflush x t ht; rw [ht]; exact h
      have ht'len : ((phaseB (lat (phaseADone x t b)) (phaseADone x t b) N).take t.length).length
          = t.length := by
        rw [List.length_take, phaseB_length, phaseADone_length]; omega
      have ih := ciosFold_val lat b N hmont hflush xs
          ((phaseB (lat (phaseADone x t b)) (phaseADone x t b) N).take t.length)
          (by rw [ht'len]; exact ht) hN
      rw [bignumVal_take_of_lt t.length _ hflushx] at ih
      simp only [ciosFold, bignumVal, List.length_cons]
      set R1 := bignumVal (ciosFold lat b N xs
          ((phaseB (lat (phaseADone x t b)) (phaseADone x t b) N).take t.length)).1 with hR1
      set R2 := (ciosFold lat b N xs
          ((phaseB (lat (phaseADone x t b)) (phaseADone x t b) N).take t.length)).2 with hR2
      set PB := bignumVal (phaseB (lat (phaseADone x t b)) (phaseADone x t b) N) with hPB
      have hpow2 : (2 ^ 64 : ℕ) ^ (xs.length + 1) * R1
          = 2 ^ 64 * ((2 ^ 64) ^ xs.length * R1) := by rw [pow_succ]; ring
      have hd1 : (x.toNat + 2 ^ 64 * bignumVal xs) * bignumVal b
          = x.toNat * bignumVal b + 2 ^ 64 * (bignumVal xs * bignumVal b) := by ring
      have hd2 : ((lat (phaseADone x t b)).toNat + 2 ^ 64 * R2) * bignumVal N
          = (lat (phaseADone x t b)).toNat * bignumVal N + 2 ^ 64 * (R2 * bignumVal N) := by ring
      rw [hpow2, hd1, hd2]
      generalize (2 ^ 64 : ℕ) ^ xs.length * R1 = D at ih ⊢
      generalize bignumVal xs * bignumVal b = B at ih ⊢
      generalize R2 * bignumVal N = C at ih ⊢
      generalize bignumVal t = T at hpass ⊢
      generalize x.toNat * bignumVal b = XB at hpass ⊢
      generalize (lat (phaseADone x t b)).toNat * bignumVal N = MN at hpass ⊢
      omega

/-- **Montgomery congruence of the fold.** Starting from a zero-valued
    accumulator, the fold's result `t_n` satisfies
    `bignumVal t_n · (2^64)^|a| ≡ bignumVal a · bignumVal b  (mod bignumVal N)`:
    the accumulated Montgomery multiple `M · bignumVal N` vanishes modulo the
    modulus. -/
theorem ciosFold_congr (lat : List (BitVec 64) → BitVec 64) (b N : List (BitVec 64))
    (hmont : ∀ (y : BitVec 64) (s : List (BitVec 64)), s.length = b.length →
      bignumVal (phaseADone (lat (phaseADone y s b)) (phaseADone y s b) N) % 2 ^ 64 = 0)
    (hflush : ∀ (y : BitVec 64) (s : List (BitVec 64)), s.length = b.length →
      bignumVal (phaseB (lat (phaseADone y s b)) (phaseADone y s b) N) < (2 ^ 64) ^ b.length)
    (a t : List (BitVec 64)) (ht : t.length = b.length) (hN : N.length = b.length + 1)
    (ht0 : bignumVal t = 0) :
    Nat.ModEq (bignumVal N)
      (bignumVal (ciosFold lat b N a t).1 * (2 ^ 64) ^ a.length)
      (bignumVal a * bignumVal b) := by
  have hval := ciosFold_val lat b N hmont hflush a t ht hN
  rw [ht0, Nat.zero_add] at hval
  show bignumVal (ciosFold lat b N a t).1 * (2 ^ 64) ^ a.length % bignumVal N
      = bignumVal a * bignumVal b % bignumVal N
  rw [Nat.mul_comm (bignumVal (ciosFold lat b N a t).1) ((2 ^ 64) ^ a.length), hval,
    Nat.add_mul_mod_self_right]

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMontMulCiosWordModel
