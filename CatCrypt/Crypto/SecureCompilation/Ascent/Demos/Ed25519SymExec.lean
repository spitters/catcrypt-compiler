/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMontMulCiosWordModel
public import CatCrypt.Crypto.Util.ScalarFieldVerified

/-!
# The symbolic executor for shipped machine code, and the `ed25519_sc_reduce` model

A part check `partCheck a es mIn mOut blk` holds when:

* `mIn` and `mOut` map machine locations (`Loc`: a register or a memory cell) to word
  expressions over slots;
* the hash-consed value table `Tb` built from the leaves of `mIn` (slots below `a`), the
  statements `es` of slots `a, a + 1, …`, and the symbolic execution `symRun` of `blk`
  from the locations of `mIn` gives every location of `mOut` the node of its expression.

`partCheck_sound` turns a passing check into the implication: if every location of `mIn`
holds the value of its expression under a slot function `ρ` satisfying the statements,
every location of `mOut` does after `runBlock`. Each value-table operation is proved
sound once (`Tb.add_spec`, `internE_spec`, `symStep_sound`).

This module holds the executor, its soundness, and the word model of
`ed25519_sc_reduce`: `reduceModel` is Barrett reduction on 64-bit words — the product
`X · μ`, `μ = ⌊2^512 / L⌋`, by rows of the multiply-accumulate sweep `phaseA`, the
quotient `Q` as limbs 8 and above, the low four limbs of `Q · L`, a four-limb subtraction
from the low half of `X`, and one masked conditional subtraction of `L`. The statement
generators (`stepG`, `phaseAG`, `mulRowsG`, `addLimbsG`, `selG`, `condSubG`, `reduceG`)
produce the single-assignment word statements `xStmts` over numbered slots. These are the
definitions and statements of `CatCrypt.Crypto.EdDSA.Ed25519ScalarEmit`
(`reduceModel_val`, `reduceG_val`), restated over expressions without loads.

The part checks themselves are `decide +kernel` over a symbolic run and cost gigabytes of
kernel memory, so they live in `Ed25519ScReduceShippedProof`, which imports this module.
Separating them keeps the executor and the model available to other programs — the
`ed25519_point_add` census among them — without paying for the checks of this one.

## Main results

* `reduceModel_val`: the word-model Barrett reduction computes `X mod L`.
* `partCheck_sound`: a passing part check carries the locations of `mIn` to those of
  `mOut` across `runBlock`.
* `symStep_sound`, `internE_spec`, `Tb.add_spec`: the per-step soundness the check rests
  on.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMontMulCiosWordModel
open CatCrypt.Util (Ed25519L ed25519L_eq)

/-! ## 1. Carry identities and the word model -/

theorem getLsbD63 (x : BitVec 64) : x.getLsbD 63 = decide (2 ^ 63 ≤ x.toNat) := by
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  have := x.isLt
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [decide_eq_true h]; apply decide_eq_true; omega
  · rw [decide_eq_false h]; apply decide_eq_false; omega

theorem shr63_eq (z : BitVec 64) : z >>> 63 = if z.getLsbD 63 then (1 : BitVec 64) else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, getLsbD63, Nat.shiftRight_eq_div_pow]
  have := z.isLt
  by_cases h : 2 ^ 63 ≤ z.toNat
  · simp only [h, decide_true, if_true]; simp; omega
  · simp only [h, decide_false]; simp; omega

theorem ofNat_allOnes : BitVec.ofNat 64 (2 ^ 64 - 1) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `bSltu` is the unsigned comparison. -/
theorem bSltu_eq' (a b : BitVec 64) : bSltu a b = (if a.ult b then (1 : BitVec 64) else 0) := by
  unfold bSltu
  rw [shr63_eq]
  congr 1
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_not, BitVec.getLsbD_xor, getLsbD63 a, getLsbD63 b, getLsbD63 (a - b),
    BitVec.toNat_sub]
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.ult, show (63 : Nat) < 64 from by decide, decide_true, Bool.true_and]
  by_cases h1 : 2 ^ 63 ≤ a.toNat <;> by_cases h2 : 2 ^ 63 ≤ b.toNat <;>
    by_cases h3 : 2 ^ 63 ≤ (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 <;>
    by_cases h4 : a.toNat < b.toNat <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.or_true, Bool.xor_true,
      Bool.xor_false] <;> omega

/-- The bit-63 carry expression is the carry comparison of `x + y`. -/
theorem carry_bit (x y : BitVec 64) :
    ((x &&& y) ^^^ ((x ^^^ y) &&& ((x + y) ^^^ BitVec.ofNat 64 (2 ^ 64 - 1)))) >>> 63
      = bSltu (x + y) x := by
  unfold bSltu
  rw [shr63_eq, shr63_eq, ofNat_allOnes, BitVec.xor_allOnes]
  have hs : x + y - x = y := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [hs]
  congr 1
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
    decide_true, Bool.true_and, show (63 : Nat) < 64 from by decide]
  cases x.getLsbD 63 <;> cases y.getLsbD 63 <;> cases (x + y).getLsbD 63 <;> rfl

theorem not_bit (x : BitVec 64) : x ^^^ BitVec.ofNat 64 (2 ^ 64 - 1) = ~~~x := by
  rw [ofNat_allOnes, BitVec.xor_allOnes]

theorem sel_bit (x y z : BitVec 64) :
    (x &&& z) ^^^ (y &&& (z ^^^ BitVec.ofNat 64 (2 ^ 64 - 1))) = (x &&& z) ||| (y &&& ~~~z) := by
  rw [not_bit]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

theorem addCarry_toNat' (a b : BitVec 64) :
    (a + b).toNat + (bSltu (a + b) a).toNat * 2 ^ 64 = a.toNat + b.toNat := by
  rw [bSltu_eq']
  have ha := a.isLt
  have hb := b.isLt
  have hadd : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add a b
  by_cases h : (a + b).ult a
  · rw [if_pos h]
    have hlt : (a + b).toNat < a.toNat := BitVec.ult_iff_toNat_lt.mp h
    simp only [show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  · rw [if_neg h]
    have hge : ¬ (a + b).toNat < a.toNat := fun hh => h (BitVec.ult_iff_toNat_lt.mpr hh)
    simp only [show (0 : BitVec 64).toNat = 0 from rfl]
    omega

theorem adc_toNat' (a b cin : BitVec 64) :
    (a + b + cin).toNat
        + (bSltu (a + b) a + bSltu (a + b + cin) (a + b)).toNat * 2 ^ 64
      = a.toNat + b.toNat + cin.toNat := by
  have e1 := addCarry_toNat' a b
  have e2 := addCarry_toNat' (a + b) cin
  have hc1 : (bSltu (a + b) a).toNat ≤ 1 := by rw [bSltu_eq']; split <;> simp
  have hc2 : (bSltu (a + b + cin) (a + b)).toNat ≤ 1 := by rw [bSltu_eq']; split <;> simp
  generalize bSltu (a + b) a = C1 at e1 hc1 ⊢
  generalize bSltu (a + b + cin) (a + b) = C2 at e2 hc2 ⊢
  have hsum2 : C1.toNat + C2.toNat < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.add_le_add hc1 hc2) (by norm_num)
  have hcsum : (C1 + C2).toNat = C1.toNat + C2.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum2]
  rw [hcsum]
  linarith [e1, e2]

theorem adc_carry_le' (a b cin : BitVec 64) (hc : cin.toNat ≤ 1) :
    (bSltu (a + b) a + bSltu (a + b + cin) (a + b)).toNat ≤ 1 := by
  have h := adc_toNat' a b cin
  have ha := a.isLt
  have hb := b.isLt
  have hs := (a + b + cin).isLt
  nlinarith [h, ha, hb, hs, hc, Nat.zero_le (a + b + cin).toNat]

theorem addLimbs_val' : ∀ (as bs : List (BitVec 64)) (c : BitVec 64), c.toNat ≤ 1 →
    as.length = bs.length →
    bignumVal (addLimbs as bs c) = bignumVal as + bignumVal bs + c.toNat
  | [], [], c, _, _ => by simp [addLimbs, bignumVal]
  | a :: as, b :: bs, c, hc, hlen => by
      have hc' := adc_carry_le' a b c hc
      have ih := addLimbs_val' as bs _ hc' (by simpa using hlen)
      have hadc := adc_toNat' a b c
      simp only [addLimbs, bignumVal]
      rw [ih]
      nlinarith [hadc]
  | [], _ :: _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, hlen => by simp at hlen

theorem subLimbs_val' (xs ys : List (BitVec 64)) (hlen : xs.length = ys.length) :
    bignumVal (subLimbs xs ys) + bignumVal ys = bignumVal xs + (2 ^ 64) ^ xs.length := by
  have hnlen : xs.length = (notLimbs ys).length := by simp [notLimbs, hlen]
  have hav := addLimbs_val' xs (notLimbs ys) 1 (by decide) hnlen
  have hnv := notLimbs_val ys
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [subLimbs]
  rw [hav, h1, hlen]
  omega

theorem selLimbs_allOnes : ∀ (a b : List (BitVec 64)), a.length = b.length →
    bignumVal (selLimbs (BitVec.allOnes 64) a b) = bignumVal a
  | [], [], _ => by simp [selLimbs, bignumVal]
  | x :: xs, y :: ys, hlen => by
      have ih := selLimbs_allOnes xs ys (by simpa using hlen)
      simp only [selLimbs, bignumVal, BitVec.and_allOnes, BitVec.not_allOnes, BitVec.and_zero,
        BitVec.or_zero, ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem selLimbs_zero' : ∀ (a b : List (BitVec 64)), a.length = b.length →
    bignumVal (selLimbs 0#64 a b) = bignumVal b
  | [], [], _ => by simp [selLimbs, bignumVal]
  | x :: xs, y :: ys, hlen => by
      have ih := selLimbs_zero' xs ys (by simpa using hlen)
      simp only [selLimbs, bignumVal, BitVec.and_zero, BitVec.not_zero, BitVec.and_allOnes,
        BitVec.zero_or, ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem ciosStep_val' (t a b c : BitVec 64) :
    (ciosStep t a b c).1.toNat + 2 ^ 64 * (ciosStep t a b c).2.toNat
      = t.toNat + a.toNat * b.toNat + c.toNat := by
  have hmul := mulWide_lo_hi a b
  have hc1 := addCarry_toNat' (a * b) c
  have hc2 := addCarry_toNat' (a * b + c) t
  have hb1 : (bSltu (a * b + c) (a * b)).toNat ≤ 1 := by rw [bSltu_eq']; split <;> simp
  have hb2 : (bSltu (a * b + c + t) (a * b + c)).toNat ≤ 1 := by rw [bSltu_eq']; split <;> simp
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

theorem phaseA_val' (x : BitVec 64) :
    ∀ (t b : List (BitVec 64)) (c : BitVec 64), b.length ≤ t.length →
      bignumVal (phaseA x t b c).1 + (2 ^ 64) ^ b.length * (phaseA x t b c).2.toNat
        = bignumVal t + x.toNat * bignumVal b + c.toNat
  | t, [], c, _ => by simp [phaseA, bignumVal]
  | [], _ :: _, _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | t0 :: ts, b0 :: bs, c, h => by
      have hlen : bs.length ≤ ts.length := by simp only [List.length_cons] at h; omega
      have hstep := ciosStep_val' t0 x b0 c
      have ih := phaseA_val' x ts bs (ciosStep t0 x b0 c).2 hlen
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

theorem condSubLimbs_val' (x p : List (BitVec 64)) (hlen : x.length = p.length)
    (hx : bignumVal x < 2 * bignumVal p) :
    bignumVal (condSubLimbs x p) = bignumVal x % bignumVal p := by
  set n := x.length with hn
  set V := bignumVal x with hV
  set P := bignumVal p with hP
  set Q := (2 ^ 64) ^ n with hQ
  have hnl : x.length = (notLimbs p).length := by
    simp only [notLimbs, List.length_map]; exact hlen
  have hdlen : (subLimbs x p).length = n + 1 := by
    simpa [subLimbs, hn] using addLimbs_length x (notLimbs p) 1 hnl
  have hne : subLimbs x p ≠ [] := by
    intro h; rw [h] at hdlen; simp at hdlen
  set d := subLimbs x p with hd
  set flag := d.getLastD 0 with hflag
  set dl := d.dropLast with hdl
  have hgl : d.getLastD 0 = d.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
  have hsplit : dl ++ [flag] = d := by
    rw [hdl, hflag, hgl]; exact List.dropLast_concat_getLast hne
  have hdllen : dl.length = n := by
    have hc := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil, hdlen] at hc
    omega
  have hsnoc : bignumVal d = bignumVal dl + flag.toNat * Q := by
    have hbs := bignumVal_snoc dl flag
    rw [hsplit, hdllen] at hbs; exact hbs
  have hsv : bignumVal d + P = V + Q := by
    have hsubv := subLimbs_val' x p hlen; rw [← hd] at hsubv; exact hsubv
  have hdllt : bignumVal dl < Q := by have := bignumVal_lt dl; rwa [hdllen] at this
  have hplt : P < Q := by have := bignumVal_lt p; rwa [← hlen] at this
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hE : bignumVal dl + flag.toNat * Q + P = V + Q := by rw [← hsnoc]; exact hsv
  have hm1 : flag.toNat ≤ 1 := by
    nlinarith [hE, hdllt, hx, hplt, hQpos, Nat.zero_le (bignumVal dl)]
  have hcases : flag.toNat = 0 ∨ flag.toNat = 1 := by omega
  rcases hcases with hf0 | hf1
  · rw [hf0] at hE
    have hVlt : V < P := by omega
    have hfeq : flag = 0 := by rw [← BitVec.toNat_inj]; simpa using hf0
    have hmask : (0 : BitVec 64) - flag = 0#64 := by rw [hfeq]; decide
    simp only [condSubLimbs, ← hd]
    rw [← hflag, ← hdl, hmask, selLimbs_zero' dl x (by rw [hdllen, hn]),
        Nat.mod_eq_of_lt hVlt]
  · rw [hf1] at hE
    have hVge : P ≤ V := by omega
    have hdlv : bignumVal dl = V - P := by omega
    have hfeq : flag = 1 := by rw [← BitVec.toNat_inj]; simpa using hf1
    have hmask : (0 : BitVec 64) - flag = BitVec.allOnes 64 := by rw [hfeq]; decide
    simp only [condSubLimbs, ← hd]
    rw [← hflag, ← hdl, hmask, selLimbs_allOnes dl x (by rw [hdllen, hn]), hdlv,
        Nat.mod_eq_sub_mod hVge, Nat.mod_eq_of_lt (by omega)]

/-- The schoolbook product of `as` and `bs` accumulated onto the window `w`
    (`|w| = |bs|`): row `i` multiply-accumulates `as[i] · bs` into the window with
    `phaseA`, emits the low word, and shifts the carry in at the top. -/
def mulRows : List (BitVec 64) → List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], _, w => w
  | a :: as, bs, w =>
      (phaseA a w bs 0).1.headD 0 ::
        mulRows as bs ((phaseA a w bs 0).1.tail ++ [(phaseA a w bs 0).2])

theorem mulRows_length : ∀ (as bs w : List (BitVec 64)), 0 < w.length →
    (mulRows as bs w).length = as.length + w.length
  | [], _, w, _ => by simp [mulRows]
  | a :: as, bs, w, hw => by
      have hl := phaseA_length a w bs 0
      simp only [mulRows, List.length_cons]
      rw [mulRows_length as bs _ (by simp)]
      simp only [List.length_append, List.length_tail, hl, List.length_singleton]
      omega

/-- For a window as long as the non-empty multiplier, `mulRows as bs w` represents
    `w + as · bs`. -/
theorem mulRows_val : ∀ (as bs w : List (BitVec 64)), w.length = bs.length → 0 < bs.length →
    bignumVal (mulRows as bs w) = bignumVal w + bignumVal as * bignumVal bs
  | [], _, w, _, _ => by simp [mulRows, bignumVal]
  | a :: as, bs, w, hw, hb => by
      have hl := phaseA_length a w bs 0
      have hv := phaseA_val' a w bs 0 (by omega)
      obtain ⟨h, tl, hr⟩ : ∃ h tl, (phaseA a w bs 0).1 = h :: tl := by
        cases hq : (phaseA a w bs 0).1 with
        | nil => rw [hq] at hl; simp at hl; omega
        | cons h tl => exact ⟨h, tl, rfl⟩
      have htl : tl.length + 1 = bs.length := by rw [hr] at hl; simp at hl; omega
      have ih := mulRows_val as bs (tl ++ [(phaseA a w bs 0).2]) (by simp; omega) hb
      simp only [mulRows, hr, List.headD_cons, List.tail_cons, bignumVal]
      rw [ih, bignumVal_snoc]
      rw [hr] at hv
      simp only [bignumVal] at hv
      have hpow : (2 ^ 64 : ℕ) ^ bs.length = 2 ^ 64 * (2 ^ 64) ^ tl.length := by
        rw [← htl, pow_succ]; ring
      rw [hpow] at hv
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0] at hv
      nlinarith [hv]

/-- The `k` little-endian 64-bit limbs of `v`. -/
def limbsOf (v k : Nat) : List Nat := (List.range k).map (fun i => v / 2 ^ (64 * i) % 2 ^ 64)

/-- The Barrett constant `⌊2^512 / L⌋`. -/
def muNat : Nat := 2 ^ 512 / Ed25519L

/-- The five limbs of `muNat`. -/
def muL : List (BitVec 64) := (limbsOf muNat 5).map (BitVec.ofNat 64)

/-- The four limbs of `L`. -/
def pL : List (BitVec 64) := (limbsOf Ed25519L 4).map (BitVec.ofNat 64)

theorem bignumVal_muL : bignumVal muL = muNat := by decide

theorem bignumVal_pL : bignumVal pL = Ed25519L := by decide

theorem bignumVal_replicate_zero : ∀ k : Nat, bignumVal (List.replicate k (0 : BitVec 64)) = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, bignumVal, bignumVal_replicate_zero k]; rfl

theorem bignumVal_take_mod (k : Nat) (l : List (BitVec 64)) :
    bignumVal (l.take k) = bignumVal l % (2 ^ 64) ^ k := by
  have hs := bignumVal_take_drop k l
  have hlt : bignumVal (l.take k) < (2 ^ 64) ^ k :=
    lt_of_lt_of_le (bignumVal_lt _) (Nat.pow_le_pow_right (by norm_num) (List.length_take_le _ _))
  rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The Barrett reduction of eight limbs modulo `L`, on the word model. -/
def reduceModel (x : List (BitVec 64)) : List (BitVec 64) :=
  condSubLimbs
    (subLimbs (x.take 4)
      ((mulRows ((mulRows x muL (List.replicate 5 0)).drop 8) pL
        (List.replicate 4 0)).take 4)).dropLast
    pL

/-- The low-limb step of the Barrett reduction: with `QP ≤ X < QP + 2L` and
    `L < 2^253`, the four-limb difference of the low halves is `X - QP`. -/
theorem barrett_low_limbs (X QP D L : Nat) (hb1 : QP ≤ X) (hb2 : X < QP + 2 * L)
    (hL : L < 2 ^ 253) (hd : D + QP % (2 ^ 64) ^ 4 = X % (2 ^ 64) ^ 4 + (2 ^ 64) ^ 4) :
    D % (2 ^ 64) ^ 4 = X - QP := by
  norm_num at hd hL ⊢
  omega

/-- The reduction model computes `X mod L`. -/
theorem reduceModel_val (x : List (BitVec 64)) (hx : x.length = 8) :
    bignumVal (reduceModel x) = bignumVal x % Ed25519L := by
  have hL : Ed25519L = 2 ^ 252 + 27742317777372353535851937790883648493 := ed25519L_eq
  have hX : bignumVal x < 2 ^ 512 := by
    have := bignumVal_lt x; rw [hx] at this; norm_num at this ⊢; exact this
  have hT : bignumVal (mulRows x muL (List.replicate 5 0)) = bignumVal x * muNat := by
    rw [mulRows_val _ _ _ (by simp [muL, limbsOf]) (by simp [muL, limbsOf]),
      bignumVal_replicate_zero, bignumVal_muL, Nat.zero_add]
  have hQ : bignumVal ((mulRows x muL (List.replicate 5 0)).drop 8)
      = bignumVal x * (2 ^ 512 / Ed25519L) / 2 ^ 512 := by
    rw [bignumVal_drop, hT]; norm_num [muNat]
  obtain ⟨hb1, hb2⟩ := barrett_bound (bignumVal x) Ed25519L 512 (by rw [hL]; norm_num) hX
  rw [← hQ] at hb1 hb2
  generalize hq : (mulRows x muL (List.replicate 5 0)).drop 8 = q at hb1 hb2
  have hQP : bignumVal (mulRows q pL (List.replicate 4 0)) = bignumVal q * Ed25519L := by
    rw [mulRows_val _ _ _ (by simp [pL, limbsOf]) (by simp [pL, limbsOf]),
      bignumVal_replicate_zero, bignumVal_pL, Nat.zero_add]
  have hQPlen : (mulRows q pL (List.replicate 4 0)).length = q.length + 4 :=
    by rw [mulRows_length _ _ _ (by simp)]; simp
  have hqp : bignumVal ((mulRows q pL (List.replicate 4 0)).take 4)
      = bignumVal q * Ed25519L % (2 ^ 64) ^ 4 := by
    rw [bignumVal_take_mod, hQP]
  have hqplen : ((mulRows q pL (List.replicate 4 0)).take 4).length = 4 := by
    rw [List.length_take, hQPlen]; omega
  have hx4 : bignumVal (x.take 4) = bignumVal x % (2 ^ 64) ^ 4 := bignumVal_take_mod 4 x
  have hx4len : (x.take 4).length = 4 := by simp [hx]
  generalize hqpd : (mulRows q pL (List.replicate 4 0)).take 4 = qp at hqp hqplen
  have hd := subLimbs_val' (x.take 4) qp (by rw [hx4len, hqplen])
  have hdlen : (subLimbs (x.take 4) qp).length = 5 := by
    simp only [subLimbs]
    rw [addLimbs_length _ _ _ (by simp [notLimbs, hx4len, hqplen]), hx4len]
  have hd4 := bignumVal_dropLast 4 _ hdlen
  have hLlt : Ed25519L < 2 ^ 253 := by rw [hL]; norm_num
  have hb2' : bignumVal x < bignumVal q * Ed25519L + 2 * Ed25519L := by
    rw [Nat.add_mul] at hb2; exact hb2
  have hE : bignumVal (subLimbs (x.take 4) qp).dropLast
      = bignumVal x - bignumVal q * Ed25519L := by
    rw [hd4]
    rw [hx4len, hqp, hx4] at hd
    exact barrett_low_limbs _ _ _ _ hb1 hb2' hLlt hd
  have hcs := condSubLimbs_val' (subLimbs (x.take 4) qp).dropLast pL
    (by simp [hdlen, pL, limbsOf])
    (by rw [hE, bignumVal_pL]; exact Nat.sub_lt_left_of_lt_add hb1 hb2')
  simp only [reduceModel]
  rw [hq, hqpd, hcs, hE, bignumVal_pL]
  obtain ⟨E, hEdef⟩ : ∃ E, bignumVal x = bignumVal q * Ed25519L + E :=
    ⟨_, (Nat.add_sub_cancel' hb1).symm⟩
  rw [hEdef, Nat.add_sub_cancel_left, Nat.mul_comm, Nat.mul_add_mod]

/-! ## 2. Word statements and their generators -/

/-- A 64-bit word expression over numbered slots. -/
inductive WE where
  | v (j : Nat)
  | lit (n : Nat)
  | add (a b : WE)
  | sub (a b : WE)
  | mul (a b : WE)
  | mulhi (a b : WE)
  | and (a b : WE)
  | xor (a b : WE)
  | shr (a : WE) (k : Nat)
  deriving Inhabited, Repr, DecidableEq

/-- The value of a word expression when slot `j` holds `ρ j`. -/
def WE.eval (ρ : Nat → BitVec 64) : WE → BitVec 64
  | .v j => ρ j
  | .lit n => BitVec.ofNat 64 n
  | .add a b => a.eval ρ + b.eval ρ
  | .sub a b => a.eval ρ - b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ
  | .mulhi a b => MultiLimbKernel.mulhi (a.eval ρ) (b.eval ρ)
  | .and a b => a.eval ρ &&& b.eval ρ
  | .xor a b => a.eval ρ ^^^ b.eval ρ
  | .shr a k => a.eval ρ >>> k

/-- The slot function `ρ` satisfies a statement list starting at slot `n`: slot `n + i`
    holds the value of expression `i` read in `ρ`. -/
def Holds (ρ : Nat → BitVec 64) : Nat → List WE → Prop
  | _, [] => True
  | n, s :: ps => ρ n = s.eval ρ ∧ Holds ρ (n + 1) ps

theorem holds_append (ρ : Nat → BitVec 64) :
    ∀ (p q : List WE) (n : Nat),
      Holds ρ n (p ++ q) ↔ Holds ρ n p ∧ Holds ρ (n + p.length) q
  | [], q, n => by simp [Holds]
  | s :: p, q, n => by
      simp only [List.cons_append, Holds, holds_append ρ p q (n + 1), List.length_cons,
        show n + 1 + p.length = n + (p.length + 1) by omega, and_assoc]

/-- The all-ones 64-bit word. -/
def ones : Nat := 2 ^ 64 - 1

/-- The carry-out of `s = a + b`: bit 63 of `(a & b) ⊕ ((a ⊕ b) & ¬s)`. -/
def carryW (s a b : WE) : WE :=
  .shr (.xor (.and a b) (.and (.xor a b) (.xor s (.lit ones)))) 63

/-- Bitwise complement as an exclusive-or with all-ones. -/
def notW (a : WE) : WE := .xor a (.lit ones)

theorem carryW_eval (ρ : Nat → BitVec 64) (s a b : WE) (h : s.eval ρ = a.eval ρ + b.eval ρ) :
    (carryW s a b).eval ρ = bSltu (s.eval ρ) (a.eval ρ) := by
  simp only [carryW, WE.eval, h]
  exact carry_bit (a.eval ρ) (b.eval ρ)

theorem notW_eval (ρ : Nat → BitVec 64) (a : WE) : (notW a).eval ρ = ~~~(a.eval ρ) := by
  simp only [notW, WE.eval]
  exact not_bit (a.eval ρ)

theorem eval_headD (ρ : Nat → BitVec 64) (l : List WE) (d : WE) :
    (l.headD d).eval ρ = (l.map (WE.eval ρ)).headD (d.eval ρ) := by
  cases l <;> rfl

/-- One multiply-accumulate position `(S, C) := t + a · b + c`, five slots. -/
def stepG (t a b c : WE) (n : Nat) : List WE :=
  [.mul a b, .mulhi a b, .add (.v n) c, .add (.v (n + 2)) t,
   .add (.add (.v (n + 1)) (carryW (.v (n + 2)) (.v n) c))
      (carryW (.v (n + 3)) (.v (n + 2)) t)]

theorem stepG_val {ρ : Nat → BitVec 64} {t a b c : WE} {n : Nat}
    (h : Holds ρ n (stepG t a b c n)) :
    ρ (n + 3) = (ciosStep (t.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ)).1 ∧
    ρ (n + 4) = (ciosStep (t.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ)).2 := by
  simp only [stepG, Holds, WE.eval, Nat.add_assoc, Nat.reduceAdd] at h
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := h
  rw [carryW_eval ρ _ _ _ (by simp only [WE.eval]; exact h2),
    carryW_eval ρ _ _ _ (by simp only [WE.eval]; exact h3)] at h4
  simp only [WE.eval] at h4
  refine ⟨?_, ?_⟩
  · simp only [ciosStep, h3, h2, h0]
  · simp only [ciosStep, h4, h3, h2, h1, h0]

/-- The generator of `phaseA`. -/
def phaseAG (x : WE) : List WE → List WE → WE → Nat → List WE × List WE × WE
  | t0 :: ts, b0 :: bs, c, n =>
      let r := phaseAG x ts bs (.v (n + 4)) (n + 5)
      (stepG t0 x b0 c n ++ r.1, .v (n + 3) :: r.2.1, r.2.2)
  | t, [], c, _ => ([], t, c)
  | [], _ :: _, c, _ => ([], [], c)

theorem phaseAG_val (ρ : Nat → BitVec 64) (x : WE) :
    ∀ (ts bs : List WE) (c : WE) (n : Nat), Holds ρ n (phaseAG x ts bs c n).1 →
      ((phaseAG x ts bs c n).2.1.map (WE.eval ρ), (phaseAG x ts bs c n).2.2.eval ρ)
        = phaseA (x.eval ρ) (ts.map (WE.eval ρ)) (bs.map (WE.eval ρ)) (c.eval ρ)
  | t0 :: ts, b0 :: bs, c, n, h => by
      simp only [phaseAG] at h ⊢
      rw [holds_append] at h
      obtain ⟨hs, hr⟩ := h
      have hlen : (stepG t0 x b0 c n).length = 5 := rfl
      rw [hlen] at hr
      obtain ⟨e3, e4⟩ := stepG_val hs
      have ih := phaseAG_val ρ x ts bs (.v (n + 4)) (n + 5) hr
      simp only [WE.eval] at ih
      rw [e4] at ih
      simp only [List.map_cons, WE.eval, phaseA, ← ih, e3]
  | t, [], c, n, _ => by simp [phaseAG, phaseA]
  | [], _ :: _, c, n, _ => by simp [phaseAG, phaseA]

/-- The generator of `mulRows`. -/
def mulRowsG : List WE → List WE → List WE → Nat → List WE × List WE
  | [], _, w, _ => ([], w)
  | a :: as, bs, w, n =>
      let r := phaseAG a w bs (.lit 0) n
      let s := mulRowsG as bs (r.2.1.tail ++ [r.2.2]) (n + r.1.length)
      (r.1 ++ s.1, r.2.1.headD (.lit 0) :: s.2)

theorem mulRowsG_val (ρ : Nat → BitVec 64) :
    ∀ (as bs w : List WE) (n : Nat), Holds ρ n (mulRowsG as bs w n).1 →
      (mulRowsG as bs w n).2.map (WE.eval ρ)
        = mulRows (as.map (WE.eval ρ)) (bs.map (WE.eval ρ)) (w.map (WE.eval ρ))
  | [], _, w, _, _ => by simp [mulRowsG, mulRows]
  | a :: as, bs, w, n, h => by
      simp only [mulRowsG] at h ⊢
      rw [holds_append] at h
      have hp := phaseAG_val ρ a w bs (.lit 0) n h.1
      have ih := mulRowsG_val ρ as bs _ _ h.2
      have h0 : WE.eval ρ (.lit 0) = 0 := rfl
      rw [h0] at hp
      rw [List.map_cons, ih, eval_headD, h0, List.map_cons, mulRows, ← hp]
      simp

/-- The generator of `addLimbs`. -/
def addLimbsG : List WE → List WE → WE → Nat → List WE × List WE
  | a :: as, b :: bs, c, n =>
      let r := addLimbsG as bs (.v (n + 2)) (n + 3)
      ([.add a b, .add (.v n) c,
        .add (carryW (.v n) a b) (carryW (.v (n + 1)) (.v n) c)] ++ r.1,
       .v (n + 1) :: r.2)
  | [], _, c, _ => ([], [c])
  | _ :: _, [], c, _ => ([], [c])

theorem addLimbsG_val (ρ : Nat → BitVec 64) :
    ∀ (as bs : List WE) (c : WE) (n : Nat), Holds ρ n (addLimbsG as bs c n).1 →
      (addLimbsG as bs c n).2.map (WE.eval ρ)
        = addLimbs (as.map (WE.eval ρ)) (bs.map (WE.eval ρ)) (c.eval ρ)
  | a :: as, b :: bs, c, n, h => by
      simp only [addLimbsG] at h ⊢
      rw [holds_append] at h
      obtain ⟨hs, hr⟩ := h
      simp only [List.length_cons, List.length_nil] at hr
      simp only [Holds, WE.eval, Nat.add_assoc, Nat.reduceAdd] at hs
      obtain ⟨h0, h1, h2, -⟩ := hs
      rw [carryW_eval ρ _ _ _ (by simp only [WE.eval]; exact h0),
        carryW_eval ρ _ _ _ (by simp only [WE.eval]; exact h1)] at h2
      simp only [WE.eval] at h2
      have ih := addLimbsG_val ρ as bs (.v (n + 2)) (n + 3) hr
      simp only [WE.eval, h2] at ih
      simp only [List.map_cons, WE.eval, addLimbs, ih, h1, h0]
  | [], _, c, n, _ => by cases ‹List WE› <;> simp [addLimbsG, addLimbs]
  | _ :: _, [], c, n, _ => by simp [addLimbsG, addLimbs]

/-- The generator of `selLimbs`: `(a & m) ⊕ (b & ¬m)` per limb. -/
def selG (m : WE) : List WE → List WE → Nat → List WE × List WE
  | a :: as, b :: bs, n =>
      (.xor (.and a m) (.and b (.xor m (.lit ones))) :: (selG m as bs (n + 1)).1,
       .v n :: (selG m as bs (n + 1)).2)
  | [], _, _ => ([], [])
  | _ :: _, [], _ => ([], [])

theorem selG_val (ρ : Nat → BitVec 64) (m : WE) :
    ∀ (as bs : List WE) (n : Nat), Holds ρ n (selG m as bs n).1 →
      (selG m as bs n).2.map (WE.eval ρ)
        = selLimbs (m.eval ρ) (as.map (WE.eval ρ)) (bs.map (WE.eval ρ))
  | a :: as, b :: bs, n, h => by
      simp only [selG, Holds] at h ⊢
      have ih := selG_val ρ m as bs (n + 1) h.2
      rw [List.map_cons, ih]
      simp only [WE.eval]
      rw [h.1]
      simp only [List.map_cons, selLimbs, WE.eval]
      congr 1
      exact sel_bit (a.eval ρ) (b.eval ρ) (m.eval ρ)
  | [], bs, n, _ => by cases bs <;> simp [selG, selLimbs]
  | _ :: _, [], n, _ => by simp [selG, selLimbs]

/-- The generator of `condSubLimbs`. -/
def condSubG (x p : List WE) (n : Nat) : List WE × List WE :=
  let d := addLimbsG x (p.map notW) (.lit 1) n
  let m := n + d.1.length
  let s := selG (.v m) d.2.dropLast x (m + 1)
  (d.1 ++ (.sub (.lit 0) (d.2.getLastD (.lit 0)) :: s.1), s.2)

theorem condSubG_val (ρ : Nat → BitVec 64) (x p : List WE) (n : Nat)
    (h : Holds ρ n (condSubG x p n).1) :
    (condSubG x p n).2.map (WE.eval ρ) = condSubLimbs (x.map (WE.eval ρ)) (p.map (WE.eval ρ)) := by
  simp only [condSubG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hd, hm, hs⟩ := h
  have hdv := addLimbsG_val ρ _ _ _ _ hd
  have hnot : (p.map notW).map (WE.eval ρ) = notLimbs (p.map (WE.eval ρ)) := by
    simp [notLimbs, notW_eval]
  rw [hnot] at hdv
  have hsv := selG_val ρ _ _ _ _ hs
  rw [hsv, List.map_dropLast, hdv]
  simp only [WE.eval] at hm ⊢
  rw [hm, ← List.getLastD_map (f := WE.eval ρ), hdv]
  rfl

/-- The expressions binding the five limbs of `muNat` and then the four limbs of `L`
    to consecutive slots. -/
def constStmts : List WE :=
  (limbsOf muNat 5).map WE.lit ++ (limbsOf Ed25519L 4).map WE.lit

/-- The handles of slots `b .. b + k - 1`. -/
def slotsFrom (b k : Nat) : List WE := (List.range k).map (fun i => .v (b + i))

theorem limbsOf_length (v k : Nat) : (limbsOf v k).length = k := by simp [limbsOf]

theorem constStmts_length : constStmts.length = 9 := by
  simp [constStmts, limbsOf_length]

theorem holds_lits (ρ : Nat → BitVec 64) :
    ∀ (l : List Nat) (n : Nat), Holds ρ n (l.map WE.lit) →
      (slotsFrom n l.length).map (WE.eval ρ) = l.map (BitVec.ofNat 64)
  | [], _, _ => rfl
  | m :: l, n, h => by
      simp only [List.map_cons, Holds, WE.eval] at h
      have ih := holds_lits ρ l (n + 1) h.2
      simp only [slotsFrom, List.map_map] at ih ⊢
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons]
      refine congrArg₂ List.cons (by simpa [WE.eval] using h.1) ?_
      rw [← ih]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_def, WE.eval]
      congr 1
      omega

theorem constStmts_eval (ρ : Nat → BitVec 64) (n : Nat) (h : Holds ρ n constStmts) :
    (slotsFrom n 5).map (WE.eval ρ) = muL ∧ (slotsFrom (n + 5) 4).map (WE.eval ρ) = pL := by
  unfold constStmts at h
  rw [holds_append] at h
  have h1 := holds_lits ρ _ _ h.1
  have h2 := holds_lits ρ _ _ h.2
  simp only [List.length_map, limbsOf_length] at h1 h2
  exact ⟨h1, h2⟩

theorem zeros_eval (ρ : Nat → BitVec 64) (k : Nat) :
    (List.replicate k (WE.lit 0)).map (WE.eval ρ) = List.replicate k 0 := by
  rw [List.map_replicate]; rfl

theorem notW_map (ρ : Nat → BitVec 64) (l : List WE) :
    (l.map notW).map (WE.eval ρ) = notLimbs (l.map (WE.eval ρ)) := by
  simp [notLimbs, notW_eval]

/-- The generator of `reduceModel` over eight input handles: the constant slots
    `n .. n + 8`, then the reduction from slot `n + 9`. -/
def reduceG (x : List WE) (n : Nat) : List WE × List WE :=
  let r1 := mulRowsG x (slotsFrom n 5) (List.replicate 5 (.lit 0)) (n + 9)
  let r2 := mulRowsG (r1.2.drop 8) (slotsFrom (n + 5) 4) (List.replicate 4 (.lit 0))
    (n + 9 + r1.1.length)
  let r3 := addLimbsG (x.take 4) ((r2.2.take 4).map notW) (.lit 1)
    (n + 9 + r1.1.length + r2.1.length)
  let r4 := condSubG r3.2.dropLast (slotsFrom (n + 5) 4)
    (n + 9 + r1.1.length + r2.1.length + r3.1.length)
  (constStmts ++ (r1.1 ++ (r2.1 ++ (r3.1 ++ r4.1))), r4.2)

theorem reduceG_val (ρ : Nat → BitVec 64) (x : List WE) (n : Nat)
    (h : Holds ρ n (reduceG x n).1) :
    (reduceG x n).2.map (WE.eval ρ) = reduceModel (x.map (WE.eval ρ)) := by
  simp only [reduceG] at h ⊢
  rw [holds_append, holds_append, holds_append, holds_append] at h
  obtain ⟨hc, h1, h2, h3, h4⟩ := h
  rw [constStmts_length] at h1 h2 h3 h4
  obtain ⟨hmu, hp⟩ := constStmts_eval ρ n hc
  rw [condSubG_val ρ _ _ _ h4, hp, List.map_dropLast, addLimbsG_val ρ _ _ _ _ h3,
    notW_map, List.map_take, List.map_take, mulRowsG_val ρ _ _ _ _ h2, List.map_drop,
    mulRowsG_val ρ _ _ _ _ h1, hmu, hp, zeros_eval, zeros_eval]
  rfl

/-- The statements of the reduction over the input slots `8 .. 15`, from slot `16`. -/
def xStmts : List WE := (reduceG (slotsFrom 8 8) 16).1

/-- The four result handles of the reduction. -/
def xOuts : List WE := (reduceG (slotsFrom 8 8) 16).2

/-! ## 3. Scoping and the slot run -/

/-- Every slot a word expression reads is below `n`. -/
def WE.scB (n : Nat) : WE → Bool
  | .v j => decide (j < n)
  | .lit _ => true
  | .add a b => a.scB n && b.scB n
  | .sub a b => a.scB n && b.scB n
  | .mul a b => a.scB n && b.scB n
  | .mulhi a b => a.scB n && b.scB n
  | .and a b => a.scB n && b.scB n
  | .xor a b => a.scB n && b.scB n
  | .shr a _ => a.scB n

/-- Every statement of a list starting at slot `n` reads only earlier slots. -/
def wfB : Nat → List WE → Bool
  | _, [] => true
  | n, e :: es => e.scB n && wfB (n + 1) es

/-- Overwrite slot `n`. -/
def updρ (ρ : Nat → BitVec 64) (n : Nat) (x : BitVec 64) : Nat → BitVec 64 :=
  fun j => if j = n then x else ρ j

/-- Run a statement list starting at slot `n`. -/
def wrun : Nat → List WE → (Nat → BitVec 64) → Nat → BitVec 64
  | _, [], ρ => ρ
  | n, e :: es, ρ => wrun (n + 1) es (updρ ρ n (e.eval ρ))

theorem WE.eval_congr {n : Nat} {ρ ρ' : Nat → BitVec 64} (hρ : ∀ j, j < n → ρ j = ρ' j) :
    ∀ e : WE, e.scB n = true → e.eval ρ = e.eval ρ' := by
  intro e
  induction e with
  | v j => intro h; exact hρ j (by simpa [WE.scB] using h)
  | lit _ => intro _; rfl
  | shr a k iha => intro h; simp only [WE.scB] at h; simp only [WE.eval, iha h]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | mulhi a b iha ihb
  | and a b iha ihb | xor a b iha ihb =>
    intro h
    simp only [WE.scB, Bool.and_eq_true] at h
    simp only [WE.eval, iha h.1, ihb h.2]

theorem wrun_below : ∀ (es : List WE) (n : Nat) (ρ : Nat → BitVec 64) (j : Nat), j < n →
    wrun n es ρ j = ρ j
  | [], _, _, _, _ => rfl
  | e :: es, n, ρ, j, hj => by
      simp only [wrun]
      rw [wrun_below es (n + 1) _ j (by omega)]
      simp only [updρ, if_neg (Nat.ne_of_lt hj)]

theorem holds_wrun : ∀ (es : List WE) (n : Nat) (ρ : Nat → BitVec 64), wfB n es = true →
    Holds (wrun n es ρ) n es
  | [], _, _, _ => trivial
  | e :: es, n, ρ, h => by
      simp only [wfB, Bool.and_eq_true] at h
      refine ⟨?_, holds_wrun es (n + 1) _ h.2⟩
      simp only [wrun]
      rw [wrun_below es (n + 1) _ n (by omega)]
      simp only [updρ]
      refine WE.eval_congr (fun j hj => ?_) e h.1
      rw [wrun_below es (n + 1) _ j (by omega)]
      simp only [updρ, if_neg (Nat.ne_of_lt hj)]

theorem holds_slice (ρ : Nat → BitVec 64) (es : List WE) (n a b : Nat) (h : Holds ρ n es)
    (ha : n ≤ a) (hab : a ≤ b) (hb : b ≤ n + es.length) :
    Holds ρ a ((es.drop (a - n)).take (b - a)) := by
  rw [← List.take_append_drop (a - n) es, holds_append] at h
  have h2 := h.2
  rw [List.length_take, Nat.min_eq_left (by omega), show n + (a - n) = a by omega,
    ← List.take_append_drop (b - a) (es.drop (a - n)), holds_append] at h2
  exact h2.1

/-! ## 4. Hash-consed value tables -/

/-- A node of a value table: a slot leaf, the entry value of a register or of a memory
    cell, a literal, or an operation on earlier nodes named by their indices. -/
inductive Nd where
  | inp (i : Nat)
  | reg (r : String)
  | cell (b : String) (o : Int)
  | lit (v : Nat)
  | add (a b : Nat)
  | sub (a b : Nat)
  | and (a b : Nat)
  | xor (a b : Nat)
  | mul (a b : Nat)
  | mulhi (a b : Nat)
  | shr (a k : Nat)
  deriving DecidableEq, Repr

/-- The meaning of the leaves: slot values `W` and the entry state `st`. -/
structure Env where
  /-- The slot values. -/
  W : Nat → BitVec 64
  /-- The entry state. -/
  st : JState 64

/-- The word a node denotes when node `j` denotes `V j`. -/
def Nd.den (E : Env) (V : Nat → BitVec 64) : Nd → BitVec 64
  | .inp i => E.W i
  | .reg r => E.st.regs r
  | .cell b o => E.st.mem b o
  | .lit v => BitVec.ofNat 64 v
  | .add a b => V a + V b
  | .sub a b => V a - V b
  | .and a b => V a &&& V b
  | .xor a b => V a ^^^ V b
  | .mul a b => V a * V b
  | .mulhi a b => MultiLimbKernel.mulhi (V a) (V b)
  | .shr a k => V a >>> k

/-- Every node index a node names is below `n`. -/
def Nd.ArgsLt (n : Nat) : Nd → Prop
  | .add a b => a < n ∧ b < n
  | .sub a b => a < n ∧ b < n
  | .and a b => a < n ∧ b < n
  | .xor a b => a < n ∧ b < n
  | .mul a b => a < n ∧ b < n
  | .mulhi a b => a < n ∧ b < n
  | .shr a _ => a < n
  | _ => True

theorem Nd.den_congr (E : Env) {V V' : Nat → BitVec 64} {n : Nat} {t : Nd} (ht : t.ArgsLt n)
    (hv : ∀ j, j < n → V j = V' j) : t.den E V = t.den E V' := by
  cases t <;> simp only [Nd.ArgsLt] at ht <;> simp only [Nd.den] <;>
    first | rw [hv _ ht.1, hv _ ht.2] | rw [hv _ ht]

/-- The node with the arguments of a commutative operation in increasing order. -/
def Nd.norm : Nd → Nd
  | .add a b => if b < a then .add b a else .add a b
  | .and a b => if b < a then .and b a else .and a b
  | .xor a b => if b < a then .xor b a else .xor a b
  | .mul a b => if b < a then .mul b a else .mul a b
  | .mulhi a b => if b < a then .mulhi b a else .mulhi a b
  | t => t

theorem mulhi_comm (a b : BitVec 64) : MultiLimbKernel.mulhi a b = MultiLimbKernel.mulhi b a := by
  simp only [MultiLimbKernel.mulhi, Nat.mul_comm]

theorem Nd.den_norm (E : Env) (V : Nat → BitVec 64) (t : Nd) : t.norm.den E V = t.den E V := by
  cases t <;> simp only [Nd.norm] <;> (try split) <;> simp only [Nd.den] <;>
    first
    | rfl
    | exact BitVec.add_comm _ _
    | exact BitVec.and_comm _ _
    | exact BitVec.xor_comm _ _
    | exact BitVec.mul_comm _ _
    | exact mulhi_comm _ _

theorem Nd.ArgsLt.norm {n : Nat} {t : Nd} (ht : t.ArgsLt n) : t.norm.ArgsLt n := by
  cases t <;> simp only [Nd.norm] <;> (try split) <;> simp only [Nd.ArgsLt] at ht ⊢ <;> omega

/-- A binary trie of buckets of `(node, index)` pairs, keyed by bit lists. -/
inductive Trie where
  | nil : Trie
  | node : List (Nd × Nat) → Trie → Trie → Trie

/-- The bucket at a key. -/
def Trie.get : Trie → List Bool → List (Nd × Nat)
  | .nil, _ => []
  | .node b _ _, [] => b
  | .node _ l _, false :: ks => l.get ks
  | .node _ _ r, true :: ks => r.get ks

/-- Add a pair to the bucket at a key. -/
def Trie.ins : Trie → List Bool → Nd × Nat → Trie
  | .nil, [], e => .node [e] .nil .nil
  | .nil, false :: ks, e => .node [] (Trie.nil.ins ks e) .nil
  | .nil, true :: ks, e => .node [] .nil (Trie.nil.ins ks e)
  | .node b l r, [], e => .node (e :: b) l r
  | .node b l r, false :: ks, e => .node b (l.ins ks e) r
  | .node b l r, true :: ks, e => .node b l (r.ins ks e)

theorem Trie.get_nil (k : List Bool) : Trie.nil.get k = [] := by
  cases k <;> rfl

theorem Trie.mem_get_ins : ∀ (k : List Bool) (t : Trie) (k' : List Bool) (e x : Nd × Nat),
    x ∈ (t.ins k e).get k' → x = e ∨ x ∈ t.get k'
  | [], .nil, k', e, x, h => by
      cases k' with
      | nil => simpa [Trie.ins, Trie.get] using h
      | cons b ks => cases b <;> simp [Trie.ins, Trie.get] at h
  | [], .node b l r, k', e, x, h => by
      cases k' with
      | nil => simpa [Trie.ins, Trie.get] using h
      | cons c ks => cases c <;> exact Or.inr (by simpa [Trie.ins, Trie.get] using h)
  | false :: ks, .nil, k', e, x, h => by
      cases k' with
      | nil => simp [Trie.ins, Trie.get] at h
      | cons c ks' =>
        cases c
        · simp only [Trie.ins, Trie.get] at h
          rcases Trie.mem_get_ins ks .nil ks' e x h with h | h
          · exact Or.inl h
          · simp [Trie.get_nil] at h
        · simp [Trie.ins, Trie.get] at h
  | true :: ks, .nil, k', e, x, h => by
      cases k' with
      | nil => simp [Trie.ins, Trie.get] at h
      | cons c ks' =>
        cases c
        · simp [Trie.ins, Trie.get] at h
        · simp only [Trie.ins, Trie.get] at h
          rcases Trie.mem_get_ins ks .nil ks' e x h with h | h
          · exact Or.inl h
          · simp [Trie.get_nil] at h
  | false :: ks, .node b l r, k', e, x, h => by
      cases k' with
      | nil => exact Or.inr (by simpa [Trie.ins, Trie.get] using h)
      | cons c ks' =>
        cases c
        · simp only [Trie.ins, Trie.get] at h ⊢
          exact Trie.mem_get_ins ks l ks' e x h
        · exact Or.inr (by simpa [Trie.ins, Trie.get] using h)
  | true :: ks, .node b l r, k', e, x, h => by
      cases k' with
      | nil => exact Or.inr (by simpa [Trie.ins, Trie.get] using h)
      | cons c ks' =>
        cases c
        · exact Or.inr (by simpa [Trie.ins, Trie.get] using h)
        · simp only [Trie.ins, Trie.get] at h ⊢
          exact Trie.mem_get_ins ks r ks' e x h

/-- The low `f` bits of `h`, least significant first. -/
def bits : Nat → Nat → List Bool
  | 0, _ => []
  | f + 1, h => (h % 2 == 1) :: bits f (h / 2)

/-- A hash of a node. -/
def Nd.hash : Nd → Nat
  | .inp i => i
  | .reg _ => 1
  | .cell _ o => o.natAbs
  | .lit v => v
  | .add a b => 2 + 3 * a + 5 * b
  | .sub a b => 3 + 5 * a + 3 * b
  | .and a b => 5 + 7 * a + 11 * b
  | .xor a b => 7 + 11 * a + 13 * b
  | .mul a b => 11 + 13 * a + 17 * b
  | .mulhi a b => 13 + 17 * a + 19 * b
  | .shr a k => 17 + 19 * a + k

/-- The trie key of a node. -/
def Nd.key (t : Nd) : List Bool := bits 14 t.hash

/-- A value table: its nodes, newest first (node `j` is the `j`-th from the end), their
    number, and a trie from node hashes to `(node, index)` pairs. -/
structure Tb where
  /-- The nodes, newest first. -/
  nodes : List Nd
  /-- The number of nodes. -/
  size : Nat
  /-- The hash-consing index. -/
  memo : Trie

/-- The empty table. -/
def Tb.empty : Tb := ⟨[], 0, .nil⟩

/-- The index recorded for `t` in a bucket. -/
def findB (t : Nd) : List (Nd × Nat) → Option Nat
  | [] => none
  | p :: ps => if p.1 = t then some p.2 else findB t ps

/-- The index of `t`, added to the table when absent. -/
def Tb.add (T : Tb) (t : Nd) : Tb × Nat :=
  match findB t (T.memo.get t.key) with
  | some j => (T, j)
  | none => (⟨t :: T.nodes, T.size + 1, T.memo.ins t.key (t, T.size)⟩, T.size)

/-- `Tb.add` on the normal form of `t`. -/
def Tb.addN (T : Tb) (t : Nd) : Tb × Nat := T.add t.norm

/-- Element `j` of the reverse of a value list. -/
def getV (vs : List (BitVec 64)) (j : Nat) : BitVec 64 := vs.reverse.getD j 0

/-- The values of a node list, newest first. -/
def valsL (E : Env) : List Nd → List (BitVec 64)
  | [] => []
  | t :: ts => t.den E (getV (valsL E ts)) :: valsL E ts

/-- The value of node `j` of a table. -/
def Tb.V (E : Env) (T : Tb) (j : Nat) : BitVec 64 := getV (valsL E T.nodes) j

/-- Node `j` of a newest-first node list. -/
def nodeAt (l : List Nd) (j : Nat) : Option Nd := l.reverse[j]?

/-- Every node names only older nodes. -/
def NodesWF : List Nd → Prop
  | [] => True
  | t :: ts => t.ArgsLt ts.length ∧ NodesWF ts

theorem valsL_length (E : Env) : ∀ l : List Nd, (valsL E l).length = l.length
  | [] => rfl
  | _ :: l => by simp [valsL, valsL_length E l]

theorem valsL_append (E : Env) (l : List Nd) :
    ∀ pre : List Nd, ∃ X, valsL E (pre ++ l) = X ++ valsL E l
  | [] => ⟨[], rfl⟩
  | p :: pre => by
      obtain ⟨X, hX⟩ := valsL_append E l pre
      exact ⟨p.den E (getV (X ++ valsL E l)) :: X, by simp only [List.cons_append, valsL, hX]⟩

theorem getV_append (X vs : List (BitVec 64)) (j : Nat) (hj : j < vs.length) :
    getV (X ++ vs) j = getV vs j := by
  simp only [getV, List.reverse_append, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hj)]

theorem getV_cons_len (v : BitVec 64) (vs : List (BitVec 64)) : getV (v :: vs) vs.length = v := by
  simp [getV, List.getD_eq_getElem?_getD]

theorem nodeAt_cons_lt (u : Nd) (us : List Nd) (j : Nat) (h : j < us.length) :
    nodeAt (u :: us) j = nodeAt us j := by
  simp only [nodeAt, List.reverse_cons]
  rw [List.getElem?_append_left (by simpa using h)]

theorem nodeAt_cons_len (u : Nd) (us : List Nd) : nodeAt (u :: us) us.length = some u := by
  simp [nodeAt]

theorem nodeAt_lt {l : List Nd} {j : Nat} {t : Nd} (h : nodeAt l j = some t) : j < l.length := by
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 h
  simpa using hj

theorem nodeAt_spec (E : Env) : ∀ (l : List Nd) (j : Nat) (t : Nd), NodesWF l →
    nodeAt l j = some t → t.ArgsLt j ∧ getV (valsL E l) j = t.den E (getV (valsL E l))
  | [], j, t, _, h => by simp [nodeAt] at h
  | u :: us, j, t, hw, h => by
      have hj := nodeAt_lt h
      simp only [List.length_cons] at hj
      have hag : ∀ i, i < us.length → getV (valsL E us) i = getV (valsL E (u :: us)) i :=
        fun i hi => (getV_append [_] _ _ (by rw [valsL_length]; exact hi)).symm
      rcases Nat.lt_or_ge j us.length with hlt | hge
      · rw [nodeAt_cons_lt u us j hlt] at h
        obtain ⟨ha, hv⟩ := nodeAt_spec E us j t hw.2 h
        refine ⟨ha, ?_⟩
        rw [← hag j hlt, hv]
        exact Nd.den_congr E ha (fun i hi => hag i (by omega))
      · have hje : j = us.length := by omega
        subst hje
        rw [nodeAt_cons_len] at h
        cases h
        refine ⟨hw.1, ?_⟩
        have e : getV (valsL E (u :: us)) us.length = u.den E (getV (valsL E us)) := by
          show getV (u.den E (getV (valsL E us)) :: valsL E us) us.length = _
          conv_lhs => rw [show us.length = (valsL E us).length from (valsL_length E us).symm]
          exact getV_cons_len _ _
        rw [e]
        exact Nd.den_congr E hw.1 hag

/-- A table is well formed: its size is its length, every node names older nodes, and the
    trie records only true `(node, index)` pairs. -/
structure Tb.WF (T : Tb) : Prop where
  size_eq : T.size = T.nodes.length
  nodes_wf : NodesWF T.nodes
  memo_ok : ∀ k x, x ∈ T.memo.get k → nodeAt T.nodes x.2 = some x.1

/-- `T'` is well formed and extends `T` by new nodes. -/
def Grows (T T' : Tb) : Prop := T'.WF ∧ ∃ pre, T'.nodes = pre ++ T.nodes

theorem Grows.refl {T : Tb} (h : T.WF) : Grows T T := ⟨h, [], rfl⟩

theorem Grows.trans {T₁ T₂ T₃ : Tb} (h₁ : Grows T₁ T₂) (h₂ : Grows T₂ T₃) : Grows T₁ T₃ := by
  obtain ⟨-, p, hp⟩ := h₁
  obtain ⟨w, q, hq⟩ := h₂
  exact ⟨w, q ++ p, by rw [hq, hp, List.append_assoc]⟩

theorem Grows.size_le {T T' : Tb} (hT : T.WF) (h : Grows T T') : T.size ≤ T'.size := by
  obtain ⟨w, p, hp⟩ := h
  rw [w.size_eq, hT.size_eq, hp, List.length_append]
  omega

theorem Grows.V_eq (E : Env) {T T' : Tb} (hT : T.WF) (h : Grows T T') {j : Nat}
    (hj : j < T.size) : T'.V E j = T.V E j := by
  obtain ⟨-, p, hp⟩ := h
  simp only [Tb.V, hp]
  obtain ⟨X, hX⟩ := valsL_append E T.nodes p
  rw [hX]
  exact getV_append _ _ _ (by rw [valsL_length, ← hT.size_eq]; exact hj)

theorem findB_spec (t : Nd) : ∀ (l : List (Nd × Nat)) (j : Nat), findB t l = some j → (t, j) ∈ l
  | [], _, h => by simp [findB] at h
  | p :: ps, j, h => by
      simp only [findB] at h
      split at h
      · rename_i hp
        cases h
        exact List.mem_cons.2 (Or.inl (by rw [← hp]))
      · exact List.mem_cons_of_mem _ (findB_spec t ps j h)

theorem Tb.empty_WF : Tb.empty.WF :=
  ⟨rfl, trivial, fun k x hx => by simp [Tb.empty, Trie.get_nil] at hx⟩

theorem Tb.add_spec (E : Env) (T : Tb) (t : Nd) (hT : T.WF) (ht : t.ArgsLt T.size) :
    Grows T (T.add t).1 ∧ (T.add t).2 < (T.add t).1.size ∧
      (T.add t).1.V E (T.add t).2 = t.den E (T.V E) := by
  unfold Tb.add
  split
  · rename_i j hj
    have hn := hT.memo_ok _ _ (findB_spec _ _ _ hj)
    obtain ⟨-, hv⟩ := nodeAt_spec E _ _ _ hT.nodes_wf hn
    refine ⟨Grows.refl hT, ?_, hv⟩
    rw [hT.size_eq]
    exact nodeAt_lt hn
  · refine ⟨⟨⟨?_, ?_, ?_⟩, [t], rfl⟩, ?_, ?_⟩
    · simp [hT.size_eq]
    · exact ⟨by rw [← hT.size_eq]; exact ht, hT.nodes_wf⟩
    · intro k x hx
      rcases Trie.mem_get_ins _ _ _ _ _ hx with rfl | hx
      · simp only
        rw [hT.size_eq]
        exact nodeAt_cons_len _ _
      · have := hT.memo_ok k x hx
        rw [nodeAt_cons_lt _ _ _ (nodeAt_lt this)]
        exact this
    · simp
    · show getV (t.den E (getV (valsL E T.nodes)) :: valsL E T.nodes) T.size = _
      rw [hT.size_eq, show T.nodes.length = (valsL E T.nodes).length from
        (valsL_length E _).symm, getV_cons_len]
      rfl

theorem Tb.addN_spec (E : Env) (T : Tb) (t : Nd) (hT : T.WF) (ht : t.ArgsLt T.size) :
    Grows T (T.addN t).1 ∧ (T.addN t).2 < (T.addN t).1.size ∧
      (T.addN t).1.V E (T.addN t).2 = t.den E (T.V E) := by
  obtain ⟨h1, h2, h3⟩ := Tb.add_spec E T t.norm hT ht.norm
  exact ⟨h1, h2, h3.trans (Nd.den_norm _ _ _)⟩

/-! ## 5. Interning statement lists -/

/-- The node of slot `j` in a newest-first slot list whose head is slot `n - 1`. -/
def sget (σ : List Nat) (n j : Nat) : Option Nat := if j < n then σ[n - 1 - j]? else none

/-- The node of a binary operation on the nodes of two interned operands. -/
def bin2 (ra : Option (Tb × Nat)) (rb : Tb → Option (Tb × Nat)) (op : Nat → Nat → Nd) :
    Option (Tb × Nat) :=
  match ra with
  | some (T₁, x) =>
    match rb T₁ with
    | some (T₂, y) => some (T₂.addN (op x y))
    | none => none
  | none => none

/-- The literals of the constant slots `16 .. 24`: the limbs of `muNat`, then of `L`. -/
def cLits : List Nat := limbsOf muNat 5 ++ limbsOf Ed25519L 4

/-- The literal of a constant slot. -/
def cK (j : Nat) : Option Nat := if 16 ≤ j then cLits[j - 16]? else none

/-- The node of a word expression: a constant slot below `a` is its literal, any other
    slot below `a` is the leaf `.inp j`, a slot `j` from `a` on is read from the slot list
    `σ` of the slots below `n`; `none` when the expression reads a slot at or above `n`. -/
def internE (a : Nat) (σ : List Nat) (n : Nat) : Tb → WE → Option (Tb × Nat)
  | T, .v j =>
    if j < a then
      match cK j with
      | some c => some (T.addN (.lit c))
      | none => some (T.add (.inp j))
    else
    match sget σ n j with
    | some x => some (T, x)
    | none => none
  | T, .lit m => some (T.addN (.lit m))
  | T, .add p q => bin2 (internE a σ n T p) (fun T₁ => internE a σ n T₁ q) .add
  | T, .sub p q => bin2 (internE a σ n T p) (fun T₁ => internE a σ n T₁ q) .sub
  | T, .mul p q => bin2 (internE a σ n T p) (fun T₁ => internE a σ n T₁ q) .mul
  | T, .mulhi p q => bin2 (internE a σ n T p) (fun T₁ => internE a σ n T₁ q) .mulhi
  | T, .and p q => bin2 (internE a σ n T p) (fun T₁ => internE a σ n T₁ q) .and
  | T, .xor p q => bin2 (internE a σ n T p) (fun T₁ => internE a σ n T₁ q) .xor
  | T, .shr p k =>
    match internE a σ n T p with
    | some (T₁, x) => some (T₁.addN (.shr x k))
    | none => none

/-- Intern a statement list whose first statement writes slot `n`, extending the slot
    list. -/
def internS (a : Nat) : List Nat → Nat → Tb → List WE → Option (Tb × List Nat)
  | σ, _, T, [] => some (T, σ)
  | σ, n, T, e :: es =>
    match internE a σ n T e with
    | some (T₁, x) => internS a (x :: σ) (n + 1) T₁ es
    | none => none

/-- Every node of a slot list is in the table. -/
def SigOK (T : Tb) (σ : List Nat) : Prop := ∀ x ∈ σ, x < T.size

/-- The slots below `a`: the leaves denote `ρ`, and a constant slot holds its literal. -/
def LeafOK (E : Env) (a : Nat) (ρ : Nat → BitVec 64) : Prop :=
  (∀ j, j < a → E.W j = ρ j) ∧ ∀ j c, j < a → cK j = some c → ρ j = BitVec.ofNat 64 c

/-- The slot values: the slots below `a` satisfy `LeafOK`, and each slot of `σ` holds the
    value of its node. -/
def SIdx (E : Env) (T : Tb) (a : Nat) (σ : List Nat) (n : Nat) (ρ : Nat → BitVec 64) :
    Prop :=
  LeafOK E a ρ ∧ ∀ j x, sget σ n j = some x → ρ j = T.V E x

theorem sget_mem {σ : List Nat} {n j x : Nat} (h : sget σ n j = some x) : x ∈ σ := by
  unfold sget at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

theorem sget_nil (n j : Nat) : sget [] n j = none := by
  simp [sget]

theorem sget_cons_eq (x : Nat) (σ : List Nat) (n j : Nat) :
    sget (x :: σ) (n + 1) j = if j = n then some x else sget σ n j := by
  unfold sget
  by_cases hj : j = n
  · subst hj; simp
  · rw [if_neg hj]
    by_cases hl : j < n
    · rw [if_pos (by omega), if_pos hl, show n + 1 - 1 - j = (n - 1 - j) + 1 by omega,
        List.getElem?_cons_succ]
    · rw [if_neg (by omega), if_neg hl]

theorem SigOK.grow {T T' : Tb} {σ : List Nat} (hT : T.WF) (hg : Grows T T') (h : SigOK T σ) :
    SigOK T' σ := fun x hx => lt_of_lt_of_le (h x hx) (hg.size_le hT)

theorem SIdx.grow {E : Env} {T T' : Tb} {a : Nat} {σ : List Nat} {n : Nat}
    {ρ : Nat → BitVec 64} (hT : T.WF) (hg : Grows T T') (hσ : SigOK T σ)
    (h : SIdx E T a σ n ρ) : SIdx E T' a σ n ρ := by
  refine ⟨h.1, fun j x hx => ?_⟩
  rw [h.2 j x hx, hg.V_eq E hT (hσ x (sget_mem hx))]

theorem bin2_spec (E : Env) (a : Nat) (σ : List Nat) (n : Nat) (T T' : Tb) (z : Nat)
    (ra : Option (Tb × Nat)) (rb : Tb → Option (Tb × Nat)) (op : Nat → Nat → Nd)
    (f : BitVec 64 → BitVec 64 → BitVec 64) (ea eb : (Nat → BitVec 64) → BitVec 64)
    (hop : ∀ (V : Nat → BitVec 64) p q, (op p q).den E V = f (V p) (V q))
    (hargs : ∀ p q m, p < m → q < m → (op p q).ArgsLt m)
    (hT : T.WF) (hσ : SigOK T σ)
    (ha : ∀ T₁ x, ra = some (T₁, x) →
      Grows T T₁ ∧ x < T₁.size ∧ ∀ ρ, SIdx E T a σ n ρ → T₁.V E x = ea ρ)
    (hb : ∀ T₁ T₂ y, T₁.WF → SigOK T₁ σ → rb T₁ = some (T₂, y) →
      Grows T₁ T₂ ∧ y < T₂.size ∧ ∀ ρ, SIdx E T₁ a σ n ρ → T₂.V E y = eb ρ)
    (h : bin2 ra rb op = some (T', z)) :
    Grows T T' ∧ z < T'.size ∧ ∀ ρ, SIdx E T a σ n ρ → T'.V E z = f (ea ρ) (eb ρ) := by
  unfold bin2 at h
  rcases hra : ra with _ | ⟨T₁, x⟩
  · simp [hra] at h
  simp only [hra] at h
  rcases hrb : rb T₁ with _ | ⟨T₂, y⟩
  · simp [hrb] at h
  simp only [hrb, Option.some.injEq] at h
  obtain ⟨g1, lx, vx⟩ := ha T₁ x hra
  obtain ⟨g2, ly, vy⟩ := hb T₁ T₂ y g1.1 (hσ.grow hT g1) hrb
  have lx2 : x < T₂.size := lt_of_lt_of_le lx (g2.size_le g1.1)
  obtain ⟨g3, lz, vz⟩ := Tb.addN_spec E T₂ (op x y) g2.1 (hargs _ _ _ lx2 ly)
  rw [h] at g3 lz vz
  refine ⟨(g1.trans g2).trans g3, lz, fun ρ hρ => ?_⟩
  rw [vz, hop, g2.V_eq E g1.1 lx, vx ρ hρ, vy ρ (hρ.grow hT g1 hσ)]

theorem internE_spec (E : Env) (a : Nat) (σ : List Nat) (n : Nat) :
    ∀ (e : WE) (T T' : Tb) (x : Nat), internE a σ n T e = some (T', x) → T.WF → SigOK T σ →
      Grows T T' ∧ x < T'.size ∧ ∀ ρ, SIdx E T a σ n ρ → T'.V E x = e.eval ρ := by
  intro e
  induction e with
  | v j =>
    intro T T' x h hT hσ
    simp only [internE] at h
    split_ifs at h with hja
    · rcases hc : cK j with _ | c
      · simp only [hc, Option.some.injEq] at h
        obtain ⟨g, l, v⟩ := Tb.add_spec E T (.inp j) hT trivial
        rw [h] at g l v
        exact ⟨g, l, fun ρ hρ => by rw [v]; exact hρ.1.1 j hja⟩
      · simp only [hc, Option.some.injEq] at h
        obtain ⟨g, l, v⟩ := Tb.addN_spec E T (.lit c) hT trivial
        rw [h] at g l v
        exact ⟨g, l, fun ρ hρ => by
          rw [v]
          simp only [Nd.den, WE.eval]
          rw [hρ.1.2 j c hja hc]⟩
    · split at h
      · rename_i y hy
        cases h
        exact ⟨Grows.refl hT, hσ _ (sget_mem hy), fun ρ hρ => (hρ.2 j _ hy).symm⟩
      · cases h
  | lit m =>
    intro T T' x h hT _
    simp only [internE, Option.some.injEq] at h
    obtain ⟨g, l, v⟩ := Tb.addN_spec E T (.lit m) hT trivial
    rw [h] at g l v
    exact ⟨g, l, fun _ _ => v⟩
  | add p q ihp ihq =>
    intro T T' x h hT hσ
    exact bin2_spec E a σ n T T' x _ _ Nd.add (· + ·) _ _ (fun _ _ _ => rfl)
      (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hσ (fun T₁ y hy => ihp T T₁ y hy hT hσ)
      (fun T₁ T₂ y h1 h2 hy => ihq T₁ T₂ y hy h1 h2) h
  | sub p q ihp ihq =>
    intro T T' x h hT hσ
    exact bin2_spec E a σ n T T' x _ _ Nd.sub (· - ·) _ _ (fun _ _ _ => rfl)
      (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hσ (fun T₁ y hy => ihp T T₁ y hy hT hσ)
      (fun T₁ T₂ y h1 h2 hy => ihq T₁ T₂ y hy h1 h2) h
  | mul p q ihp ihq =>
    intro T T' x h hT hσ
    exact bin2_spec E a σ n T T' x _ _ Nd.mul (· * ·) _ _ (fun _ _ _ => rfl)
      (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hσ (fun T₁ y hy => ihp T T₁ y hy hT hσ)
      (fun T₁ T₂ y h1 h2 hy => ihq T₁ T₂ y hy h1 h2) h
  | mulhi p q ihp ihq =>
    intro T T' x h hT hσ
    exact bin2_spec E a σ n T T' x _ _ Nd.mulhi MultiLimbKernel.mulhi _ _ (fun _ _ _ => rfl)
      (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hσ (fun T₁ y hy => ihp T T₁ y hy hT hσ)
      (fun T₁ T₂ y h1 h2 hy => ihq T₁ T₂ y hy h1 h2) h
  | and p q ihp ihq =>
    intro T T' x h hT hσ
    exact bin2_spec E a σ n T T' x _ _ Nd.and (· &&& ·) _ _ (fun _ _ _ => rfl)
      (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hσ (fun T₁ y hy => ihp T T₁ y hy hT hσ)
      (fun T₁ T₂ y h1 h2 hy => ihq T₁ T₂ y hy h1 h2) h
  | xor p q ihp ihq =>
    intro T T' x h hT hσ
    exact bin2_spec E a σ n T T' x _ _ Nd.xor (· ^^^ ·) _ _ (fun _ _ _ => rfl)
      (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hσ (fun T₁ y hy => ihp T T₁ y hy hT hσ)
      (fun T₁ T₂ y h1 h2 hy => ihq T₁ T₂ y hy h1 h2) h
  | shr p k ihp =>
    intro T T' x h hT hσ
    simp only [internE] at h
    split at h
    · rename_i T₁ y hy
      simp only [Option.some.injEq] at h
      obtain ⟨g1, l1, v1⟩ := ihp T T₁ y hy hT hσ
      obtain ⟨g2, l2, v2⟩ := Tb.addN_spec E T₁ (.shr y k) g1.1 l1
      rw [h] at g2 l2 v2
      refine ⟨g1.trans g2, l2, fun ρ hρ => ?_⟩
      rw [v2]
      simp only [Nd.den, WE.eval]
      rw [v1 ρ hρ]
    · cases h

theorem internS_spec (E : Env) (a : Nat) (ρ : Nat → BitVec 64) :
    ∀ (es : List WE) (σ : List Nat) (n : Nat) (T T' : Tb) (σ' : List Nat),
      internS a σ n T es = some (T', σ') → T.WF → SigOK T σ → Holds ρ n es →
      SIdx E T a σ n ρ →
      Grows T T' ∧ SigOK T' σ' ∧ SIdx E T' a σ' (n + es.length) ρ
  | [], σ, n, T, T', σ', h, hT, hσ, _, hI => by
      simp only [internS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Grows.refl hT, hσ, by simpa using hI⟩
  | e :: es, σ, n, T, T', σ', h, hT, hσ, hH, hI => by
      simp only [internS] at h
      split at h
      · rename_i T₁ x hx
        obtain ⟨g1, l1, v1⟩ := internE_spec E a σ n e T T₁ x hx hT hσ
        have hσ1 : SigOK T₁ (x :: σ) := by
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact l1
          · exact hσ.grow hT g1 y hy
        have hI1 : SIdx E T₁ a (x :: σ) (n + 1) ρ := by
          refine ⟨hI.1, fun j y hy => ?_⟩
          rw [sget_cons_eq] at hy
          split_ifs at hy with hj
          · subst hj
            simp only [Option.some.injEq] at hy
            subst hy
            rw [hH.1, v1 ρ hI]
          · rw [hI.2 j y hy, g1.V_eq E hT (hσ y (sget_mem hy))]
        obtain ⟨g2, hσ2, hI2⟩ := internS_spec E a ρ es (x :: σ) (n + 1) T₁ T' σ' h g1.1
          hσ1 hH.2 hI1
        refine ⟨g1.trans g2, hσ2, ?_⟩
        rw [show n + (e :: es).length = n + 1 + es.length by simp; omega]
        exact hI2
      · cases h

/-! ## 6. Symbolic execution of the canonical block -/

/-- The first entry of `r` in an association list. -/
def lk {α : Type} [DecidableEq α] : List (α × Nat) → α → Option Nat
  | [], _ => none
  | (k, x) :: t, r => if r = k then some x else lk t r

/-- Set the entry of `d`. -/
def insK {α : Type} [DecidableEq α] (l : List (α × Nat)) (d : α) (x : Nat) : List (α × Nat) :=
  (d, x) :: l.filter (fun p => !decide (p.1 = d))

theorem lk_mem {α : Type} [DecidableEq α] :
    ∀ (l : List (α × Nat)) (r : α) (x : Nat), lk l r = some x → (r, x) ∈ l
  | [], _, _, h => by simp [lk] at h
  | (k, y) :: t, r, x, h => by
      simp only [lk] at h
      split_ifs at h with hr
      · simp only [Option.some.injEq] at h
        subst hr; subst h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lk_mem t r x h)

theorem lk_filter {α : Type} [DecidableEq α] (d r : α) (h : r ≠ d) :
    ∀ l : List (α × Nat), lk (l.filter (fun p => !decide (p.1 = d))) r = lk l r
  | [] => rfl
  | (k, x) :: t => by
      by_cases hk : k = d
      · subst hk
        simp [List.filter, lk, h, lk_filter k r h t]
      · simp [List.filter, lk, hk, lk_filter d r h t]

theorem lk_insK {α : Type} [DecidableEq α] (l : List (α × Nat)) (d : α) (x : Nat) (r : α) :
    lk (insK l d x) r = if r = d then some x else lk l r := by
  by_cases hr : r = d
  · simp [insK, lk, hr]
  · simp only [insK, lk, if_neg hr]
    exact lk_filter d r hr l

theorem mem_insK {α : Type} [DecidableEq α] {l : List (α × Nat)} {d : α} {x : Nat}
    {p : α × Nat} (h : p ∈ insK l d x) : p = (d, x) ∨ p ∈ l := by
  simp only [insK, List.mem_cons, List.mem_filter] at h
  exact h.imp id (fun h => h.1)

/-- A symbolic machine state: the nodes of the listed registers and memory cells. -/
structure SSt where
  /-- The listed registers and their nodes. -/
  regs : List (String × Nat) := []
  /-- The listed cells and their nodes. -/
  mem : List ((String × Int) × Nat) := []

/-- Set the node of register `d`. -/
def SSt.setR (S : SSt) (d : String) (x : Nat) : SSt := { S with regs := insK S.regs d x }

/-- Set the node of cell `c`. -/
def SSt.setM (S : SSt) (c : String × Int) (x : Nat) : SSt := { S with mem := insK S.mem c x }

/-- The registers `R` and memory `M` agree with the symbolic state: a listed location
    holds the value of its node, an unlisted one its entry value; listed nodes are in the
    table. -/
def SRel (E : Env) (T : Tb) (S : SSt) (R : String → BitVec 64) (M : JMem 64) : Prop :=
  (∀ r, R r = (lk S.regs r).elim (E.st.regs r) (T.V E)) ∧
  (∀ b o, M b o = (lk S.mem (b, o)).elim (E.st.mem b o) (T.V E)) ∧
  (∀ p ∈ S.regs, p.2 < T.size) ∧ (∀ p ∈ S.mem, p.2 < T.size)

theorem SRel.grow {E : Env} {T T' : Tb} {S : SSt} {R : String → BitVec 64} {M : JMem 64}
    (hT : T.WF) (hg : Grows T T') (h : SRel E T S R M) : SRel E T' S R M := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun r => ?_, fun b o => ?_, fun p hp => lt_of_lt_of_le (h3 p hp) (hg.size_le hT),
    fun p hp => lt_of_lt_of_le (h4 p hp) (hg.size_le hT)⟩
  · rw [h1 r]
    cases hl : lk S.regs r with
    | none => rfl
    | some x => exact (hg.V_eq E hT (h3 _ (lk_mem _ _ _ hl))).symm
  · rw [h2 b o]
    cases hl : lk S.mem (b, o) with
    | none => rfl
    | some x => exact (hg.V_eq E hT (h4 _ (lk_mem _ _ _ hl))).symm

theorem SRel.setR {E : Env} {T : Tb} {S : SSt} {R : String → BitVec 64} {M : JMem 64}
    (h : SRel E T S R M) (d : String) (x : Nat) (hx : x < T.size) (v : BitVec 64)
    (hv : T.V E x = v) : SRel E T (S.setR d x) (fun r => if r = d then v else R r) M := by
  refine ⟨fun r => ?_, h.2.1, fun p hp => ?_, h.2.2.2⟩
  · simp only [SSt.setR, lk_insK]
    by_cases hr : r = d
    · simp [hr, hv]
    · simp only [hr, if_false]
      exact h.1 r
  · rcases mem_insK hp with rfl | hp
    · exact hx
    · exact h.2.2.1 p hp

theorem SRel.setM {E : Env} {T : Tb} {S : SSt} {R : String → BitVec 64} {M : JMem 64}
    (h : SRel E T S R M) (b : String) (o : Int) (x : Nat) (hx : x < T.size) (v : BitVec 64)
    (hv : T.V E x = v) :
    SRel E T (S.setM (b, o) x) R (fun b' o' => if b' = b ∧ o' = o then v else M b' o') := by
  refine ⟨h.1, fun b' o' => ?_, h.2.2.1, fun p hp => ?_⟩
  · simp only [SSt.setM, lk_insK, Prod.mk.injEq]
    by_cases hr : b' = b ∧ o' = o
    · simp [hr, hv]
    · simp only [hr, if_false]
      exact h.2.1 b' o'
  · rcases mem_insK hp with rfl | hp
    · exact hx
    · exact h.2.2.2 p hp

/-- The node of register `r`, added as a leaf when unlisted. -/
def rdR (T : Tb) (S : SSt) (r : String) : Tb × Nat :=
  match lk S.regs r with
  | some x => (T, x)
  | none => T.add (.reg r)

/-- The node of cell `(b, o)`, added as a leaf when unlisted. -/
def rdM (T : Tb) (S : SSt) (b : String) (o : Int) : Tb × Nat :=
  match lk S.mem (b, o) with
  | some x => (T, x)
  | none => T.add (.cell b o)

theorem rdR_spec (E : Env) (T : Tb) (S : SSt) (R : String → BitVec 64) (M : JMem 64)
    (r : String) (hT : T.WF) (h : SRel E T S R M) :
    Grows T (rdR T S r).1 ∧ (rdR T S r).2 < (rdR T S r).1.size ∧
      (rdR T S r).1.V E (rdR T S r).2 = R r := by
  unfold rdR
  cases hl : lk S.regs r with
  | some x =>
    refine ⟨Grows.refl hT, h.2.2.1 _ (lk_mem _ _ _ hl), ?_⟩
    rw [h.1 r, hl]
    rfl
  | none =>
    obtain ⟨g, l, v⟩ := Tb.add_spec E T (.reg r) hT trivial
    refine ⟨g, l, ?_⟩
    rw [v, h.1 r, hl]
    rfl

theorem rdM_spec (E : Env) (T : Tb) (S : SSt) (R : String → BitVec 64) (M : JMem 64)
    (b : String) (o : Int) (hT : T.WF) (h : SRel E T S R M) :
    Grows T (rdM T S b o).1 ∧ (rdM T S b o).2 < (rdM T S b o).1.size ∧
      (rdM T S b o).1.V E (rdM T S b o).2 = M b o := by
  unfold rdM
  cases hl : lk S.mem (b, o) with
  | some x =>
    refine ⟨Grows.refl hT, h.2.2.2 _ (lk_mem _ _ _ hl), ?_⟩
    rw [h.2.1 b o, hl]
    rfl
  | none =>
    obtain ⟨g, l, v⟩ := Tb.add_spec E T (.cell b o) hT trivial
    refine ⟨g, l, ?_⟩
    rw [v, h.2.1 b o, hl]
    rfl

/-- The symbolic effect of `d := op d r`. -/
def symBin (T : Tb) (S : SSt) (d r : String) (op : Nat → Nat → Nd) : Tb × SSt :=
  match rdR T S d with
  | (T₁, x) =>
    match rdR T₁ S r with
    | (T₂, y) =>
      match T₂.addN (op x y) with
      | (T₃, z) => (T₃, S.setR d z)

theorem symBin_spec (E : Env) (T : Tb) (S : SSt) (R : String → BitVec 64) (M : JMem 64)
    (d r : String) (op : Nat → Nat → Nd) (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hop : ∀ (V : Nat → BitVec 64) p q, (op p q).den E V = f (V p) (V q))
    (hargs : ∀ p q m, p < m → q < m → (op p q).ArgsLt m)
    (hT : T.WF) (hR : SRel E T S R M) :
    Grows T (symBin T S d r op).1 ∧
      SRel E (symBin T S d r op).1 (symBin T S d r op).2
        (fun r' => if r' = d then f (R d) (R r) else R r') M := by
  rcases h1 : rdR T S d with ⟨T₁, x⟩
  obtain ⟨g1, l1, v1⟩ := rdR_spec E T S R M d hT hR
  rw [h1] at g1 l1 v1
  have hR1 := hR.grow hT g1
  rcases h2 : rdR T₁ S r with ⟨T₂, y⟩
  obtain ⟨g2, l2, v2⟩ := rdR_spec E T₁ S R M r g1.1 hR1
  rw [h2] at g2 l2 v2
  have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
  rcases h3 : T₂.addN (op x y) with ⟨T₃, z⟩
  obtain ⟨g3, l3, v3⟩ := Tb.addN_spec E T₂ (op x y) g2.1 (hargs _ _ _ hx2 l2)
  rw [h3] at g3 l3 v3
  simp only [symBin, h1, h2, h3]
  refine ⟨(g1.trans g2).trans g3, ((hR1.grow g1.1 g2).grow g2.1 g3).setR d z l3 _ ?_⟩
  rw [v3, hop, g2.V_eq E g1.1 l1, v1, v2]

/-- One instruction on the symbolic state; `none` outside the handled forms. -/
def symStep (T : Tb) (S : SSt) : JInstr 64 → Option (Tb × SSt)
  | .mov d (.reg r) => match rdR T S r with | (T₁, x) => some (T₁, S.setR d x)
  | .mov d (.imm n) => match T.addN (.lit n) with | (T₁, x) => some (T₁, S.setR d x)
  | .add d (.reg r) => some (symBin T S d r .add)
  | .sub d (.reg r) => some (symBin T S d r .sub)
  | .and_ d (.reg r) => some (symBin T S d r .and)
  | .xor_ d (.reg r) => some (symBin T S d r .xor)
  | .imul d (.reg r) => some (symBin T S d r .mul)
  | .shr d (.imm k) =>
    if 0 < k ∧ k < 64 then
      match rdR T S d with
      | (T₁, x) =>
        match T₁.addN (.shr x k) with
        | (T₂, z) => some (T₂, S.setR d z)
    else none
  | .mulx h l (.reg a) (.reg b) =>
    if h = l then none else
      match rdR T S a with
      | (T₁, x) =>
        match rdR T₁ S b with
        | (T₂, y) =>
          match T₂.addN (.mul x y) with
          | (T₃, lo) =>
            match T₃.addN (.mulhi x y) with
            | (T₄, hi) => some (T₄, (S.setR l lo).setR h hi)
  | .loadMem d b o => match rdM T S b o with | (T₁, x) => some (T₁, S.setR d x)
  | .storeMem b o (.reg r) => match rdR T S r with | (T₁, x) => some (T₁, S.setM (b, o) x)
  | .storeMem b o (.imm n) => match T.addN (.lit n) with | (T₁, x) => some (T₁, S.setM (b, o) x)
  | _ => none

/-- A block on the symbolic state. -/
def symRun : Tb → SSt → List (JInstr 64) → Option (Tb × SSt)
  | T, S, [] => some (T, S)
  | T, S, i :: is =>
    match symStep T S i with
    | some (T₁, S₁) => symRun T₁ S₁ is
    | none => none

theorem evalInstr_shr_regs (s : JState 64) (d : String) (k : Nat) (hk0 : 0 < k) (hk : k < 64) :
    (evalInstr s (.shr d (.imm k))).regs = fun r => if r = d then s.regs d >>> k else s.regs r := by
  funext r
  have hk' : k % 64 = k := Nat.mod_eq_of_lt hk
  have hk'' : k ≠ 0 := by omega
  simp [evalInstr, JState.writeB5W, x86_SHR, shiftCount, rflags_OF, wshr, hk', hk'',
    Nat.min_eq_right hk.le]

theorem evalInstr_mulx_regs (s : JState 64) (h l a b : String) :
    (evalInstr s (.mulx h l (.reg a) (.reg b))).regs = fun r =>
      if r = h then MultiLimbKernel.mulhi (s.regs a) (s.regs b)
      else if r = l then s.regs a * s.regs b else s.regs r := by
  funext r
  have hlo : BitVec.ofNat 64 ((s.regs a).toNat * (s.regs b).toNat) = s.regs a * s.regs b := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul]
  have hhi : (high_bits ((s.regs a).toNat * (s.regs b).toNat) : BitVec 64)
      = MultiLimbKernel.mulhi (s.regs a) (s.regs b) := by
    simp [high_bits, MultiLimbKernel.mulhi, Nat.shiftRight_eq_div_pow]
  simp only [evalInstr, JState.setReg, x86_MULX_lo_hi, wumul, JOperand.eval, JState.get, hlo,
    hhi]

theorem symStep_sound (E : Env) {T T' : Tb} {S S' : SSt} (s : JState 64) (i : JInstr 64)
    (h : symStep T S i = some (T', S')) (hT : T.WF) (hR : SRel E T S s.regs s.mem) :
    Grows T T' ∧ SRel E T' S' (evalInstr s i).regs (evalInstr s i).mem := by
  cases i
  case mov d src =>
    cases src with
    | reg r =>
      rcases hp : rdR T S r with ⟨T₁, x⟩
      simp only [symStep, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := rdR_spec E T S _ _ r hT hR
      rw [hp] at g l v
      exact ⟨g, (hR.grow hT g).setR d x l _ v⟩
    | imm n =>
      rcases hp : T.addN (.lit n) with ⟨T₁, x⟩
      simp only [symStep, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := Tb.addN_spec E T (.lit n) hT trivial
      rw [hp] at g l v
      exact ⟨g, (hR.grow hT g).setR d x l _ v⟩
  case add d src =>
    cases src with
    | reg r =>
      simp only [symStep, Option.some.injEq] at h
      have := symBin_spec E T S s.regs s.mem d r Nd.add (· + ·) (fun _ _ _ => rfl)
        (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hR
      rw [h] at this
      exact this
    | imm _ => simp [symStep] at h
  case sub d src =>
    cases src with
    | reg r =>
      simp only [symStep, Option.some.injEq] at h
      have := symBin_spec E T S s.regs s.mem d r Nd.sub (· - ·) (fun _ _ _ => rfl)
        (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hR
      rw [h] at this
      exact this
    | imm _ => simp [symStep] at h
  case and_ d src =>
    cases src with
    | reg r =>
      simp only [symStep, Option.some.injEq] at h
      have := symBin_spec E T S s.regs s.mem d r Nd.and (· &&& ·) (fun _ _ _ => rfl)
        (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hR
      rw [h] at this
      exact this
    | imm _ => simp [symStep] at h
  case xor_ d src =>
    cases src with
    | reg r =>
      simp only [symStep, Option.some.injEq] at h
      have := symBin_spec E T S s.regs s.mem d r Nd.xor (· ^^^ ·) (fun _ _ _ => rfl)
        (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hR
      rw [h] at this
      exact this
    | imm _ => simp [symStep] at h
  case imul d src =>
    cases src with
    | reg r =>
      simp only [symStep, Option.some.injEq] at h
      have := symBin_spec E T S s.regs s.mem d r Nd.mul (· * ·) (fun _ _ _ => rfl)
        (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hR
      rw [h] at this
      exact this
    | imm _ => simp [symStep] at h
  case shr d src =>
    cases src with
    | reg _ => simp [symStep] at h
    | imm k =>
      simp only [symStep] at h
      split_ifs at h with hk
      · rcases hp : rdR T S d with ⟨T₁, x⟩
        obtain ⟨g1, l1, v1⟩ := rdR_spec E T S _ _ d hT hR
        rw [hp] at g1 l1 v1
        rcases hq : T₁.addN (.shr x k) with ⟨T₂, z⟩
        obtain ⟨g2, l2, v2⟩ := Tb.addN_spec E T₁ (.shr x k) g1.1 l1
        rw [hq] at g2 l2 v2
        simp only [hp, hq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [evalInstr_shr_regs s d k hk.1 hk.2]
        refine ⟨g1.trans g2, ((hR.grow hT g1).grow g1.1 g2).setR d z l2 _ ?_⟩
        rw [v2]
        simp only [Nd.den, v1]
  case mulx hd ld a b =>
    cases a with
    | imm _ => simp [symStep] at h
    | reg a =>
      cases b with
      | imm _ => simp [symStep] at h
      | reg b =>
        simp only [symStep] at h
        split_ifs at h with hhl
        rcases h1 : rdR T S a with ⟨T₁, x⟩
        obtain ⟨g1, l1, v1⟩ := rdR_spec E T S _ _ a hT hR
        rw [h1] at g1 l1 v1
        have hR1 := hR.grow hT g1
        rcases h2 : rdR T₁ S b with ⟨T₂, y⟩
        obtain ⟨g2, l2, v2⟩ := rdR_spec E T₁ S _ _ b g1.1 hR1
        rw [h2] at g2 l2 v2
        have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
        rcases h3 : T₂.addN (.mul x y) with ⟨T₃, lo⟩
        obtain ⟨g3, l3, v3⟩ := Tb.addN_spec E T₂ (.mul x y) g2.1 ⟨hx2, l2⟩
        rw [h3] at g3 l3 v3
        have hx3 : x < T₃.size := lt_of_lt_of_le hx2 (g3.size_le g2.1)
        have hy3 : y < T₃.size := lt_of_lt_of_le l2 (g3.size_le g2.1)
        rcases h4 : T₃.addN (.mulhi x y) with ⟨T₄, hi⟩
        obtain ⟨g4, l4, v4⟩ := Tb.addN_spec E T₃ (.mulhi x y) g3.1 ⟨hx3, hy3⟩
        rw [h4] at g4 l4 v4
        simp only [h1, h2, h3, h4, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [evalInstr_mulx_regs]
        have hlo4 : lo < T₄.size := lt_of_lt_of_le l3 (g4.size_le g3.1)
        have hR3 := (hR1.grow g1.1 g2).grow g2.1 g3
        have hxv : T₂.V E x = s.regs a := by rw [g2.V_eq E g1.1 l1, v1]
        have hlo : T₃.V E lo = s.regs a * s.regs b := by
          rw [v3]
          simp only [Nd.den]
          rw [hxv, v2]
        refine ⟨((g1.trans g2).trans g3).trans g4,
          ((hR3.setR ld lo l3 _ hlo).grow g3.1 g4).setR hd hi l4 _ ?_⟩
        rw [v4]
        simp only [Nd.den]
        rw [g3.V_eq E g2.1 hx2, g3.V_eq E g2.1 l2, hxv, v2]
  case loadMem d b o =>
    rcases hp : rdM T S b o with ⟨T₁, x⟩
    simp only [symStep, hp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨g, l, v⟩ := rdM_spec E T S _ _ b o hT hR
    rw [hp] at g l v
    exact ⟨g, (hR.grow hT g).setR d x l _ v⟩
  case storeMem b o src =>
    cases src with
    | imm n =>
      rcases hp : T.addN (.lit n) with ⟨T₁, x⟩
      simp only [symStep, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := Tb.addN_spec E T (.lit n) hT trivial
      rw [hp] at g l v
      exact ⟨g, (hR.grow hT g).setM b o x l _ v⟩
    | reg r =>
      rcases hp : rdR T S r with ⟨T₁, x⟩
      simp only [symStep, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := rdR_spec E T S _ _ r hT hR
      rw [hp] at g l v
      exact ⟨g, (hR.grow hT g).setM b o x l _ v⟩
  all_goals simp [symStep] at h

/-- Running a concatenation runs the first block, then the second from where it ends. -/
theorem runBlock_cat (s : JState 64) (xs ys : List (JInstr 64)) :
    runBlock s (xs ++ ys) = runBlock (runBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => exact ih (evalInstr s i)

theorem symRun_sound (E : Env) : ∀ (blk : List (JInstr 64)) (T T' : Tb) (S S' : SSt)
    (s : JState 64), symRun T S blk = some (T', S') → T.WF → SRel E T S s.regs s.mem →
    Grows T T' ∧ SRel E T' S' (runBlock s blk).regs (runBlock s blk).mem
  | [], T, T', S, S', s, h, hT, hR => by
      simp only [symRun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Grows.refl hT, hR⟩
  | i :: is, T, T', S, S', s, h, hT, hR => by
      simp only [symRun] at h
      split at h
      · rename_i T₁ S₁ hs
        obtain ⟨g1, hR1⟩ := symStep_sound E s i hs hT hR
        obtain ⟨g2, hR2⟩ := symRun_sound E is T₁ T' S₁ S' (evalInstr s i) h g1.1 hR1
        exact ⟨g1.trans g2, hR2⟩
      · cases h

/-! ## 7. Part checks -/

/-- A machine location: a register or a memory cell. -/
inductive Loc where
  | reg (r : String)
  | cell (b : String) (o : Int)
  deriving Repr

/-- The word at a location. -/
def Loc.val (s : JState 64) : Loc → BitVec 64
  | .reg r => s.regs r
  | .cell b o => s.mem b o

/-- The node the symbolic state lists at a location. -/
def Loc.node (S : SSt) : Loc → Option Nat
  | .reg r => lk S.regs r
  | .cell b o => lk S.mem (b, o)

/-- Set the node of a location. -/
def SSt.put (S : SSt) : Loc → Nat → SSt
  | .reg r, x => S.setR r x
  | .cell b o, x => S.setM (b, o) x

/-- Every location of `m` holds the value of its expression under `ρ`. -/
def MapHolds (ρ : Nat → BitVec 64) (m : List (Loc × WE)) (s : JState 64) : Prop :=
  ∀ p ∈ m, p.1.val s = p.2.eval ρ

theorem SRel.put {E : Env} {T : Tb} {S : SSt} {s : JState 64} (h : SRel E T S s.regs s.mem)
    (l : Loc) (x : Nat) (hx : x < T.size) (hv : T.V E x = l.val s) :
    SRel E T (S.put l x) s.regs s.mem := by
  cases l with
  | reg r =>
    have e : (fun r' => if r' = r then s.regs r else s.regs r') = s.regs := by
      funext r'
      split_ifs with hr
      · rw [hr]
      · rfl
    have := h.setR r x hx _ hv
    simp only [Loc.val] at this
    rw [e] at this
    exact this
  | cell b o =>
    have e : (fun b' o' => if b' = b ∧ o' = o then s.mem b o else s.mem b' o') = s.mem := by
      funext b' o'
      split_ifs with hr
      · rw [hr.1, hr.2]
      · rfl
    have := h.setM b o x hx _ hv
    simp only [Loc.val] at this
    rw [e] at this
    exact this

theorem SRel.node {E : Env} {T : Tb} {S : SSt} {s : JState 64} (h : SRel E T S s.regs s.mem)
    (l : Loc) (x : Nat) (hl : l.node S = some x) : x < T.size ∧ l.val s = T.V E x := by
  cases l with
  | reg r =>
    simp only [Loc.node] at hl
    refine ⟨h.2.2.1 _ (lk_mem _ _ _ hl), ?_⟩
    simp only [Loc.val]
    rw [h.1 r, hl]
    rfl
  | cell b o =>
    simp only [Loc.node] at hl
    refine ⟨h.2.2.2 _ (lk_mem _ _ _ hl), ?_⟩
    simp only [Loc.val]
    rw [h.2.1 b o, hl]
    rfl

/-- Intern the expressions of an entry map, over the leaves below `a`, and list their
    nodes at their locations. -/
def enter (a : Nat) : Tb → SSt → List (Loc × WE) → Option (Tb × SSt)
  | T, S, [] => some (T, S)
  | T, S, (l, e) :: m =>
    match internE a [] a T e with
    | some (T₁, x) => enter a T₁ (S.put l x) m
    | none => none

/-- Every location of an exit map lists the node of its expression. -/
def exitOK (a : Nat) (σ : List Nat) (n : Nat) (S : SSt) : Tb → List (Loc × WE) → Bool
  | _, [] => true
  | T, (l, e) :: m =>
    match internE a σ n T e, l.node S with
    | some (T₁, y), some x => decide (x = y) && exitOK a σ n S T₁ m
    | _, _ => false

theorem enter_sound (E : Env) (a : Nat) (ρ : Nat → BitVec 64) (hW : LeafOK E a ρ)
    (s : JState 64) : ∀ (m : List (Loc × WE)) (T T' : Tb) (S S' : SSt),
      enter a T S m = some (T', S') → T.WF → SRel E T S s.regs s.mem → MapHolds ρ m s →
      Grows T T' ∧ SRel E T' S' s.regs s.mem
  | [], T, T', S, S', h, hT, hR, _ => by
      simp only [enter, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Grows.refl hT, hR⟩
  | (l, e) :: m, T, T', S, S', h, hT, hR, hm => by
      simp only [enter] at h
      split at h
      · rename_i T₁ x hx
        obtain ⟨g1, l1, v1⟩ := internE_spec E a [] a e T T₁ x hx hT (fun _ h => by cases h)
        have hv : T₁.V E x = l.val s := by
          rw [v1 ρ ⟨hW, fun j y hy => by simp [sget_nil] at hy⟩]
          exact (hm (l, e) List.mem_cons_self).symm
        have hR1 := (hR.grow hT g1).put l x l1 hv
        obtain ⟨g2, hR2⟩ := enter_sound E a ρ hW s m T₁ T' (S.put l x) S' h g1.1 hR1
          (fun p hp => hm p (List.mem_cons_of_mem _ hp))
        exact ⟨g1.trans g2, hR2⟩
      · cases h

theorem exitOK_sound (E : Env) (a : Nat) (σ : List Nat) (n : Nat) (S : SSt)
    (ρ : Nat → BitVec 64) (s : JState 64) : ∀ (m : List (Loc × WE)) (T : Tb),
      exitOK a σ n S T m = true → T.WF → SigOK T σ → SIdx E T a σ n ρ →
      SRel E T S s.regs s.mem → MapHolds ρ m s
  | [], _, _, _, _, _, _ => fun _ h => by cases h
  | (l, e) :: m, T, h, hT, hσ, hI, hR => by
      simp only [exitOK] at h
      split at h
      · rename_i T₁ y x hy hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hxy, hrest⟩ := h
        obtain ⟨g1, -, v1⟩ := internE_spec E a σ n e T T₁ y hy hT hσ
        obtain ⟨lx, vx⟩ := hR.node l x hx
        have ih := exitOK_sound E a σ n S ρ s m T₁ hrest g1.1 (hσ.grow hT g1)
          (hI.grow hT g1 hσ) (hR.grow hT g1)
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · simp only
          rw [vx, ← g1.V_eq E hT lx, hxy, v1 ρ hI]
        · exact ih p hp
      · cases h

/-- The check of one part: the entry map interned over the leaves below `a`, the
    statements `es` of slots `a, a + 1, …`, the symbolic run of `blk`, and the exit map. -/
def partCheck (a : Nat) (es : List WE) (mIn mOut : List (Loc × WE))
    (blk : List (JInstr 64)) : Bool :=
  match enter a Tb.empty {} mIn with
  | some (T₀, S₀) =>
    match internS a [] a T₀ es with
    | some (T₁, σ) =>
      match symRun T₁ S₀ blk with
      | some (T₂, S₂) => exitOK a σ (a + es.length) S₂ T₂ mOut
      | none => false
    | none => false
  | none => false

theorem partCheck_sound (a : Nat) (es : List WE) (mIn mOut : List (Loc × WE))
    (blk : List (JInstr 64)) (h : partCheck a es mIn mOut blk = true) (ρ : Nat → BitVec 64)
    (hH : Holds ρ a es) (hK : ∀ j c, j < a → cK j = some c → ρ j = BitVec.ofNat 64 c)
    (s : JState 64) (hin : MapHolds ρ mIn s) :
    MapHolds ρ mOut (runBlock s blk) := by
  let E : Env := ⟨ρ, s⟩
  have hR0 : SRel E Tb.empty {} s.regs s.mem :=
    ⟨fun _ => rfl, fun _ _ => rfl, fun _ hp => by simp at hp, fun _ hp => by simp at hp⟩
  unfold partCheck at h
  split at h
  · rename_i T₀ S₀ he
    split at h
    · rename_i T₁ σ hs
      split at h
      · rename_i T₂ S₂ hr
        obtain ⟨g0, hR⟩ := enter_sound E a ρ ⟨fun _ _ => rfl, hK⟩ s mIn _ _ _ _ he
          Tb.empty_WF hR0 hin
        obtain ⟨g1, hσ1, hI1⟩ := internS_spec E a ρ es [] a T₀ T₁ σ hs g0.1
          (fun _ h => by cases h) hH
          ⟨⟨fun _ _ => rfl, hK⟩, fun j y hy => by simp [sget_nil] at hy⟩
        obtain ⟨g2, hR2⟩ := symRun_sound E blk T₁ T₂ S₀ S₂ s hr g1.1 (hR.grow g0.1 g1)
        exact exitOK_sound E a σ _ S₂ ρ _ mOut T₂ h g2.1 (hσ1.grow g1.1 g2)
          (hI1.grow g1.1 g2 hσ1) hR2
      · cases h
    · cases h
  · cases h

/-! ## 8. The eight parts of `ed25519_sc_reduce` -/

/-- The statements of slots `a .. b - 1`. -/
def xSlice (a b : Nat) : List WE := (xStmts.drop (a - 16)).take (b - a)

/-- The eight input limbs: cell `(%rsi, 8k)` holds slot `8 + k`. -/
def scrIn : List (Loc × WE) :=
  (List.range 8).map (fun k => (Loc.cell "%rsi" ((8 * k : Nat) : Int), WE.v (8 + k)))

/-- Register `r` holds the value of `e`. -/
def rg (r : String) (e : WE) : Loc × WE := (.reg r, e)

/-- The stack cell at offset `o` holds the value of `e`. -/
def sk (o : Int) (e : WE) : Loc × WE := (.cell "%rsp" o, e)

/-- The output cell at offset `o` holds slot `j`. -/
def dk (o : Int) (j : Nat) : Loc × WE := (.cell "%rdi" o, .v j)

/-- The four output limbs: cell `(%rdi, 8i)` holds slot `350 + i`. -/
def scrOut : List (Loc × WE) := [dk 0 350, dk 8 351, dk 16 352, dk 24 353]

/-- The stack cells holding the limbs of `L` and the upper input limbs, used by parts 2 to 7. -/
def scrKeep : List (Loc × WE) :=
  [sk 88 (.lit 1152921504606846976), sk 96 (.lit 0), sk 104 (.lit 1503914060200516822),
    sk 112 (.lit 6346243789798364141), sk 128 (.v 11), sk 120 (.v 10), sk 80 (.v 9),
    sk 72 (.v 8)]

/-- The stack cells holding the limbs of `muNat`, used by parts 2 and 3. -/
def scrMu : List (Loc × WE) :=
  [sk 40 (.lit 15), sk 32 (.lit 18446744073709551615), sk 24 (.lit 18446744073709551595),
    sk 16 (.lit 2379626136568277415), sk 8 (.lit 17121812371768873755)]

/-- The carry-out expression of `s = p + q` with the all-ones literal written first in the
    complement, the operand order of the machine code. -/
def cw (s : WE) (p q : WE) : WE :=
  .shr (.xor (.and p q) (.and (.xor p q) (.xor (.lit 18446744073709551615) s))) 63

/-- The locations after part 1. -/
def scrMap1 : List (Loc × WE) :=
  [rg "%rbp" (.lit 18446744073709551615), rg "%rdi" (.xor (.v 43) (.v 62)),
    rg "%rcx" (.and (.v 43) (.v 62)), rg "%rsi" (.add (.v 61) (cw (.v 62) (.v 59) (.v 60))),
    rg "%r10" (.v 63), rg "%r11" (.v 58), rg "%rax" (.v 49), rg "%rbx" (.v 48)] ++
    scrMu ++ [sk 64 (.v 15), sk 56 (.v 14), sk 48 (.v 13), sk 0 (.v 12)] ++ scrKeep

/-- The locations after part 2. -/
def scrMap2 : List (Loc × WE) :=
  [rg "%rsi" (.v 115), rg "%rbx" (.v 114), rg "%r10" (.v 113), rg "%r11" (.v 108),
    rg "%rax" (.v 99), rg "%r8" (.v 98)] ++
    scrMu ++ [sk 64 (.v 15), sk 56 (.v 14), sk 48 (.v 13), sk 0 (.v 12)] ++ scrKeep

/-- The locations after part 3. -/
def scrMap3 : List (Loc × WE) :=
  [rg "%r12" (.xor (.v 164) (.v 165)), rg "%rcx" (.and (.v 164) (.v 165)), rg "%r9" (.v 168),
    rg "%rbp" (.v 167), rg "%rdi" (.v 166), rg "%r10" (.v 163), rg "%r11" (.v 158),
    rg "%rax" (.v 149), rg "%r8" (.v 148)] ++
    scrMu ++ [sk 64 (.v 15), sk 56 (.v 14), sk 48 (.v 13)] ++ scrKeep

/-- The locations after part 4. -/
def scrMap4 : List (Loc × WE) :=
  [rg "%rsi" (.xor (.v 198) (.v 217)), rg "%rbx" (.and (.v 198) (.v 217)),
    rg "%rcx" (.add (.v 216) (cw (.v 217) (.v 214) (.v 215))), rg "%r9" (.v 218),
    rg "%r10" (.v 213), rg "%r11" (.v 208), rg "%rax" (.v 199), sk 40 (.lit 15),
    sk 64 (.v 15)] ++ scrKeep

/-- The locations after part 5. -/
def scrMap5 : List (Loc × WE) :=
  [rg "%rcx" (.v 267), rg "%rdi" (.add (.v 266) (cw (.v 267) (.lit 0) (.v 265))),
    rg "%rbp" (.v 268), rg "%rbx" (.v 267), rg "%r11" (.v 258), rg "%r12" (.v 253),
    rg "%r9" (.v 218), sk 48 (.v 248), sk 64 (.v 228), sk 40 (.v 223)] ++ scrKeep

/-- The locations after part 6. -/
def scrMap6 : List (Loc × WE) :=
  [rg "%rbp" (.v 268), sk 32 (.v 288), sk 48 (.v 248), sk 64 (.v 228)] ++ scrKeep

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
