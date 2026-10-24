/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.FoldRange
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Bit-scanning loops of the haxpipeT surface

Square-and-multiply and double-and-add loops as haxpipeT prints them: a counter
`Hax.whileFold` that decrements its counter from `n` to `0`, whose body scans the
bits of a `w`-bit limb from the most significant down with a nested counter loop
of the same shape, and the `Hax.foldRange 0 N` form that selects between the
doubled and the doubled-plus-base accumulator at each bit.

## Main results

* `downFold` — the fold of `g (n-1)`, …, `g 0`, and `downFold_eq_foldl`.
* `whileFold_countdown`, `whileFold_countdown_int` — the decrementing counter loop
  is `downFold` of its body.
* `bitand_shr_w_one`, `beq_bitand_shr_w_one` — the extracted bit test is
  `Nat.testBit` of the limb.
* `innerBody`, `outerBody` — the two nested loop bodies of the square-and-multiply
  scan, as the extraction prints them.
* `outerBody_whileFold` — the scan is a `downFold` of `downFold`s of `bitStep`.
* `squareMultiply_rel` — under a simulation relation `R` into a monoid, the scan
  over `n` limbs of `w` bits computes `x ^ (∑ limb_k 2^(w k))`.
* `doubleAdd_rel` — the additive version, `(∑ limb_k 2^(w k)) • P`.
* `foldRange_select_rel` — the `Hax.foldRange 0 N` select loop computes
  `(∑_{j<N} bit_j 2^j) • P`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.BitScan

open scoped BigOperators

variable {α : Type}

/-! ## Countdown folds -/

/-- `downFold g n acc` applies `g (n-1)`, then `g (n-2)`, …, then `g 0` to `acc`. -/
def downFold (g : Nat → α → α) : Nat → α → α
  | 0, acc => acc
  | n + 1, acc => downFold g n (g n acc)

/-- `downFold` is the left fold of `g` over `n-1, n-2, …, 0`. -/
theorem downFold_eq_foldl (g : Nat → α → α) (n : Nat) (acc : α) :
    downFold g n acc = (List.range n).reverse.foldl (fun a i => g i a) acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp [downFold, ih, List.range_succ]

/-- A decrementing counter `Hax.whileFold` from `n`, whose body steps the state
    with `g` at the decremented counter, returns `(0, downFold g n acc)`. -/
theorem whileFold_countdown {β : Type} (g : Int → β → β)
    (body : Int × β → ControlFlow (Int × β) (Int × β))
    (hbody : ∀ i acc, body (i, acc) =
      if Hax.gt i (0 : Int) then Hax.cfContinue (Hax.sub i (1 : Int), g (Hax.sub i (1 : Int)) acc)
      else Hax.cfBreak (i, acc))
    (n : Nat) (acc : β) :
    Hax.whileFold ((n : Int), acc) (fun _ => true) body
      = ControlFlow.Break (0, downFold (fun k a => g (k : Int) a) n acc) := by
  refine Hax.whileFold_eq_of_fuel (n := n + 1) ?_
  induction n generalizing acc with
  | zero => simp [Hax.whileFoldFuel, hbody, Hax.gt, Hax.cfBreak, downFold]
  | succ n ih =>
    have hs : Hax.sub ((n + 1 : Nat) : Int) (1 : Int) = (n : Int) := by
      simp [Hax.sub]
    have hg : Hax.gt ((n + 1 : Nat) : Int) (0 : Int) = true := by
      simp [Hax.gt]
    rw [Hax.whileFoldFuel]
    simp only [hbody, hg, hs, ite_true, Hax.cfContinue]
    exact ih (g n acc)

/-- The decrementing counter loop from an integer `n ≥ 0`. -/
theorem whileFold_countdown_int {β : Type} (g : Int → β → β)
    (body : Int × β → ControlFlow (Int × β) (Int × β))
    (hbody : ∀ i acc, body (i, acc) =
      if Hax.gt i (0 : Int) then Hax.cfContinue (Hax.sub i (1 : Int), g (Hax.sub i (1 : Int)) acc)
      else Hax.cfBreak (i, acc))
    (n : Int) (hn : 0 ≤ n) (acc : β) :
    (Hax.whileFold (n, acc) (fun _ => true) body).merge
      = (0, downFold (fun k a => g (k : Int) a) n.toNat acc) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [whileFold_countdown g body hbody m acc]
  rfl

/-! ## The bit test -/

/-- The extracted bit test `(limb >> i) & 1` at width `w` is bit `i` of the limb
    reduced mod `2^w`. -/
theorem bitand_shr_w_one (w : Nat) (hw : 0 < w) (limb i : Int) :
    Hax.bitand_w w (Hax.shr_w w limb i) (1 : Int)
      = if (limb.toNat % 2 ^ w).testBit i.toNat then 1 else 0 := by
  have hm : limb.toNat % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have h1 : (1 : Nat) % 2 ^ w = 1 := Nat.one_mod_two_pow hw
  unfold Hax.bitand_w Hax.shr_w
  generalize limb.toNat % 2 ^ w = m at hm ⊢
  have hsh : m >>> i.toNat % 2 ^ w = m >>> i.toNat :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) hm)
  rw [Int.toNat_natCast, hsh, Int.toNat_one, h1, Nat.and_one_is_mod,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i.toNat) with h | h <;> simp [h]

/-- The extracted bit comparison `(limb >> i) & 1 == 1` at width `w` is bit `i`
    of the limb reduced mod `2^w`. -/
theorem beq_bitand_shr_w_one (w : Nat) (hw : 0 < w) (limb i : Int) :
    Hax.beq (Hax.bitand_w w (Hax.shr_w w limb i) (1 : Int)) (1 : Int)
      = (limb.toNat % 2 ^ w).testBit i.toNat := by
  rw [bitand_shr_w_one w hw]
  split <;> simp [Hax.beq, *]

/-- The extracted bit comparison on a limb in `[0, 2^w)` is bit `i` of the limb. -/
theorem beq_bitand_shr_w_one_of_lt (w : Nat) (hw : 0 < w) (limb i : Int)
    (h0 : 0 ≤ limb) (hlt : limb < 2 ^ w) :
    Hax.beq (Hax.bitand_w w (Hax.shr_w w limb i) (1 : Int)) (1 : Int)
      = limb.toNat.testBit i.toNat := by
  rw [beq_bitand_shr_w_one w hw, Nat.mod_eq_of_lt ((Int.toNat_lt h0).mpr (by exact_mod_cast hlt))]

/-! ## The square-and-multiply loop bodies -/

/-- The inner loop body of the extracted square-and-multiply scan: decrement the
    bit counter, square, and multiply when the bit of `limb` at the counter is set. -/
def innerBody (w : Nat) (limb : Int) (sq mulx : α → α) :
    Int × α → ControlFlow (Int × α) (Int × α) :=
  fun (i, acc) =>
    if Hax.gt i (0 : Int) then
      let i := Hax.sub i (1 : Int)
      let acc := sq acc
      if Hax.beq (Hax.bitand_w w (Hax.shr_w w limb i) (1 : Int)) (1 : Int) then
        let acc := mulx acc
        Hax.cfContinue (i, acc)
      else
        Hax.cfContinue (i, acc)
    else
      Hax.cfBreak (i, acc)

/-- The outer loop body of the extracted square-and-multiply scan: decrement the
    limb counter and run the inner bit loop over the limb at the counter. -/
def outerBody (w : Nat) (limbAt : Int → Int) (sq mulx : α → α) :
    Int × α → ControlFlow (Int × α) (Int × α) :=
  fun (k, acc) =>
    if Hax.gt k (0 : Int) then
      let k := Hax.sub k (1 : Int)
      let limb := limbAt k
      let _wf := Hax.whileFold ((w : Int), acc) (fun _ => true) (innerBody w limb sq mulx)
      let (_, acc) := _wf.merge
      Hax.cfContinue (k, acc)
    else
      Hax.cfBreak (k, acc)

/-- One step of the bit scan at bit `k`: square, then multiply when bit `k` of
    `limb` is set. -/
def bitStep (w : Nat) (limb : Int) (sq mulx : α → α) (k : Nat) (a : α) : α :=
  if Hax.beq (Hax.bitand_w w (Hax.shr_w w limb (k : Int)) (1 : Int)) (1 : Int) then
    mulx (sq a) else sq a

/-- The inner bit loop from `w` is the `downFold` of `bitStep` over `w` bits. -/
theorem innerBody_whileFold (w : Nat) (limb : Int) (sq mulx : α → α) (a : α) :
    (Hax.whileFold ((w : Int), a) (fun _ => true) (innerBody w limb sq mulx)).merge
      = (0, downFold (bitStep w limb sq mulx) w a) := by
  rw [whileFold_countdown (fun j b =>
      if Hax.beq (Hax.bitand_w w (Hax.shr_w w limb j) (1 : Int)) (1 : Int) then mulx (sq b)
      else sq b)]
  · rfl
  · intro i acc
    simp only [innerBody]
    split_ifs <;> rfl

/-- The outer limb loop from `n` is the `downFold` over the limbs of the inner
    `downFold` of `bitStep`. -/
theorem outerBody_whileFold (w : Nat) (limbAt : Int → Int) (sq mulx : α → α)
    (n : Nat) (a : α) :
    (Hax.whileFold ((n : Int), a) (fun _ => true) (outerBody w limbAt sq mulx)).merge
      = (0, downFold (fun k b => downFold (bitStep w (limbAt (k : Int)) sq mulx) w b) n a) := by
  rw [whileFold_countdown (fun j b =>
      (Hax.whileFold ((w : Int), b) (fun _ => true) (innerBody w (limbAt j) sq mulx)).merge.2)]
  · refine congrArg (Prod.mk 0) ?_
    simp only [innerBody_whileFold]
  · intro i acc
    simp only [outerBody]

/-! ## Square-and-multiply under a simulation relation -/

section Monoid

variable {M : Type} [Monoid M] (R : α → M → Prop) (x : M) {sq mulx : α → α}

/-- The bit scan over the low `k` bits of a limb maps `x ^ e` to
    `x ^ (e * 2^k + L % 2^k)`, where `L` is the limb reduced mod `2^w`. -/
theorem downFold_bitStep_rel (hsq : ∀ a m, R a m → R (sq a) (m * m))
    (hmul : ∀ a m, R a m → R (mulx a) (m * x)) (w : Nat) (hw : 0 < w) (limb : Int)
    (k : Nat) (a : α) (e : Nat) (ha : R a (x ^ e)) :
    R (downFold (bitStep w limb sq mulx) k a)
      (x ^ (e * 2 ^ k + limb.toNat % 2 ^ w % 2 ^ k)) := by
  induction k generalizing a e with
  | zero => simpa [downFold, Nat.mod_one] using ha
  | succ k ih =>
    have hbeq := beq_bitand_shr_w_one w hw limb (k : Int)
    rw [Int.toNat_natCast, Nat.testBit_eq_decide_div_mod_eq] at hbeq
    have hmod : limb.toNat % 2 ^ w % 2 ^ (k + 1)
        = limb.toNat % 2 ^ w % 2 ^ k + 2 ^ k * (limb.toNat % 2 ^ w / 2 ^ k % 2) :=
      Nat.mod_pow_succ
    simp only [downFold]
    rcases Nat.mod_two_eq_zero_or_one (limb.toNat % 2 ^ w / 2 ^ k) with hd | hd
    · have h1 : R (bitStep w limb sq mulx k a) (x ^ (2 * e)) := by
        simp only [bitStep, hbeq, hd]
        simpa [two_mul, pow_add] using hsq a _ ha
      convert ih _ _ h1 using 2
      rw [hmod, hd, pow_succ]; ring
    · have h1 : R (bitStep w limb sq mulx k a) (x ^ (2 * e + 1)) := by
        simp only [bitStep, hbeq, hd]
        simpa [two_mul, pow_add] using hmul _ _ (hsq a _ ha)
      convert ih _ _ h1 using 2
      rw [hmod, hd, pow_succ]; ring

/-- The limb scan over `n` limbs of `w` bits maps `x ^ e` to
    `x ^ (e * 2^(w n) + ∑_{k<n} limb_k 2^(w k))`. -/
theorem downFold_limbs_rel (hsq : ∀ a m, R a m → R (sq a) (m * m))
    (hmul : ∀ a m, R a m → R (mulx a) (m * x)) (w : Nat) (hw : 0 < w)
    (limbAt : Int → Int) (n : Nat)
    (hlimb : ∀ k : Nat, k < n → 0 ≤ limbAt k ∧ limbAt k < 2 ^ w)
    (a : α) (e : Nat) (ha : R a (x ^ e)) :
    R (downFold (fun k b => downFold (bitStep w (limbAt (k : Int)) sq mulx) w b) n a)
      (x ^ (e * 2 ^ (w * n) + ∑ k ∈ Finset.range n, (limbAt k).toNat * 2 ^ (w * k))) := by
  induction n generalizing a e with
  | zero => simpa [downFold] using ha
  | succ n ih =>
    obtain ⟨h0, hlt⟩ := hlimb n (Nat.lt_succ_self n)
    have hl : (limbAt n).toNat % 2 ^ w = (limbAt n).toNat :=
      Nat.mod_eq_of_lt ((Int.toNat_lt h0).mpr (by exact_mod_cast hlt))
    have h1 := downFold_bitStep_rel R x hsq hmul w hw (limbAt n) w a e ha
    rw [hl, hl] at h1
    simp only [downFold]
    convert ih (fun k hk => hlimb k (Nat.lt_succ_of_lt hk)) _ _ h1 using 2
    rw [Finset.sum_range_succ, Nat.mul_succ, pow_add]
    ring

/-- The extracted square-and-multiply scan over `n` limbs of `w` bits, started from
    a state related to `x ^ e`, ends related to
    `x ^ (e * 2^(w n) + ∑_{k<n} limb_k 2^(w k))`. -/
theorem squareMultiply_rel (hsq : ∀ a m, R a m → R (sq a) (m * m))
    (hmul : ∀ a m, R a m → R (mulx a) (m * x)) (w : Nat) (hw : 0 < w)
    (limbAt : Int → Int) (n : Nat)
    (hlimb : ∀ k : Nat, k < n → 0 ≤ limbAt k ∧ limbAt k < 2 ^ w)
    (a : α) (e : Nat) (ha : R a (x ^ e)) :
    R (Hax.whileFold ((n : Int), a) (fun _ => true) (outerBody w limbAt sq mulx)).merge.2
      (x ^ (e * 2 ^ (w * n) + ∑ k ∈ Finset.range n, (limbAt k).toNat * 2 ^ (w * k))) := by
  rw [outerBody_whileFold]
  exact downFold_limbs_rel R x hsq hmul w hw limbAt n hlimb a e ha

end Monoid

/-- The extracted double-and-add scan over `n` limbs of `w` bits, started from a
    state related to `e • P`, ends related to
    `(e * 2^(w n) + ∑_{k<n} limb_k 2^(w k)) • P`. -/
theorem doubleAdd_rel {M : Type} [AddMonoid M] (R : α → M → Prop) (P : M)
    {dbl addP : α → α} (hdbl : ∀ a m, R a m → R (dbl a) (m + m))
    (hadd : ∀ a m, R a m → R (addP a) (m + P)) (w : Nat) (hw : 0 < w)
    (limbAt : Int → Int) (n : Nat)
    (hlimb : ∀ k : Nat, k < n → 0 ≤ limbAt k ∧ limbAt k < 2 ^ w)
    (a : α) (e : Nat) (ha : R a (e • P)) :
    R (Hax.whileFold ((n : Int), a) (fun _ => true) (outerBody w limbAt dbl addP)).merge.2
      ((e * 2 ^ (w * n) + ∑ k ∈ Finset.range n, (limbAt k).toNat * 2 ^ (w * k)) • P) := by
  have h := squareMultiply_rel (fun b (m : Multiplicative M) => R b m.toAdd)
    (Multiplicative.ofAdd P) (sq := dbl) (mulx := addP)
    (fun b m hb => by simpa using hdbl b _ hb) (fun b m hb => by simpa using hadd b _ hb)
    w hw limbAt n hlimb a e (by simpa using ha)
  simpa using h

/-! ## The `foldRange` select loop -/

/-- The top `t` of `N` bits as a number: `∑_{j<t} bit (N - t + j) * 2^j`. -/
def hiVal (bit : Int → Int) (N t : Nat) : Nat :=
  ∑ j ∈ Finset.range t, (bit ((N - t + j : Nat) : Int)).toNat * 2 ^ j

/-- The top `t + 1` bits are bit `N - (t + 1)` plus twice the top `t` bits. -/
theorem hiVal_succ (bit : Int → Int) (N t : Nat) (ht : t < N) :
    hiVal bit N (t + 1) = (bit ((N - (t + 1) : Nat) : Int)).toNat + 2 * hiVal bit N t := by
  unfold hiVal
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show N - (t + 1) + (j + 1) = N - t + j by omega, pow_succ]
    ring

/-- All `N` bits: `hiVal bit N N = ∑_{j<N} bit j * 2^j`. -/
theorem hiVal_self (bit : Int → Int) (N : Nat) :
    hiVal bit N N = ∑ j ∈ Finset.range N, (bit j).toNat * 2 ^ j := by
  simp [hiVal]

/-- The extracted MSB-first select loop over `N` bits, started from a state
    related to `e • P`, ends related to `(e * 2^N + ∑_{j<N} bit_j 2^j) • P`; each
    step doubles, adds the base and selects the sum when the bit at `top - i` is
    `1` and the double when it is `0`. The select step is required to relate its
    result only when both of its arguments are related. -/
theorem foldRange_select_rel {M : Type} [AddMonoid M] (R : α → M → Prop) (P : M)
    {dbl addP : α → α} {sel : Int → α → α → α}
    (hdbl : ∀ a m, R a m → R (dbl a) (m + m))
    (hadd : ∀ a m, R a m → R (addP a) (m + P))
    (hsel : ∀ c a b ma mb, (c = 0 ∨ c = 1) → R a ma → R b mb →
      R (sel c a b) (if c = 1 then ma else mb))
    (N : Nat) (top : Int) (htop : top + 1 = N) (bit : Int → Int)
    (hbit : ∀ j : Nat, j < N → bit j = 0 ∨ bit j = 1)
    (init : α) (e : Nat) (hinit : R init (e • P)) :
    R (Hax.foldRange 0 (N : Int) init
        (fun i acc => sel (bit (Hax.sub top i)) (addP (dbl acc)) (dbl acc)))
      ((e * 2 ^ N + ∑ j ∈ Finset.range N, (bit j).toNat * 2 ^ j) • P) := by
  have key := Hax.foldRange_induct
    (P := fun i acc => ∀ t : Nat, i = t → R acc ((e * 2 ^ t + hiVal bit N t) • P))
    (lo := 0) (hi := (N : Int))
    (f := fun i acc => sel (bit (Hax.sub top i)) (addP (dbl acc)) (dbl acc))
    (init := init) (Int.natCast_nonneg N) ?_ ?_ N rfl
  · rwa [hiVal_self] at key
  · intro t ht
    obtain rfl : t = 0 := by omega
    simpa [hiVal] using hinit
  · intro i acc hi0 hiN ih t hit
    obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
    have hst : t = s + 1 := by omega
    subst hst
    have hsN : s < N := by omega
    have hacc := ih s rfl
    have hidx : Hax.sub top (s : Int) = ((N - (s + 1) : Nat) : Int) := by
      simp only [Hax.sub]; omega
    have hdbl' := hdbl _ _ hacc
    have hadd' := hadd _ _ hdbl'
    rw [hidx, hiVal_succ bit N s hsN]
    rcases hbit (N - (s + 1)) (by omega) with hb | hb <;> rw [hb]
    · have h := hsel 0 _ _ _ _ (Or.inl rfl) hadd' hdbl'
      rw [ite_eq_right (by decide)] at h
      convert h using 2
      rw [← add_nsmul]; congr 1; simp; ring
    · have h := hsel 1 _ _ _ _ (Or.inr rfl) hadd' hdbl'
      rw [ite_eq_left rfl] at h
      convert h using 2
      rw [← add_nsmul, ← succ_nsmul]; congr 1; simp; ring

end CatCrypt.Hax.BitScan
