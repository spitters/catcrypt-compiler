/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.Linarith

/-!
# The interval domain of a lane-wise range analysis

An integer interval `i = (lo, hi)` bounds a `w`-bit word `x` when `x` is the residue
mod `2^w` of some integer in `[lo, hi]` (`Iv.Mem`). The interval may reach below zero or
past `2^w`, so a subtraction that wraps keeps an exact bound. The lane interval
`ivLane w i` is the shift of `i` into `[0, 2^w)` when `i` meets one multiple of `2^w`
only, and the full lane range otherwise; it bounds `x.toNat` itself.

The module is independent of any IR: its statements are over `BitVec w` and its
operations, so an analysis over any word-level IR instantiates it.

## Main definitions

* `Iv`, `Iv.Mem`, `ivTop`, `ivNorm`, `ivLane`, `ivConst`, `ivSingle?`: the domain.
* `ivAdd`, `ivSub`, `ivMul`, `ivAnd`, `ivShr`, `ivShl`, `ivMulhi`, `ivCast`: the
  transfer functions.
* `condAdd`, `umin`, `ivCondAdd?`: the conditional add `d + ((0 - (d >>> (w-1))) &&& C)`
  and its range.
* `barrettBound`, `ivBarrett?`: the range of the Barrett remainder.

## Main results

* `Iv.mem_lane`: a member of `i` has its `toNat` in the lane interval;
  `Iv.toNat_eq_of_single`: a one-point lane interval fixes `toNat`.
* `Iv.mem_add`, `Iv.mem_sub`, `Iv.mem_mul`, `Iv.mem_and`, `Iv.mem_shr`, `Iv.mem_shl`,
  `Iv.mem_mulhi`, `Iv.mem_cast`, `Iv.mem_const`: soundness of the transfer functions.
* `Iv.mem_condAdd`, `Iv.mem_ivCondAdd`: soundness of the conditional-add rule.
* `condAdd_eq_umin`, `condAdd_sub_eq_umin`: the conditional add of a constant is the
  unsigned minimum of `d` and `d + C`, and of `x` and `x - C` when `d = x - C`.
* `barrett_nat`, `Iv.mem_barrett_toNat`, `Iv.mem_barrett`, `Iv.mem_ivBarrett`: the
  Barrett remainder lies in
  `[0, min X (X·δ/2^(s+t) + p·m/2^t + p + 1)]`, `δ = 2^(s+t) - m·p`.
* `mul_eq_mul_setWidth32`: a 64-bit product of operands below `2^32` is the product of
  their zero-extended low halves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RangeDomain

/-! ## 1. The domain -/

/-- An integer interval `[lo, hi]`. -/
abbrev Iv := Int × Int

/-- `x` is the residue mod `2^w` of an integer in `[i.1, i.2]`. -/
def Iv.Mem (w : Nat) (i : Iv) (x : BitVec w) : Prop :=
  ∃ v : Int, i.1 ≤ v ∧ v ≤ i.2 ∧ v % 2 ^ w = (x.toNat : Int)

/-- The full lane range `[0, 2^w - 1]`. -/
def ivTop (w : Nat) : Iv := (0, 2 ^ w - 1)

/-- `i` when it spans fewer than `2^w` integers, else the full lane range. -/
def ivNorm (w : Nat) (i : Iv) : Iv :=
  if i.2 - i.1 < 2 ^ w then i else ivTop w

/-- The lane values of `i`: its shift into `[0, 2^w)` when `i` meets one multiple of
    `2^w` only, else the full lane range. -/
def ivLane (w : Nat) (i : Iv) : Iv :=
  if i.2 / 2 ^ w = i.1 / 2 ^ w then
    (i.1 - i.1 / 2 ^ w * 2 ^ w, i.2 - i.1 / 2 ^ w * 2 ^ w)
  else ivTop w

/-- The interval of the constant `BitVec.ofNat w n`. -/
def ivConst (w n : Nat) : Iv := (((n % 2 ^ w : Nat) : Int), ((n % 2 ^ w : Nat) : Int))

/-- The value of a one-point interval `[k, k]` with `0 ≤ k`. -/
def ivSingle? (i : Iv) : Option Nat :=
  if 0 ≤ i.1 ∧ i.1 = i.2 then some i.1.toNat else none

namespace Iv

variable {w : Nat}

theorem mem_iff_ofInt (i : Iv) (x : BitVec w) :
    i.Mem w x ↔ ∃ v : Int, i.1 ≤ v ∧ v ≤ i.2 ∧ BitVec.ofInt w v = x := by
  have key : ∀ v : Int, v % 2 ^ w = (x.toNat : Int) ↔ BitVec.ofInt w v = x := by
    intro v
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofInt]; push_cast; rw [h]; simp
    · intro h
      subst h
      rw [BitVec.toNat_ofInt]
      push_cast
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  unfold Iv.Mem
  constructor
  · rintro ⟨v, h1, h2, h3⟩; exact ⟨v, h1, h2, (key v).1 h3⟩
  · rintro ⟨v, h1, h2, h3⟩; exact ⟨v, h1, h2, (key v).2 h3⟩

/-- A natural-number witness: `x` is `n mod 2^w` for `n` in `i`. -/
theorem mem_of_nat {i : Iv} {x : BitVec w} (n : Nat) (h1 : i.1 ≤ (n : Int))
    (h2 : (n : Int) ≤ i.2) (hx : x.toNat = n % 2 ^ w) : i.Mem w x :=
  ⟨n, h1, h2, by rw [hx]; push_cast; rfl⟩

theorem mem_of_bounds {i : Iv} {x : BitVec w} (h1 : i.1 ≤ (x.toNat : Int))
    (h2 : (x.toNat : Int) ≤ i.2) : i.Mem w x :=
  mem_of_nat x.toNat h1 h2 (Nat.mod_eq_of_lt x.isLt).symm

theorem toNat_lt_int (x : BitVec w) : (x.toNat : Int) < 2 ^ w := by
  exact_mod_cast x.isLt

theorem mem_top (x : BitVec w) : (ivTop w).Mem w x :=
  mem_of_bounds (by simp [ivTop]) (by have := toNat_lt_int x; simp only [ivTop]; omega)

theorem Mem.norm {i : Iv} {x : BitVec w} (h : i.Mem w x) : (ivNorm w i).Mem w x := by
  unfold ivNorm; split
  · exact h
  · exact mem_top x

/-- A member of `i` has its `toNat` in the lane interval of `i`. -/
theorem mem_lane {i : Iv} {x : BitVec w} (h : i.Mem w x) :
    (ivLane w i).1 ≤ (x.toNat : Int) ∧ (x.toNat : Int) ≤ (ivLane w i).2 := by
  obtain ⟨v, h1, h2, hv⟩ := h
  have hM : (0 : Int) < 2 ^ w := by positivity
  unfold ivLane
  split
  · rename_i hk
    have e1 : i.1 / 2 ^ w ≤ v / 2 ^ w := Int.ediv_le_ediv hM h1
    have e2 : v / 2 ^ w ≤ i.2 / 2 ^ w := Int.ediv_le_ediv hM h2
    have hq : v / 2 ^ w = i.1 / 2 ^ w := by omega
    have hd := Int.emod_def v (2 ^ w)
    rw [hq] at hd
    constructor
    · show i.1 - i.1 / 2 ^ w * 2 ^ w ≤ _
      rw [← hv, hd]; linarith
    · show _ ≤ i.2 - i.1 / 2 ^ w * 2 ^ w
      rw [← hv, hd]; linarith
  · have := toNat_lt_int x
    simp only [ivTop]; omega

theorem lane_fst_nonneg (i : Iv) : 0 ≤ (ivLane w i).1 := by
  unfold ivLane
  split
  · show 0 ≤ i.1 - i.1 / 2 ^ w * 2 ^ w
    have := Int.ediv_mul_le i.1 (b := 2 ^ w) (by positivity)
    linarith
  · simp [ivTop]

/-- The lane interval as an interval of members. -/
theorem Mem.lane {i : Iv} {x : BitVec w} (h : i.Mem w x) : (ivLane w i).Mem w x :=
  mem_of_bounds (mem_lane h).1 (mem_lane h).2

/-- A member of `i` whose lane interval is the point `k` has `toNat = k`. -/
theorem toNat_eq_of_single {i : Iv} {x : BitVec w} {k : Nat} (h : i.Mem w x)
    (hk : ivSingle? (ivLane w i) = some k) : x.toNat = k := by
  obtain ⟨h1, h2⟩ := mem_lane h
  unfold ivSingle? at hk
  split at hk
  · rename_i hc
    obtain ⟨hc1, hc2⟩ := hc
    cases hk
    omega
  · cases hk

end Iv

/-! ## 2. Transfer functions -/

/-- The interval of a sum. -/
def ivAdd (w : Nat) (a b : Iv) : Iv :=
  ivNorm w (a.1 + b.1, a.2 + b.2)

/-- The interval of a difference. -/
def ivSub (w : Nat) (a b : Iv) : Iv :=
  ivNorm w (a.1 - b.2, a.2 - b.1)

/-- The interval of a low product, from the lane intervals. -/
def ivMul (w : Nat) (a b : Iv) : Iv :=
  ivNorm w ((ivLane w a).1 * (ivLane w b).1, (ivLane w a).2 * (ivLane w b).2)

/-- The interval of a bitwise `and`. -/
def ivAnd (w : Nat) (a b : Iv) : Iv :=
  (0, min (ivLane w a).2 (ivLane w b).2)

/-- The interval of a logical right shift by `k`. -/
def ivShr (w : Nat) (a : Iv) (k : Nat) : Iv :=
  ((ivLane w a).1 / 2 ^ k, (ivLane w a).2 / 2 ^ k)

/-- The interval of a left shift by `k`. -/
def ivShl (w : Nat) (a : Iv) (k : Nat) : Iv :=
  ivNorm w ((ivLane w a).1 * 2 ^ k, (ivLane w a).2 * 2 ^ k)

/-- The interval of the high multiply `(a·b) / 2^w`. -/
def ivMulhi (w : Nat) (a b : Iv) : Iv :=
  ((ivLane w a).1 * (ivLane w b).1 / 2 ^ w, (ivLane w a).2 * (ivLane w b).2 / 2 ^ w)

/-- The interval of the zero-extension or truncation to `w'` bits. -/
def ivCast (w w' : Nat) (a : Iv) : Iv :=
  if (ivLane w a).2 < 2 ^ w' then ivLane w a else ivTop w'

namespace Iv

variable {w : Nat} {a b : Iv} {x y : BitVec w}

theorem mem_const (n : Nat) : (ivConst w n).Mem w (BitVec.ofNat w n) :=
  mem_of_bounds (by simp [ivConst]) (by simp [ivConst])

theorem mem_add (ha : a.Mem w x) (hb : b.Mem w y) : (ivAdd w a b).Mem w (x + y) := by
  apply Mem.norm
  rw [mem_iff_ofInt] at ha hb ⊢
  obtain ⟨u, hu1, hu2, rfl⟩ := ha
  obtain ⟨v, hv1, hv2, rfl⟩ := hb
  exact ⟨u + v, by simp only; omega, by simp only; omega, BitVec.ofInt_add u v⟩

theorem mem_sub (ha : a.Mem w x) (hb : b.Mem w y) : (ivSub w a b).Mem w (x - y) := by
  apply Mem.norm
  rw [mem_iff_ofInt] at ha hb ⊢
  obtain ⟨u, hu1, hu2, rfl⟩ := ha
  obtain ⟨v, hv1, hv2, rfl⟩ := hb
  refine ⟨u - v, by simp only; omega, by simp only; omega, ?_⟩
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem mem_mul (ha : a.Mem w x) (hb : b.Mem w y) : (ivMul w a b).Mem w (x * y) := by
  apply Mem.norm
  obtain ⟨ha1, ha2⟩ := mem_lane ha
  obtain ⟨hb1, hb2⟩ := mem_lane hb
  have h0a := lane_fst_nonneg (w := w) a
  have h0b := lane_fst_nonneg (w := w) b
  refine mem_of_nat (x.toNat * y.toNat) ?_ ?_ (BitVec.toNat_mul x y)
  · push_cast; exact Int.mul_le_mul ha1 hb1 h0b (by omega)
  · push_cast; exact Int.mul_le_mul ha2 hb2 (by omega) (by omega)

theorem mem_and (ha : a.Mem w x) (hb : b.Mem w y) : (ivAnd w a b).Mem w (x &&& y) := by
  have h1 := (mem_lane ha).2
  have h2 := (mem_lane hb).2
  refine mem_of_bounds (by simp [ivAnd]) ?_
  rw [BitVec.toNat_and]
  have e1 : x.toNat &&& y.toNat ≤ x.toNat := Nat.and_le_left
  have e2 : x.toNat &&& y.toNat ≤ y.toNat := Nat.and_le_right
  simp only [ivAnd, le_min_iff]
  constructor <;> omega

theorem mem_shr (ha : a.Mem w x) (k : Nat) : (ivShr w a k).Mem w (x >>> k) := by
  obtain ⟨h1, h2⟩ := mem_lane ha
  have hk : (0 : Int) < 2 ^ k := by positivity
  refine mem_of_bounds ?_ ?_
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; push_cast
    exact Int.ediv_le_ediv hk h1
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; push_cast
    exact Int.ediv_le_ediv hk h2

theorem mem_shl (ha : a.Mem w x) (k : Nat) : (ivShl w a k).Mem w (x <<< k) := by
  apply Mem.norm
  obtain ⟨h1, h2⟩ := mem_lane ha
  have hk : (0 : Int) ≤ 2 ^ k := by positivity
  refine mem_of_nat (x.toNat * 2 ^ k) ?_ ?_ ?_
  · push_cast; exact Int.mul_le_mul_of_nonneg_right h1 hk
  · push_cast; exact Int.mul_le_mul_of_nonneg_right h2 hk
  · rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem mem_mulhi (ha : a.Mem w x) (hb : b.Mem w y) :
    (ivMulhi w a b).Mem w (BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)) := by
  obtain ⟨ha1, ha2⟩ := mem_lane ha
  obtain ⟨hb1, hb2⟩ := mem_lane hb
  have h0a := lane_fst_nonneg (w := w) a
  have h0b := lane_fst_nonneg (w := w) b
  have hM : (0 : Int) < 2 ^ w := by positivity
  refine mem_of_nat (x.toNat * y.toNat / 2 ^ w) ?_ ?_ (BitVec.toNat_ofNat _ _)
  · push_cast
    exact Int.ediv_le_ediv hM (Int.mul_le_mul ha1 hb1 h0b (by omega))
  · push_cast
    exact Int.ediv_le_ediv hM (Int.mul_le_mul ha2 hb2 (by omega) (by omega))

theorem mem_cast {w' : Nat} (ha : a.Mem w x) : (ivCast w w' a).Mem w' (x.setWidth w') := by
  obtain ⟨h1, h2⟩ := mem_lane ha
  unfold ivCast
  split
  · rename_i hlt
    have hx : x.toNat < 2 ^ w' := by
      have : (x.toNat : Int) < 2 ^ w' := by omega
      exact_mod_cast this
    refine mem_of_bounds ?_ ?_ <;> rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx] <;> assumption
  · exact mem_top _

end Iv

/-! ## 3. The conditional add -/

/-- The conditional add of `C`: `d + C` when the top bit of `d` is set, else `d`. -/
def condAdd {w : Nat} (d C : BitVec w) : BitVec w :=
  d + ((0 - (d >>> (w - 1))) &&& C)

/-- The unsigned minimum. -/
def umin {w : Nat} (a b : BitVec w) : BitVec w :=
  if a.toNat ≤ b.toNat then a else b

theorem umin_comm {w : Nat} (a b : BitVec w) : umin a b = umin b a := by
  unfold umin
  split <;> split
  · exact BitVec.eq_of_toNat_eq (by omega)
  · rfl
  · rfl
  · exact absurd (by omega : a.toNat ≤ b.toNat) ‹_›

theorem two_pow_eq {w : Nat} (hw : 0 < w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  have : w = (w - 1) + 1 := by omega
  conv_lhs => rw [this, Nat.pow_succ]
  omega

theorem condAdd_of_lt {w : Nat} (d C : BitVec w) (h : d.toNat < 2 ^ (w - 1)) :
    condAdd d C = d := by
  have hs : d >>> (w - 1) = 0#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
    simp
  simp [condAdd, hs]

theorem condAdd_of_ge {w : Nat} (hw : 0 < w) (d C : BitVec w) (h : 2 ^ (w - 1) ≤ d.toNat) :
    condAdd d C = d + C := by
  have hM := two_pow_eq hw
  have hd := d.isLt
  have hs : d >>> (w - 1) = 1#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    simp only [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp [condAdd, hs, BitVec.zero_sub, BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]

/-- The two cases of a member `d` of `id` with `-C ≤ id.1` and `id.2 < 2^(w-1)`: `d` is
    an integer `v ∈ [0, 2^(w-1))`, or `d = v + 2^w` for `v ∈ [-C, 0)`. -/
theorem condAdd_cases {w : Nat} (hw : 0 < w) {id : Iv} {d : BitVec w} (c : Int)
    (hd : id.Mem w d) (hlo : -c ≤ id.1) (hhi : id.2 < 2 ^ (w - 1)) (hc : c < 2 ^ (w - 1)) :
    ∃ v : Int, id.1 ≤ v ∧ v ≤ id.2 ∧
      ((0 ≤ v ∧ (d.toNat : Int) = v) ∨ (v < 0 ∧ (d.toNat : Int) = v + 2 ^ w)) := by
  obtain ⟨v, h1, h2, hv⟩ := hd
  have hM : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by exact_mod_cast two_pow_eq hw
  refine ⟨v, h1, h2, ?_⟩
  rcases le_or_gt 0 v with h0 | h0
  · left
    refine ⟨h0, ?_⟩
    rw [← hv, Int.emod_eq_of_lt h0 (by omega)]
  · right
    refine ⟨h0, ?_⟩
    rw [← hv, ← Int.add_mul_emod_self_right v 1 (2 ^ w), Int.one_mul,
      Int.emod_eq_of_lt (by omega) (by omega)]

variable {w : Nat}

/-- The range of the conditional add for `d ∈ id` and the lanes of `C` in `ic`. -/
def condAddIv (id ic : Iv) : Iv :=
  if 0 ≤ id.1 then id else (0, max id.2 (ic.2 - 1))

/-- The range of the conditional add, when the sign test reads the sign of `d`:
    `ic.2 < 2^(w-1)`, `-ic.1 ≤ id.1`, `id.2 < 2^(w-1)`. -/
def ivCondAdd? (w : Nat) (id ic : Iv) : Option Iv :=
  if 0 < w ∧ ic.2 < 2 ^ (w - 1) ∧ -ic.1 ≤ id.1 ∧ id.2 < 2 ^ (w - 1) then
    some (condAddIv id ic)
  else none

theorem Iv.mem_condAdd (hw : 0 < w) {id ic : Iv} {d C : BitVec w} (hd : id.Mem w d)
    (hC1 : ic.1 ≤ (C.toNat : Int)) (hC2 : (C.toNat : Int) ≤ ic.2)
    (hc : ic.2 < 2 ^ (w - 1)) (hlo : -ic.1 ≤ id.1) (hhi : id.2 < 2 ^ (w - 1)) :
    (condAddIv id ic).Mem w (condAdd d C) := by
  have hM : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by exact_mod_cast two_pow_eq hw
  obtain ⟨v, h1, h2, hcase⟩ := condAdd_cases hw ic.1 hd hlo hhi (by omega)
  rcases hcase with ⟨h0, hv⟩ | ⟨h0, hv⟩
  · have hlt : d.toNat < 2 ^ (w - 1) := by
      have : (d.toNat : Int) < 2 ^ (w - 1) := by omega
      exact_mod_cast this
    rw [condAdd_of_lt d C hlt]
    unfold condAddIv
    split
    · exact Iv.mem_of_bounds (by omega) (by omega)
    · exact Iv.mem_of_bounds (by simp only; omega) (by simp only; omega)
  · have hge : 2 ^ (w - 1) ≤ d.toNat := by
      have : (2 : Int) ^ (w - 1) ≤ d.toNat := by omega
      exact_mod_cast this
    rw [condAdd_of_ge hw d C hge]
    have hidneg : ¬ 0 ≤ id.1 := by omega
    simp only [condAddIv, hidneg, if_false]
    have hlt : d.toNat + C.toNat - 2 ^ w < 2 ^ w := by
      have := d.isLt; have := C.isLt; omega
    have hsum : (d + C).toNat = d.toNat + C.toNat - 2 ^ w := by
      rw [BitVec.toNat_add]
      have hge' : 2 ^ w ≤ d.toNat + C.toNat := by
        have : (2 : Int) ^ w ≤ d.toNat + C.toNat := by omega
        exact_mod_cast this
      rw [← Nat.mod_eq_of_lt hlt, Nat.mod_eq_sub_mod hge']
    have hcast : ((d + C).toNat : Int) = v + C.toNat := by
      rw [hsum]
      have hge' : 2 ^ w ≤ d.toNat + C.toNat := by
        have : (2 : Int) ^ w ≤ d.toNat + C.toNat := by omega
        exact_mod_cast this
      push_cast [hge']
      omega
    exact Iv.mem_of_bounds (by simp only; omega) (by simp only; omega)

/-- `ivCondAdd?` is sound: its interval holds the conditional add of a member of `id` and
    a constant whose `toNat` lies in `ic`. -/
theorem Iv.mem_ivCondAdd {id ic r : Iv} {d C : BitVec w} (hd : id.Mem w d)
    (hC1 : ic.1 ≤ (C.toNat : Int)) (hC2 : (C.toNat : Int) ≤ ic.2)
    (hr : ivCondAdd? w id ic = some r) : r.Mem w (condAdd d C) := by
  unfold ivCondAdd? at hr
  split at hr
  · rename_i hc
    obtain ⟨hw, h1, h2, h3⟩ := hc
    cases hr
    exact Iv.mem_condAdd hw hd hC1 hC2 h1 h2 h3
  · cases hr

/-- The conditional add of a constant `C < 2^(w-1)` on `d ∈ [-C, 2^(w-1))` is the
    unsigned minimum of `d` and `d + C`. -/
theorem condAdd_eq_umin (hw : 0 < w) {id : Iv} {d C : BitVec w} (hd : id.Mem w d)
    (hc : C.toNat < 2 ^ (w - 1)) (hlo : -(C.toNat : Int) ≤ id.1)
    (hhi : id.2 < 2 ^ (w - 1)) :
    condAdd d C = umin d (d + C) := by
  have hM : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by exact_mod_cast two_pow_eq hw
  have hMn := two_pow_eq hw
  have hcI : (C.toNat : Int) < 2 ^ (w - 1) := by exact_mod_cast hc
  obtain ⟨v, h1, h2, hcase⟩ := condAdd_cases hw C.toNat hd hlo hhi hcI
  rcases hcase with ⟨h0, hv⟩ | ⟨h0, hv⟩
  · have hlt : d.toNat < 2 ^ (w - 1) := by
      have : (d.toNat : Int) < 2 ^ (w - 1) := by omega
      exact_mod_cast this
    rw [condAdd_of_lt d C hlt]
    have hsum : (d + C).toNat = d.toNat + C.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    unfold umin
    rw [if_pos (by omega)]
  · have hge : 2 ^ (w - 1) ≤ d.toNat := by
      have : (2 : Int) ^ (w - 1) ≤ d.toNat := by omega
      exact_mod_cast this
    have hge' : 2 ^ w ≤ d.toNat + C.toNat := by
      have : (2 : Int) ^ w ≤ d.toNat + C.toNat := by omega
      exact_mod_cast this
    rw [condAdd_of_ge hw d C hge]
    have hsum : (d + C).toNat = d.toNat + C.toNat - 2 ^ w := by
      rw [BitVec.toNat_add, Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt]
      have := d.isLt; have := C.isLt; omega
    unfold umin
    rw [if_neg (by have := C.isLt; omega)]

/-- The direct form: for `d = x - C` in range, the conditional add is the unsigned
    minimum of `x` and `x - C`. -/
theorem condAdd_sub_eq_umin (hw : 0 < w) {id : Iv} {x C : BitVec w} (hd : id.Mem w (x - C))
    (hc : C.toNat < 2 ^ (w - 1)) (hlo : -(C.toNat : Int) ≤ id.1)
    (hhi : id.2 < 2 ^ (w - 1)) :
    condAdd (x - C) C = umin x (x - C) := by
  rw [condAdd_eq_umin hw hd hc hlo hhi, BitVec.sub_add_cancel, umin_comm]

/-! ## 4. The Barrett remainder -/

/-- The Barrett bound `X·δ/2^(s+t) + p·m/2^t + p + 1`, `δ = 2^(s+t) - m·p`. -/
def barrettBound (X s t m p : Nat) : Nat :=
  X * (2 ^ (s + t) - m * p) / 2 ^ (s + t) + p * m / 2 ^ t + p + 1

/-- The Barrett quotient `q = ⌊⌊x/2^s⌋·m/2^t⌋` satisfies `q·p ≤ x`, and the remainder
    `x - q·p` is at most `min X (barrettBound X s t m p)` for `x ≤ X`, when
    `m·p ≤ 2^(s+t)`. -/
theorem barrett_nat (x X s t m p : Nat) (hx : x ≤ X) (hmp : m * p ≤ 2 ^ (s + t)) :
    x / 2 ^ s * m / 2 ^ t * p ≤ x ∧
      x - x / 2 ^ s * m / 2 ^ t * p ≤ min X (barrettBound X s t m p) := by
  have hS : 0 < 2 ^ s := Nat.two_pow_pos s
  have hT : 0 < 2 ^ t := Nat.two_pow_pos t
  have hST : 2 ^ (s + t) = 2 ^ s * 2 ^ t := Nat.pow_add 2 s t
  set S := 2 ^ s
  set T := 2 ^ t
  set h := x / S with hh
  set q := h * m / T with hq
  -- `h·S ≤ x < h·S + S` and `q·T ≤ h·m < q·T + T`
  have f1 : h * S ≤ x := Nat.div_mul_le_self x S
  have f1' : x < h * S + S := Nat.lt_div_mul_add hS
  have f2 : q * T ≤ h * m := Nat.div_mul_le_self (h * m) T
  have f2' : h * m < q * T + T := Nat.lt_div_mul_add hT
  have hlow : q * p ≤ x := by
    have e1 : q * T * p ≤ h * m * p := Nat.mul_le_mul_right p f2
    have e2 : h * (m * p) ≤ h * (S * T) := Nat.mul_le_mul_left h (hST ▸ hmp)
    have e3 : q * p * T ≤ x * T := by
      have : h * S * T ≤ x * T := Nat.mul_le_mul_right T f1
      nlinarith only [e1, e2, this]
    exact Nat.le_of_mul_le_mul_right e3 hT
  refine ⟨hlow, ?_⟩
  refine le_min (by omega) ?_
  unfold barrettBound
  rw [hST]
  set δ := S * T - m * p with hδ
  have hδ' : δ + m * p = S * T := by
    have hmp' : m * p ≤ S * T := hST ▸ hmp
    omega
  set A := X * δ / (S * T)
  set B := p * m / T
  have f3 : X * δ < A * (S * T) + S * T := Nat.lt_div_mul_add (Nat.mul_pos hS hT)
  have f4 : p * m < B * T + T := Nat.lt_div_mul_add hT
  have g1 : x * δ ≤ X * δ := Nat.mul_le_mul_right δ hx
  -- `x·m·p + m·p ≤ (h+1)·S·m·p`
  have g2 : (x + 1) * (m * p) ≤ (h * S + S) * (m * p) := Nat.mul_le_mul_right _ f1'
  -- `(h·m + 1)·p ≤ (q·T + T)·p`, scaled by `S`
  have g3 : (h * m + 1) * p * S ≤ (q * T + T) * p * S :=
    Nat.mul_le_mul_right S (Nat.mul_le_mul_right p f2')
  -- `(p·m + 1)·S ≤ (B·T + T)·S`
  have g4 : (p * m + 1) * S ≤ (B * T + T) * S := Nat.mul_le_mul_right S f4
  have key : x * (S * T) < (q * p + A + B + p + 2) * (S * T) := by
    have e : x * (S * T) = x * δ + x * (m * p) := by rw [← hδ', Nat.mul_add]
    rw [e]
    clear_value δ A B q h S T
    nlinarith only [g1, f3, g2, g3, g4]
  have := Nat.lt_of_mul_lt_mul_right key
  omega

/-- The range of the Barrett remainder for `x ∈ ix`, when `ix` lies in `[0, 2^w)`. -/
def ivBarrett? (w : Nat) (ix : Iv) (s t m p : Nat) : Option Iv :=
  if 0 ≤ ix.1 ∧ ix.2 < 2 ^ w ∧ m * p ≤ 2 ^ (s + t) then
    some (0, ((min ix.2.toNat (barrettBound ix.2.toNat s t m p) : Nat) : Int))
  else none

/-- The Barrett remainder `x - ((((x >>> s) * M) >>> t) * P)` with no wrapping product
    lies in `[0, min X (barrettBound X s t m p)]` for `x ≤ X`, `m = M.toNat`,
    `p = P.toNat`. -/
theorem Iv.mem_barrett_toNat {x y : BitVec w} {s t m p X : Nat} (hx : x.toNat ≤ X)
    (hmp : m * p ≤ 2 ^ (s + t)) (hy : y.toNat = x.toNat / 2 ^ s * m / 2 ^ t * p) :
    Iv.Mem w (0, ((min X (barrettBound X s t m p) : Nat) : Int)) (x - y) := by
  obtain ⟨hl, hu⟩ := barrett_nat x.toNat X s t m p hx hmp
  have hle : y ≤ x := by
    rw [BitVec.le_def, hy]; exact hl
  refine Iv.mem_of_bounds (Int.natCast_nonneg _) ?_
  show _ ≤ ((min X (barrettBound X s t m p) : Nat) : Int)
  rw [BitVec.toNat_sub_of_le hle, hy]
  exact_mod_cast hu

/-- The Barrett remainder `x - ((((x >>> s) * M) >>> t) * P)` with no wrapping product
    lies in `[0, min X (barrettBound X s t m p)]` for `x ≤ X`, `m = M.toNat`,
    `p = P.toNat`. -/
theorem Iv.mem_barrett {x M P : BitVec w} (s t X : Nat) (hx : x.toNat ≤ X)
    (hmp : M.toNat * P.toNat ≤ 2 ^ (s + t)) (hg : x.toNat / 2 ^ s * M.toNat < 2 ^ w)
    (hy : x.toNat / 2 ^ s * M.toNat / 2 ^ t * P.toNat < 2 ^ w) :
    Iv.Mem w (0, ((min X (barrettBound X s t M.toNat P.toNat) : Nat) : Int))
      (x - (((x >>> s) * M) >>> t) * P) := by
  refine Iv.mem_barrett_toNat hx hmp ?_
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hy]

/-- `ivBarrett?` is sound: its interval holds `x - y` for a member `x` of `ix` and `y`
    the Barrett product `⌊⌊x/2^s⌋·m/2^t⌋·p`. -/
theorem Iv.mem_ivBarrett {ix r : Iv} {x y : BitVec w} {s t m p : Nat} (h : ix.Mem w x)
    (hr : ivBarrett? w ix s t m p = some r)
    (hy : y.toNat = x.toNat / 2 ^ s * m / 2 ^ t * p) :
    r.Mem w (x - y) := by
  unfold ivBarrett? at hr
  split at hr
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases hr
    have hl := (Iv.mem_lane h).2
    have hx : x.toNat ≤ ix.2.toNat := by
      have hlane : ivLane w ix = ix := by
        unfold ivLane
        have hM : (0 : Int) < 2 ^ w := by positivity
        have e1 : ix.1 / 2 ^ w = 0 := Int.ediv_eq_zero_of_lt h1 (by
          have : ix.1 ≤ ix.2 := by
            obtain ⟨v, hv1, hv2, _⟩ := h; omega
          omega)
        have e2 : ix.2 / 2 ^ w = 0 := Int.ediv_eq_zero_of_lt (by
          obtain ⟨v, hv1, hv2, _⟩ := h; omega) h2
        simp [e1, e2]
      rw [hlane] at hl
      omega
    exact Iv.mem_barrett_toNat hx h3 hy
  · cases hr

/-! ## 5. The narrow multiply -/

/-- A 64-bit product of operands below `2^32` is the product of their low 32 bits
    zero-extended to 64 bits (the `vpmuludq` semantics). -/
theorem mul_eq_mul_setWidth32 (a b : BitVec 64) (ha : a.toNat < 2 ^ 32)
    (hb : b.toNat < 2 ^ 32) :
    a * b = (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 := by
  have ea : (a.setWidth 32).setWidth 64 = a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt a.isLt]
  have eb : (b.setWidth 32).setWidth 64 = b := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt b.isLt]
  rw [ea, eb]

end CatCrypt.Crypto.SecureCompilation.RangeDomain
