/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-!
# BigNat: a canonical variable-width natural-number carrier over limb lists

A verified `Nat` carrier built on the pure-list bignum kernels of
`MultiLimbKernel`. `bignumVal` (little-endian base `2^64`) is the abstraction
function `toNat`; this module makes it a bijection between *canonical* limb
lists (no high zero limbs) and `Nat`, and lifts the kernels' value specs to
carrier-level `Nat`-operation equations.

## Main results

* `Canonical` / `norm` — the canonical form (no trailing zero limbs) and the
  normalizer, with `bignumVal_norm` and `canonical_norm`.
* `ofNat` — base-`2^64` little-endian digits, with the round trip
  `toNat_ofNat`, `canonical_ofNat`, and `ofNat_toNat` (`Canonical l → ofNat
  (bignumVal l) = l`), giving `ofNat_norm : ofNat (bignumVal l) = norm l`.
* Operation drivers: `add_val` (`bignumVal (add a b) = bignumVal a + bignumVal
  b`), `mul_val` (`= bignumVal a * bignumVal b`), and `satSub_val`
  (`bignumVal (satSub a b) = bignumVal a - bignumVal b`, saturating, for
  equal-length operands).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNat

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-- Carrier value: little-endian base-`2^64` limb list to `Nat`. -/
abbrev toNat (l : List (BitVec 64)) : Nat := bignumVal l

/-! ## Canonicalization -/

/-- A limb list is canonical when it has no high zero limbs: the empty list, or
    a list whose last (highest) limb is nonzero. -/
def Canonical (l : List (BitVec 64)) : Prop := l.getLast? ≠ some 0

/-- Strip trailing (high) zero limbs. Recurses front-to-back: normalize the
    tail; a limb kept only as the highest limb survives just when it is
    nonzero. -/
def norm : List (BitVec 64) → List (BitVec 64)
  | [] => []
  | x :: xs =>
    match norm xs with
    | [] => if x == 0 then [] else [x]
    | y :: ys => x :: y :: ys

theorem bignumVal_norm : ∀ l : List (BitVec 64), bignumVal (norm l) = bignumVal l
  | [] => rfl
  | x :: xs => by
      have ih := bignumVal_norm xs
      cases hxs : norm xs with
      | nil =>
        simp only [norm, hxs]
        rw [hxs] at ih
        by_cases hx : x == 0
        · have hx0 : x = 0 := by simpa using hx
          simp only [hx, bignumVal, if_pos]
          simp [bignumVal, hx0] at ih ⊢
          omega
        · simp only [hx, if_neg, Bool.not_eq_true] at *
          simp only [bignumVal] at ih ⊢
          omega
      | cons y ys =>
        simp only [norm, hxs, bignumVal]
        rw [hxs] at ih
        simp only [bignumVal] at ih
        omega

theorem canonical_norm : ∀ l : List (BitVec 64), Canonical (norm l)
  | [] => by simp [norm, Canonical]
  | x :: xs => by
      have ih := canonical_norm xs
      cases hxs : norm xs with
      | nil =>
        simp only [norm, hxs, Canonical]
        by_cases hx : x = 0
        · simp [hx]
        · rw [if_neg (by simpa using hx)]
          simp only [List.getLast?_singleton, ne_eq, Option.some.injEq]
          simpa using hx
      | cons y ys =>
        simp only [norm, hxs, Canonical] at *
        rwa [List.getLast?_cons_cons]

/-! ## The round trip `Nat ↔ canonical limb list` -/

/-- Base-`2^64` little-endian digit expansion of a `Nat`. -/
def ofNat (n : Nat) : List (BitVec 64) :=
  if h : n = 0 then []
  else BitVec.ofNat 64 (n % 2 ^ 64) :: ofNat (n / 2 ^ 64)
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

theorem ofNat_zero : ofNat 0 = [] := by rw [ofNat]; simp

theorem ofNat_pos {n : Nat} (h : n ≠ 0) :
    ofNat n = BitVec.ofNat 64 (n % 2 ^ 64) :: ofNat (n / 2 ^ 64) := by
  rw [ofNat]; simp [h]

/-- **Round trip, one direction.** The digit expansion evaluates back to `n`. -/
theorem toNat_ofNat : ∀ n : Nat, bignumVal (ofNat n) = n
  | 0 => by rw [ofNat_zero]; rfl
  | n + 1 => by
      have h : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have ih := toNat_ofNat ((n + 1) / 2 ^ 64)
      rw [ofNat_pos h]
      simp only [bignumVal]
      rw [ih, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (dvd_refl _)]
      have := Nat.mod_add_div (n + 1) (2 ^ 64)
      omega
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- The digit expansion is canonical (no high zero limbs). -/
theorem canonical_ofNat : ∀ n : Nat, Canonical (ofNat n)
  | 0 => by rw [ofNat_zero]; simp [Canonical]
  | n + 1 => by
      have h : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have ih := canonical_ofNat ((n + 1) / 2 ^ 64)
      rw [ofNat_pos h]
      by_cases hq : (n + 1) / 2 ^ 64 = 0
      · rw [hq, ofNat_zero]
        simp only [Canonical, List.getLast?_singleton, ne_eq, Option.some.injEq]
        have hlt : n + 1 < 2 ^ 64 := by
          rcases Nat.div_eq_zero_iff.mp hq with h | h
          · exact absurd h (by norm_num)
          · exact h
        have hmod : (n + 1) % 2 ^ 64 = n + 1 := Nat.mod_eq_of_lt hlt
        rw [hmod]
        intro hc
        have : ((BitVec.ofNat 64 (n + 1)).toNat) = 0 := by rw [hc]; rfl
        rw [BitVec.toNat_ofNat, hmod] at this
        omega
      · have hne : ofNat ((n + 1) / 2 ^ 64) ≠ [] := by
          intro he; rw [ofNat_pos hq] at he; simp at he
        obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hne
        rw [hz] at ih ⊢
        simpa only [Canonical, List.getLast?_cons_cons] using ih
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- Positive value of a nonempty canonical list. -/
theorem bignumVal_pos_of_canonical :
    ∀ l : List (BitVec 64), Canonical l → l ≠ [] → 0 < bignumVal l
  | [], _, h => absurd rfl h
  | [x], hc, _ => by
      simp only [Canonical, List.getLast?_singleton, ne_eq, Option.some.injEq] at hc
      have hx : x.toNat ≠ 0 := by
        intro h0; exact hc (by rw [← BitVec.toNat_inj]; simpa using h0)
      simp only [bignumVal]; omega
  | x :: y :: ys, hc, _ => by
      have hc' : Canonical (y :: ys) := by
        simpa only [Canonical, List.getLast?_cons_cons] using hc
      have ih := bignumVal_pos_of_canonical (y :: ys) hc' (by simp)
      have hstep : bignumVal (x :: y :: ys) = x.toNat + 2 ^ 64 * bignumVal (y :: ys) := rfl
      omega

/-- **Round trip, other direction.** A canonical list is recovered from its
    value. -/
theorem ofNat_toNat :
    ∀ l : List (BitVec 64), Canonical l → ofNat (bignumVal l) = l
  | [], _ => by simp [bignumVal, ofNat_zero]
  | [x], hc => by
      simp only [Canonical, List.getLast?_singleton, ne_eq, Option.some.injEq] at hc
      have hx : x.toNat ≠ 0 := by
        intro h0; exact hc (by rw [← BitVec.toNat_inj]; simpa using h0)
      simp only [bignumVal, Nat.mul_zero, Nat.add_zero]
      rw [ofNat_pos hx]
      have hlt := x.isLt
      rw [Nat.mod_eq_of_lt hlt, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        Nat.div_eq_of_lt hlt, ofNat_zero]
  | x :: y :: ys, hc => by
      have hc' : Canonical (y :: ys) := by
        simpa only [Canonical, List.getLast?_cons_cons] using hc
      have ih := ofNat_toNat (y :: ys) hc'
      have hpos := bignumVal_pos_of_canonical (y :: ys) hc' (by simp)
      have hxlt := x.isLt
      set V := bignumVal (x :: y :: ys) with hV
      have hVeq : V = x.toNat + 2 ^ 64 * bignumVal (y :: ys) := by
        rw [hV]; simp only [bignumVal]
      have hVne : V ≠ 0 := by rw [hVeq]; positivity
      have hmod : V % 2 ^ 64 = x.toNat := by
        rw [hVeq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxlt]
      have hdiv : V / 2 ^ 64 = bignumVal (y :: ys) := by
        rw [hVeq, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hxlt, Nat.zero_add]
      rw [ofNat_pos hVne, hmod, hdiv, ih, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `ofNat ∘ bignumVal` is normalization. -/
theorem ofNat_norm (l : List (BitVec 64)) : ofNat (bignumVal l) = norm l := by
  rw [← bignumVal_norm l, ofNat_toNat (norm l) (canonical_norm l)]

/-! ## Operation drivers -/

/-- Carrier addition: the schoolbook add-with-carry chain (any limb lengths). -/
def add (a b : List (BitVec 64)) : List (BitVec 64) := bnAdd a b 0

/-- **Addition.** `toNat (add a b) = toNat a + toNat b`. -/
theorem add_val (a b : List (BitVec 64)) :
    bignumVal (add a b) = bignumVal a + bignumVal b := by
  simp only [add, bnAdd_val]; rfl

/-- Carrier multiplication: full schoolbook multiply. -/
def mul (a b : List (BitVec 64)) : List (BitVec 64) := mulBignum a b

/-- **Multiplication.** `toNat (mul a b) = toNat a * toNat b`. -/
theorem mul_val (a b : List (BitVec 64)) :
    bignumVal (mul a b) = bignumVal a * bignumVal b :=
  mulBignum_val a b

/-- Value of an all-zero limb list. -/
theorem bignumVal_replicate_zero : ∀ n : Nat, bignumVal (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by
      have ih := bignumVal_replicate_zero n
      simp only [List.replicate_succ, bignumVal]
      simpa using ih

/-- Carrier saturating subtraction: the two's-complement difference, selecting
    zero on borrow. The top limb of `subLimbs` is the not-borrow flag (`1` iff
    `a ≥ b`); it drives a branchless per-limb select between the low limbs of the
    difference and an all-zero list. -/
def satSub (a b : List (BitVec 64)) : List (BitVec 64) :=
  let d := subLimbs a b
  selLimbs (0 - d.getLastD 0) d.dropLast (List.replicate a.length 0)

/-- **Saturating subtraction.** For equal-length operands,
    `toNat (satSub a b) = toNat a - toNat b` (truncated `Nat` subtraction). -/
theorem satSub_val (a b : List (BitVec 64)) (hlen : a.length = b.length) :
    bignumVal (satSub a b) = bignumVal a - bignumVal b := by
  set n := a.length with hn
  set V := bignumVal a with hVd
  set P := bignumVal b with hPd
  set Q := (2 ^ 64) ^ n with hQd
  have hnl : a.length = (notLimbs b).length := by
    simp only [notLimbs, List.length_map]; exact hlen
  have hdlen : (subLimbs a b).length = n + 1 := by
    simpa [subLimbs, hn] using addLimbs_length a (notLimbs b) 1 hnl
  have hne : subLimbs a b ≠ [] := by
    intro h; rw [h] at hdlen; simp at hdlen
  set d := subLimbs a b with hdd
  set flag := d.getLastD 0 with hflagd
  set dl := d.dropLast with hdld
  have hgl : d.getLastD 0 = d.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
  have hsplit : dl ++ [flag] = d := by
    rw [hdld, hflagd, hgl]; exact List.dropLast_concat_getLast hne
  have hdllen : dl.length = n := by
    have hc := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil, hdlen] at hc
    omega
  have hsnoc : bignumVal d = bignumVal dl + flag.toNat * Q := by
    have hbs := bignumVal_snoc dl flag
    rw [hsplit, hdllen] at hbs; exact hbs
  have hsv : bignumVal d + P = V + Q := by
    have hsubv := subLimbs_val a b hlen; rw [← hdd] at hsubv; exact hsubv
  have hdllt : bignumVal dl < Q := by have := bignumVal_lt dl; rwa [hdllen] at this
  have hVlt : V < Q := by have := bignumVal_lt a; rwa [← hn] at this
  have hQpos : 0 < Q := by rw [hQd]; positivity
  have hE : bignumVal dl + flag.toNat * Q + P = V + Q := by rw [← hsnoc]; exact hsv
  have hm1 : flag.toNat ≤ 1 := by
    nlinarith [hE, hdllt, hVlt, hQpos, Nat.zero_le (bignumVal dl), Nat.zero_le P]
  have hcases : flag.toNat = 0 ∨ flag.toNat = 1 := by omega
  rcases hcases with hf0 | hf1
  · rw [hf0] at hE
    have hVltP : V < P := by omega
    have hfeq : flag = 0 := by rw [← BitVec.toNat_inj]; simpa using hf0
    have hmask : (0 : BitVec 64) - flag = 0 := by rw [hfeq]; decide
    simp only [satSub, ← hdd, ← hflagd, ← hdld, hmask]
    rw [selLimbs_zero dl (List.replicate a.length 0)
        (by rw [hdllen, hn, List.length_replicate]),
      bignumVal_replicate_zero]
    omega
  · rw [hf1] at hE
    have hVgeP : P ≤ V := by omega
    have hdlv : bignumVal dl = V - P := by omega
    have hfeq : flag = 1 := by rw [← BitVec.toNat_inj]; simpa using hf1
    have hmask : (0 : BitVec 64) - flag = -1 := by rw [hfeq]; decide
    simp only [satSub, ← hdd, ← hflagd, ← hdld, hmask]
    rw [selLimbs_ones dl (List.replicate a.length 0)
        (by rw [hdllen, hn, List.length_replicate]), hdlv]
