/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnDivRemSpec
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option autoImplicit false

/-!
# VERIFIED REFERENCES for the bounded-list runtime extras of a verified GMP

**EXPERIMENTAL FILE — runtime-extras spec foundation.**  GMP-style bignum code
needs a handful of *small* helper routines alongside the carry-chain
arithmetic (`MpnAddPrototype`) and the division kernel (`MpnDivRemSpec`):

1. **`log2` / `sizeinbase` base 2** — the position of the top set bit, used to
   size buffers and to normalize the divisor before Knuth-D.
2. **machine-int ↔ big conversions** — low-word extraction (`mpn_get_d`-style
   "least significant limb") and the "fits in one machine word" predicate.
3. **`Int` sign/rounding wrappers** — the four integer division conventions
   (Euclidean `ediv`/`emod`, truncating `tdiv`/`tmod`, flooring `fdiv`/`fmod`)
   expressed in terms of the *magnitude* divmod (`|a| / |b|`, `|a| % |b|`) plus
   the operand signs.  This is what a signed bignum front-end (`mpz`) layers on
   top of the unsigned `mpn` divmod (`MpnDivRemSpec.mpnDivRem`).

These are *runtime extras*, not kernel-TCB code, so the deliverable is at the
algorithm / spec level: pure reference functions over `List (BitVec 64)` (the
little-endian `toNat` denotation reused from `MpnAddPrototype`) and their
functional specs.  No Jasmin emit / `bignumExecFuel` bridge is needed (the loops
here are trivial single-limb walks; the load-bearing loop infrastructure already
lives in `MpnAddPrototype`).

## What is proved here (axiom-clean)

1. `mpnLog2 a = Nat.log2 (toNat a)` for `toNat a ≠ 0` (`mpnLog2_spec`).
2. `mpnToLow64 a = (toNat a) % 2^64` (`mpnToLow64_spec`) and the `mpnFits64`
   predicate with its `toNat`-level characterization.
3. The four `Int` rounding correspondences, each stated in terms of the
   magnitude divmod `|a| / |b|`, `|a| % |b|` and the operand signs:
   `Int.tdiv`/`Int.tmod`, `Int.ediv`/`Int.emod`, `Int.fdiv`/`Int.fmod`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnMiscPrototype

open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype (toNat)
open CatCrypt.Crypto.Jasmin.Examples.MpnDivRemSpec (mpnDivRem)

/-! ## §1  `log2` / `sizeinbase` base 2

GMP's `mpn_sizeinbase(p, n, 2)` returns the bit length of the bignum, i.e.
`Nat.log2 (toNat p) + 1` for nonzero input.  The underlying primitive is the
position of the most-significant set bit, which is `Nat.log2`.  We compute it
limb by limb: walk down from the top limb to find the highest nonzero limb,
then add `64 ·` (its index) to the `BitVec`-level log2 of that limb.

We phrase the algorithm via the more convenient *bit-position* form
`mpnLog2 a = (index of top nonzero limb) * 64 + BitVec.log2 (top nonzero limb)`,
and prove it equals `Nat.log2 (toNat a)`. -/

/-- `BitVec`-level top-set-bit position: `Nat.log2` of the limb's value.
    For a nonzero `w : BitVec 64`, this is the index of its most significant
    set bit (`0 ≤ · < 64`). -/
def bvLog2 (w : BitVec 64) : Nat := Nat.log2 w.toNat

/-- Limb-list `log2` (top-set-bit position, MSB index), little-endian input.
    Walk from the *front* (least significant limb): the value of the tail is
    scaled by `2^64`, so if the tail is nonzero its contribution dominates and
    the answer is `64 + mpnLog2 tail`; otherwise the head determines it. -/
def mpnLog2 : List (BitVec 64) → Nat
  | []      => 0
  | w :: ws =>
      if toNat ws = 0 then bvLog2 w else 64 + mpnLog2 ws

/-! ### §1.1  `mpnLog2_spec` -/

/-- The `BitVec`-level log2 agrees with `Nat.log2` on the limb value. -/
theorem bvLog2_eq (w : BitVec 64) : bvLog2 w = Nat.log2 w.toNat := rfl

/-- The high-limb log2 shift: for `lo < 2^64` and `hi ≠ 0`,
    `Nat.log2 (lo + 2^64 · hi) = 64 + Nat.log2 hi`.  The `2^64 · hi` term
    dominates, so the top set bit is `64` above that of `hi`.  Proved through
    the bracketing characterization `Nat.log2_eq_iff`. -/
theorem log2_lo_add_high (lo hi : Nat) (hlo : lo < 2 ^ 64) (hhi : hi ≠ 0) :
    Nat.log2 (lo + 2 ^ 64 * hi) = 64 + Nat.log2 hi := by
  have hvalNZ : lo + 2 ^ 64 * hi ≠ 0 := by
    have : 0 < 2 ^ 64 * hi := Nat.mul_pos (Nat.two_pow_pos 64) (Nat.pos_of_ne_zero hhi)
    omega
  -- Bracketing for `hi`: `2^(log2 hi) ≤ hi < 2^(log2 hi + 1)`.
  obtain ⟨hlb, hub⟩ := (Nat.log2_eq_iff hhi).mp rfl
  rw [Nat.log2_eq_iff hvalNZ]
  constructor
  · -- 2^(64 + log2 hi) = 2^64 · 2^(log2 hi) ≤ 2^64 · hi ≤ value
    have : 2 ^ (64 + Nat.log2 hi) = 2 ^ 64 * 2 ^ Nat.log2 hi := by rw [pow_add]
    rw [this]
    calc 2 ^ 64 * 2 ^ Nat.log2 hi ≤ 2 ^ 64 * hi := by
            exact Nat.mul_le_mul_left _ hlb
      _ ≤ lo + 2 ^ 64 * hi := by omega
  · -- value = lo + 2^64·hi < 2^64·(hi+1) ≤ 2^64·2^(log2 hi+1) = 2^(64+log2 hi+1)
    have hstep : lo + 2 ^ 64 * hi < 2 ^ 64 * (hi + 1) := by
      have : 2 ^ 64 * (hi + 1) = 2 ^ 64 * hi + 2 ^ 64 := by ring
      omega
    have hle : 2 ^ 64 * (hi + 1) ≤ 2 ^ 64 * 2 ^ (Nat.log2 hi + 1) := by
      apply Nat.mul_le_mul_left
      omega
    have hpow : 2 ^ (64 + Nat.log2 hi + 1) = 2 ^ 64 * 2 ^ (Nat.log2 hi + 1) := by
      rw [← pow_add]; ring_nf
    rw [hpow]
    omega

/-- **`log2` correctness.**  For a nonzero limb list, the limb-walk top-bit
    position equals `Nat.log2` of the little-endian value.  By induction on the
    limb list, splitting on whether the high part (`toNat ws`) vanishes. -/
theorem mpnLog2_spec :
    ∀ (a : List (BitVec 64)), toNat a ≠ 0 → mpnLog2 a = Nat.log2 (toNat a) := by
  intro a
  induction a with
  | nil => intro h; simp [toNat] at h
  | cons w ws ih =>
    intro h
    rw [mpnLog2]
    by_cases hws : toNat ws = 0
    · -- tail is zero: value is `w.toNat`, answer is `bvLog2 w`.
      simp only [hws, if_true, toNat, mul_zero, add_zero, bvLog2]
    · -- tail nonzero: value `= w.toNat + 2^64 · toNat ws`, with the tail term
      -- dominating; `Nat.log2` of it is `64 + Nat.log2 (toNat ws)`.
      simp only [hws, if_false]
      rw [ih hws, toNat, log2_lo_add_high w.toNat (toNat ws) w.isLt hws]

/-! ## §2  Machine-int ↔ big conversions

Lean's runtime back-end converts between a bignum and a single machine word in
two directions used by `GMP`/`mpz`:

* **low-word extraction** (`mpn_get_d`-flavoured "take the least significant
  limb"): the head limb's `Nat` value, which is exactly `toNat a % 2^64`;
* **the "fits in one machine word" check** (`mpz_fits_*`): the predicate
  `toNat a < 2^64`, decided by "all but the head limb are zero".

Both are direct facts about the little-endian `toNat` denotation; no loop is
involved beyond inspecting the tail. -/

/-- Low 64-bit word of a bignum: the head limb (`0` for the empty list).  This
    is the least-significant machine word, the value Lean's runtime reads when
    truncating a big integer to `u64`. -/
def mpnToLow64 : List (BitVec 64) → BitVec 64
  | []     => 0
  | w :: _ => w

/-- **Low-word spec.**  `mpnToLow64 a`, read as a `Nat`, is `toNat a % 2^64` —
    the low machine word of the bignum.  The head limb carries the low 64 bits;
    the `2^64 ·`-scaled tail contributes nothing mod `2^64`. -/
theorem mpnToLow64_spec (a : List (BitVec 64)) :
    (mpnToLow64 a).toNat = toNat a % 2 ^ 64 := by
  cases a with
  | nil => simp [mpnToLow64, toNat]
  | cons w ws =>
    -- toNat (w :: ws) = w.toNat + 2^64 · toNat ws; mod 2^64 kills the tail and
    -- leaves w.toNat (which is already < 2^64).
    simp only [mpnToLow64, toNat, Nat.add_mul_mod_self_left,
               Nat.mod_eq_of_lt w.isLt]

/-- Predicate: the bignum fits in a single 64-bit machine word, i.e. its
    little-endian denotation is below `2^64`.  This is the value-level
    "fits in a word" check Lean's runtime performs before truncating to `u64`.

    (Note: this is a *value* predicate, not the structural "list has one limb".
    A normalized bignum has no trailing zero limbs, so for normalized inputs the
    value predicate `toNat a < 2^64` coincides with "at most one limb"; but
    `[w, 0]` also denotes `< 2^64` while having two limbs, so we keep the value
    form — it is the property the conversions actually depend on.) -/
def mpnFits64 (a : List (BitVec 64)) : Prop := toNat a < 2 ^ 64

/-- The fits-in-64 predicate is decidable (it is a `Nat` inequality). -/
instance (a : List (BitVec 64)) : Decidable (mpnFits64 a) :=
  inferInstanceAs (Decidable (toNat a < 2 ^ 64))

/-- **Fits-in-64 spec.**  `mpnFits64 a ↔ toNat a < 2^64` — definitional, recorded
    as the public characterization used by the conversion sites. -/
theorem mpnFits64_iff (a : List (BitVec 64)) :
    mpnFits64 a ↔ toNat a < 2 ^ 64 := Iff.rfl

/-- When the bignum fits in 64 bits, the low-word extraction is *lossless*: the
    head limb recovers the whole value.  This is the conversion correctness that
    the `mpz → u64` cast relies on. -/
theorem mpnToLow64_of_fits (a : List (BitVec 64)) (h : mpnFits64 a) :
    (mpnToLow64 a).toNat = toNat a := by
  rw [mpnToLow64_spec, Nat.mod_eq_of_lt h]

/-! ## §3  `Int` sign / rounding wrappers

A signed bignum front-end (`mpz`) implements the four integer-division
conventions on top of the unsigned `mpn` divmod.  The *magnitudes* are divided
once (the verified `MpnDivRemSpec.mpnDivRem` over limb lists / `Nat.div`,
`Nat.mod` over `Nat`), and each convention adds a documented sign adjustment:

| convention | quotient toward | remainder sign |
|------------|-----------------|----------------|
| T (`tdiv`/`tmod`, "truncate")   | 0 (truncation)   | dividend `a`        |
| E (`ediv`/`emod`, Euclidean)    | (so `0 ≤ rem`)   | always `≥ 0`        |
| F (`fdiv`/`fmod`, "floor")      | −∞ (floor)       | divisor `b`         |

Each theorem below pins the *exact integer value* of the variant in terms of the
magnitude divmod `a.natAbs / b.natAbs`, `a.natAbs % b.natAbs` and the operand
signs (`a.sign`, `b.sign`) — the "documented sign-adjusted value".  All are a
finite sign-case analysis, built on Mathlib's
`Int.sign_mul_natAbs`/`Int.natAbs_tdiv`/`Int.sign_tdiv` (T-rounding, the closest
to the magnitude divmod) and the convention bridges `Int.ediv_eq_tdiv`,
`Int.fdiv_eq_ediv`, `Int.fmod_eq_emod`, `Int.natAbs_emod`. -/

/-! ### §3.1  T-rounding (truncate toward zero): `tdiv` / `tmod` -/

/-- **T-division value.**  Truncating integer division has *magnitude*
    `a.natAbs / b.natAbs` and *sign* the product of the operand signs
    (`Int.tdiv` rounds toward zero, so it is purely multiplicative in sign).
    When `a.natAbs < b.natAbs` the quotient is `0`, consistent with the formula
    (`a.natAbs / b.natAbs = 0`, killing the sign factor). -/
theorem tdiv_eq_sign_mul (a b : Int) :
    a.tdiv b = a.sign * b.sign * ((a.natAbs / b.natAbs : Nat) : Int) := by
  conv_lhs => rw [← Int.sign_mul_natAbs (a.tdiv b)]
  rw [Int.natAbs_tdiv, Int.sign_tdiv]
  by_cases h : a.natAbs < b.natAbs
  · simp [h, Nat.div_eq_of_lt h]
  · rw [if_neg h]; rfl

/-- **T-remainder value.**  Truncating remainder has magnitude
    `a.natAbs % b.natAbs` and takes the sign of the *dividend* `a`
    (`Int.tmod a b + b * Int.tdiv a b = a`, with `tmod` toward zero). -/
theorem tmod_eq_sign_mul (a b : Int) :
    a.tmod b = a.sign * ((a.natAbs % b.natAbs : Nat) : Int) := by
  conv_lhs => rw [← Int.sign_mul_natAbs (a.tmod b)]
  rw [Int.natAbs_tmod, Int.sign_tmod]
  by_cases h : b ∣ a
  · have hd : b.natAbs ∣ a.natAbs := Int.natAbs_dvd_natAbs.mpr h
    have hz : a.natAbs % b.natAbs = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [if_pos h, hz]; simp
  · rw [if_neg h]

/-! ### §3.2  Euclidean (`ediv` / `emod`, the default `/` `%` on `Int`)

E-division keeps the remainder in `[0, |b|)`.  Its quotient differs from the
T-quotient by a `0`/`sign b` correction (the floor-vs-truncate adjustment when
the dividend is negative and not divisible). -/

/-- **E-division value.**  Euclidean `a / b` equals the T-quotient
    (`a.sign * b.sign * (a.natAbs / b.natAbs)`) minus a correction `sign b` in
    exactly the case where the result must round so that the remainder stays
    nonnegative (negative dividend, not divisible).  Via `Int.ediv_eq_tdiv`. -/
theorem ediv_eq_sign_mul (a b : Int) :
    a / b = a.sign * b.sign * ((a.natAbs / b.natAbs : Nat) : Int)
      - (if 0 ≤ a ∨ b ∣ a then 0 else Int.sign b) := by
  rw [Int.ediv_eq_tdiv]
  congr 1
  exact tdiv_eq_sign_mul a b

/-- **E-remainder value.**  Euclidean remainder is always `≥ 0`; its magnitude is
    `a.natAbs % b.natAbs` when `a ≥ 0` (or `b ∣ a`), else the complemented
    `b.natAbs - a.natAbs % b.natAbs`.  This is `Int.natAbs_emod` re-expressed at
    the integer-value level (using `0 ≤ a % b`). -/
theorem emod_eq_natAbs (a b : Int) (hb : b ≠ 0) :
    a % b = ((if 0 ≤ a ∨ b ∣ a then a.natAbs % b.natAbs
             else b.natAbs - a.natAbs % b.natAbs : Nat) : Int) := by
  conv_lhs => rw [← Int.natAbs_of_nonneg (Int.emod_nonneg a hb)]
  rw [Int.natAbs_emod a hb]

/-! ### §3.3  Flooring (`fdiv` / `fmod`)

F-division rounds the quotient toward `−∞`; its remainder takes the sign of the
*divisor*.  Both differ from the E-versions by a documented `0`/`b`(or `1`)
correction (`Int.fdiv_eq_ediv`, `Int.fmod_eq_emod`). -/

/-- **F-division value.**  Flooring `a.fdiv b = ⌊a / b⌋` equals the E-quotient
    minus a `0`/`1` floor correction (negative divisor, not divisible), and the
    E-quotient is itself the sign-adjusted magnitude quotient.  Fully expanded
    in terms of `a.natAbs / b.natAbs` and the signs. -/
theorem fdiv_eq_sign_mul (a b : Int) :
    a.fdiv b =
      (a.sign * b.sign * ((a.natAbs / b.natAbs : Nat) : Int)
        - (if 0 ≤ a ∨ b ∣ a then 0 else Int.sign b))
      - (if 0 ≤ b ∨ b ∣ a then 0 else 1) := by
  rw [Int.fdiv_eq_ediv]
  congr 1
  exact ediv_eq_sign_mul a b

/-- **F-remainder value.**  Flooring remainder equals the (nonnegative)
    E-remainder plus a `0`/`b` correction (so it ends up with the sign of `b`).
    Via `Int.fmod_eq_emod` + the E-remainder magnitude form. -/
theorem fmod_eq_natAbs (a b : Int) (hb : b ≠ 0) :
    a.fmod b = ((if 0 ≤ a ∨ b ∣ a then a.natAbs % b.natAbs
                else b.natAbs - a.natAbs % b.natAbs : Nat) : Int)
      + (if 0 ≤ b ∨ b ∣ a then 0 else b) := by
  rw [Int.fmod_eq_emod]
  congr 1
  exact emod_eq_natAbs a b hb

/-! ### §3.4  Bridge to the verified limb-list divmod

For *nonnegative* bignums the magnitude divmod `a.natAbs / b.natAbs` /
`a.natAbs % b.natAbs` appearing in §3.1–§3.3 is computed by the verified
`MpnDivRemSpec.mpnDivRem` over little-endian limb lists.  This connects the
signed `Int` wrappers to the unsigned `mpn` kernel. -/

/-- The magnitude quotient `|↑(toNat a)| / |↑(toNat b)|` of the *Int* embeddings
    of two limb lists is computed by the verified `mpnDivRem` quotient (nonzero
    divisor).  `(↑(toNat a) : Int).natAbs = toNat a`, reducing to
    `mpnDivRem_quot_rem`. -/
theorem natAbs_div_eq_mpnDivRem_quot (a b : List (BitVec 64)) (hd : toNat b ≠ 0) :
    ((toNat a : Int)).natAbs / ((toNat b : Int)).natAbs
      = toNat (mpnDivRem a b).1 := by
  rw [Int.natAbs_natCast, Int.natAbs_natCast]
  exact (MpnDivRemSpec.mpnDivRem_quot_rem a b hd).1.symm

/-- The magnitude remainder `|↑(toNat a)| % |↑(toNat b)|` of the *Int* embeddings
    of two limb lists is computed by the verified `mpnDivRem` remainder. -/
theorem natAbs_mod_eq_mpnDivRem_rem (a b : List (BitVec 64)) (hd : toNat b ≠ 0) :
    ((toNat a : Int)).natAbs % ((toNat b : Int)).natAbs
      = toNat (mpnDivRem a b).2 := by
  rw [Int.natAbs_natCast, Int.natAbs_natCast]
  exact (MpnDivRemSpec.mpnDivRem_quot_rem a b hd).2.symm

/-! ### §3.5  Concrete sanity checks (the four conventions, decidable) -/

/-- `(-7).tdiv 2 = -3` (truncate toward 0): sign `(-)(+) = -`, magnitude `7/2 = 3`. -/
example : ((-7 : Int).tdiv 2) = -3 := by decide
/-- `(-7) / 2 = -4` (Euclidean floors the negative quotient so `rem = 1 ≥ 0`). -/
example : ((-7 : Int) / 2) = -4 := by decide
example : ((-7 : Int) % 2) = 1 := by decide
/-- `(-7).fdiv 2 = -4`, `(-7).fmod 2 = 1` (floor; here same as Euclidean since `b > 0`). -/
example : ((-7 : Int).fdiv 2) = -4 := by decide
/-- `(-7).fmod (-2) = -1` (floor remainder takes the sign of the divisor). -/
example : ((-7 : Int).fmod (-2)) = -1 := by decide

end CatCrypt.Crypto.Jasmin.Examples.MpnMiscPrototype
