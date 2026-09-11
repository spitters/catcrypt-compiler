/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

/-!
# VERIFIED REFERENCE + correctness contract for `mpn_divrem`

**EXPERIMENTAL FILE — Phase 3 spec foundation.**  This file establishes the
*verified mathematical reference* for the hardest GMP primitive, multi-precision
division (`mpn_divrem` / GMP `mpn_tdiv_qr`), together with the **Euclidean
division contract** that any optimized implementation (Knuth Algorithm D, the
production Jasmin kernel) must refine.

It does **not** implement the optimized Knuth-D kernel: q-hat estimation, the
at-most-2 correction, normalization-by-leading-zero-shift, the multiply-subtract
inner loop.  Those are a later *verify-against-this-spec* step.  Here we pin down
**what** correct division means at the `List (BitVec 64)` denotation level, so the
optimized kernel has a fixed target.

## Design choice: bit-by-bit restoring long division as the reference

The reference is the textbook **restoring (shift-and-subtract) long division**,
expressed at the `Nat` level over a most-significant-bit-first list of the
dividend's bits.  This is the cleanest *provably correct* division algorithm:

* It is a genuine algorithm (a left fold over the dividend bits, maintaining a
  running remainder `< denom`), not a thin wrapper around `Nat.div`.
* Its loop invariant — "the running remainder is always `< denom`" — is exactly
  the invariant Knuth D maintains per quotient digit, just at radix 2 instead of
  radix `2^64`.  So this reference is the *radix-2 specialization* of the same
  schoolbook division that Knuth D performs in radix `2^64`; the q-hat machinery
  is purely the radix-`2^64` quotient-digit *estimate*, which at radix 2 is the
  trivial "is `rem ≥ denom`?" comparison and needs no correction.
* We prove the reference computes `(numer / denom, numer % denom)` exactly,
  so the Euclidean contract follows from `Nat.div_add_mod` + `Nat.mod_lt`.

The limb-list wrapper `mpnDivRem` converts `List (BitVec 64)` ↔ `Nat` via the
existing little-endian `toNat` denotation (reused from `MpnAddPrototype`), runs
the bit-level reference, and recomposes quotient/remainder limb lists.

## What is proved here (axiom-clean)

1. `bitsToNat` (MSB-first bit list → Nat) and its single-bit cons step.
2. `longDivBits` : the restoring-division left fold; `longDivBits_spec` proves
   the running invariant `r < denom ∧ acc·2^|bits| + bitsToNat bits = q·denom + r`
   by induction on the bit list.
3. `divModNat numer denom = (numer / denom, numer % denom)` for `denom > 0`
   (the bit-level reference agrees with `Nat`).
4. `mpnDivRem` : the limb-list reference, and **`mpnDivRem_spec`**, the Euclidean
   contract at the `toNat` level:
   `toNat numer = toNat quot * toNat denom + toNat rem  ∧  toNat rem < toNat denom`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype (toNat)

/-! ## §1  Most-significant-bit-first bit lists and their value -/

/-- Value of a most-significant-bit-first list of bits.
    `bitsToNat [b₀, b₁, …, bₖ] = b₀·2ᵏ + b₁·2ᵏ⁻¹ + … + bₖ` (head is the MSB). -/
def bitsToNat : List Bool → Nat
  | []      => 0
  | b :: bs => (if b then 1 else 0) * 2 ^ bs.length + bitsToNat bs

@[simp] theorem bitsToNat_nil : bitsToNat [] = 0 := rfl

theorem bitsToNat_cons (b : Bool) (bs : List Bool) :
    bitsToNat (b :: bs) = (if b then 1 else 0) * 2 ^ bs.length + bitsToNat bs := rfl

/-- The MSB-first bit list of `n` of exactly `width` bits: `bitsOf width n` has
    `bit (width-1-i) = testBit n (width-1-i)`, head = the most significant bit.
    Built MSB-first by recursion on `width`. -/
def bitsOf : Nat → Nat → List Bool
  | 0,     _ => []
  | w + 1, n => n.testBit w :: bitsOf w n

@[simp] theorem bitsOf_zero (n : Nat) : bitsOf 0 n = [] := rfl

theorem bitsOf_succ (w n : Nat) :
    bitsOf (w + 1) n = n.testBit w :: bitsOf w n := rfl

@[simp] theorem bitsOf_length (w n : Nat) : (bitsOf w n).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [bitsOf_succ, ih]

/-- A `width`-bit MSB-first decomposition recomposes to `n % 2^width`: the bit
    list captures the low `width` bits.  By induction on `width`. -/
theorem bitsToNat_bitsOf (w n : Nat) : bitsToNat (bitsOf w n) = n % 2 ^ w := by
  induction w with
  | zero => simp [bitsOf, Nat.mod_one]
  | succ w ih =>
    rw [bitsOf_succ, bitsToNat_cons, bitsOf_length, ih]
    -- testBit n w = decide (n / 2^w % 2 = 1); and
    -- n % 2^(w+1) = n % (2^w · 2) = n % 2^w + 2^w · (n / 2^w % 2)  (Nat.mod_mul)
    rw [Nat.testBit_eq_decide_div_mod_eq, pow_succ, Nat.mod_mul]
    rcases (by omega : n / 2 ^ w % 2 = 0 ∨ n / 2 ^ w % 2 = 1) with h | h <;>
      simp [h, Nat.add_comm]

/-! ## §2  Restoring (shift-and-subtract) long division — the reference

`longDivBits denom acc bits` processes `bits` MSB-first, maintaining a running
remainder `acc`.  At each bit: shift in the bit (`acc·2 + bit`), and if the
result is `≥ denom`, set the quotient bit to 1 and subtract `denom`, else the
quotient bit is 0.  Returns `(quotient, remainder)`.  The running remainder is
kept `< denom` — the loop invariant proved in `longDivBits_spec`. -/

/-- One restoring-division step on the running remainder `r` with new bit `b`:
    `r' = 2·r + b`; if `r' ≥ denom` emit quotient bit 1 and `r' - denom`,
    else quotient bit 0 and `r'`. -/
def divStep (denom r : Nat) (b : Bool) : Bool × Nat :=
  let r' := 2 * r + (if b then 1 else 0)
  if denom ≤ r' then (true, r' - denom) else (false, r')

/-- Restoring long division: fold `divStep` MSB-first across `bits`, threading
    the running remainder `acc`, collecting quotient bits MSB-first.
    Returns `(quotient bits, final remainder)`. -/
def longDivBits (denom : Nat) : Nat → List Bool → List Bool × Nat
  | acc, []      => ([], acc)
  | acc, b :: bs =>
      let (qb, acc') := divStep denom acc b
      let (qbs, r)   := longDivBits denom acc' bs
      (qb :: qbs, r)

/-- The quotient bit list has the same length as the input bit list (one
    quotient bit per processed dividend bit).  By induction on the bit list. -/
theorem longDivBits_length (denom : Nat) :
    ∀ (acc : Nat) (bits : List Bool), (longDivBits denom acc bits).1.length = bits.length := by
  intro acc bits
  induction bits generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    rcases hstep : divStep denom acc b with ⟨qb, acc'⟩
    rcases hrec : longDivBits denom acc' bs with ⟨qbs, r⟩
    have hres : longDivBits denom acc (b :: bs) = (qb :: qbs, r) := by
      simp only [longDivBits, hstep, hrec]
    rw [hres]
    simp only [List.length_cons]
    have := ih acc'
    rw [hrec] at this
    simp only at this
    omega

/-- **The restoring-division invariant.**  Proved by induction on the bit list.

    If the incoming running remainder `acc` is already `< denom` (`denom > 0`),
    then after processing `bits`:
    * the final remainder `r` is `< denom` (invariant preserved), and
    * the combined dividend `acc·2^|bits| + bitsToNat bits` equals
      `bitsToNat quot · denom + r` (the division identity for the processed bits).

    This is the radix-2 specialization of the per-quotient-digit invariant Knuth
    Algorithm D maintains in radix `2^64`. -/
theorem longDivBits_spec (denom : Nat) (hd : 0 < denom) :
    ∀ (bits : List Bool) (acc : Nat), acc < denom →
      let (quot, r) := longDivBits denom acc bits
      r < denom ∧
        acc * 2 ^ bits.length + bitsToNat bits = bitsToNat quot * denom + r := by
  intro bits
  induction bits with
  | nil =>
    intro acc hacc
    simp [longDivBits, bitsToNat]
    exact hacc
  | cons b bs ih =>
    intro acc hacc
    -- Name the one-step remainder `r'` and the quotient bit / stepped accumulator
    -- coming out of `divStep`.
    set r' : Nat := 2 * acc + (if b then 1 else 0) with hr'
    have hb1 : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
    have hpow : (0 : Nat) < 2 ^ bs.length := Nat.two_pow_pos bs.length
    -- The stepped accumulator `acc'` (= `r'` or `r' - denom`) and the IH on the tail.
    by_cases hge : denom ≤ r'
    · -- quotient bit 1, acc' = r' - denom
      have hstep : divStep denom acc b = (true, r' - denom) := by
        simp only [divStep, ← hr', hge, if_true]
      have hacc' : r' - denom < denom := by omega
      have htail := ih (r' - denom) hacc'
      -- Destructure the recursive result on the tail.
      rcases hrec : longDivBits denom (r' - denom) bs with ⟨qbs, r⟩
      rw [hrec] at htail
      simp only at htail
      obtain ⟨hrlt, heq⟩ := htail
      -- Compute the cons result explicitly from the step + tail.
      have hres : longDivBits denom acc (b :: bs) = (true :: qbs, r) := by
        simp only [longDivBits, hstep, hrec]
      -- The quotient tail has the same length as `bs`.
      have hqlen : qbs.length = bs.length := by
        have := longDivBits_length denom (r' - denom) bs; rw [hrec] at this
        simpa using this
      rw [hres]
      simp only
      refine ⟨hrlt, ?_⟩
      simp only [bitsToNat_cons, List.length_cons, hqlen, if_true]
      -- Subtraction-free form of `heq` (using `denom ≤ r'` and `Nat.sub_mul`):
      --   r'·2^|bs| + bitsToNat bs = (bitsToNat qbs·denom + r) + denom·2^|bs|.
      have heq' : r' * 2 ^ bs.length + bitsToNat bs
          = bitsToNat qbs * denom + r + denom * 2 ^ bs.length := by
        have hh : (r' - denom) * 2 ^ bs.length + denom * 2 ^ bs.length
            = r' * 2 ^ bs.length := by
          rw [← Nat.add_mul]; congr 1; omega
        omega
      -- Goal (after pow_succ on the GOAL only): acc·(2^|bs|·2) + (1·2^|bs| + bitsToNat bs)
      --                        = (1·2^|bs| + bitsToNat qbs)·denom + r.
      -- Generalize 2^|bs| and close with nlinarith (r' = 2·acc + bit).
      rw [pow_succ]
      rw [hr'] at heq'
      nlinarith [heq', hb1]
    · -- quotient bit 0, acc' = r'
      have hstep : divStep denom acc b = (false, r') := by
        simp only [divStep, ← hr', hge, if_false]
      have hacc' : r' < denom := by omega
      have htail := ih r' hacc'
      rcases hrec : longDivBits denom r' bs with ⟨qbs, r⟩
      rw [hrec] at htail
      simp only at htail
      obtain ⟨hrlt, heq⟩ := htail
      have hres : longDivBits denom acc (b :: bs) = (false :: qbs, r) := by
        simp only [longDivBits, hstep, hrec]
      have hqlen : qbs.length = bs.length := by
        have := longDivBits_length denom r' bs; rw [hrec] at this
        simpa using this
      rw [hres]
      simp only
      refine ⟨hrlt, ?_⟩
      simp only [bitsToNat_cons, List.length_cons, hqlen,
                 show (false = true) = False from by simp, if_false, Nat.zero_mul, Nat.zero_add]
      rw [pow_succ]
      rw [hr'] at heq
      nlinarith [heq, hb1]

/-! ## §3  `Nat`-level reference and its agreement with `Nat.div`/`Nat.mod`

`divModNat numer denom` runs the restoring division over a `bitLen`-bit
MSB-first decomposition of `numer`, where `bitLen` is any width with
`numer < 2^bitLen` (we use `numer.size`, Lean's bit length).  It returns
`(quotient as a Nat, remainder)`.  We prove it equals `(numer / denom,
numer % denom)`. -/

/-- The bit-level division reference at the `Nat` level: decompose `numer` into
    its low `bitLen` bits (MSB-first), run restoring division with initial
    remainder 0, and read the quotient back as a Nat. -/
def divModNat (numer denom bitLen : Nat) : Nat × Nat :=
  let (qbits, r) := longDivBits denom 0 (bitsOf bitLen numer)
  (bitsToNat qbits, r)

/-- **The reference computes Euclidean division.**  For `denom > 0` and any
    width `bitLen` with `numer < 2^bitLen`, `divModNat` returns exactly
    `(numer / denom, numer % denom)`.

    Proof: `longDivBits_spec` gives `numer = q·denom + r ∧ r < denom` (using
    `bitsToNat (bitsOf bitLen numer) = numer` since `numer < 2^bitLen`); the
    uniqueness of Euclidean division (`Nat.div_add_mod` characterization) then
    pins `q = numer/denom` and `r = numer%denom`. -/
theorem divModNat_eq (numer denom bitLen : Nat) (hd : 0 < denom)
    (hb : numer < 2 ^ bitLen) :
    divModNat numer denom bitLen = (numer / denom, numer % denom) := by
  unfold divModNat
  have hspec := longDivBits_spec denom hd (bitsOf bitLen numer) 0 hd
  rcases hrec : longDivBits denom 0 (bitsOf bitLen numer) with ⟨qbits, r⟩
  rw [hrec] at hspec
  simp only at hspec ⊢
  obtain ⟨hrlt, heq⟩ := hspec
  -- 0·2^… + bitsToNat (bitsOf …) = bitsToNat qbits · denom + r
  rw [Nat.zero_mul, Nat.zero_add, bitsToNat_bitsOf, Nat.mod_eq_of_lt hb] at heq
  -- numer = (bitsToNat qbits)·denom + r, r < denom ⇒ identify with div/mod.
  -- Rewrite the target `numer` via `heq` and use the multiple-plus-remainder
  -- div/mod identities (`Nat.mul_add_div`, `Nat.mul_add_mod'`) with `r < denom`.
  have hq : numer / denom = bitsToNat qbits := by
    rw [heq, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hrlt, Nat.zero_add]
  have hr : numer % denom = r := by
    rw [heq, Nat.mul_add_mod', Nat.mod_eq_of_lt hrlt]
  rw [hq, hr]

/-! ## §4  Limb-list reference `mpnDivRem` and the Euclidean contract

The little-endian limb denotation `toNat` is reused from `MpnAddPrototype`.
`fromNat k n` is its inverse for `k` limbs (little-endian base `2^64`); we only
need that `toNat (fromNat k n) = n % (2^64)^k` and that `mpnDivRem` produces
limb lists large enough to hold quotient and remainder. -/

/-- Little-endian limb decomposition: `fromNat k n` returns `k` limbs with
    `toNat = n % (2^64)^k`.  Inverse of `toNat` on `k`-limb-bounded values. -/
def fromNat : Nat → Nat → List (BitVec 64)
  | 0,     _ => []
  | k + 1, n => BitVec.ofNat 64 n :: fromNat k (n / 2 ^ 64)

@[simp] theorem fromNat_length (k n : Nat) : (fromNat k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [fromNat, ih]

/-- `toNat (fromNat k n) = n % (2^64)^k`: the limb decomposition captures the
    low `k` limbs.  By induction on `k`. -/
theorem toNat_fromNat (k n : Nat) : toNat (fromNat k n) = n % (2 ^ 64) ^ k := by
  -- Generalize the limb base `B = 2^64` so `pow_succ'` only matches `B^(k+1)`
  -- (not the literal `2^64` inside the head limb's `% 2^64`).
  induction k generalizing n with
  | zero => simp [fromNat, toNat, Nat.mod_one]
  | succ k ih =>
    rw [fromNat, toNat, ih, BitVec.toNat_ofNat]
    -- LHS: n % 2^64 + 2^64 · (n / 2^64 % (2^64)^k)
    -- RHS: n % (2^64)^(k+1) = n % (2^64 · (2^64)^k) = (Nat.mod_mul) the LHS.
    set B : Nat := 2 ^ 64 with hB
    rw [pow_succ', Nat.mod_mul]

/-- A number `< (2^64)^k` round-trips through `fromNat k`: `toNat (fromNat k n) = n`. -/
theorem toNat_fromNat_of_lt (k n : Nat) (h : n < (2 ^ 64) ^ k) :
    toNat (fromNat k n) = n := by
  rw [toNat_fromNat, Nat.mod_eq_of_lt h]

/-- **The limb-list division reference.**  `mpnDivRem numer denom` divides the
    little-endian limb lists.  It runs the verified bit-level reference
    `divModNat` over the dividend value `toNat numer` (using a bit width that
    bounds it), then re-encodes quotient and remainder as little-endian limb
    lists: the quotient gets `numer.length` limbs (the GMP `mpn_tdiv_qr`
    quotient occupies `lnum - lden + 1` limbs ≤ `lnum`), the remainder gets
    `denom.length` limbs (it is `< toNat denom ≤ (2^64)^|denom|`). -/
def mpnDivRem (numer denom : List (BitVec 64)) :
    List (BitVec 64) × List (BitVec 64) :=
  let bitLen := 64 * numer.length
  let (q, r) := divModNat (toNat numer) (toNat denom) bitLen
  (fromNat numer.length q, fromNat denom.length r)

/-- `toNat numer < 2^(64·|numer|)`: the little-endian denotation of an
    `m`-limb list is below `2^(64m)`.  By induction on the limb list. -/
theorem toNat_lt (numer : List (BitVec 64)) :
    toNat numer < 2 ^ (64 * numer.length) := by
  induction numer with
  | nil => simp [toNat]
  | cons w ws ih =>
    rw [toNat, List.length_cons]
    have hw : w.toNat < 2 ^ 64 := w.isLt
    have : 64 * (ws.length + 1) = 64 + 64 * ws.length := by ring
    rw [this, pow_add]
    -- w.toNat + 2^64 · toNat ws < 2^64 · 2^(64·|ws|)
    have hpos : (0 : Nat) < 2 ^ (64 * ws.length) := Nat.two_pow_pos _
    nlinarith [ih, hw, hpos]

/-- `(2^64)^k = 2^(64·k)`: bridge between the limb-base power and the bit power. -/
theorem base_pow_eq (k : Nat) : (2 ^ 64) ^ k = 2 ^ (64 * k) := by
  rw [← pow_mul]

/-! ### §4.1  The Euclidean division contract — the load-bearing spec -/

/-- **The Euclidean division contract for `mpnDivRem`.**  For nonzero denominator
    (`toNat denom ≠ 0`), the limb-list reference satisfies the textbook
    division identity at the `toNat` denotation level:

    `toNat numer = toNat quot · toNat denom + toNat rem  ∧  toNat rem < toNat denom`.

    This is **the specification any optimized Knuth-D implementation must refine.**
    It is proved by reducing to `divModNat_eq` (the bit-level reference computes
    `Nat`-division exactly) and then the limb re-encoding round-trips:
    * the remainder `< toNat denom ≤ (2^64)^|denom|` round-trips (`toNat_fromNat_of_lt`);
    * the quotient `= toNat numer / toNat denom < 2^(64·|numer|) = (2^64)^|numer|`
      round-trips, since `toNat numer < 2^(64·|numer|)` and dividing only shrinks. -/
theorem mpnDivRem_spec (numer denom : List (BitVec 64)) (hd : toNat denom ≠ 0) :
    toNat numer
      = toNat (mpnDivRem numer denom).1 * toNat denom + toNat (mpnDivRem numer denom).2
    ∧ toNat (mpnDivRem numer denom).2 < toNat denom := by
  have hdpos : 0 < toNat denom := Nat.pos_of_ne_zero hd
  -- Run the bit-level reference; it equals Nat division.
  have hbound : toNat numer < 2 ^ (64 * numer.length) := toNat_lt numer
  have hdm := divModNat_eq (toNat numer) (toNat denom) (64 * numer.length) hdpos hbound
  -- Unfold mpnDivRem to expose the divModNat result.
  unfold mpnDivRem
  simp only [hdm]
  -- Now goal mentions fromNat numer.length (toNat numer / toNat denom)
  --             and fromNat denom.length (toNat numer % toNat denom).
  -- Remainder round-trips: it is < toNat denom ≤ (2^64)^|denom|.
  have hrem_lt_denom : toNat numer % toNat denom < toNat denom :=
    Nat.mod_lt _ hdpos
  have hdenom_lt : toNat denom < (2 ^ 64) ^ denom.length := by
    rw [base_pow_eq]; exact toNat_lt denom
  have hrem : toNat (fromNat denom.length (toNat numer % toNat denom))
      = toNat numer % toNat denom :=
    toNat_fromNat_of_lt _ _ (by omega)
  -- Quotient round-trips: it is ≤ toNat numer < 2^(64·|numer|) = (2^64)^|numer|.
  have hquot_lt : toNat numer / toNat denom < (2 ^ 64) ^ numer.length := by
    rw [base_pow_eq]
    calc toNat numer / toNat denom ≤ toNat numer := Nat.div_le_self _ _
      _ < 2 ^ (64 * numer.length) := hbound
  have hquot : toNat (fromNat numer.length (toNat numer / toNat denom))
      = toNat numer / toNat denom :=
    toNat_fromNat_of_lt _ _ hquot_lt
  simp only [hrem, hquot]
  -- Reduces to Nat.div_add_mod' + Nat.mod_lt.
  refine ⟨?_, hrem_lt_denom⟩
  -- Goal: numer = (numer/denom)·denom + numer%denom  (Nat.div_add_mod' is exactly this, flipped).
  exact (Nat.div_add_mod' (toNat numer) (toNat denom)).symm

/-- Entry-point restatement: `mpnDivRem` produces `(quot, rem)` with
    `toNat quot = toNat numer / toNat denom` and
    `toNat rem  = toNat numer % toNat denom` (denominator nonzero).
    The two together immediately give the Euclidean contract. -/
theorem mpnDivRem_quot_rem (numer denom : List (BitVec 64)) (hd : toNat denom ≠ 0) :
    toNat (mpnDivRem numer denom).1 = toNat numer / toNat denom ∧
    toNat (mpnDivRem numer denom).2 = toNat numer % toNat denom := by
  have hdpos : 0 < toNat denom := Nat.pos_of_ne_zero hd
  have hbound : toNat numer < 2 ^ (64 * numer.length) := toNat_lt numer
  have hdm := divModNat_eq (toNat numer) (toNat denom) (64 * numer.length) hdpos hbound
  unfold mpnDivRem
  simp only [hdm]
  have hdenom_lt : toNat denom < (2 ^ 64) ^ denom.length := by
    rw [base_pow_eq]; exact toNat_lt denom
  have hrem : toNat (fromNat denom.length (toNat numer % toNat denom))
      = toNat numer % toNat denom :=
    toNat_fromNat_of_lt _ _ (by have := Nat.mod_lt (toNat numer) hdpos; omega)
  have hquot_lt : toNat numer / toNat denom < (2 ^ 64) ^ numer.length := by
    rw [base_pow_eq]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hbound
  have hquot : toNat (fromNat numer.length (toNat numer / toNat denom))
      = toNat numer / toNat denom :=
    toNat_fromNat_of_lt _ _ hquot_lt
  exact ⟨hquot, hrem⟩

/-! ### §4.2  Concrete sanity checks (decidable `#eval` / `native_decide`) -/

/-- `7 / 3 = 2 rem 1` on single limbs. -/
example : mpnDivRem [7] [3] = ([2], [1]) := by native_decide

/-- `100 / 7 = 14 rem 2` on single limbs. -/
example : mpnDivRem [100] [7] = ([14], [2]) := by native_decide

/-- Two-limb dividend by single-limb divisor: `(2^64 + 5) / 2 = 2^63 + 2 rem 1`.
    `toNat [5, 1] = 5 + 2^64`. -/
example : toNat (mpnDivRem [5, 1] [2]).1 = (5 + 2 ^ 64) / 2 := by native_decide

example : toNat (mpnDivRem [5, 1] [2]).2 = (5 + 2 ^ 64) % 2 := by native_decide

/-! ## §5  Jasmin-bridge feasibility — STRUCTURAL PLAN (not implemented)

This reference is the *spec target*; the optimized kernel is a later phase.  The
production division kernel is **Knuth Algorithm D** (radix `2^64` schoolbook
long division), exactly the structure of Lean's own fallback `mpn_div`
(`runtime/mpn.cpp`: `div_normalize` / `div_n` / `div_1` / `div_unnormalize`),
WhyMP's `wmpn_tdiv_qr`, and s2n-bignum's `bignum_divmod`.  The bridge maps onto
the existing `MpnAddPrototype` plumbing as follows.

### §5.1  The four Knuth-D phases and their Lean obligations

1. **Normalization** (`div_normalize`).  Left-shift both `numer` and `denom` by
   `d = clz(denom[lden-1])` so the top denominator limb has its MSB set
   (`denom[n-1] ≥ 2^63`).  This guarantees the q-hat estimate is tight (within 2
   of the true digit).  *Obligation*: `toNat (shiftLeft numer d) = toNat numer · 2^d`
   and likewise for `denom`; division commutes with the common shift (the shared
   factor `2^d` cancels in quotient, scales the remainder).  Reuses a shift-by-`d`
   limb walk — a sibling of the per-limb carry walk in `mpnAddN`.

2. **Per-quotient-digit loop** (`div_n`, the `for j` loop).  For each quotient
   limb position `j` from high to low: form the 2-limb numerator window, compute
   the estimate `q̂ = ⌊(numer[j+n]·2^64 + numer[j+n-1]) / denom[n-1]⌋`, correct it
   (see §5.2), then `numer[j..j+n] -= q̂ · denom` and store `q̂`.  *Obligation*:
   the radix-`2^64` analogue of `longDivBits_spec` — the running remainder window
   stays `< denom` after each digit.  **This is the exact invariant proved here in
   `longDivBits_spec`, lifted from radix 2 to radix `2^64`.**

3. **Multiply-subtract inner loop** (`mpn_mul` of `q̂·denom` then `mpn_sub`).
   This is `mpn_submul_1`: subtract `q̂ · denom` from the numerator window.
   **This reuses the proven plumbing directly** — `mpn_submul_1` is the sibling of
   the already-verified `mpn_mul_1` (`MpnMul1Prototype`) and `mpn_addmul_1`
   (carry/borrow chain over limbs), and its borrow walk is the dual of `mpnAddN`'s
   carry walk (`MpnAddPrototype`, `MpnSubPrototype`).  The `if borrow` add-back
   (`div_n` lines 257–264: `quot[j]--; numer[j..] += denom`) is one `mpnAddN`
   pass over `n+1` limbs — *already verified plumbing*.

4. **Unnormalization** (`div_unnormalize`).  Right-shift the remainder by `d` to
   undo step 1.  *Obligation*: `toNat (shiftRight rem d) = toNat rem / 2^d`, the
   inverse of step 1's shift; trivial once §5.1.1 is in place.

### §5.2  The load-bearing NEW obligation: the q-hat 2-step correction bound

The single genuinely new proof obligation — the one with no analogue in the
add/sub/mul plumbing — is the **correctness of the q-hat estimate and its
at-most-2 correction** (`mpn.cpp` `div_n` lines 244–249, the `recheck` loop):

```
q̂ = ⌊(uₙ·B + uₙ₋₁) / vₙ₋₁⌋ ;  r̂ = (uₙ·B + uₙ₋₁) mod vₙ₋₁
while  q̂ ≥ B  ∨  q̂·vₙ₋₂ > r̂·B + uₙ₋₂ :
    q̂-- ; r̂ += vₙ₋₁ ; (repeat while r̂ < B)
```

The classical theorem (Knuth TAOCP Vol. 2, §4.3.1, Theorem B) is:

> with `denom` normalized (`vₙ₋₁ ≥ 2^63`), the true quotient digit `q` satisfies
> `q̂ - 2 ≤ q ≤ q̂`, and the two-condition `recheck` test reduces `q̂` to either
> `q` or `q + 1`; the single subsequent `if borrow` add-back (step 3) fixes the
> remaining off-by-one.

So the new obligation decomposes as:
* **(a) Estimate upper bound** `q ≤ q̂` : from `vₙ₋₁ ≥ 2^63` and `q̂ = ⌊window/vₙ₋₁⌋`.
* **(b) Estimate lower bound after recheck** `q̂ ≤ q + 1` : the two-term test
  `q̂·vₙ₋₂ ≤ r̂·B + uₙ₋₂` plus normalization rules out `q̂ ≥ q + 2`.
* **(c) Termination + final correction** : the `recheck` loop runs ≤ 2 times,
  and the post-multiply-subtract `if borrow` add-back turns `q̂ ∈ {q, q+1}` into
  exactly `q`.

`(a)`/`(b)` are pure `Nat`/`BitVec` inequalities over the 3 top limbs
(`vₙ₋₁, vₙ₋₂, uₙ, uₙ₋₁, uₙ₋₂`) plus the normalization bound — discharge with
`omega`/`nlinarith` after `bv_decide`-shaped facts about the 2-limb window, in
the same style as `adcStep_spec`/`addCarryIn_spec` here.  `(c)` is the radix-`2^64`
instance of the digit-step in `longDivBits_spec` (the `denom ≤ r'` branch ↔ the
`if borrow` add-back).

### §5.3  Reuse summary

| Knuth-D piece                       | Lean status / reuse                                  |
|-------------------------------------|------------------------------------------------------|
| normalize / unnormalize shift       | new limb shift-by-`d` walk; sibling of `mpnAddN` walk |
| per-digit remainder-window invariant| **proved** here as `longDivBits_spec` (radix 2 → 2^64)|
| multiply-subtract `q̂·denom`         | `mpn_submul_1` = sibling of proven `mpn_mul_1`/`mpn_addmul_1` |
| `if borrow` add-back                | one `mpnAddN` pass — **already verified plumbing**    |
| Euclidean output contract           | **proved** here as `mpnDivRem_spec` (the refinement target) |
| **q-hat estimate + 2-step correct.**| **NEW** — Knuth Thm B; §5.2 (a)/(b)/(c). Load-bearing.|

The only piece with no existing analogue is the q-hat correction (§5.2); every
other phase reuses the carry/borrow/limb-walk plumbing already verified in the
`Mpn*Prototype` files, and the *output* contract is exactly `mpnDivRem_spec`. -/

end CatCrypt.Crypto.Jasmin.Mpn.DivRemSpec
