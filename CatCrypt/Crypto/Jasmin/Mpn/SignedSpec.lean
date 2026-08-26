/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
import CatCrypt.Crypto.Jasmin.Mpn.SubPrototype
import CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
import CatCrypt.Crypto.Jasmin.Mpn.ComparePrototype

set_option autoImplicit false

/-!
# The SIGNED-integer (`mpz`) layer over the verified unsigned `mpn` kernels

**EXPERIMENTAL FILE.**  GMP / Lean's runtime represent a multi-precision
*signed* integer as a sign bit plus an unsigned magnitude (`mpz_t` is exactly
`int _mp_size` whose absolute value is the limb count and whose sign is the
sign of the number).  The signed arithmetic (`mpz_add`, `mpz_sub`, `mpz_mul`)
is implemented as a thin sign+magnitude dispatcher over the unsigned `mpn`
kernels: same sign → add magnitudes; different sign → compare magnitudes and
subtract the smaller from the larger; multiply → multiply magnitudes, XOR the
signs.  In Lean's runtime this `mpz` dispatch layer is **reused, trusted C
glue** sitting on top of the (also trusted) `mpn` kernels.

The companion prototypes verify the unsigned `mpn` kernels natively:

* `MpnAddPrototype`  — `mpnAddN` (add limb lists with carry) + `mpnAddN_spec`;
* `MpnSubPrototype`  — `mpnSubN` (subtract limb lists with borrow) + `mpnSubN_spec`;
* `MpnMulPrototype`  — `mpnMul`  (schoolbook product)            + `mpnMul_toNat`;
* `MpnComparePrototype` — `mpnCompare` (unsigned ordering)       + `mpnCompare_eq_compare`.

This file verifies the **signed dispatch layer on top of them**, against
Mathlib `Int`.  It models a signed bignum as `(neg : Bool) × (mag :
List (BitVec 64))` and defines the three signed ops by sign+magnitude case
analysis over the verified unsigned kernels, then proves each computes the
corresponding Mathlib `Int` operation:

```
toInt (signedAdd x y) = toInt x + toInt y
toInt (signedSub x y) = toInt x - toInt y
toInt (signedMul x y) = toInt x * toInt y
```

Verifying this layer natively removes the `mpz` dispatcher from the trusted
surface, moving toward the full kernel-TCB goal.

## Equal-length magnitudes

The unsigned kernel specs (`mpnAddN_spec`, `mpnSubN_spec`,
`mpnCompare_eq_compare`) are stated for **equal-length** limb lists — the
natural in-memory invariant, where operands are zero-padded to a common limb
width before the call.  The signed ops therefore take the two magnitudes at a
common length `x.length = y.length`; this is exactly the precondition GMP's
own dispatcher establishes (it normalises both operands to the wider limb
count).  The width-growth on add (the carry-out can push one limb higher) is
handled by appending the carry limb, so the result is always *exactly correct*
as an `Int`, with no truncation.

## Honest note on the sign/zero normalisation

The one place where the modelling must be careful is the **`-0 = 0`
normalisation**.  Sign+magnitude has two representations of zero (`(true, 0)`
and `(false, 0)`); GMP canonicalises to `(false, 0)` (`mpz` of value 0 always
has `_mp_size = 0`, i.e. non-negative).  We mirror that:

* `signedAdd`, in the different-sign branch, sets the result sign to *false*
  whenever the magnitudes are equal (`mpnCompare = .eq`), so the zero result is
  the canonical `(false, 0)`.  This is the load-bearing case in the proof of
  `signedAdd_toInt` — the `.eq` branch is where `toNat x = toNat y` with
  opposite signs cancels to `0`, and `toInt (false, _)` reads off as `0`.
* `signedMul` XORs the signs, which would make `0 · (negative)` carry a `true`
  sign over a zero magnitude (`(true, 0)`, denoting `-0`).  Since `toInt
  (true, mag) = -(toNat mag : Int)` and `toNat mag = 0` here, `-0 = 0` holds
  *definitionally as an `Int`*, so the correctness theorem goes through with
  the un-normalised sign.  We do **not** normalise the sign bit in `signedMul`
  (matching that the bound is about the *denotation*, not the bit pattern); a
  comment records that the emitted GMP code would additionally force the sign
  to non-negative on a zero result to keep the canonical `mpz` invariant.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.SignedSpec

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
open CatCrypt.Crypto.Jasmin.Mpn.SubPrototype
open CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
open CatCrypt.Crypto.Jasmin.Mpn.ComparePrototype

/-! ## §1  The signed model and its `Int` denotation -/

/-- A signed multi-precision integer in sign+magnitude form: a sign bit `neg`
    (`true` = negative) and an unsigned magnitude as a little-endian limb list.
    This is the Lean/GMP `mpz` shape (`_mp_size`'s sign + the limb array). -/
abbrev Signed : Type := Bool × List (BitVec 64)

/-- The `Int` denotation of a signed bignum: `+toNat mag` if non-negative,
    `-toNat mag` if negative.  Note `(true, 0)` and `(false, 0)` both denote
    `0` (sign+magnitude has two zeros; `toInt` collapses them). -/
def toInt (x : Signed) : Int :=
  if x.1 then -(toNat x.2 : Int) else (toNat x.2 : Int)

@[simp] theorem toInt_pos (mag : List (BitVec 64)) :
    toInt (false, mag) = (toNat mag : Int) := by simp [toInt]

@[simp] theorem toInt_neg (mag : List (BitVec 64)) :
    toInt (true, mag) = -(toNat mag : Int) := by simp [toInt]

/-- Negation flips the sign bit, leaving the magnitude untouched.  The two
    zeros are *not* renormalised here (`negate (false, 0) = (true, 0)`), but
    both still denote `0`. -/
def negate (x : Signed) : Signed := (!x.1, x.2)

@[simp] theorem toInt_negate (x : Signed) : toInt (negate x) = -toInt x := by
  cases x with
  | mk neg mag => cases neg <;> simp [negate, toInt]

/-! ## §2  Signed addition

Same sign → add magnitudes (carry appended so no width is lost).
Different sign → compare magnitudes, subtract the smaller from the larger, keep
the larger operand's sign (zero result canonicalised to non-negative). -/

/-- Append-the-carry magnitude add: `mpnAddN x y false`'s limbs with the
    carry-out appended at the top limb.  This is *exactly* `toNat x + toNat y`
    (no truncation), at width `|x| + 1`. -/
def addMagFull (x y : List (BitVec 64)) : List (BitVec 64) :=
  (mpnAddN x y false).1 ++ [BitVec.ofNat 64 (carryNat (mpnAddN x y false).2)]

/-- `addMagFull` denotes the exact unsigned sum.  Direct from
    `mpnAddN_spec_carryIn_false` (the carry-out lands at limb `|x|`). -/
theorem addMagFull_toNat (x y : List (BitVec 64)) (hlen : x.length = y.length) :
    toNat (addMagFull x y) = toNat x + toNat y := by
  rw [addMagFull, toNat_append]
  simp only [toNat, mpnAddN_length _ _ false hlen, Nat.mul_zero, Nat.add_zero]
  -- The appended carry limb is `0` or `1`; decode it back to `carryNat`.
  have hcle : carryNat (mpnAddN x y false).2 ≤ 1 := by
    unfold carryNat; cases (mpnAddN x y false).2 <;> simp
  have hcdecode : (BitVec.ofNat 64 (carryNat (mpnAddN x y false).2)).toNat
      = carryNat (mpnAddN x y false).2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hcdecode]
  have h := mpnAddN_spec_carryIn_false x y hlen
  -- h : toNat (...).1 + (2^64)^|x| * carryNat (...).2 = toNat x + toNat y
  omega

/-- **Signed addition** by sign+magnitude dispatch over the unsigned kernels.

    * **same sign** (`neg_x = neg_y`): keep that sign, magnitude `= x + y`
      (`addMagFull`, carry appended);
    * **different sign**: `mpnCompare` the magnitudes —
      `eq` ⇒ result `(false, mpnSubN x y false)` (zero, canonical non-negative);
      `gt` (`toNat x > toNat y`) ⇒ `(neg_x, mpnSubN x y false)` (`|x| - |y|`);
      `lt` (`toNat x < toNat y`) ⇒ `(neg_y, mpnSubN y x false)` (`|y| - |x|`).

    In the different-sign branch the subtraction is always larger-minus-smaller,
    so the borrow-out is `false` and the result magnitude is exact. -/
def signedAdd (x y : Signed) : Signed :=
  if x.1 = y.1 then
    (x.1, addMagFull x.2 y.2)
  else
    match mpnCompare x.2 y.2 with
    | .eq => (false, (mpnSubN x.2 y.2 false).1)
    | .gt => (x.1, (mpnSubN x.2 y.2 false).1)
    | .lt => (y.1, (mpnSubN y.2 x.2 false).1)

/-! ### §2.1  The different-sign subtraction is exact (borrow-out `false`)

When `toNat b ≤ toNat a`, `mpnSubN a b false` has borrow-out `false` and its
magnitude denotes exactly `toNat a - toNat b`.  This is the load-bearing fact
for the different-sign add (and for the `gt`/`lt` branches of the compare). -/

/-- `mpnSubN` preserves the left operand's length (independent of the borrow-in),
    for equal-length operands.  Mirror of `mpnAddN_length`. -/
theorem mpnSubN_length (a b : List (BitVec 64)) (bin : Bool) (h : a.length = b.length) :
    (mpnSubN a b bin).1.length = a.length := by
  induction a generalizing b bin with
  | nil => simp [mpnSubN]
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      have h' : as.length = bs.length := by simpa using h
      simp only [mpnSubN, List.length_cons]
      rw [ih bs (sbbStep a b bin).2 h']

/-- For equal-length magnitudes with `toNat b ≤ toNat a`, the borrow-out of
    `mpnSubN a b false` is `false` and the result denotes `toNat a - toNat b`.
    The borrow-out is forced `false` because a `true` borrow would (by
    `mpnSubN_spec`) push the identity past `2^(64·|a|)`, contradicting the
    radix bound `toNat result < 2^(64·|a|)` and `toNat b ≤ toNat a`. -/
theorem mpnSubN_exact (a b : List (BitVec 64)) (hlen : a.length = b.length)
    (hle : toNat b ≤ toNat a) :
    (mpnSubN a b false).2 = false ∧
      (toNat (mpnSubN a b false).1 : Int) = (toNat a : Int) - (toNat b : Int) := by
  have hspec := mpnSubN_spec_borrowIn_false a b hlen
  -- hspec : toNat (...).1 + toNat b = toNat a + (2^64)^|a| * borrowNat (...).2
  have hreslen : (mpnSubN a b false).1.length = a.length := mpnSubN_length a b false hlen
  have hresbound : toNat (mpnSubN a b false).1 < (2 ^ 64) ^ a.length := by
    have := Mpn.MulPrototype.toNat_lt (mpnSubN a b false).1
    rwa [hreslen] at this
  have hpow_pos : 0 < (2 ^ 64) ^ a.length := by positivity
  -- If the borrow-out were `true`, hspec gives
  --   toNat result + toNat b = toNat a + 2^(64|a|),
  -- but toNat result + toNat b < 2^(64|a|) + toNat a (radix bound + hle),
  -- a contradiction.  So borrow-out = false.
  have hbor0 : (mpnSubN a b false).2 = false := by
    by_contra hbor
    have hbor' : (mpnSubN a b false).2 = true := by
      cases h : (mpnSubN a b false).2 <;> simp_all
    rw [hbor'] at hspec
    simp only [borrowNat, reduceIte, Nat.mul_one] at hspec
    omega
  refine ⟨hbor0, ?_⟩
  rw [hbor0] at hspec
  simp only [borrowNat, Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at hspec
  -- hspec : toNat result + toNat b = toNat a, with toNat b ≤ toNat a; cast to Int.
  omega

/-- **Signed addition is correct.**  `toInt (signedAdd x y) = toInt x + toInt y`
    for equal-length magnitudes.  The same-sign branch is `addMagFull_toNat`
    (with the sign factored out); the different-sign branch case-splits on
    `mpnCompare` (`= compare (toNat x) (toNat y)` by `mpnCompare_eq_compare`)
    and uses `mpnSubN_exact` to read off the exact magnitude difference, the
    `.eq` branch being the zero-normalisation case. -/
theorem signedAdd_toInt (x y : Signed) (hlen : x.2.length = y.2.length) :
    toInt (signedAdd x y) = toInt x + toInt y := by
  obtain ⟨nx, mx⟩ := x
  obtain ⟨ny, my⟩ := y
  simp only at hlen
  unfold signedAdd
  by_cases hsign : nx = ny
  · -- Same sign: add magnitudes, factor out the common sign.
    subst hsign
    simp only [reduceIte]
    have hmag := addMagFull_toNat mx my hlen
    cases nx <;> (simp only [toInt]; rw [hmag]; push_cast; ring)
  · -- Different sign: nx ≠ ny ⇒ nx = !ny; substitute and reduce to `cases ny`.
    simp only [if_neg hsign]
    have hnx : nx = !ny := by cases nx <;> cases ny <;> simp_all
    subst hnx
    have hcmp : mpnCompare mx my = compare (toNat mx) (toNat my) :=
      mpnCompare_eq_compare mx my hlen
    rw [hcmp]
    rcases lt_trichotomy (toNat mx) (toNat my) with h | h | h
    · -- toNat mx < toNat my  ⇒  compare = lt  ⇒  larger is `my`, sign `ny`.
      rw [Nat.compare_eq_lt.mpr h]
      obtain ⟨_, hval⟩ := mpnSubN_exact my mx hlen.symm (le_of_lt h)
      cases ny <;> (simp only [toInt, hval, Bool.not_false, Bool.not_true]; push_cast; ring)
    · -- toNat mx = toNat my  ⇒  compare = eq  ⇒  result 0 (canonical).
      rw [Nat.compare_eq_eq.mpr h]
      obtain ⟨_, hval⟩ := mpnSubN_exact mx my hlen (le_of_eq h.symm)
      -- result (false, _) denotes toNat mx - toNat my = 0; opposite signs cancel.
      cases ny <;>
        (simp only [toInt, hval, h, Bool.not_false, Bool.not_true]; push_cast; ring)
    · -- toNat mx > toNat my  ⇒  compare = gt  ⇒  larger is `mx`, sign `!ny`.
      rw [Nat.compare_eq_gt.mpr h]
      obtain ⟨_, hval⟩ := mpnSubN_exact mx my hlen (le_of_lt h)
      cases ny <;> (simp only [toInt, hval, Bool.not_false, Bool.not_true]; push_cast; ring)

/-! ## §3  Signed subtraction: `x - y = x + (-y)` -/

/-- **Signed subtraction** as `signedAdd x (negate y)`: subtraction is addition
    of the negation, exactly as GMP's `mpz_sub` dispatches to the same
    sign+magnitude add with `y`'s sign flipped. -/
def signedSub (x y : Signed) : Signed := signedAdd x (negate y)

/-- **Signed subtraction is correct.**  `toInt (signedSub x y) = toInt x - toInt
    y`.  Immediate from `signedAdd_toInt` (the magnitude of `negate y` is `y`'s,
    so the length precondition is preserved) and `toInt_negate`. -/
theorem signedSub_toInt (x y : Signed) (hlen : x.2.length = y.2.length) :
    toInt (signedSub x y) = toInt x - toInt y := by
  unfold signedSub
  have hlen' : x.2.length = (negate y).2.length := by
    simpa [negate] using hlen
  rw [signedAdd_toInt x (negate y) hlen', toInt_negate]
  ring

/-! ## §4  Signed multiplication: sign = XOR, magnitude = `mpnMul` -/

/-- **Signed multiplication**: the sign is `neg_x XOR neg_y`, the magnitude is
    the unsigned product `mpnMul`.  No length precondition (`mpnMul` handles
    arbitrary widths).

    On a zero operand the XOR'd sign may be `true` over a zero magnitude
    (denoting `-0`); the correctness theorem still holds because `-0 = 0` as an
    `Int`.  GMP additionally forces the sign to non-negative on a zero result
    (the canonical `_mp_size = 0`); see the file header. -/
def signedMul (x y : Signed) : Signed :=
  (xor x.1 y.1, mpnMul x.2 y.2)

/-- **Signed multiplication is correct.**  `toInt (signedMul x y) = toInt x *
    toInt y`.  The magnitude product is `mpnMul_toNat`; the four sign cases
    follow by `push_cast`/`ring` over `Int`, the zero-sign cases (`-0 = 0`)
    among them. -/
theorem signedMul_toInt (x y : Signed) :
    toInt (signedMul x y) = toInt x * toInt y := by
  obtain ⟨nx, mx⟩ := x
  obtain ⟨ny, my⟩ := y
  have hmul : (toNat (mpnMul mx my) : Int) = (toNat mx : Int) * (toNat my : Int) := by
    rw [mpnMul_toNat]; push_cast; ring
  -- Rewrite the magnitude product first so every sign case shares the same RHS;
  -- then the four `xor`-sign cases close by `ring` over `Int` (the zero-sign
  -- `-0 = 0` cases included).
  simp only [signedMul, toInt, hmul]
  cases nx <;> cases ny <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.false_eq_true, reduceIte,
      Bool.not_true, Bool.not_false, neg_mul, mul_neg, neg_neg]

/-! ## §5  The signed-layer contract, named for the GMP `mpz` dispatch

The three theorems below are the full statement that the signed (`mpz`)
dispatch layer over the verified unsigned `mpn` kernels computes the Mathlib
`Int` operations.  Bundled here as the headline deliverable. -/

/-- **The signed (`mpz`) layer is correct.**  Add / sub / mul over the
    sign+magnitude model compute the corresponding `Int` operations, reusing the
    unsigned kernel specs (`mpnAddN_spec`, `mpnSubN_spec`, `mpnCompare`'s
    ordering, `mpnMul_toNat`).  This verifies the `mpz` dispatch layer that
    Lean's runtime currently treats as reused, trusted C glue. -/
theorem signed_layer_correct (x y : Signed) (hlen : x.2.length = y.2.length) :
    toInt (signedAdd x y) = toInt x + toInt y ∧
    toInt (signedSub x y) = toInt x - toInt y ∧
    toInt (signedMul x y) = toInt x * toInt y :=
  ⟨signedAdd_toInt x y hlen, signedSub_toInt x y hlen, signedMul_toInt x y⟩

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `(+5) + (-7) = -2`: different sign, `|7| > |5|`, result negative `[2]`. -/
example : toInt (signedAdd (false, [5]) (true, [7])) = -2 := by native_decide

/-- `(-5) + (-7) = -12`: same sign, magnitude `[12, 0]`. -/
example : toInt (signedAdd (true, [5]) (true, [7])) = -12 := by native_decide

/-- `(+5) + (-5) = 0`: different sign, equal magnitudes ⇒ canonical `(false, 0)`. -/
example : signedAdd (false, [5]) (true, [5]) = (false, [0]) := by native_decide
example : toInt (signedAdd (false, [5]) (true, [5])) = 0 := by native_decide

/-- `(+5) - (-7) = 12`. -/
example : toInt (signedSub (false, [5]) (true, [7])) = 12 := by native_decide

/-- `(-3) · (+5) = -15`. -/
example : toInt (signedMul (true, [3]) (false, [5])) = -15 := by native_decide

/-- `(-3) · (-5) = 15` (sign XOR cancels). -/
example : toInt (signedMul (true, [3]) (true, [5])) = 15 := by native_decide

/-- `0 · (-7) = 0` even with the XOR'd `true` sign over a zero magnitude
    (`-0 = 0`). -/
example : toInt (signedMul (false, [0]) (true, [7])) = 0 := by native_decide

-- Axiom-cleanliness check: the signed-layer correctness theorems depend only on
-- the standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`),
-- no `sorryAx`.
#print axioms signedAdd_toInt
#print axioms signedSub_toInt
#print axioms signedMul_toInt
#print axioms signed_layer_correct

end CatCrypt.Crypto.Jasmin.Mpn.SignedSpec
