/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.MemoryModel
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.MemoryModel
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.UInt


@[expose] public section
set_option autoImplicit false

/-!
# WIDTH-PARAMETRIC mpn core — dissolving the 32-vs-64 limb-width fork

**EXPERIMENTAL FILE.** A fresh, *generic-over-`w`* re-development of the
multi-precision add core, designed to instantiate at `w = 32` (Lean's
fallback seam) and `w = 64` (real GMP) from **one** proof. It does not
refactor the existing 64-bit `MpnAddPrototype`; it stands alongside it as
the generic foundation.

The width-parametric story splits into two layers:

* **Part 1 — functional core (free-generic).** The carry-chain spec
  `mpnAddNW_spec` is the existing `mpnAddN_spec` proof with every `64`
  replaced by `w`. The induction is width-agnostic: it only uses the
  per-limb bound `(a : BitVec w).isLt : a.toNat < 2 ^ w`. We *demonstrate*
  it goes through `∀ w` unchanged.

* **Part 2 — memory algebra (generic-by-induction).** The existing
  read-back / frame lemmas (`load64Mem_store64_same`, `..._disjoint`) close
  by `bv_decide` on a **concrete** 8-byte word. `bv_decide` bitblasts, so
  it needs a concrete width and *cannot* prove `∀ w`. We reformulate over
  a recursive `storeBytesLE` / `loadBytesLE` and prove read-back + frame by
  **induction on the byte list** — the per-step address inequalities are
  single-byte `UInt64` facts (concrete width, `bv_decide`-friendly), but
  the induction over the *count* takes the place of the whole-word
  bitblast. This technique makes the memory layer width-generic.

The limb-decompose bridge (`storeWLimb` / `loadWLimb` over `k = w / 8`
bytes) connects a `BitVec w` limb to its `k` little-endian bytes and is
proved generic in `k` by the same byte-count induction.

## What stays per-width (by design)

The interpreter / emission layer is *intrinsically* per-width: the
machine word is `U32` vs `U64`, and the carry intrinsic is `ADC_32` vs
`ADC_64`. Those are concrete machine ops, chosen at instantiation time;
the generic development above is exactly the part that is *shared* across
the fork. This file validates resolution (c) of the limb-width fork: one
generic core, two concrete machine instantiations.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.GenericWidth

open CatCrypt.Crypto.Jasmin.MemoryModel

/-! ## Part 1 — generic functional core

Generic over `w : Nat`; limbs are `BitVec w`. This is the §2–§3 content of
`MpnAddPrototype` with `64 → w`. -/

/-- Little-endian denotation over base `2 ^ w`:
    `toNatW w [x0, x1, …] = x0 + 2^w · x1 + (2^w)^2 · x2 + …`. -/
def toNatW (w : Nat) : List (BitVec w) → Nat
  | []      => 0
  | x :: xs => x.toNat + 2 ^ w * toNatW w xs

/-- One ADC step on `BitVec w`: returns `(sum, carry-out)`.
    `sum = (a + b + cin) mod 2^w`, `carry-out = (a + b + cin) ≥ 2^w`. -/
def adcStepW (w : Nat) (a b : BitVec w) (cin : Bool) : BitVec w × Bool :=
  let s : Nat := a.toNat + b.toNat + (if cin then 1 else 0)
  (BitVec.ofNat w s, decide (s ≥ 2 ^ w))

/-- Pure reference for width-`w` `mpn_add_n`: add two limb lists with a
    carry chain, recursing in lockstep. Returns `(result limbs, final
    carry-out)`. -/
def mpnAddNW (w : Nat) : List (BitVec w) → List (BitVec w) → Bool →
    (List (BitVec w) × Bool)
  | a :: as, b :: bs, cin =>
      let (r, cout) := adcStepW w a b cin
      let (rs, fcout) := mpnAddNW w as bs cout
      (r :: rs, fcout)
  | _, _, cin => ([], cin)

/-- Boolean carry as a `Nat` (0 or 1). -/
def carryNat (c : Bool) : Nat := if c then 1 else 0

/-- The single-step ADC identity, on `Nat`, **generic in `w`**:
    `adcStepW w a b cin` produces `(sum, cout)` with
    `sum.toNat + 2^w · cout = a.toNat + b.toNat + cin`.

    The only width-specific fact used is `(a : BitVec w).isLt : a.toNat < 2^w`;
    everything else is `omega`. This is `Mpn.AddPrototype.adcStep_spec`
    with `64 → w`. -/
theorem adcStepW_spec (w : Nat) (a b : BitVec w) (cin : Bool) :
    (adcStepW w a b cin).1.toNat + 2 ^ w * carryNat (adcStepW w a b cin).2
      = a.toNat + b.toNat + carryNat cin := by
  unfold adcStepW carryNat
  have ha : a.toNat < 2 ^ w := a.isLt
  have hb : b.toNat < 2 ^ w := b.isLt
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
  set s : Nat := a.toNat + b.toNat + (if cin then 1 else 0) with hs
  have hc1 : (if cin then 1 else 0) ≤ 1 := by cases cin <;> simp
  have hub : s < 2 ^ w * 2 := by rw [hs]; omega
  by_cases hge : s ≥ 2 ^ w
  · -- `s % 2^w = s - 2^w` for an opaque modulus: `omega` cannot eliminate the
    -- `mod` with a non-numeral base, so peel it with `Nat.mod_eq_sub_mod`.
    have hmod : s % 2 ^ w = s - 2 ^ w := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    simp only [hge, if_true, hmod]
    omega
  · have hlt : s < 2 ^ w := by omega
    simp only [hge, if_false]
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- **Main functional spec — proved by induction on the limb list,
    GENERIC in `w`.**

    For equal-length limb lists `a, b` and any carry-in `cin`, the pure
    reference `mpnAddNW` satisfies the multi-precision addition identity:
    the denotation of the output limbs, plus the final carry-out shifted
    to bit `w·|a|`, equals `toNatW a + toNatW b + cin`.

    This is the existing `mpnAddN_spec` proof with `64 → w`; the induction
    is width-agnostic — it routes the per-limb bound through
    `adcStepW_spec` (which uses `BitVec.isLt`) and the IH over the
    `2^w`-scaled tail. -/
theorem mpnAddNW_spec (w : Nat) :
    ∀ (a b : List (BitVec w)), a.length = b.length → ∀ (cin : Bool),
      toNatW w (mpnAddNW w a b cin).1
        + (2 ^ w) ^ a.length * carryNat (mpnAddNW w a b cin).2
      = toNatW w a + toNatW w b + carryNat cin := by
  intro a
  induction a with
  | nil =>
    intro b hlen cin
    cases b with
    | nil => simp [mpnAddNW, toNatW, carryNat]; rfl
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro b hlen cin
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      set p := adcStepW w a b cin with hp
      have hstep := adcStepW_spec w a b cin
      rw [← hp] at hstep
      set q := mpnAddNW w as bs p.2 with hq
      have htail := ih bs hlen' p.2
      rw [← hq] at htail
      have hunfold : mpnAddNW w (a :: as) (b :: bs) cin = (p.1 :: q.1, q.2) := by
        simp only [mpnAddNW, hp, hq]
      rw [hunfold]
      simp only [toNatW, List.length_cons]
      have hpow : (2 ^ w) ^ (as.length + 1) = 2 ^ w * (2 ^ w) ^ as.length := by
        rw [pow_succ]; ring
      rw [hpow]
      have hkey : 2 ^ w * toNatW w q.1 + 2 ^ w * (2 ^ w) ^ as.length * carryNat q.2
          = 2 ^ w * (toNatW w as + toNatW w bs + carryNat p.2) := by
        rw [← htail]; ring
      -- The triple product `2^w · (2^w)^|as| · carryNat q.2` is nonlinear in
      -- the opaque atoms `2^w`, `(2^w)^|as|` (at concrete `w = 64` these were
      -- numerals and `omega` sufficed); generically, `nlinarith` matches it
      -- against `hkey` and combines with the head spec (`hstep`).
      nlinarith [hstep, htail, hkey]

/-- The usual entry point: carry-in 0, generic in `w`. -/
theorem mpnAddNW_spec_carryIn_false (w : Nat) (a b : List (BitVec w))
    (hlen : a.length = b.length) :
    toNatW w (mpnAddNW w a b false).1
      + (2 ^ w) ^ a.length * carryNat (mpnAddNW w a b false).2
    = toNatW w a + toNatW w b := by
  have h := mpnAddNW_spec w a b hlen false
  simpa [carryNat] using h

/-! ### Width-parametric SBB (subtract-with-borrow) core

Mirrors the ADC core above, with `+` swapped for `-` and `carry` for
`borrow`. Same width-parametric structure: a per-limb step `sbbStepW`, the
borrow `Nat` encoding `borrowNat`, the multi-precision sub `mpnSubNW`, and
the corresponding spec by induction on the limb list. Specializes to
`Mpn.SubPrototype.sbbStep` / `mpnSubN` at `w = 64`, and to the local
`sbbStep32` / `mpnSubN32` in `MpnSub32Refines` at `w = 32` (modulo
`funext` + the equation-compiler shuffle — see `MpnWidthInstances`). -/

/-- One SBB step on `BitVec w`: returns `(diff, borrow-out)`.
    `diff = (a - b - bin) mod 2^w`, `borrow-out = (a < b + bin)`.
    Mirror of `adcStepW`, with the borrow encoded as the unsigned wrap. -/
def sbbStepW (w : Nat) (a b : BitVec w) (bin : Bool) : BitVec w × Bool :=
  let d : Nat := b.toNat + (if bin then 1 else 0)
  (BitVec.ofNat w ((a.toNat + 2 ^ w - d) % 2 ^ w), decide (a.toNat < d))

/-- Boolean borrow as a `Nat` (0 or 1). Same encoding as `carryNat`, but
    re-named for documentation purposes. -/
def borrowNat (b : Bool) : Nat := if b then 1 else 0

/-- Pure reference for width-`w` `mpn_sub_n`: subtract two limb lists with
    a borrow chain, recursing in lockstep. Returns `(result limbs, final
    borrow-out)`. Mirror of `mpnAddNW`. -/
def mpnSubNW (w : Nat) : List (BitVec w) → List (BitVec w) → Bool →
    (List (BitVec w) × Bool)
  | a :: as, b :: bs, bin =>
      let (r, bout) := sbbStepW w a b bin
      let (rs, fbout) := mpnSubNW w as bs bout
      (r :: rs, fbout)
  | _, _, bin => ([], bin)

/-- The single-step SBB identity, on `Nat`, **generic in `w`**:
    `sbbStepW w a b bin` produces `(diff, bout)` with
    `diff.toNat + b.toNat + bin = a.toNat + 2^w · bout`.

    The only width-specific fact used is `(a : BitVec w).isLt`; the rest
    is `omega`. This is `Mpn.SubPrototype.sbbStep_spec` with `64 → w`. -/
theorem sbbStepW_spec (w : Nat) (a b : BitVec w) (bin : Bool) :
    (sbbStepW w a b bin).1.toNat + b.toNat + borrowNat bin
      = a.toNat + 2 ^ w * borrowNat (sbbStepW w a b bin).2 := by
  have ha : a.toNat < 2 ^ w := a.isLt
  have hb : b.toNat < 2 ^ w := b.isLt
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have hc1 : (if bin then 1 else 0) ≤ 1 := by cases bin <;> simp
  unfold sbbStepW borrowNat
  simp only [BitVec.toNat_ofNat, Nat.mod_mod, decide_eq_true_eq]
  by_cases hlt : a.toNat < b.toNat + (if bin then 1 else 0)
  · have hmod : (a.toNat + 2 ^ w - (b.toNat + (if bin then 1 else 0))) % 2 ^ w
        = a.toNat + 2 ^ w - (b.toNat + (if bin then 1 else 0)) := by
      apply Nat.mod_eq_of_lt; omega
    rw [if_pos hlt, hmod]; omega
  · have hmod : (a.toNat + 2 ^ w - (b.toNat + (if bin then 1 else 0))) % 2 ^ w
        = a.toNat - (b.toNat + (if bin then 1 else 0)) := by
      have he : a.toNat + 2 ^ w - (b.toNat + (if bin then 1 else 0))
          = (a.toNat - (b.toNat + (if bin then 1 else 0))) + 2 ^ w := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [if_neg hlt, hmod]; omega

/-- **Main functional spec — proved by induction on the limb list,
    GENERIC in `w`.**

    For equal-length limb lists `a, b` and any borrow-in `bin`, the pure
    reference `mpnSubNW` satisfies the multi-precision subtraction
    identity: the denotation of the output limbs, plus `toNatW b` and the
    borrow-in, equals `toNatW a` plus the final borrow-out shifted to bit
    `w·|a|`. Mirror of `mpnAddNW_spec`. -/
theorem mpnSubNW_toNat (w : Nat) :
    ∀ (a b : List (BitVec w)), a.length = b.length → ∀ (bin : Bool),
      toNatW w (mpnSubNW w a b bin).1 + toNatW w b + borrowNat bin
        = toNatW w a + (2 ^ w) ^ a.length * borrowNat (mpnSubNW w a b bin).2 := by
  intro a
  induction a with
  | nil =>
    intro b hlen bin
    cases b with
    | nil => simp [mpnSubNW, toNatW, borrowNat]; rfl
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro b hlen bin
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      set p := sbbStepW w a b bin with hp
      have hstep := sbbStepW_spec w a b bin
      rw [← hp] at hstep
      set q := mpnSubNW w as bs p.2 with hq
      have htail := ih bs hlen' p.2
      rw [← hq] at htail
      have hunfold : mpnSubNW w (a :: as) (b :: bs) bin = (p.1 :: q.1, q.2) := by
        simp only [mpnSubNW, hp, hq]
      rw [hunfold]
      simp only [toNatW, List.length_cons]
      have hpow : (2 ^ w) ^ (as.length + 1) = 2 ^ w * (2 ^ w) ^ as.length := by
        rw [pow_succ]; ring
      rw [hpow]
      -- IH (scaled by `2^w`) + head step (`sbbStepW_spec`) close the linear
      -- goal. The triple product `2^w · (2^w)^|as| · borrowNat q.2` is
      -- nonlinear in the opaque atoms `2^w`, `(2^w)^|as|` (at concrete
      -- `w = 64` these were numerals and `omega` sufficed); generically,
      -- `nlinarith` matches it against `hkey` and combines with `hstep`.
      have hkey : 2 ^ w * toNatW w q.1 + 2 ^ w * toNatW w bs + 2 ^ w * borrowNat p.2
          = 2 ^ w * toNatW w as + 2 ^ w * ((2 ^ w) ^ as.length * borrowNat q.2) := by
        have := congrArg (2 ^ w * ·) htail
        simpa [Nat.mul_add, Nat.add_assoc] using this
      nlinarith [hstep, htail, hkey]

/-- The usual entry point: borrow-in 0, generic in `w`. Mirror of
    `mpnAddNW_spec_carryIn_false`. -/
theorem mpnSubNW_toNat_borrowIn_false (w : Nat) (a b : List (BitVec w))
    (hlen : a.length = b.length) :
    toNatW w (mpnSubNW w a b false).1 + toNatW w b
      = toNatW w a + (2 ^ w) ^ a.length * borrowNat (mpnSubNW w a b false).2 := by
  have h := mpnSubNW_toNat w a b hlen false
  simpa [borrowNat] using h

/-! ### Width-parametric divrem / divexact core

Mirror of the ADC/SBB cores above, for `mpn_tdiv_qr` and `mpn_divexact`.

Per-limb step `divRemStepW w hi lo d`: a 2-by-1 division at width `w`,
`(hi · 2^w + lo) ÷ d`, returning `(quotient limb, remainder limb)`.  This
is the generic analogue of `BignumExec.divrem64`; at `w = 64` it is
extensionally that function. The multi-precision routines `mpnDivRemNW`
and `mpnDivExactW` work at the `Nat`-denotation level (compute
`toNatW`-div / `toNatW`-mod, then re-encode through `fromNatW`), mirroring
the structure of `Mpn.DivRemSpec.mpnDivRem` / `Mpn.DivExactSpec.mpnDivExact`
at arbitrary width.

Same width-parametric story as add/sub: a single `∀ w` reference, with
`w = 32` / `w = 64` instances dropping out by definitional specialization.
Specializes to `Mpn.DivRemSpec.mpnDivRem` / `Mpn.DivExactSpec.mpnDivExact` at
`w = 64` (pointwise-definitional after a `funext`; see
`MpnWidthInstances` for the tie-ins). -/

/-- **One 2-by-1 division step on `BitVec w`.** Given a window of two limbs
    `(hi, lo)` and a divisor `d`, compute the quotient and remainder of
    `(hi · 2^w + lo) ÷ d` as `BitVec w`s. The unbounded quotient may
    overflow the limb if `hi ≥ d`; callers that depend on no-overflow
    (Knuth Algorithm D's q̂ trial) carry that obligation explicitly.

    At `w = 64` this is `BignumExec.divrem64` pointwise; at `w = 32` it is
    the analogous 32-bit DIV intrinsic. Mirror of `adcStepW`/`sbbStepW`. -/
def divRemStepW (w : Nat) (hi lo d : BitVec w) : BitVec w × BitVec w :=
  let dd : Nat := hi.toNat * 2 ^ w + lo.toNat
  let dv : Nat := d.toNat
  (BitVec.ofNat w (dd / dv), BitVec.ofNat w (dd % dv))

/-! ### Limb decomposition `fromNatW` (the `toNatW` inverse, generic in `w`)

Width-parametric analogue of `Mpn.DivRemSpec.fromNat`. `fromNatW w k n`
returns a `k`-limb little-endian list with `toNatW = n % (2^w)^k`. -/

/-- Little-endian limb decomposition at width `w`: `fromNatW w k n` returns
    `k` limbs with `toNatW w (fromNatW w k n) = n % (2^w)^k`. Inverse of
    `toNatW` on `k`-limb-bounded values. -/
def fromNatW (w : Nat) : Nat → Nat → List (BitVec w)
  | 0,     _ => []
  | k + 1, n => BitVec.ofNat w n :: fromNatW w k (n / 2 ^ w)

@[simp] theorem fromNatW_length (w k n : Nat) : (fromNatW w k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [fromNatW, ih]

/-- `toNatW w (fromNatW w k n) = n % (2^w)^k`: the limb decomposition
    captures the low `k` base-`2^w` digits. By induction on `k`. Mirror of
    `Mpn.DivRemSpec.toNat_fromNat`. -/
theorem toNatW_fromNatW (w k n : Nat) :
    toNatW w (fromNatW w k n) = n % (2 ^ w) ^ k := by
  induction k generalizing n with
  | zero => simp [fromNatW, toNatW, Nat.mod_one]
  | succ k ih =>
    rw [fromNatW, toNatW, ih, BitVec.toNat_ofNat]
    -- LHS: n % 2^w + 2^w · (n / 2^w % (2^w)^k)
    -- RHS: n % (2^w)^(k+1) = n % (2^w · (2^w)^k) = (Nat.mod_mul) the LHS.
    rw [pow_succ', Nat.mod_mul]

/-- A number `< (2^w)^k` round-trips through `fromNatW w k`. Mirror of
    `Mpn.DivRemSpec.toNat_fromNat_of_lt`. -/
theorem toNatW_fromNatW_of_lt (w k n : Nat) (h : n < (2 ^ w) ^ k) :
    toNatW w (fromNatW w k n) = n := by
  rw [toNatW_fromNatW, Nat.mod_eq_of_lt h]

/-- `toNatW w numer < (2 ^ w) ^ numer.length`: the little-endian denotation
    of an `m`-limb list at width `w` is below `(2^w)^m`. By induction on the
    limb list. Mirror of `Mpn.DivRemSpec.toNat_lt` (which uses the equivalent
    `2 ^ (64 · m)` bound at `w = 64`). -/
theorem toNatW_lt (w : Nat) (numer : List (BitVec w)) :
    toNatW w numer < (2 ^ w) ^ numer.length := by
  induction numer with
  | nil => simp [toNatW]
  | cons x xs ih =>
    rw [toNatW, List.length_cons, pow_succ']
    have hx : x.toNat < 2 ^ w := x.isLt
    have hpos : (0 : Nat) < (2 ^ w) ^ xs.length :=
      pow_pos (Nat.two_pow_pos _) _
    -- x.toNat + 2^w · toNatW xs < 2^w · (2^w)^|xs|
    nlinarith [ih, hx, hpos]

/-! ### Width-parametric multi-precision divrem

Mirror of `Mpn.DivRemSpec.mpnDivRem` at arbitrary width: compute the Euclidean
division of `toNatW numer` by `toNatW denom` at the `Nat` level, then
re-encode quotient (`numer.length` limbs) and remainder (`denom.length`
limbs) through `fromNatW`. `noncomputable` because it pivots through the
unrestricted `Nat.div` / `Nat.mod`. -/

/-- **Width-parametric `mpn_tdiv_qr` reference.** Mirror of
    `Mpn.DivRemSpec.mpnDivRem`, generic in `w`: divide the little-endian
    limb lists at width `w` by computing `toNatW`-div / `toNatW`-mod and
    re-encoding through `fromNatW`. At `w = 64` this is
    `Mpn.DivRemSpec.mpnDivRem` pointwise (definitionally). -/
noncomputable def mpnDivRemNW (w : Nat) (numer denom : List (BitVec w)) :
    List (BitVec w) × List (BitVec w) :=
  (fromNatW w numer.length (toNatW w numer / toNatW w denom),
   fromNatW w denom.length (toNatW w numer % toNatW w denom))

/-- **Euclidean division contract for `mpnDivRemNW`, GENERIC in `w`.**
    For nonzero denominator (`toNatW w denom ≠ 0`), the width-parametric
    limb-list reference satisfies the textbook division identity at the
    `toNatW` denotation level:

    `toNatW numer = toNatW quot · toNatW denom + toNatW rem`
    `∧  toNatW rem < toNatW denom`.

    Proof structure: unfold to the underlying `Nat.div` / `Nat.mod`, show
    both round-trip through `fromNatW` (the remainder is `< toNatW denom
    ≤ (2^w)^|denom|`; the quotient is `≤ toNatW numer < (2^w)^|numer|`),
    then close with `Nat.div_add_mod'` + `Nat.mod_lt`. Mirror of
    `Mpn.DivRemSpec.mpnDivRem_spec` and analogous to `mpnAddNW_spec` /
    `mpnSubNW_toNat` in shape (denotation identity from per-step `toNatW`
    facts). -/
theorem mpnDivRemNW_toNat (w : Nat) (numer denom : List (BitVec w))
    (hd : toNatW w denom ≠ 0) :
    toNatW w numer
      = toNatW w (mpnDivRemNW w numer denom).1 * toNatW w denom
        + toNatW w (mpnDivRemNW w numer denom).2
    ∧ toNatW w (mpnDivRemNW w numer denom).2 < toNatW w denom := by
  have hdpos : 0 < toNatW w denom := Nat.pos_of_ne_zero hd
  have hnum_lt : toNatW w numer < (2 ^ w) ^ numer.length := toNatW_lt w numer
  have hden_lt : toNatW w denom < (2 ^ w) ^ denom.length := toNatW_lt w denom
  -- Remainder round-trips: rem < toNatW denom ≤ (2^w)^|denom|.
  have hrem_lt_denom : toNatW w numer % toNatW w denom < toNatW w denom :=
    Nat.mod_lt _ hdpos
  have hrem : toNatW w (fromNatW w denom.length
        (toNatW w numer % toNatW w denom))
      = toNatW w numer % toNatW w denom :=
    toNatW_fromNatW_of_lt _ _ _ (by omega)
  -- Quotient round-trips: quot ≤ numer < (2^w)^|numer|.
  have hquot_lt : toNatW w numer / toNatW w denom < (2 ^ w) ^ numer.length := by
    calc toNatW w numer / toNatW w denom ≤ toNatW w numer := Nat.div_le_self _ _
      _ < (2 ^ w) ^ numer.length := hnum_lt
  have hquot : toNatW w (fromNatW w numer.length
        (toNatW w numer / toNatW w denom))
      = toNatW w numer / toNatW w denom :=
    toNatW_fromNatW_of_lt _ _ _ hquot_lt
  unfold mpnDivRemNW
  simp only [hrem, hquot]
  refine ⟨?_, hrem_lt_denom⟩
  -- numer = (numer/denom)·denom + numer%denom
  exact (Nat.div_add_mod' (toNatW w numer) (toNatW w denom)).symm

/-! ### Width-parametric `mpn_divexact` core

Mirror of `Mpn.DivExactSpec.mpnDivExact` at arbitrary width: the quotient
projection of `mpnDivRemNW`, with the exact-division contract under the
divisibility precondition `toNatW denom ∣ toNatW numer`. -/

/-- **One-limb exact-division step.** The quotient projection of
    `divRemStepW`. At `w = 64` matches the quotient half of `divrem64`;
    used as the per-step kernel when the runtime guarantees `r = 0`. -/
def mpnDivExactStepW (w : Nat) (hi lo d : BitVec w) : BitVec w :=
  (divRemStepW w hi lo d).1

/-- **Width-parametric `mpn_divexact` reference.** The quotient projection
    of `mpnDivRemNW`. Under the precondition `toNatW denom ∣ toNatW numer`
    this denotes the exact quotient `toNatW numer / toNatW denom` with zero
    remainder. Mirror of `Mpn.DivExactSpec.mpnDivExact`. -/
noncomputable def mpnDivExactW (w : Nat) (numer denom : List (BitVec w)) :
    List (BitVec w) :=
  (mpnDivRemNW w numer denom).1

set_option linter.unusedVariables false in
/-- **Exact-division contract for `mpnDivExactW`, GENERIC in `w`.**  Under
    nonzero denominator the width-parametric reference denotes the
    Euclidean quotient at the `toNatW` level:

    `toNatW (mpnDivExactW numer denom) = toNatW numer / toNatW denom`.

    Proof: `mpnDivExactW` is by definition the `mpnDivRemNW` quotient,
    whose denotation `toNatW`-round-trips to `toNatW numer / toNatW denom`
    (the `fromNatW` bound is `numer < (2^w)^|numer|`, and the quotient is
    `≤ numer`). Mirror of `Mpn.DivExactSpec.mpnDivExact_spec`; the
    divisibility hypothesis is **not** needed for the quotient equation
    (Euclidean and exact division agree on the quotient irrespective), but
    the spec is the one the fast Hensel kernel refines under `b ∣ a`. -/
theorem mpnDivExactW_toNat (w : Nat) (numer denom : List (BitVec w))
    (hd : toNatW w denom ≠ 0) :
    toNatW w (mpnDivExactW w numer denom)
      = toNatW w numer / toNatW w denom := by
  unfold mpnDivExactW mpnDivRemNW
  have hnum_lt : toNatW w numer < (2 ^ w) ^ numer.length := toNatW_lt w numer
  have hquot_lt : toNatW w numer / toNatW w denom < (2 ^ w) ^ numer.length := by
    calc toNatW w numer / toNatW w denom ≤ toNatW w numer := Nat.div_le_self _ _
      _ < (2 ^ w) ^ numer.length := hnum_lt
  exact toNatW_fromNatW_of_lt _ _ _ hquot_lt

/-- Under the divisibility precondition the remainder limb list denotes
    `0`: `toNatW (mpnDivRemNW numer denom).2 = 0`. Mirror of
    `Mpn.DivExactSpec.mpnDivExact_rem_zero`. -/
theorem mpnDivRemNW_rem_zero (w : Nat) (numer denom : List (BitVec w))
    (h : toNatW w denom ∣ toNatW w numer) (hd : toNatW w denom ≠ 0) :
    toNatW w (mpnDivRemNW w numer denom).2 = 0 := by
  have hdpos : 0 < toNatW w denom := Nat.pos_of_ne_zero hd
  have hrem_lt_denom : toNatW w numer % toNatW w denom < toNatW w denom :=
    Nat.mod_lt _ hdpos
  have hden_lt : toNatW w denom < (2 ^ w) ^ denom.length := toNatW_lt w denom
  have hrem : toNatW w (fromNatW w denom.length
        (toNatW w numer % toNatW w denom))
      = toNatW w numer % toNatW w denom :=
    toNatW_fromNatW_of_lt _ _ _ (by omega)
  unfold mpnDivRemNW
  simp only [hrem]
  exact Nat.dvd_iff_mod_eq_zero.mp h

/-- Multiplicative form of the width-parametric exact-division contract.
    Under `toNatW denom ∣ toNatW numer` and `toNatW denom ≠ 0`,
    `toNatW (mpnDivExactW numer denom) * toNatW denom = toNatW numer`.
    Mirror of `Mpn.DivExactSpec.mpnDivExact_mul`. -/
theorem mpnDivExactW_mul (w : Nat) (numer denom : List (BitVec w))
    (h : toNatW w denom ∣ toNatW w numer) (hd : toNatW w denom ≠ 0) :
    toNatW w (mpnDivExactW w numer denom) * toNatW w denom
      = toNatW w numer := by
  have hquot := mpnDivExactW_toNat w numer denom hd
  rw [hquot]
  exact Nat.div_mul_cancel h

/-! ### Concrete sanity checks at BOTH widths from the SAME sub definitions -/

-- w = 64: `[0] - [1]` underflows.
example : mpnSubNW 64 [(0 : BitVec 64)] [1] false = ([-1], true) := by native_decide
-- w = 32: the SAME underflow at the fallback width.
example : mpnSubNW 32 [(0 : BitVec 32)] [1] false = ([-1], true) := by native_decide
-- w = 64: equal limbs, no borrow.
example : mpnSubNW 64 [12, 0] [7, 0] false = ([5, 0], false) := by native_decide
-- w = 32: equal limbs, no borrow at the fallback width.
example : mpnSubNW 32 [12, 0] [7, 0] false = ([5, 0], false) := by native_decide

/-! ### Concrete sanity checks at BOTH widths from the SAME definitions

`mpnAddNW` and the spec are generic; we instantiate at `w = 32` and
`w = 64` to witness the dissolved fork. -/

-- w = 64: `[0xFFFF…FFFF] + [1]` overflows.
example : mpnAddNW 64 [(-1 : BitVec 64)] [1] false = ([0], true) := by native_decide
-- w = 32: the SAME overflow at the fallback width.
example : mpnAddNW 32 [(-1 : BitVec 32)] [1] false = ([0], true) := by native_decide
-- w = 64: carry propagation across two limbs.
example : mpnAddNW 64 [(-1 : BitVec 64), 0] [1, 0] false = ([0, 1], false) := by
  native_decide
-- w = 32: carry propagation at the fallback width.
example : mpnAddNW 32 [(-1 : BitVec 32), 0] [1, 0] false = ([0, 1], false) := by
  native_decide

/-! ## Part 2 — generic memory algebra by byte-count induction

`storeBytesLE` / `loadBytesLE` are
recursive over a byte list / count; read-back and frame are proved by
**induction on the byte list**, NOT by `bv_decide` on a whole concrete
word. Each induction step uses only single-byte `UInt64` address facts
(`Mem.loadByte_storeByte_same/_other`), which are concrete-width and so
`bv_decide`-friendly. -/

/-- Store a list of bytes little-endian: `bytes[0]` at `a`, `bytes[1]` at
    `a + 1`, …, recursing on the tail at `a + 1`. -/
def storeBytesLE (m : Mem) (a : UInt64) : List UInt8 → Mem
  | []      => m
  | b :: bs => storeBytesLE (m.storeByte a b) (a + 1) bs

/-- Read `k` bytes little-endian starting at `a`. Returns `none` if any
    byte is unallocated. -/
def loadBytesLE (m : Mem) (a : UInt64) : Nat → Option (List UInt8)
  | 0     => some []
  | k + 1 =>
      match m.loadByte a with
      | none   => none
      | some b =>
          match loadBytesLE m (a + 1) k with
          | none    => none
          | some bs => some (b :: bs)

/-! ### Address-arithmetic step lemma

The single fact the byte-count induction needs about `UInt64` addresses:
`a + ofNat (k+1) = (a + 1) + ofNat k`. This is a concrete-width (UInt64)
identity used to *advance the base pointer one byte* in the inductive
step — not a whole-word bitblast. We prove it purely (no `bv_decide` SAT
axiom): split `ofNat (k+1) = 1 + ofNat k` via `UInt64.toNat` + `omega`,
then reassociate with `add_assoc`. -/

theorem addr_succ (a : UInt64) (k : Nat) :
    a + UInt64.ofNat (k + 1) = (a + 1) + UInt64.ofNat k := by
  have hsplit : UInt64.ofNat (k + 1) = 1 + UInt64.ofNat k := by
    apply UInt64.toNat.inj
    simp only [UInt64.toNat_ofNat', UInt64.toNat_add,
               show ((1 : UInt64).toNat) = 1 from rfl]
    omega
  rw [hsplit, ← add_assoc]

/-! ### Read-back by induction on the byte list

`loadBytesLE (storeBytesLE m a bs) a bs.length = some bs`. The key
subtlety: after `storeBytesLE (m.storeByte a b) (a+1) bs`, the byte at
`a` written first is *not* overwritten by the recursive tail stores
(they all live at `a + 1 + …`). We capture that with a frame lemma over
`storeBytesLE` proved by the same induction. -/

/-- A `storeBytesLE` at base `a'` does not disturb the byte at `a` when
    `a` differs from every address `a', a'+1, …, a'+(|bs|-1)` the store
    touches. Proved by induction on the byte list; each step peels one
    `storeByte` (single-byte `_other` frame) and advances the base via
    `addr_succ`. -/
theorem loadByte_storeBytesLE_frame (a : UInt64) :
    ∀ (bs : List UInt8) (m : Mem) (a' : UInt64),
      (∀ j : Nat, j < bs.length → a ≠ a' + UInt64.ofNat j) →
      (storeBytesLE m a' bs).loadByte a = m.loadByte a := by
  intro bs
  induction bs with
  | nil => intro m a' _; simp [storeBytesLE]
  | cons b bs ih =>
    intro m a' hne
    simp only [storeBytesLE]
    -- Recurse over the tail stores (base advanced to `a' + 1`).
    rw [ih (m.storeByte a' b) (a' + 1) ?_]
    · -- The head store at `a'` does not touch `a` (j = 0 case).
      have h0 : a ≠ a' := by
        have := hne 0 (by simp)
        simpa using this
      exact Mem.loadByte_storeByte_other m a a' b h0
    · -- Tail disjointness: `a ≠ (a'+1) + ofNat j` for `j < |bs|`,
      -- from `a ≠ a' + ofNat (j+1)` (the `j+1` source byte) via addr_succ.
      intro j hj
      have := hne (j + 1) (by simpa using Nat.succ_lt_succ hj)
      rwa [addr_succ a' j] at this

/-- **No-wrap precondition.** The byte block `[a, a + n)` does not wrap
    around the `2 ^ 64` address boundary: `a.toNat + n ≤ 2 ^ 64`. Under
    this, all `n` addresses `a, a + 1, …, a + (n-1)` are distinct (a store
    at `a + i` cannot alias the load at `a`), which is what the read-back
    needs. -/
def NoWrap (a : UInt64) (n : Nat) : Prop := a.toNat + n ≤ 2 ^ 64

/-- Under no-wrap of `[a, a + (n+1))`, the head byte at `a` differs from
    every later byte `(a + 1) + ofNat j` for `j < n`. A single-byte
    `UInt64` fact, but driven by the `toNat` no-wrap bound rather than by
    `bv_decide` on the whole block. -/
theorem head_ne_of_noWrap (a : UInt64) (n j : Nat)
    (hnw : NoWrap a (n + 1)) (hj : j < n) :
    a ≠ (a + 1) + UInt64.ofNat j := by
  unfold NoWrap at hnw
  intro heq
  -- Compare `toNat`s.  `((a+1) + ofNat j).toNat = (a.toNat + 1 + j) % 2^64`,
  -- and `a.toNat + 1 + j < 2^64` by no-wrap, so the mod is inert; then
  -- `a.toNat = a.toNat + 1 + j` is impossible.
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt
  have hjlt : a.toNat + 1 + j < 2 ^ 64 := by omega
  have hlhs : ((a + 1) + UInt64.ofNat j).toNat = a.toNat + 1 + j := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat',
               show ((1 : UInt64).toNat) = 1 from rfl]
    omega
  have := congrArg UInt64.toNat heq
  rw [hlhs] at this
  omega

/-- **Read-back, GENERIC by byte-count induction.** Under the no-wrap
    precondition on `[a, a + |bs|)`, loading back exactly the bytes just
    stored returns them. Proved by induction on the byte list: the head
    byte survives the tail stores (`loadByte_storeBytesLE_frame`, with the
    head/later inequality from `head_ne_of_noWrap`), and the tail reads
    back `bs` by the IH on the shrunk block (still no-wrap). No `bv_decide`
    on a whole word — only `toNat`/`omega` single-byte address facts. -/
theorem loadBytesLE_storeBytesLE_same :
    ∀ (bs : List UInt8) (m : Mem) (a : UInt64),
      NoWrap a bs.length →
      loadBytesLE (storeBytesLE m a bs) a bs.length = some bs := by
  intro bs
  induction bs with
  | nil => intro m a _; simp [storeBytesLE, loadBytesLE]
  | cons b bs ih =>
    intro m a hnw
    simp only [storeBytesLE, List.length_cons, loadBytesLE]
    -- The byte at `a` is the head `b`: the tail stores (at `a+1, …`) do not
    -- touch `a` (no-wrap ⇒ head ≠ later bytes).
    have hhead :
        (storeBytesLE (m.storeByte a b) (a + 1) bs).loadByte a = some b := by
      rw [loadByte_storeBytesLE_frame a bs (m.storeByte a b) (a + 1) ?_]
      · exact Mem.loadByte_storeByte_same m a b
      · intro j hj
        exact head_ne_of_noWrap a bs.length j (by simpa [NoWrap] using hnw) hj
    rw [hhead]
    -- The tail loads back `bs` by the IH; the tail block `[a+1, a+1+|bs|)`
    -- still does not wrap.
    have hnw' : NoWrap (a + 1) bs.length := by
      unfold NoWrap at hnw ⊢
      have ha : a.toNat < 2 ^ 64 := a.toNat_lt
      have h1 : (a + 1).toNat = (a.toNat + 1) % 2 ^ 64 := by
        simp only [UInt64.toNat_add, show ((1 : UInt64).toNat) = 1 from rfl]
      rw [h1]
      -- From `a.toNat + (|bs|+1) ≤ 2^64` we get `a.toNat + 1 ≤ 2^64`, so the
      -- mod is inert and `(a.toNat+1) + |bs| ≤ 2^64`.
      have : a.toNat + 1 ≤ 2 ^ 64 := by simp only [List.length_cons] at hnw; omega
      rcases Nat.lt_or_ge (a.toNat + 1) (2 ^ 64) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]; simp only [List.length_cons] at hnw; omega
      · -- a.toNat + 1 = 2^64, so |bs| = 0.
        have heq : a.toNat + 1 = 2 ^ 64 := by omega
        simp only [List.length_cons] at hnw
        have hbs0 : bs.length = 0 := by omega
        rw [heq, Nat.mod_self, hbs0]; omega
    rw [ih (m.storeByte a b) (a + 1) hnw']

/-! ### Frame by induction on the byte list

Storing a *disjoint* byte range leaves `loadBytesLE` unchanged. We use a
range-disjointness predicate mirroring `MemoryModel.Disjoint` / `range`:
the read block `[a, a + k)` is disjoint from the written block
`[a', a' + |bs|)`. -/

/-- **Single-byte frame lift:** if the read address `a` lies outside the
    written block `[a', a' + |bs|)`, the `storeBytesLE` leaves
    `loadByte a` unchanged. (Specialization of
    `loadByte_storeBytesLE_frame` using the `range`/`Disjoint` witness.) -/
theorem loadByte_storeBytesLE_disjoint (m : Mem) (a a' : UInt64)
    (bs : List UInt8)
    (hdisj : MemoryModel.Disjoint (range a 1) (range a' bs.length)) :
    (storeBytesLE m a' bs).loadByte a = m.loadByte a := by
  refine loadByte_storeBytesLE_frame a bs m a' (fun j hj => ?_)
  intro heq
  -- `a ∈ range a 1` (witness 0) and `a = a' + ofNat j ∈ range a' |bs|`.
  have h_in_a : range a 1 a := ⟨0, by omega, by
    show a = a + UInt64.ofNat 0
    rw [show (UInt64.ofNat 0) = (0 : UInt64) from rfl, add_zero]⟩
  have h_in_b : range a' bs.length a := ⟨j, hj, heq⟩
  exact hdisj a ⟨h_in_a, h_in_b⟩

/-- **Frame, GENERIC by byte-count induction.** A `storeBytesLE` into a
    block `[a', a' + |bs|)` disjoint from the read block `[a, a + k)`
    leaves `loadBytesLE … a k` unchanged. Proved by induction on the read
    count `k`: each byte of the read range is individually framed via
    `loadByte_storeBytesLE_disjoint`, and the recursive read advances by
    one byte. -/
theorem loadBytesLE_storeBytesLE_disjoint :
    ∀ (k : Nat) (m : Mem) (a a' : UInt64) (bs : List UInt8),
      MemoryModel.Disjoint (range a k) (range a' bs.length) →
      loadBytesLE (storeBytesLE m a' bs) a k = loadBytesLE m a k := by
  intro k
  induction k with
  | zero => intro m a a' bs _; simp [loadBytesLE]
  | succ k ih =>
    intro m a a' bs hdisj
    -- The head byte `a` is framed (it's in `range a (k+1)`, disjoint from
    -- the written block).
    have hhead : (storeBytesLE m a' bs).loadByte a = m.loadByte a := by
      refine loadByte_storeBytesLE_disjoint m a a' bs ?_
      intro x ⟨hx1, hx2⟩
      -- `x ∈ range a 1 ⊆ range a (k+1)`; combine with `x ∈ range a' |bs|`.
      obtain ⟨i, hi, hxi⟩ := hx1
      exact hdisj x ⟨⟨i, by omega, hxi⟩, hx2⟩
    -- The tail read at `a + 1`, count `k`, is framed by the IH (the read
    -- block `[a+1, a+1+k)` is contained in `[a, a+(k+1))`, still disjoint).
    have htail : MemoryModel.Disjoint (range (a + 1) k) (range a' bs.length) := by
      intro x ⟨hx1, hx2⟩
      obtain ⟨i, hi, hxi⟩ := hx1
      refine hdisj x ⟨⟨i + 1, by omega, ?_⟩, hx2⟩
      rw [hxi, addr_succ a i]
    simp only [loadBytesLE, hhead]
    cases hm : m.loadByte a with
    | none => simp
    | some b =>
      simp only
      rw [ih m (a + 1) a' bs htail]

/-! ### Connect to limbs: a `BitVec w` limb decomposes to `k = w / 8` bytes

We assume `w = 8 * k` (the byte-aligned case, true for `w ∈ {32, 64}`).
`limbBytes` extracts the `k` little-endian bytes of a `BitVec w`;
`storeWLimb` / `loadWLimb` store / read one limb over `k` bytes. The
read-back is proved GENERIC in `k` from `loadBytesLE_storeBytesLE_same`
plus the byte/word round-trip. -/

/-- The `i`-th little-endian byte of a `BitVec w` limb. -/
def limbByteAt (w : Nat) (v : BitVec w) (i : Nat) : UInt8 :=
  (v >>> (i * 8)).toNat.toUInt8

/-- The `k` little-endian bytes of a `BitVec w` limb. -/
def limbBytes (w : Nat) (v : BitVec w) (k : Nat) : List UInt8 :=
  (List.range k).map (fun i => limbByteAt w v i)

@[simp] theorem limbBytes_length (w : Nat) (v : BitVec w) (k : Nat) :
    (limbBytes w v k).length = k := by
  simp [limbBytes]

/-- Store one `BitVec w` limb as its `k` little-endian bytes at `a`. -/
def storeWLimb (w : Nat) (m : Mem) (a : UInt64) (v : BitVec w) (k : Nat) : Mem :=
  storeBytesLE m a (limbBytes w v k)

/-- Read `k` little-endian bytes at `a` as a byte list (the limb's byte
    image). -/
def loadWLimb (m : Mem) (a : UInt64) (k : Nat) : Option (List UInt8) :=
  loadBytesLE m a k

/-- **Limb read-back, GENERIC in `k`.** Reading back the `k` bytes of a
    freshly stored `BitVec w` limb returns exactly its byte image. This
    is `loadBytesLE_storeBytesLE_same` specialized to the limb's byte
    list — generic in the byte count `k`, with no `bv_decide` on the
    whole word. -/
theorem loadWLimb_storeWLimb_same (w : Nat) (m : Mem) (a : UInt64)
    (v : BitVec w) (k : Nat) (hnw : NoWrap a k) :
    loadWLimb (storeWLimb w m a v k) a k = some (limbBytes w v k) := by
  unfold loadWLimb storeWLimb
  have := loadBytesLE_storeBytesLE_same (limbBytes w v k) m a
    (by rwa [limbBytes_length])
  rwa [limbBytes_length] at this

/-- **Limb frame, GENERIC in `k`.** A `storeWLimb` into a disjoint block
    leaves a `loadWLimb` over `[a, a + k)` unchanged. -/
theorem loadWLimb_storeWLimb_disjoint (w : Nat) (m : Mem) (a a' : UInt64)
    (v : BitVec w) (k k' : Nat)
    (hdisj : MemoryModel.Disjoint (range a k) (range a' k')) :
    loadWLimb (storeWLimb w m a' v k') a k = loadWLimb m a k := by
  unfold loadWLimb storeWLimb
  apply loadBytesLE_storeBytesLE_disjoint
  rwa [limbBytes_length]

/-! ## Scope (see module docstring)

* **(a)** `mpnAddNW_spec` is proved `∀ w` (axiom-clean) — the functional
  core is *free-generic*: the 64-bit proof transports to arbitrary `w` by
  routing the per-limb bound through `BitVec.isLt`.
* **(b)** Read-back (`loadBytesLE_storeBytesLE_same`, under a `NoWrap`
  precondition) and frame (`loadBytesLE_storeBytesLE_disjoint`) are proved
  by **byte-count / byte-list induction** — no `bv_decide` on a whole word.
  In fact no `bv_decide` at all: the single-byte `UInt64` address facts
  (`addr_succ` base advance, `head_ne_of_noWrap`) go through `UInt64.toNat`
  + `omega` + `add_assoc`, so the memory layer is *fully axiom-clean* (only
  the Lean trio `propext`/`Classical.choice`/`Quot.sound`). The limb bridge
  (`loadWLimb_storeWLimb_same/_disjoint`) is generic in the byte count
  `k = w / 8`.
* **(c)** What stays per-width is *only* the interpreter / emission layer:
  the machine word (`U32` vs `U64`) and the carry intrinsic (`ADC_32` vs
  `ADC_64`). Those are concrete machine ops chosen at instantiation. The
  shared, width-generic core is exactly what this file builds — validating
  resolution (c) of the limb-width fork.
-/

end CatCrypt.Crypto.Jasmin.Mpn.GenericWidth
