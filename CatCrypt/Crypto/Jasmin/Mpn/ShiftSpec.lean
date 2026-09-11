/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

/-!
# FEASIBILITY PROTOTYPE — verified limb-level shifts `mpn_lshift` / `mpn_rshift`

**EXPERIMENTAL FILE.**  This is the algorithm-level (pure `List (BitVec 64)`)
correctness proof for the multi-precision shift kernels that a verified GMP
replacement needs:

* `mpn_lshift` — shift a limb array left by `k` bits  (multiply by `2^k`)
* `mpn_rshift` — shift a limb array right by `k` bits (divide by `2^k`)

It backs the standard library `Nat.shiftLeft` / `Nat.shiftRight` (equivalently
`· * 2^k` / `· / 2^k`) under the little-endian denotation
`toNat` from `MpnAddPrototype` (`toNat [w0, w1, …] = w0 + 2^64·w1 + …`).

## The cross-limb bit shift (the load-bearing structural idea)

Write the shift count `k = 64·q + r` with `r < 64`.

* The `64·q` part is a **whole-limb shift**: left-shift prepends `q` zero
  limbs (`· * 2^(64·q)`); right-shift drops the `q` low limbs (`· / 2^(64·q)`).
  These are exact at the limb granularity — no bit arithmetic.

* The remaining `r < 64` part is the genuine **cross-limb bit shift**.  For a
  left shift by `r`, limb `i` of the output is

  ```
  out[i] = (a[i] <<< r) ||| (a[i-1] >>> (64 - r))
  ```

  i.e. limb `i` keeps its own low part shifted up, OR-ed with the `r` high
  bits that spilled out of the limb below.  A high "spill" limb
  `a[n-1] >>> (64 - r)` is appended.  We implement this by threading the
  spill word `prev` (the `>>> (64-r)` of the previous limb) through a fold:
  `bitShiftLeftAux r prev (w :: ws) = ((w <<< r) ||| prev) :: …`, started at
  `prev = 0`.  Symmetrically for the right shift,
  `out[i] = (a[i] >>> r) ||| (a[i+1] <<< (64 - r))`.

  The OR is in fact an **addition**: `a[i] <<< r` has its low `r` bits zero,
  and the spill `prev = a[i-1] >>> (64-r)` fits in `r` bits, so the two
  operands occupy disjoint bit ranges (`disjoint_or_toNat`).  This is exactly
  why the OR-based hardware/`SHRD` idiom is denotation-preserving.

The `r = 0` corner is handled uniformly: `64 - r = 64`, every spill word is
`w >>> 64 = 0`, and the appended spill limb denotes `0`, so `bitShiftLeft a 0`
denotes `toNat a * 2^0 = toNat a` (with one harmless trailing zero limb).

## What the Jasmin emission would need (serial `BignumExec` work item)

This file is purely at the `List (BitVec 64)` algorithm level.  Emitting the
loops as real `.jazz` needs three x86 shift intrinsics wired into
`BignumExec.evalCmdW` / the `#Oasm` decoder — none of which exist there yet:

* `SHL_64` / `SHR_64` — the per-limb `<<< r` / `>>> r`;
* `SHRD_64` (double-precision shift right) — computes
  `(lo >>> r) ||| (hi <<< (64 - r))` in one instruction, the exact
  cross-limb idiom above (and `SHLD_64` for the left direction);
* a variable shift-amount path (the count `r` is a runtime `cl` register).

Adding those `InstrR`/`Oasm` shapes + their `BignumExec` semantics, then a
`Cwhile` refinement à la `MpnAddNJasminRefines`, is the follow-up serial step.
This file completes the last unstarted kernel at the algorithm level.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.ShiftSpec

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype (toNat)

/-! ## §1  A disjoint-bit OR is an addition

The cross-limb formula uses `|||` to merge a limb's shifted body with the
spill bits from its neighbour.  Because those two contributions live in
disjoint bit ranges, the OR equals the sum.  We package this as the single
Nat-level fact `disjoint_or_toNat` and reuse it for both directions. -/

/-- If `2^r ∣ x` (the low `r` bits of `x` are zero) and `y < 2^r`, then the
    bitwise OR of `x` and `y` is their sum: they occupy disjoint bit ranges.

    Proved by bit extensionality: below position `r` only `y` contributes
    (and `x`'s bits there are zero), at/above `r` only `x` contributes (`y`'s
    bits there are zero), so the OR agrees bit-for-bit with the carry-free
    sum.  Mirrors the `SHRD` "merge two disjoint halves" idiom. -/
theorem nat_lor_eq_add_of_disjoint (r x y : Nat) (hx : 2 ^ r ∣ x) (hy : y < 2 ^ r) :
    x ||| y = x + y := by
  obtain ⟨c, rfl⟩ := hx
  -- Bit extensionality.  `2^r * c` is `c` shifted up by `r` (bits `< r` zero);
  -- `y < 2^r` lives entirely below bit `r`.  So below `r` only `y`
  -- contributes, at/above `r` only the shifted `c`; `Nat.testBit_two_pow_mul_add`
  -- gives exactly that split for the carry-free sum `2^r * c + y`.
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add c hy i,
      show 2 ^ r * c = c <<< r by rw [Nat.shiftLeft_eq]; ring,
      Nat.testBit_shiftLeft]
  by_cases hir : i < r
  · -- below bit `r`: shifted part is zero (`¬ r ≤ i`), `y` survives.
    simp only [hir, if_true, show ¬ (i ≥ r) by omega, decide_false,
               Bool.false_and, Bool.false_or]
  · -- at/above bit `r`: `y`'s bit is `false` (`y < 2^r ≤ 2^i`), shifted survives.
    have hyb : y.testBit i = false := Nat.testBit_lt_two_pow (by
      calc y < 2 ^ r := hy
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    simp only [hir, if_false, hyb, show i ≥ r by omega, decide_true,
               Bool.true_and, Bool.or_false]

/-- The `BitVec 64` version: for `x` with low `r` bits zero (`2^r ∣ x.toNat`)
    and `y` with `y.toNat < 2 ^ r`, `(x ||| y).toNat = x.toNat + y.toNat`. -/
theorem disjoint_or_toNat (x y : BitVec 64) (r : Nat)
    (hx : 2 ^ r ∣ x.toNat) (hy : y.toNat < 2 ^ r) :
    (x ||| y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_or]
  exact nat_lor_eq_add_of_disjoint r x.toNat y.toNat hx hy

/-! ## §2  Per-limb bit facts

The two structural facts the cross-limb merge relies on: a left-shifted limb
has its low `r` bits zero (so it is the "high" disjoint half), and a right-
shifted limb fits in `r` bits (so it is the "low" disjoint half). -/

/-- `(w <<< r).toNat = (w.toNat * 2^r) % 2^64`. -/
theorem toNat_shiftLeft (w : BitVec 64) (r : Nat) :
    (w <<< r).toNat = (w.toNat * 2 ^ r) % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- A left-shifted limb has its low `r` bits zero (`r ≤ 64`): it is the high
    half in the cross-limb merge. -/
theorem dvd_toNat_shiftLeft (w : BitVec 64) (r : Nat) (hr : r ≤ 64) :
    2 ^ r ∣ (w <<< r).toNat := by
  rw [toNat_shiftLeft]
  -- `2^r ∣ 2^64` (since `r ≤ 64`), so `2^r ∣ (w.toNat * 2^r) % 2^64`
  -- iff `2^r ∣ w.toNat * 2^r`, which is immediate.
  rw [Nat.dvd_mod_iff (pow_dvd_pow 2 hr)]
  exact Dvd.intro_left _ rfl

/-- `(w >>> s).toNat = w.toNat / 2^s`. -/
theorem toNat_ushiftRight (w : BitVec 64) (s : Nat) :
    (w >>> s).toNat = w.toNat / 2 ^ s := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The spill word `w >>> (64 - r)` fits in `r` bits (`r ≤ 64`): it is the
    low half in the cross-limb left-shift merge of the limb above.  (At
    `r = 0` it says `w >>> 64 = 0`.) -/
theorem toNat_spill_lt (w : BitVec 64) (r : Nat) (hr : r ≤ 64) :
    (w >>> (64 - r)).toNat < 2 ^ r := by
  rw [toNat_ushiftRight]
  -- `w.toNat / 2^(64-r) < 2^r ↔ w.toNat < 2^r * 2^(64-r) = 2^64`.
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show r + (64 - r) = 64 by omega]
  exact w.isLt

/-! ## §3  Cross-limb bit shift left (the `r = k mod 64` part)

`bitShiftLeftAux r prev (w :: ws)` emits `(w <<< r) ||| prev` and recurses
with the new spill `w >>> (64 - r)`.  Started at `prev = 0` it realises
`out[i] = (a[i] <<< r) ||| (a[i-1] >>> (64-r))` and appends the final spill
limb `a[n-1] >>> (64-r)`.  The `r = 0` corner is uniform: every spill is
`w >>> 64 = 0`, so `prev` stays `0` and the merge is the identity `w ||| 0`. -/

/-- Cross-limb bit shift left by `r`, threading the spill word `prev` (the
    `>>> (64-r)` bits that spilled out of the limb below).  The recursion
    appends the running spill as a high limb at the end. -/
def bitShiftLeftAux (r : Nat) (prev : BitVec 64) : List (BitVec 64) → List (BitVec 64)
  | []      => [prev]
  | w :: ws => ((w <<< r) ||| prev) :: bitShiftLeftAux r (w >>> (64 - r)) ws

/-- **Cross-limb bit-shift invariant.**  For `r ≤ 64` and a spill word
    `prev` that fits in `r` bits, the cross-limb bit shift denotes
    `prev + 2^r · toNat ws`.  Proved by induction on the limb list: each step
    splits `(w <<< r) ||| prev` into the disjoint sum `(w <<< r) + prev`
    (`disjoint_or_toNat`), and the new spill `w >>> (64-r)` again fits in `r`
    bits (`toNat_spill_lt`) so the IH applies. -/
theorem bitShiftLeftAux_toNat (r : Nat) (hr : r ≤ 64) :
    ∀ (ws : List (BitVec 64)) (prev : BitVec 64), prev.toNat < 2 ^ r →
      toNat (bitShiftLeftAux r prev ws) = prev.toNat + 2 ^ r * toNat ws := by
  intro ws
  induction ws with
  | nil =>
    intro prev _
    simp [bitShiftLeftAux, toNat]
  | cons w ws ih =>
    intro prev hprev
    -- Peel one limb: `((w <<< r) ||| prev) :: bitShiftLeftAux r (w >>> (64-r)) ws`.
    simp only [bitShiftLeftAux, toNat]
    -- Head merge is a disjoint sum.
    rw [disjoint_or_toNat (w <<< r) prev r (dvd_toNat_shiftLeft w r hr) hprev]
    -- Tail: new spill `w >>> (64-r)` fits in `r` bits, apply IH.
    rw [ih (w >>> (64 - r)) (toNat_spill_lt w r hr)]
    -- `(w <<< r).toNat = (w.toNat * 2^r) % 2^64` and the spill recompose the
    -- limb `w` (the spill is carried up by `2^64`, since it occupies bits
    -- `64-r … 64` of `w` shifted to the next limb's low end):
    -- `(w.toNat * 2^r) % 2^64 + 2^64 * (w.toNat / 2^(64-r)) = 2^r * w.toNat`.
    rw [toNat_shiftLeft, toNat_ushiftRight]
    have hw : w.toNat < 2 ^ 64 := w.isLt
    have hdiv : (w.toNat * 2 ^ r) / 2 ^ 64 = w.toNat / 2 ^ (64 - r) := by
      -- `2^64 = 2^(64-r) * 2^r`, then cancel the common `2^r` factor.
      rw [show (2 : Nat) ^ 64 = 2 ^ (64 - r) * 2 ^ r by rw [← pow_add]; congr 1; omega,
          Nat.mul_div_mul_right _ _ (by positivity)]
    have hsplit : (w.toNat * 2 ^ r) % 2 ^ 64
        + 2 ^ 64 * (w.toNat / 2 ^ (64 - r)) = w.toNat * 2 ^ r := by
      have hdm : 2 ^ 64 * ((w.toNat * 2 ^ r) / 2 ^ 64) + (w.toNat * 2 ^ r) % 2 ^ 64
          = w.toNat * 2 ^ r := Nat.div_add_mod _ _
      rw [hdiv] at hdm
      omega
    -- Regroup the cons denotation `head + 2^64 * tail` and close with `hsplit`.
    -- Distribute `2^r * (w.toNat + 2^64 * toNat ws)` so both sides share atoms.
    rw [show 2 ^ r * (w.toNat + 2 ^ 64 * toNat ws)
          = w.toNat * 2 ^ r + 2 ^ 64 * (2 ^ r * toNat ws) by ring,
        Nat.mul_add]
    omega

/-! ## §4  Whole-limb shift left + the top-level `mpn_lshift`

Prepending `q` zero limbs multiplies the denotation by `2^(64·q)` (it shifts
every limb up by `q` positions).  Combined with the §3 bit shift this gives
`mpn_lshift` for an arbitrary bit count `k = 64·q + r`. -/

/-- Prepending `q` zero limbs scales the denotation by `2^(64·q)`. -/
theorem toNat_replicate_zero_append (q : Nat) (a : List (BitVec 64)) :
    toNat (List.replicate q 0 ++ a) = 2 ^ (64 * q) * toNat a := by
  induction q with
  | zero => simp
  | succ q ih =>
    -- `replicate (q+1) 0 = 0 :: replicate q 0`.
    rw [List.replicate_succ, List.cons_append]
    simp only [toNat, show ((0 : BitVec 64).toNat) = 0 from rfl, Nat.zero_add]
    rw [ih, ← Nat.mul_assoc, ← pow_add,
        show 64 + 64 * q = 64 * (q + 1) by ring]

/-- `mpn_lshift(a, k)` at the limb-list level: shift `a` left by `k` bits.
    Decompose `k = 64·q + r` (`q = k / 64`, `r = k % 64`): prepend `q` zero
    limbs (the whole-limb part, `· * 2^(64·q)`), then apply the cross-limb
    bit shift by `r` (`· * 2^r`), started with spill `0`. -/
def mpnShiftLeft (a : List (BitVec 64)) (k : Nat) : List (BitVec 64) :=
  bitShiftLeftAux (k % 64) 0 (List.replicate (k / 64) 0 ++ a)

/-- **`mpn_lshift` correctness.**  The little-endian denotation of the shifted
    limbs is `toNat a * 2^k` — i.e. `mpnShiftLeft` backs `· <<< k`
    (`Nat.shiftLeft`).  Combines the whole-limb scale `2^(64·(k/64))` with the
    bit-shift scale `2^(k%64)`; their product is `2^k` since
    `64·(k/64) + k%64 = k`. -/
theorem mpnShiftLeft_spec (a : List (BitVec 64)) (k : Nat) :
    toNat (mpnShiftLeft a k) = toNat a * 2 ^ k := by
  unfold mpnShiftLeft
  -- Bit shift by `r = k % 64` (< 64), spill `0` (which is `< 2^r`).
  rw [bitShiftLeftAux_toNat (k % 64) (by omega) _ 0 (by positivity),
      toNat_replicate_zero_append]
  -- `0 + 2^(k%64) * (2^(64·(k/64)) * toNat a) = toNat a * 2^k`.
  rw [show ((0 : BitVec 64).toNat) = 0 from rfl, Nat.zero_add,
      ← Nat.mul_assoc, ← pow_add, show k % 64 + 64 * (k / 64) = k by omega]
  ring

/-- `mpnShiftLeft` realises `Nat.shiftLeft` on the denotation. -/
theorem mpnShiftLeft_spec_shiftLeft (a : List (BitVec 64)) (k : Nat) :
    toNat (mpnShiftLeft a k) = toNat a <<< k := by
  rw [mpnShiftLeft_spec, Nat.shiftLeft_eq]

/-! ## §5  Cross-limb bit shift right (the `r = k mod 64` part)

The down-shift is the mirror of §3, but it looks *one limb ahead*: limb `i`
takes its own high part `a[i] >>> r` OR-ed with the low `r` bits of the limb
above, raised to the top: `a[i+1] <<< (64 - r)`.  No spill limb is appended
(the top limb just loses its low bits).  The split point of the disjoint OR is
`64 - r`: `a[i] >>> r` fits in the low `64-r` bits, and `a[i+1] <<< (64-r)`
has those `64-r` bits zero. -/

/-- A right-shifted limb fits in `64 - r` bits (`r ≤ 64`): it is the low half
    in the cross-limb right-shift merge. -/
theorem toNat_ushiftRight_lt (w : BitVec 64) (r : Nat) (hr : r ≤ 64) :
    (w >>> r).toNat < 2 ^ (64 - r) := by
  rw [toNat_ushiftRight]
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show (64 - r) + r = 64 by omega]
  exact w.isLt

/-- Cross-limb bit shift right by `r`.  Looks one limb ahead: each limb's high
    part `w >>> r` is merged with the low `r` bits of the next limb pulled down
    via `w' <<< (64 - r)`.  The top limb (`[w]`) drops its low `r` bits. -/
def bitShiftRight (r : Nat) : List (BitVec 64) → List (BitVec 64)
  | []           => []
  | [w]          => [w >>> r]
  | w :: w' :: ws => ((w >>> r) ||| (w' <<< (64 - r))) :: bitShiftRight r (w' :: ws)

/-- **Cross-limb right-shift invariant.**  For `r < 64`, the cross-limb bit
    shift right denotes `toNat ws / 2^r` — i.e. it divides by `2^r`.

    Proved by induction.  The cons-cons step splits the head merge into the
    disjoint sum `(w >>> r) + (w' <<< (64-r))` (`disjoint_or_toNat` at split
    point `64-r`), and then a `Nat` division identity recombines: writing
    `T = toNat (w'::ws)`, since `2^r ∣ 2^64 · toNat ws` we have
    `T % 2^r = w'.toNat % 2^r`, and `(w.toNat + 2^64·toNat ws) / 2^r`
    telescopes through `Nat.div_add_mod` to match the emitted head plus
    `2^64 · (T / 2^r)` (the IH). -/
theorem bitShiftRight_toNat (r : Nat) (hr : r < 64) :
    ∀ (ws : List (BitVec 64)), toNat (bitShiftRight r ws) = toNat ws / 2 ^ r := by
  intro ws
  induction ws with
  | nil => simp [bitShiftRight, toNat]
  | cons w ws ih =>
    cases ws with
    | nil =>
      -- single limb: `[w >>> r]`, `toNat = w.toNat / 2^r = toNat [w] / 2^r`.
      simp only [bitShiftRight, toNat, toNat_ushiftRight, Nat.mul_zero, Nat.add_zero]
    | cons w' ws =>
      -- `bitShiftRight r (w :: w' :: ws) = head :: bitShiftRight r (w' :: ws)`.
      simp only [bitShiftRight, toNat]
      -- Disjoint head merge at split point `64-r`: high = `w' <<< (64-r)`
      -- (low `64-r` bits zero), low = `w >>> r` (< 2^(64-r)).
      rw [show (w >>> r) ||| (w' <<< (64 - r)) = (w' <<< (64 - r)) ||| (w >>> r)
            from BitVec.or_comm _ _,
          disjoint_or_toNat (w' <<< (64 - r)) (w >>> r) (64 - r)
            (dvd_toNat_shiftLeft w' (64 - r) (by omega))
            (toNat_ushiftRight_lt w r (by omega))]
      -- IH on the tail `w' :: ws`.
      rw [ih]
      -- Abbreviate `T = toNat (w' :: ws) = w'.toNat + 2^64 * toNat ws`.
      simp only [toNat] at *
      rw [toNat_shiftLeft, toNat_ushiftRight]
      -- Now a pure `Nat` division identity (see docstring); discharge with the
      -- div/mod facts below.
      have hw : w.toNat < 2 ^ 64 := w.isLt
      have hw' : w'.toNat < 2 ^ 64 := w'.isLt
      -- Abbreviate `R = 2^r`, `S = 2^(64-r)`, with `R*S = 2^64` (`r < 64`).
      have hRpos : 0 < 2 ^ r := by positivity
      have hpow : (2 : Nat) ^ 64 = 2 ^ r * 2 ^ (64 - r) := by
        rw [← pow_add]; congr 1; omega
      -- (1) RHS telescopes: `(w.toNat + (R*S)·T) / R = w.toNat/R + S·T`.
      have hrhs : (w.toNat + 2 ^ 64 * (w'.toNat + 2 ^ 64 * toNat ws)) / 2 ^ r
          = w.toNat / 2 ^ r + 2 ^ (64 - r) * (w'.toNat + 2 ^ 64 * toNat ws) := by
        conv_lhs => rw [show 2 ^ 64 * (w'.toNat + 2 ^ 64 * toNat ws)
              = 2 ^ r * (2 ^ (64 - r) * (w'.toNat + 2 ^ 64 * toNat ws)) by
                rw [← Nat.mul_assoc, ← hpow]]
        rw [Nat.add_mul_div_left _ _ hRpos, Nat.add_comm]
      -- (2) tail division telescopes: `T / R = w'.toNat/R + S·toNat ws`.
      have htdiv : (w'.toNat + 2 ^ 64 * toNat ws) / 2 ^ r
          = w'.toNat / 2 ^ r + 2 ^ (64 - r) * toNat ws := by
        conv_lhs => rw [show 2 ^ 64 * toNat ws
              = 2 ^ r * (2 ^ (64 - r) * toNat ws) by rw [← Nat.mul_assoc, ← hpow]]
        rw [Nat.add_mul_div_left _ _ hRpos, Nat.add_comm]
      -- (3) high half: `(w'.toNat · S) % (R·S) = (w'.toNat % R)·S`.
      have hmod : w'.toNat * 2 ^ (64 - r) % 2 ^ 64
          = (w'.toNat % 2 ^ r) * 2 ^ (64 - r) := by
        rw [hpow, Nat.mul_mod_mul_right]
      -- (4) limb recomposition `w'.toNat = w'.toNat % R + R · (w'.toNat / R)`.
      have hmd : w'.toNat % 2 ^ r + 2 ^ r * (w'.toNat / 2 ^ r) = w'.toNat :=
        Nat.mod_add_div _ _
      rw [hrhs, hmod, htdiv]
      -- Goal: `(w'.toNat%R)·S + w.toNat/R + (R·S)·(w'.toNat/R + S·toNat ws)`
      --      = `w.toNat/R + S·(w'.toNat + (R·S)·toNat ws)`.  The `w.toNat/R`
      -- and `toNat ws` terms cancel; what remains, after `R·S = 2^64`, is
      -- `(w'.toNat%R)·S + S·(R·(w'.toNat/R)) = S·w'.toNat`, i.e. `S·` of (4).
      rw [hpow]
      nlinarith [hmd]

/-! ## §6  Whole-limb shift right + the top-level `mpn_rshift`

Dropping the `q` low limbs divides the denotation by `2^(64·q)` (the mirror of
the §4 zero-prepend).  Combined with the §5 bit shift this gives `mpn_rshift`
for an arbitrary bit count `k = 64·q + r`. -/

/-- Dropping the `q` low limbs divides the denotation by `2^(64·q)`. -/
theorem toNat_drop (q : Nat) (a : List (BitVec 64)) :
    toNat (a.drop q) = toNat a / 2 ^ (64 * q) := by
  induction q generalizing a with
  | zero => simp
  | succ q ih =>
    cases a with
    | nil => simp [toNat]
    | cons w ws =>
      -- `(w :: ws).drop (q+1) = ws.drop q`; peel the low limb `w` then divide
      -- the remaining `2^64 · toNat ws` head by `2^(64·q)`.
      rw [List.drop_succ_cons, ih]
      -- `toNat (w::ws) / 2^(64·(q+1)) = (w.toNat + 2^64·toNat ws) / 2^(64·(q+1))`.
      simp only [toNat]
      -- `2^(64·(q+1)) = 2^64 · 2^(64·q)`; split the division and drop the low
      -- limb `w` (since `w.toNat < 2^64` it contributes nothing to `/2^64`).
      rw [show 64 * (q + 1) = 64 + 64 * q by ring, pow_add,
          ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ 64),
          Nat.div_eq_of_lt w.isLt, Nat.zero_add]

/-- `mpn_rshift(a, k)` at the limb-list level: shift `a` right by `k` bits.
    Decompose `k = 64·q + r`: drop the `q` low limbs (the whole-limb part,
    `· / 2^(64·q)`), then apply the cross-limb bit shift down by `r`
    (`· / 2^r`). -/
def mpnShiftRight (a : List (BitVec 64)) (k : Nat) : List (BitVec 64) :=
  bitShiftRight (k % 64) (a.drop (k / 64))

/-- **`mpn_rshift` correctness.**  The little-endian denotation of the shifted
    limbs is `toNat a / 2^k` — i.e. `mpnShiftRight` backs `· >>> k`
    (`Nat.shiftRight`).  Combines the whole-limb division `· / 2^(64·(k/64))`
    with the bit-shift division `· / 2^(k%64)`; iterating the two divisions is
    a single `· / 2^k` since `64·(k/64) + k%64 = k`. -/
theorem mpnShiftRight_spec (a : List (BitVec 64)) (k : Nat) :
    toNat (mpnShiftRight a k) = toNat a / 2 ^ k := by
  unfold mpnShiftRight
  -- Bit shift by `r = k % 64 < 64`, on the limb-dropped list.
  rw [bitShiftRight_toNat (k % 64) (by omega), toNat_drop]
  -- `(toNat a / 2^(64·(k/64))) / 2^(k%64) = toNat a / 2^k`.
  rw [Nat.div_div_eq_div_mul, ← pow_add,
      show 64 * (k / 64) + k % 64 = k by omega]

/-- `mpnShiftRight` realises `Nat.shiftRight` on the denotation. -/
theorem mpnShiftRight_spec_shiftRight (a : List (BitVec 64)) (k : Nat) :
    toNat (mpnShiftRight a k) = toNat a >>> k := by
  rw [mpnShiftRight_spec, Nat.shiftRight_eq_div_pow]

/-! ## §7  Sanity checks (decidable `#eval`)

Concrete instances of the two specs, checked by `native_decide`. -/

/-- Left shift by 1 bit within a limb: `[3] <<< 1 = [6]` (+ zero spill). -/
example : toNat (mpnShiftLeft [3] 1) = 3 * 2 ^ 1 := by native_decide

/-- Left shift by 64 bits = one whole-limb shift: `toNat ([5] <<< 64) = 5·2^64`
    (the limb list is `[0, 5, 0]` — a leading zero limb and a zero spill). -/
example : toNat (mpnShiftLeft [5] 64) = 5 * 2 ^ 64 := by native_decide

/-- Cross-limb left shift by 4: top nibble of limb 0 spills into limb 1.
    `[0xF000…0000, 0] <<< 4`: the top nibble `0xF` moves to limb 1's low nibble. -/
example : toNat (mpnShiftLeft [(0xF000000000000000 : BitVec 64), 0] 4)
    = toNat [(0xF000000000000000 : BitVec 64), 0] * 2 ^ 4 := by native_decide

/-- Right shift by 1: `[6] >>> 1 = [3]`. -/
example : toNat (mpnShiftRight [6] 1) = 6 / 2 ^ 1 := by native_decide

/-- Right shift by 64 = drop one limb: `[7, 9] >>> 64 = [9]`. -/
example : mpnShiftRight [7, 9] 64 = [9] := by native_decide

/-- Cross-limb right shift by 4: low nibble of limb 1 pulls down into limb 0.
    `[0, 0xF] >>> 4` pulls `0xF`'s low bits to the top of limb 0. -/
example : toNat (mpnShiftRight [(0 : BitVec 64), 0xF] 4)
    = toNat [(0 : BitVec 64), 0xF] / 2 ^ 4 := by native_decide

end CatCrypt.Crypto.Jasmin.Mpn.ShiftSpec
