/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype

@[expose] public section

set_option autoImplicit false

/-!
# Phase 2 — verified full schoolbook multiply `mpn_mul`

**EXPERIMENTAL FILE.**  Phase-2 companion to `Mpn.Mul1Prototype.lean` /
`Mpn.Addmul1Prototype.lean`.  It proves the GMP kernel `mpn_mul`
(`out[] = a[] * b[]`, the full `N×M` schoolbook product) at the **pure
functional** level: a clean reference `mpnMul` producing the `|a|+|b|`-limb
product, with the headline correctness statement

```
toNat (mpnMul a b) = toNat a * toNat b
```

proved by induction on `b`, reusing the single-limb kernels
`mpnMul1` (`MpnMul1Prototype`) and `mpnAddN` (`MpnAddPrototype`) and their
already-proved `toNat` specs.

## Why `mpn_mul` is structurally harder than the single-limb kernels

`mpn_mul_1` / `mpn_addmul_1` are *single* `Cwhile` loops.  The full
`mpn_mul` is a **nested** loop: an outer loop over `b`'s limbs whose body is
an `mpn_addmul_1` of `a` (scaled by `b[j]`) into the result window
`out[j .. j+|a|]`.  The existing one-`Cwhile`-loop rule
(`bignumExecFuel_loopMul_step` / `bignumExecFuel_loopAddmul_step`) does not
cover a loop whose body is itself a loop.  Two emission structures are
available for the Jasmin bridge:

  (a) **Ccall composition** — the outer-loop body is a `Ccall` to
      `mpn_addmul_1`'s `FunDecl`, registered in a `BignumRegistry`; each call
      is discharged by `MpnAddmul1JasminRefines`.  `bignumExecFuel`'s `Ccall`
      case (void return) inherits the callee's `mem`, so the result region
      accumulates limb by limb.

  (b) **Nested `Cwhile`** — inline `mpn_addmul_1` as an inner loop; needs a
      genuine two-level loop invariant.

This file delivers the PURE reference + `toNat`-correctness solid and
axiom-clean (priority 1), and records precisely what the outer-loop /
result-region-frame infrastructure needs for the Jasmin bridge (priority 2,
§5).

## Functional spec

`mpnMul a b` produces `|a|+|b|` limbs with

```
toNat (mpnMul a b) = toNat a · toNat b
```

The recursion is on `b`, using `a · (b0 :: bs) = a·b0 + 2^64·(a·bs)`:

  * `a·b0` is the single-limb product `mpnMul1 a b0` (its `|a|` low limbs plus
    the carry-out at limb `|a|`), padded with `|bs|` zero limbs to width
    `|a|+|bs|+1`;
  * `2^64·(a·bs)` is `0 :: (mpnMul a bs)` (the recursive product shifted up one
    limb), also width `|a|+|bs|+1`;
  * the sum is one `mpnAddN` of the two equal-width operands, and the carry-out
    is provably `false` because the full product fits in `|a|+|b|` limbs.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.MulPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype hiding vr pv loadAt0 storeAt0 binImm
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype

/-! ## §1  `toNat` algebra: append, replicate-zero, the size bound, length

These four facts about the little-endian denotation `toNat` (from
`MpnAddPrototype`) are what the `mpnMul` correctness induction needs.  They
are stated and proved here (none exists upstream). -/

/-- Denotation of a concatenation: the high block is shifted by `2^(64·|xs|)`.
    `toNat (xs ++ ys) = toNat xs + 2^(64·|xs|) · toNat ys`. -/
theorem toNat_append (xs ys : List (BitVec 64)) :
    toNat (xs ++ ys) = toNat xs + (2 ^ 64) ^ xs.length * toNat ys := by
  induction xs with
  | nil => simp [toNat]
  | cons x xs ih =>
    simp only [List.cons_append, toNat, List.length_cons, ih, pow_succ]
    ring

/-- A run of zero limbs denotes `0`. -/
theorem toNat_replicate_zero (k : Nat) : toNat (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp [toNat]
  | succ k ih =>
    rw [List.replicate_succ, toNat, ih]
    simp

/-- The denotation of a `k`-limb list is below `2^(64·k)` (each limb `< 2^64`).
    This is the bound that forces the top `mpnAddN` carry-out to be `false`. -/
theorem toNat_lt (xs : List (BitVec 64)) : toNat xs < (2 ^ 64) ^ xs.length := by
  induction xs with
  | nil => simp [toNat]
  | cons x xs ih =>
    simp only [toNat, List.length_cons, pow_succ]
    have hx : x.toNat < 2 ^ 64 := x.isLt
    have hpos : 0 < (2 ^ 64) ^ xs.length := by positivity
    -- x.toNat + 2^64 * toNat xs < 2^64 + 2^64 * (2^64^k - 1) ... ≤ 2^64^k * 2^64.
    calc x.toNat + 2 ^ 64 * toNat xs
        < 2 ^ 64 + 2 ^ 64 * toNat xs := by omega
      _ ≤ 2 ^ 64 + 2 ^ 64 * ((2 ^ 64) ^ xs.length - 1) := by
          have := Nat.mul_le_mul_left (2 ^ 64) (Nat.le_sub_one_of_lt ih)
          omega
      _ = (2 ^ 64) ^ xs.length * 2 ^ 64 := by
          rw [Nat.mul_sub_one]; omega

/-- **Little-endian representation is unique.**  Two limb lists of the *same
    length* with the *same* `toNat` denotation are equal: each limb is recovered
    as the residue of the running value mod `2^64`.  This is the pure ingredient
    that lets a windowed in-place accumulation (length `|a|+|b|`, value
    `toNat a · toNat b`) be identified with the `mpnAddN`-based `mpnMul` without
    matching structure — both share length and `toNat` (`mpnMul_contract`). -/
theorem toNat_inj (xs ys : List (BitVec 64))
    (hlen : xs.length = ys.length) (hval : toNat xs = toNat ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      simp only [toNat] at hval
      have hx := x.isLt
      have hy := y.isLt
      -- Heads agree mod 2^64; since both < 2^64, they are equal.
      have hhead : x.toNat = y.toNat := by omega
      have htail : toNat xs = toNat ys := by omega
      rw [BitVec.eq_of_toNat_eq hhead, ih ys hlen' htail]

/-- `mpnAddN` of equal-length operands preserves the output length. -/
theorem mpnAddN_length (a b : List (BitVec 64)) (cin : Bool) (h : a.length = b.length) :
    (mpnAddN a b cin).1.length = a.length := by
  induction a generalizing b cin with
  | nil => simp [mpnAddN]
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      have h' : as.length = bs.length := by simpa using h
      simp only [mpnAddN]
      simp only [List.length_cons]
      rw [ih bs (adcStep a b cin).2 h']

/-! ## §2  The pure reference `mpnMul` -/

/-- The single-limb product `a · b0` as a width-`|a|+1` limb list:
    `mpnMul1 a b0`'s `|a|` low limbs, with the carry-out appended at limb `|a|`.
    `toNat (mul1Full a b0) = toNat a · b0` exactly (no residual carry). -/
def mul1Full (a : List (BitVec 64)) (b0 : BitVec 64) : List (BitVec 64) :=
  (mpnMul1 a b0 0).1 ++ [(mpnMul1 a b0 0).2]

/-- The `mpnMul1` result has exactly `|a|` low limbs. -/
theorem mpnMul1_length (a : List (BitVec 64)) (b cy : BitVec 64) :
    (mpnMul1 a b cy).1.length = a.length := by
  induction a generalizing cy with
  | nil => simp [mpnMul1]
  | cons a as ih =>
    simp only [mpnMul1, List.length_cons]
    rw [ih (mul1Step a b cy).2]

/-- The `mpnAddmul1` result has exactly `out.length` low limbs (for equal-length
    `out`/`a`).  Mirror of `mpnMul1_length`, recursing in lockstep. -/
theorem mpnAddmul1_length (out a : List (BitVec 64)) (b cy : BitVec 64)
    (h : out.length = a.length) :
    (mpnAddmul1 out a b cy).1.length = out.length := by
  induction out generalizing a cy with
  | nil => simp [mpnAddmul1]
  | cons o os ih =>
    cases a with
    | nil => simp at h
    | cons x xs =>
      have h' : os.length = xs.length := by simpa using h
      simp only [mpnAddmul1, List.length_cons]
      rw [ih xs (addmul1Step o x b cy).2 h']

/-- `mul1Full a b0` has width `|a| + 1`. -/
theorem mul1Full_length (a : List (BitVec 64)) (b0 : BitVec 64) :
    (mul1Full a b0).length = a.length + 1 := by
  simp [mul1Full, mpnMul1_length]

/-- `mul1Full` denotes the exact single-limb product `toNat a · b0`. -/
theorem mul1Full_toNat (a : List (BitVec 64)) (b0 : BitVec 64) :
    toNat (mul1Full a b0) = toNat a * b0.toNat := by
  rw [mul1Full, toNat_append]
  simp only [toNat, mpnMul1_length]
  -- toNat row + 2^(64|a|) * carry = toNat a * b0  (mpnMul1 carry-in-0 spec)
  have h := mpnMul1_spec_carryIn_zero a b0
  -- h : toNat (mpnMul1 a b0 0).1 + (2^64)^|a| * (mpnMul1 a b0 0).2.toNat = toNat a * b0.toNat
  omega

/-- **Pure reference for `mpn_mul`** — the full `|a|+|b|`-limb schoolbook
    product, recursing on `b`.

    * `[]`            ⇒ `replicate |a| 0` (the all-zero `|a|`-limb product `a·0`);
    * `b0 :: bs`      ⇒ `mpnAddN (mul1Full a b0 ++ replicate |bs| 0) (0 :: mpnMul a bs) false`
                        — `a·b0` (width `|a|+1`, zero-padded to `|a|+|bs|+1`)
                        added to `2^64·(a·bs)` (the recursive product shifted up
                        one limb).  Both operands have width `|a|+|bs|+1`; the
                        carry-out is dropped (provably `false`). -/
def mpnMul (a : List (BitVec 64)) : List (BitVec 64) → List (BitVec 64)
  | []        => List.replicate a.length 0
  | b0 :: bs  =>
      (mpnAddN (mul1Full a b0 ++ List.replicate bs.length 0)
        (0 :: mpnMul a bs) false).1

/-- `mpnMul a b` has width exactly `|a| + |b|`. -/
theorem mpnMul_length (a b : List (BitVec 64)) :
    (mpnMul a b).length = a.length + b.length := by
  induction b with
  | nil => simp [mpnMul, List.length_replicate]
  | cons b0 bs ih =>
    -- mpnAddN over equal-length operands preserves the LHS length.
    have hlhs : (mul1Full a b0 ++ List.replicate bs.length 0).length
        = a.length + bs.length + 1 := by
      simp [mul1Full_length, List.length_replicate]; omega
    have hrhs : (0 :: mpnMul a bs).length = a.length + bs.length + 1 := by
      simp only [List.length_cons, ih]
    have heq : (mul1Full a b0 ++ List.replicate bs.length 0).length
        = (0 :: mpnMul a bs).length := by rw [hlhs, hrhs]
    simp only [mpnMul, List.length_cons]
    rw [mpnAddN_length _ _ false heq, hlhs]
    omega

/-! ## §3  Correctness: `toNat (mpnMul a b) = toNat a · toNat b`

The headline deliverable, by induction on `b`.  Each step:

  * the head operand denotes `a·b0` (`mul1Full_toNat`, zero-padding adds 0);
  * the shifted recursive operand denotes `2^64·(a·bs)` (IH + `toNat`-cons);
  * `mpnAddN_spec` combines them: `lhs + rhs + 2^(64·width)·carry = a·b`;
  * the size bound (`toNat_lt`) forces `carry = false`, since both `a·b` and the
    `(|a|+|b|)`-limb output fit below `2^(64·(|a|+|b|))`. -/

/-- The shifted recursive operand `0 :: mpnMul a bs` denotes `2^64 · (a · bs)`. -/
theorem shifted_rec_toNat (a bs : List (BitVec 64)) (ih : toNat (mpnMul a bs) = toNat a * toNat bs) :
    toNat (0 :: mpnMul a bs) = 2 ^ 64 * (toNat a * toNat bs) := by
  simp only [toNat]
  rw [ih]; simp

/-- The head operand `mul1Full a b0 ++ replicate |bs| 0` denotes `a · b0`. -/
theorem padded_head_toNat (a bs : List (BitVec 64)) (b0 : BitVec 64) :
    toNat (mul1Full a b0 ++ List.replicate bs.length 0) = toNat a * b0.toNat := by
  rw [toNat_append, toNat_replicate_zero, mul1Full_toNat]; simp

/-- **Main correctness theorem — proved by induction on `b`.**

    The pure `mpn_mul` reference computes the exact `|a|+|b|`-limb product:
    `toNat (mpnMul a b) = toNat a · toNat b`. -/
theorem mpnMul_toNat (a b : List (BitVec 64)) :
    toNat (mpnMul a b) = toNat a * toNat b := by
  induction b with
  | nil =>
    show toNat (List.replicate a.length 0) = toNat a * toNat ([] : List (BitVec 64))
    rw [toNat_replicate_zero]; simp [toNat]
  | cons b0 bs ih =>
    -- Equal-width operands for the `mpnAddN` step.
    have hlhs_len : (mul1Full a b0 ++ List.replicate bs.length 0).length
        = a.length + bs.length + 1 := by
      simp [mul1Full_length, List.length_replicate]; omega
    have hrhs_len : (0 :: mpnMul a bs).length = a.length + bs.length + 1 := by
      simp only [List.length_cons, mpnMul_length]
    have hwidth : (mul1Full a b0 ++ List.replicate bs.length 0).length
        = (0 :: mpnMul a bs).length := by rw [hlhs_len, hrhs_len]
    -- Denotations of the two operands.
    have hhead := padded_head_toNat a bs b0
    have htail := shifted_rec_toNat a bs ih
    -- The `mpnAddN` carry-chain identity (carry-in `false`).
    have hadd := mpnAddN_spec _ _ hwidth false
    simp only [carryNat, Bool.false_eq_true, if_false, Nat.add_zero] at hadd
    rw [hhead, htail] at hadd
    -- Abbreviate the addN result and the operand width.
    set W : Nat := a.length + bs.length + 1 with hW
    set res := mpnAddN (mul1Full a b0 ++ List.replicate bs.length 0)
      (0 :: mpnMul a bs) false with hres
    -- hadd : toNat res.1 + (2^64)^|lhs| * carryNat res.2 = a·b0 + 2^64·(a·bs)
    rw [hlhs_len] at hadd
    -- The product fits in W limbs, forcing the carry-out to 0.
    have hresw : toNat res.1 < (2 ^ 64) ^ W := by
      have hlen : res.1.length = W := by
        rw [hres, mpnAddN_length _ _ false hwidth, hlhs_len]
      have := toNat_lt res.1
      rwa [hlen] at this
    -- The full product is below `2^(64·W)`.
    have hprodbound : toNat a * b0.toNat + 2 ^ 64 * (toNat a * toNat bs) < (2 ^ 64) ^ W := by
      have hprod : toNat a * b0.toNat + 2 ^ 64 * (toNat a * toNat bs)
          = toNat a * toNat (b0 :: bs) := by simp only [toNat]; ring
      have hpa : toNat a < (2 ^ 64) ^ a.length := toNat_lt a
      have hpb : toNat (b0 :: bs) < (2 ^ 64) ^ (b0 :: bs).length := toNat_lt (b0 :: bs)
      have hbound : toNat a * toNat (b0 :: bs)
          < (2 ^ 64) ^ a.length * (2 ^ 64) ^ (b0 :: bs).length :=
        Nat.mul_lt_mul_of_lt_of_le hpa (Nat.le_of_lt hpb) (by positivity)
      rw [← pow_add] at hbound
      have hWeq : a.length + (b0 :: bs).length = W := by
        simp only [List.length_cons, hW]; omega
      rw [hWeq] at hbound
      rw [hprod]; exact hbound
    -- The `if`-carry term in `hadd` is 0: if it were `2^(64·W)·1`, the RHS
    -- (the product, `< 2^(64·W)`) could not equal `toNat res.1 (≥0) + 2^(64·W)`.
    have hpow_pos : 0 < (2 ^ 64) ^ W := by positivity
    have hcarry0 : (2 ^ 64) ^ W * (if res.2 = true then 1 else 0) = 0 := by
      by_cases hc : res.2 = true
      · -- carry-out `true` ⇒ `hadd` forces product ≥ 2^(64·W), contradicting bound.
        exfalso
        rw [hc, if_pos rfl] at hadd
        omega
      · rw [if_neg hc, Nat.mul_zero]
    rw [hcarry0, Nat.add_zero] at hadd
    -- Now: toNat res.1 = a·b0 + 2^64·(a·bs) = a·(b0::bs).
    simp only [mpnMul, ← hres, toNat]
    rw [hadd]; ring

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `[3] · [5] = 15` (single-limb × single-limb), two output limbs `[15, 0]`. -/
example : mpnMul [3] [5] = [15, 0] := by native_decide

/-- `[2^32] · [2^32] = 2^64`, i.e. limb `[0, 1]`. -/
example : mpnMul [(BitVec.ofNat 64 (2 ^ 32))] [(BitVec.ofNat 64 (2 ^ 32))] = [0, 1] := by
  native_decide

/-- `[0xFFFF…FFFF] · [0xFFFF…FFFF] = (2^64-1)^2 = 2^128 - 2^65 + 1`.
    Low limb `1`, high limb `2^64 - 2`. -/
example : mpnMul [(-1 : BitVec 64)] [(-1 : BitVec 64)]
    = [1, (BitVec.ofNat 64 (2 ^ 64 - 2))] := by native_decide

/-- Two-limb × two-limb product, checked via `toNat`. -/
example : toNat (mpnMul [5, 7] [11, 13]) = toNat [5, 7] * toNat [11, 13] := by
  native_decide

#eval toNat (mpnMul [(-1 : BitVec 64)] [(-1 : BitVec 64)])  -- (2^64-1)^2

/-! ## §4  The headline corollary, named for the GMP contract

`mpn_mul(rp, up, n, vp, m)` writes the `n+m`-limb product `up·vp` into `rp`.
Our pure `mpnMul a b` matches: width `|a|+|b|`, value `toNat a · toNat b`. -/

/-- **The GMP `mpn_mul` functional contract, at the pure level.**  `mpnMul a b`
    is an `|a|+|b|`-limb little-endian number whose value is the exact product
    `toNat a · toNat b`. -/
theorem mpnMul_contract (a b : List (BitVec 64)) :
    (mpnMul a b).length = a.length + b.length ∧
    toNat (mpnMul a b) = toNat a * toNat b :=
  ⟨mpnMul_length a b, mpnMul_toNat a b⟩

-- Axiom-cleanliness check: the pure correctness theorem depends only on the
-- standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`),
-- no `sorryAx`.
#print axioms mpnMul_toNat
#print axioms mpnMul_contract

/-- `mpn_mul_1`'s single step equals `mpn_addmul_1`'s step accumulating into a
    zero limb (the second `addCarry` against `0` is a no-op). -/
theorem addmul1Step_zero (a b cy : BitVec 64) :
    addmul1Step 0 a b cy = mul1Step a b cy := by
  unfold addmul1Step mul1Step; simp only [addCarry, BitVec.add_zero]; simp [BitVec.ult]

/-- **`mpn_mul_1` is `mpn_addmul_1` over a zeroed accumulator.**  Writing row 0
    into the (initially zero) result window via `mpn_mul_1` produces the same
    limbs as `mpn_addmul_1` would — the schoolbook accumulation's first row. -/
theorem mpnMul1_eq_mpnAddmul1_replicate (a : List (BitVec 64)) (b0 cy : BitVec 64) :
    mpnMul1 a b0 cy = mpnAddmul1 (List.replicate a.length 0) a b0 cy := by
  induction a generalizing cy with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.replicate_succ, mpnMul1, mpnAddmul1, addmul1Step_zero, ih]

/-! ## §3a  The windowed in-place accumulation reference `mulAcc`

`mulAcc a bs acc` models the *in-place sliding-window* accumulation that the
emitted assembly performs: `acc` is the current result region (length
`|a| + |bs|`); each row multiply-accumulates `a · b[j]` into the active window
`acc[0 .. |a|]` (an `mpn_addmul_1` over the low `|a|` limbs plus the carry-out at
limb `|a|`), then *finalizes* the lowest limb and slides one limb up.  This is
exactly the per-row carry-window step `mpnMul_per_row_carry` repeated `|bs|`
times.  We prove (a) it has the right length, (b) `toNat (mulAcc a bs acc) =
toNat acc + toNat a · toNat bs`, so on a zeroed region it equals `mpnMul a b`. -/

/-- One row of the in-place accumulation: replace the active window
    `acc[0 .. |a|]` with `(mpnAddmul1 (acc.take |a|) a b0 0).1 ++ [carry]`
    (length `|a|+1`), finalize the lowest limb, and slide.  Recurses on `bs`. -/
def mulAcc (a : List (BitVec 64)) : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [],       acc => acc
  | b0 :: bs, acc =>
      let p := mpnAddmul1 (acc.take a.length) a b0 0
      let win := p.1 ++ [p.2]
      win.headI :: mulAcc a bs (win.tail ++ acc.drop (a.length + 1))

/-- `mulAcc a bs acc` has length `|a| + |bs|` when `|acc| = |a| + |bs|`. -/
theorem mulAcc_length (a bs acc : List (BitVec 64)) (hacc : acc.length = a.length + bs.length) :
    (mulAcc a bs acc).length = a.length + bs.length := by
  induction bs generalizing acc with
  | nil => simpa using! hacc
  | cons b0 bs ih =>
    -- the window has length |a|+1; its tail length |a|; the drop length |bs|.
    have htake : (acc.take a.length).length = a.length := by
      rw [List.length_take]; omega
    have hp1 : (mpnAddmul1 (acc.take a.length) a b0 0).1.length = a.length := by
      rw [mpnAddmul1_length (acc.take a.length) a b0 0 (by rw [htake]), htake]
    simp only [mulAcc, List.length_cons]
    have hnext : ((mpnAddmul1 (acc.take a.length) a b0 0).1 ++
        [(mpnAddmul1 (acc.take a.length) a b0 0).2]).tail.length
        + (acc.drop (a.length + 1)).length = a.length + bs.length := by
      rw [List.length_tail, List.length_append, hp1, List.length_drop]
      simp only [List.length_cons] at hacc
      simp only [List.length_singleton]; omega
    rw [ih _ (by rw [List.length_append]; exact hnext)]
    omega

/-- **Value of the windowed accumulation.**  When the result region `acc`
    (length `|a| + |bs|`) has its high `|bs|` limbs zero (the schoolbook
    invariant: limb `acc[|a|]` and beyond are untouched zeros when each row
    starts), the in-place accumulation `mulAcc a bs acc` denotes
    `toNat acc + toNat a · toNat bs`.  Proved by induction on `bs`, using the
    per-row `mpn_addmul_1` identity (`mpnAddmul1_spec_carryIn_zero`) and the fact
    that the carry-out lands on a zero limb (so no value is lost). -/
theorem mulAcc_toNat (a bs acc : List (BitVec 64))
    (hacc : acc.length = a.length + bs.length)
    (hzero : acc.drop a.length = List.replicate bs.length 0) :
    toNat (mulAcc a bs acc) = toNat acc + toNat a * toNat bs := by
  induction bs generalizing acc with
  | nil =>
    simp only [mulAcc, toNat, List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  | cons b0 bs ih =>
    have htake_len : (acc.take a.length).length = a.length := by
      rw [List.length_take]; omega
    -- Decompose `acc = take |a| ++ (w0 :: rest)`, with `w0 = 0` and
    -- `rest = replicate |bs| 0`.
    have hsplit : acc.drop a.length = (0 : BitVec 64) :: List.replicate bs.length 0 := by
      rw [hzero, List.length_cons, List.replicate_succ]
    have hacc_eq : acc = acc.take a.length ++ ((0 : BitVec 64) :: List.replicate bs.length 0) := by
      conv_lhs => rw [← List.take_append_drop a.length acc, hsplit]
    set p := mpnAddmul1 (acc.take a.length) a b0 0 with hp
    have hp1_len : p.1.length = a.length := by
      rw [hp, mpnAddmul1_length (acc.take a.length) a b0 0 (by rw [htake_len]), htake_len]
    set win := p.1 ++ [p.2] with hwin
    have hwin_len : win.length = a.length + 1 := by
      rw [hwin, List.length_append, hp1_len]; simp
    -- `toNat win = toNat (take |a|) + toNat a · b0` (mpn_addmul_1, carry-in 0).
    have hwin_toNat : toNat win = toNat (acc.take a.length) + toNat a * b0.toNat := by
      rw [hwin, toNat_append, hp1_len]
      have hspec := mpnAddmul1_spec_carryIn_zero (acc.take a.length) a (by rw [htake_len]) b0
      rw [← hp] at hspec
      simp only [toNat, hp1_len]
      omega
    -- `win` is nonempty, so `win = win.headI :: win.tail` (toNat-cons).
    have hwin_cons : win.headI :: win.tail = win := by rw [hwin]; cases p.1 <;> simp
    have hwin_split : toNat win = win.headI.toNat + 2 ^ 64 * toNat win.tail := by
      conv_lhs => rw [← hwin_cons]
      simp only [toNat]
    have hwin_tail_len : win.tail.length = a.length := by
      rw [List.length_tail, hwin_len]; omega
    -- The drop of the original accumulator past the carry limb is still zeros.
    have hdrop1 : acc.drop (a.length + 1) = List.replicate bs.length 0 := by
      rw [← List.drop_drop, hzero, List.length_cons, List.drop_replicate]
      simp
    -- The new accumulator after sliding.
    set acc' := win.tail ++ acc.drop (a.length + 1) with hacc'
    have hacc'_len : acc'.length = a.length + bs.length := by
      rw [hacc', List.length_append, hwin_tail_len, hdrop1, List.length_replicate]
    have hacc'_zero : acc'.drop a.length = List.replicate bs.length 0 := by
      rw [hacc', List.drop_left' (by rw [hwin_tail_len]), hdrop1]
    -- The drop past the carry limb is all zeros, hence denotes 0.
    have hdrop1_toNat : toNat (acc.drop (a.length + 1)) = 0 := by
      rw [hdrop1, toNat_replicate_zero]
    -- `toNat acc' = toNat win.tail` (the slid-in rest is all zeros).
    have hacc'_toNat : toNat acc' = toNat win.tail := by
      rw [hacc', toNat_append, hwin_tail_len, hdrop1_toNat, Nat.mul_zero, Nat.add_zero]
    -- `toNat acc = toNat (acc.take |a|)` (everything past the window is zero).
    have hacc_toNat : toNat acc = toNat (acc.take a.length) := by
      conv_lhs => rw [hacc_eq]
      rw [toNat_append, htake_len]
      have : toNat ((0 : BitVec 64) :: List.replicate bs.length 0) = 0 := by
        rw [← List.replicate_succ, toNat_replicate_zero]
      rw [this, Nat.mul_zero, Nat.add_zero]
    -- Assemble.
    show toNat (win.headI :: mulAcc a bs acc') = _
    simp only [toNat]
    rw [ih acc' hacc'_len hacc'_zero, hacc'_toNat]
    have h1 : win.headI.toNat + 2 ^ 64 * toNat win.tail
        = toNat (acc.take a.length) + toNat a * b0.toNat := by
      rw [← hwin_split, hwin_toNat]
    rw [hacc_toNat]
    nlinarith [h1]

/-- **The windowed accumulation on a zeroed region computes the product.**
    Starting from a zeroed `|a|+|b|`-limb result region, the in-place
    accumulation `mulAcc a b (replicate (|a|+|b|) 0)` *is* `mpnMul a b`: both
    have length `|a|+|b|` and denote `toNat a · toNat b`, so `toNat_inj` (unique
    little-endian representation) identifies them.  This is the pure
    window-equivalence that lets the assembly's sliding accumulation be matched
    to the `mpnAddN`-based reference without a structural rewrite. -/
theorem mulAcc_zero_eq_mpnMul (a b : List (BitVec 64)) :
    mulAcc a b (List.replicate (a.length + b.length) 0) = mpnMul a b := by
  set acc0 : List (BitVec 64) := List.replicate (a.length + b.length) 0 with hacc0
  have hacc0_len : acc0.length = a.length + b.length := by
    rw [hacc0, List.length_replicate]
  have hacc0_zero : acc0.drop a.length = List.replicate b.length 0 := by
    rw [hacc0, List.drop_replicate]
    congr 1; omega
  apply toNat_inj
  · -- equal lengths
    rw [mulAcc_length a b acc0 hacc0_len, mpnMul_length]
  · -- equal denotations
    rw [mulAcc_toNat a b acc0 hacc0_len hacc0_zero, hacc0, toNat_replicate_zero,
        Nat.zero_add, mpnMul_toNat]

/-! ## §5  Jasmin bridge — the nested-loop structure (Ccall composition)

`mpn_mul` is a **nested** loop: an outer loop over `b`'s limbs whose body is
a single-limb kernel (`mpn_mul_1` for the first row, `mpn_addmul_1` for the
rest).  The single-loop bridge rules (`MpnMul1JasminRefines`,
`MpnAddmul1JasminRefines`) discharge each inner kernel; what is *new* here is
the outer loop and the **sliding result window**: at outer iteration `j` the
inner kernel writes the result region `out[j .. j+|a|]`, and the window slides
one limb per `j`.

We pick the **Ccall composition** structure (`bignumExecFuel`'s `Ccall` case
with a void return inherits the callee's `mem`, so the result region
accumulates across calls).  The outer body advances a result pointer `op` by
one limb and a `b`-pointer `bp` by one limb each iteration, calling
`mpn_addmul_1(op, ap, [bp], n)`.  This section builds the structure, proves it
emits and is CT-shaped, runs it end-to-end on a concrete state (validating the
nested semantics), and states precisely the remaining refinement obligation.

### Why this is the *structure*, not yet a refinement theorem

The remaining gap (see `mpnMul_outer_loop_obligation` below) is twofold:

1. **Outer-loop / result-window frame.**  An induction over `b`'s limbs whose
   per-step rule says: one `Ccall` to `mpn_addmul_1` (discharged by
   `MpnAddmul1JasminRefines`) updates `out[j..j+|a|]`, leaving `out[0..j-1]`
   (already-finalized low limbs) untouched.  This needs a *result-region* frame
   (the addmul store window `[op+8j, op+8j+8|a|)` is disjoint from the
   finalized prefix `[op, op+8j)`), the dual of the input-region frame the
   single-loop rules already carry.

2. **Registry independence.**  `MpnAddmul1JasminRefines` is stated over
   `bignumExecFuel emptyRegistry`, but the outer Ccall runs the callee under a
   *non-empty* registry (containing `mpn_addmul_1`).  Since `bodyAddmul` has no
   `Ccall`, the registry is never consulted, so the runs agree — but that needs
   the lemma `bignumExecFuel_registry_irrel_of_noCcall` (stated below as the
   obligation `addmul_registry_irrel`), an induction over `bignumExecFuel`'s
   `Cwhile`-unfolding recursion.

Both are recorded as explicit `Prop`s at the end so the missing infrastructure
is named, not hidden.  The pure correctness above (`mpnMul_toNat`) is the
solid deliverable; this section is the (honest, partial) bridge scaffold. -/

/-! ### Carry-storing kernels (the `mpn_mul_basecase` row store)

The verified single-limb kernels `mpn_mul_1` / `mpn_addmul_1` are *void* — they
write only the `|a|` low limbs `out[0..|a|)` and leave the carry-out in register
`cy` (their ABI return value).  GMP's `mpn_mul_basecase` does
`rp[n] = mpn_mul_1(rp, up, n, vp[0])` / `rp[i+n] = mpn_addmul_1(rp+i, …)`, i.e. it
*stores* each returned carry into the high result limb.

In our `Ccall` model a void return inherits only the callee's **memory**, not its
registers (`bignumExecFuel`'s `Ccall` arm: `caller regs unchanged`), so the carry
in the callee's `cy` is dropped at the call boundary.  We therefore push the
`mpn_mul_basecase` store *into the kernel*: the carry-storing kernel runs the
verified kernel body, then — `op` having been advanced to `op_init + 8·|a|` by the
loop — emits a single `[:u64 op + 0] = cy`, writing the carry-out to `out[|a|]`.
The full `|a|+1`-limb window then survives the void return.  This is exactly the
`rp[i+n] = …` store of `mpn_mul_basecase`, realised inside the void kernel. -/

/-- `mpn_addmul_1`'s body, extended with the trailing carry store `[op] = cy`.
    After the loop, `op = op_init + 8·|a|`, so this writes the carry-out to
    `out[|a|]` — the dropped row carry the bare void kernel loses. -/
def bodyAddmulCarry : List InstrR :=
  bodyAddmul ++ [Mpn.Mul1Prototype.storeAt0 "op" "cy"]

/-- `mpn_mul_1`'s body, extended with the trailing carry store `[op] = cy`. -/
def bodyMulCarry : List InstrR :=
  Mpn.Mul1Prototype.bodyMul ++ [Mpn.Mul1Prototype.storeAt0 "op" "cy"]

/-- The carry-storing `mpn_addmul_1` FunDecl (writes `|a|+1` limbs: the
    multiply-accumulated `|a|` low limbs and the carry-out at `out[|a|]`). -/
def mpnAddmul1CarryFd : FunDecl where
  name := { name := "mpn_addmul_1" }
  params := mpnAddmul1Fd.params
  body := bodyAddmulCarry
  results := []

/-- The carry-storing `mpn_mul_1` FunDecl (writes `|a|+1` limbs). -/
def mpnMul1CarryFd : FunDecl where
  name := { name := "mpn_mul_1" }
  params := Mpn.Mul1Prototype.mpnMul1Fd.params
  body := bodyMulCarry
  results := []

/-- Registry exposing the two **carry-storing** single-limb kernels to `Ccall`.
    Each kernel writes `|a|+1` limbs (low limbs + carry-out), matching the
    `rp[i+n] = …` store of GMP's `mpn_mul_basecase`. -/
def mulRegistry : BignumRegistry := fun name =>
  if name = "mpn_addmul_1" then some mpnAddmul1CarryFd
  else if name = "mpn_mul_1" then some mpnMul1CarryFd
  else none

/-- One outer-iteration body of the GMP `mpn_mul` accumulation loop: call
    `mpn_addmul_1(op, ap, [bp+0], n)` (multiply-accumulate `a·b[j]` into the
    current result window `out[j..j+|a|]`), then slide the result pointer `op`
    and the `b`-pointer `bp` up one limb.  `ap`, `n` are fixed (`a` and `|a|`).

    The scalar argument is the *memory load* `[:u64 bp + 0]` (= `b[j]`), and
    the destination/output flows through `op` (void return, the callee writes
    `op[0..|a|]` and we advance `op` by 8). -/
def mulOuterBody : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_addmul_1" }
      [ pv "op", pv "ap", .Pload .U64 { var := vr "bp" } (.Pconst 0), pv "n" ]
  , binImm "op" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8 ]

/-- The full GMP `mpn_mul` body, Ccall-composed:
    ```
    mpn_mul_1(op, ap, [bp+0], n);   // row 0: out[0..|a|] = a · b[0]
    op  += 8;  bp += 8;             // slide to row 1
    for j in 1..m { mulOuterBody }  // each: out[j..j+|a|] += a · b[j]; slide
    ```
    `m = |b|` (held in register `m`).  The first `mpn_mul_1` initialises the
    low `|a|+1` limbs; each subsequent `mpn_addmul_1` accumulates one more row
    with its carry landing at `out[j+|a|]`.  This is exactly the schoolbook
    accumulation the pure `mpnMul` denotes. -/
def mulBody (m : Nat) : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_mul_1" }
      [ pv "op", pv "ap", .Pload .U64 { var := vr "bp" } (.Pconst 0), pv "n" ]
  , binImm "op" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , .Cfor { var := vr "j" } { dir := .UpTo, lo := 1, hi := m } mulOuterBody ]

/-- `mpn_mul(op, ap, bp, n, m)` as a Jasmin `FunDecl` (the `Cfor` upper bound
    `m = |b|` is baked in as a structural parameter, mirroring how GMP's
    `mpn_mul` takes both lengths `n, m`). -/
def mpnMulFd (m : Nat) : FunDecl where
  name := { name := "mpn_mul" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := mulBody m
  results := []

/-- The registry resolves both carry-storing kernels. -/
example : mulRegistry "mpn_addmul_1" = some mpnAddmul1CarryFd := by
  simp [mulRegistry]
example : mulRegistry "mpn_mul_1" = some mpnMul1CarryFd := by
  simp [mulRegistry]

/-! ### §5.1  Registry independence for `Ccall`-free bodies (Obligation 1)

The outer `Ccall`s in `mulBody` run their callee (`mpn_addmul_1` / `mpn_mul_1`)
*under* `mulRegistry`, but the single-loop bridges `MpnAddmul1JasminRefines` /
`MpnMul1JasminRefines` are stated over `emptyRegistry`.  Since neither callee
body contains a `Ccall`, the registry is never consulted, so the two runs
coincide.  We prove this as a fully general lemma over `bignumExecFuel`'s
recursion: for *any* body with no `Ccall`, the registry is irrelevant. -/

/-- `i.noCcall`: instruction `i` (and, recursively, every sub-body of a
    `Cif`/`Cfor`/`Cwhile`) contains no `Ccall`.  `Ccall` itself is `False`. -/
def noCcallI : InstrR → Prop
  | .Cassgn _ _ _ _ => True
  | .Copn _ _ _ _ => True
  | .Cif _ cthen celse => (∀ i ∈ cthen, noCcallI i) ∧ (∀ i ∈ celse, noCcallI i)
  | .Cfor _ _ body => ∀ i ∈ body, noCcallI i
  | .Cwhile cbefore _ cafter => (∀ i ∈ cbefore, noCcallI i) ∧ (∀ i ∈ cafter, noCcallI i)
  | .Ccall _ _ _ _ => False

/-- A body has no `Ccall` if every instruction does. -/
abbrev NoCcallBody (body : List InstrR) : Prop := ∀ i ∈ body, noCcallI i

theorem nil_noCcall : NoCcallBody [] := by intro j hj; simp at hj

theorem singleton_noCcall {i : InstrR} (hi : noCcallI i) : NoCcallBody [i] := by
  intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact hi

theorem append_noCcall {xs ys : List InstrR} (hx : NoCcallBody xs) (hy : NoCcallBody ys) :
    NoCcallBody (xs ++ ys) := by
  intro i hi
  rw [List.mem_append] at hi
  rcases hi with h | h
  · exact hx i h
  · exact hy i h

theorem mkSetVarConst_noCcall (v : VarI) (k : Nat) : noCcallI (mkSetVarConst v k) := by
  simp only [mkSetVarConst, noCcallI]

/-- The `Cfor`-unrolling preserves "no `Ccall`" (the inserted `set v := k`
    instructions are `Cassgn`). -/
theorem unrollFor_noCcall (v : VarI) (range : Range) (body : List InstrR)
    (h : NoCcallBody body) : NoCcallBody (unrollFor v range body) := by
  intro i hi
  unfold unrollFor at hi
  simp only at hi
  cases hd : range.dir <;> rw [hd] at hi <;> simp only at hi <;>
    · rw [List.mem_flatMap] at hi
      obtain ⟨k, _, hk2⟩ := hi
      rw [List.mem_cons] at hk2
      rcases hk2 with rfl | hmem
      · exact mkSetVarConst_noCcall _ _
      · exact h i hmem

/-- A straight-line instruction (`Cassgn`/`Copn`) has no `Ccall`. -/
theorem noCcall_of_straightLine {i : InstrR} (h : i.isStraightLine = true) : noCcallI i := by
  cases i <;> simp_all [InstrR.isStraightLine, noCcallI]

/-- A straight-line body has no `Ccall`. -/
theorem noCcallBody_of_straightLine {body : List InstrR}
    (h : InstrR.bodyIsStraightLine body) : NoCcallBody body := by
  induction body with
  | nil => exact nil_noCcall
  | cons i is ih =>
    obtain ⟨hi, his⟩ := h
    intro j hj
    rw [List.mem_cons] at hj
    rcases hj with rfl | hmem
    · exact noCcall_of_straightLine hi
    · exact ih his j hmem

/-- **Registry independence — fully general.**  For any `Ccall`-free body, the
    interpreter `bignumExecFuel` ignores the registry: the result under `reg`
    equals the result under `emptyRegistry`.  Proved by well-founded recursion
    mirroring `bignumExecFuel`'s `(fuel, body.length)` lex order — the only
    registry-reading arm is `Ccall`, which `NoCcallBody` rules out; the
    `Cfor`/`Cwhile` arms re-enter at strictly smaller fuel after an
    unroll/unfold that preserves `NoCcallBody`. -/
theorem bignumExecFuel_registry_irrel (reg : BignumRegistry) (fuel : Nat) :
    ∀ (body : List InstrR) (s : BignumState),
      NoCcallBody body →
      bignumExecFuel reg fuel body s = bignumExecFuel emptyRegistry fuel body s := by
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihfuel =>
    intro body
    induction body with
    | nil => intro s _; cases fuel <;> simp only [bignumExecFuel]
    | cons i is ihbody =>
      intro s h
      have hi : noCcallI i := h i (List.mem_cons_self ..)
      have his : NoCcallBody is := fun j hj => h j (List.mem_cons_of_mem _ hj)
      cases fuel with
      | zero => simp only [bignumExecFuel]
      | succ f =>
        have hfuel_lt : f < f + 1 := Nat.lt_succ_self f
        cases i with
        | Ccall _ _ _ _ => simp only [noCcallI] at hi
        | Cassgn _ _ _ _ =>
          simp only [bignumExecFuel]
          cases execInstr s _ with
          | none => rfl
          | some s' => exact ihbody s' his
        | Copn _ _ _ _ =>
          simp only [bignumExecFuel]
          cases execInstr s _ with
          | none => rfl
          | some s' => exact ihbody s' his
        | Cif cond cthen celse =>
          simp only [noCcallI] at hi
          obtain ⟨hthen, helse⟩ := hi
          simp only [bignumExecFuel]
          cases hev : evalPExpr s cond with
          | none => rfl
          | some condV =>
            simp only
            have hbranch : NoCcallBody (if condV != 0 then cthen else celse) := by
              split <;> assumption
            rw [ihfuel f hfuel_lt _ s hbranch]
            cases bignumExecFuel emptyRegistry f (if condV != 0 then cthen else celse) s with
            | none => rfl
            | some s' => exact ihbody s' his
        | Cfor v range body =>
          simp only [noCcallI] at hi
          show bignumExecFuel reg (f + 1) (.Cfor v range body :: is) s = _
          rw [bignumExecFuel, bignumExecFuel]
          exact ihfuel f hfuel_lt _ s
            (append_noCcall (unrollFor_noCcall v range body hi) his)
        | Cwhile cbefore cond cafter =>
          simp only [noCcallI] at hi
          obtain ⟨hbefore, hafter⟩ := hi
          show bignumExecFuel reg (f + 1) (.Cwhile cbefore cond cafter :: is) s = _
          rw [bignumExecFuel, bignumExecFuel]
          apply ihfuel f hfuel_lt _ s
          apply append_noCcall _ his
          apply append_noCcall hbefore
          apply singleton_noCcall
          simp only [noCcallI]
          refine ⟨append_noCcall hafter (singleton_noCcall ?_), nil_noCcall⟩
          simp only [noCcallI]; exact ⟨hbefore, hafter⟩

/-- `bodyAddmul` (and `loopBodyAddmul`) contain no `Ccall`. -/
theorem bodyAddmul_noCcall : NoCcallBody bodyAddmul := by
  intro i hi
  simp only [bodyAddmul, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simp only [noCcallI]
  · simp only [noCcallI]
    exact ⟨nil_noCcall, noCcallBody_of_straightLine loopBodyAddmul_straightLine⟩

/-- `bodyMul` (`mpn_mul_1`'s body) contains no `Ccall`. -/
theorem bodyMul_noCcall : NoCcallBody Mpn.Mul1Prototype.bodyMul := by
  intro i hi
  simp only [Mpn.Mul1Prototype.bodyMul, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simp only [noCcallI]
  · simp only [noCcallI]
    exact ⟨nil_noCcall, noCcallBody_of_straightLine Mpn.Mul1Prototype.loopBodyMul_straightLine⟩

/-! ### End-to-end execution test of the nested-Ccall structure

The strongest available evidence that the nested structure is *correct* (short
of the full refinement theorem) is to actually run it through the real
`bignumExecFuel` semantics on a concrete memory and check the result limbs
match the pure `mpnMul`.  We lay out `a` at byte address `0x1000`, `b` at
`0x4000`, the result region at `0x8000` (all disjoint), set `n=|a|`, run
`mulBody |b|` under `mulRegistry`, and read back `|a|+|b|` result limbs. -/

/-- Concrete operands for the execution test (`a = [7, 0]`, `b = [3, 5]`). -/
def testA : List (BitVec 64) := [7, 0]
def testB : List (BitVec 64) := [3, 5]

/-- Lay out a limb list little-endian at byte `base` into memory `m`. -/
def storeLimbs (m : Mem) (base : UInt64) : List (BitVec 64) → Mem
  | []      => m
  | w :: ws => storeLimbs (m.store64 base (UInt64.ofNat w.toNat)) (base + 8) ws

/-- Read `k` limbs little-endian from byte `base`. -/
def readLimbs (m : Mem) (base : UInt64) : Nat → List (BitVec 64)
  | 0     => []
  | k + 1 =>
      (BitVec.ofNat 64 ((m.load64 base).getD 0).toNat)
        :: readLimbs m (base + 8) k

/-- Initial state: `a` at `0x1000`, `b` at `0x4000`, result region zeroed at
    `0x8000`; pointers and `n` set in registers. -/
def testInit : BignumState :=
  let m0 : Mem := Mem.empty
  let m1 := storeLimbs m0 0x1000 testA
  let m2 := storeLimbs m1 0x4000 testB
  let m3 := storeLimbs m2 0x8000 (List.replicate (testA.length + testB.length) 0)
  { mem := m3
  , regs := fun x =>
      if x = "ap" then 0x1000
      else if x = "bp" then 0x4000
      else if x = "op" then 0x8000
      else if x = "n" then BitVec.ofNat 64 testA.length
      else 0 }

/-- **End-to-end: the nested-Ccall `mpn_mul` body, run through the real
    `bignumExecFuel` semantics, computes `mpnMul testA testB`.**

    This exercises the *full* nesting: the outer `Cfor`, the two `Ccall`s into
    the verified single-limb kernels (`mpn_mul_1`, `mpn_addmul_1`), each kernel's
    inner `Cwhile`, and the sliding result window — all under `mulRegistry`.
    The result region at `0x8000` ends up holding exactly the pure product. -/
example :
    (match bignumExecFuel mulRegistry 100000 (mulBody testB.length) testInit with
     | some s' => readLimbs s'.mem 0x8000 (testA.length + testB.length)
     | none => [])
    = mpnMul testA testB := by native_decide

/-- A second end-to-end check with carry across limbs: `a=[2^63,1]`, `b=[4,0]`,
    so `a·b[0]` carries the top bit of limb 0 into limb 1. -/
example :
    let a : List (BitVec 64) := [(BitVec.ofNat 64 (2 ^ 63)), 1]
    let b : List (BitVec 64) := [4, 6]
    let init : BignumState :=
      { mem := storeLimbs (storeLimbs (storeLimbs Mem.empty 0x1000 a) 0x4000 b)
                 0x8000 (List.replicate (a.length + b.length) 0)
      , regs := fun x =>
          if x = "ap" then 0x1000 else if x = "bp" then 0x4000
          else if x = "op" then 0x8000
          else if x = "n" then BitVec.ofNat 64 a.length else 0 }
    (match bignumExecFuel mulRegistry 100000 (mulBody b.length) init with
     | some s' => readLimbs s'.mem 0x8000 (a.length + b.length)
     | none => [])
    = mpnMul a b := by native_decide

/-- **Carry-crossing end-to-end check** (the case the dropped-carry bug failed):
    `a = [2^63]`, `b = [4, 0]`.  Row 0 is `mpn_mul_1([2^63], 4)`: the low limb is
    `0` and the carry-out is `2` (= `2^65 / 2^64`).  The carry-storing kernel
    writes that `2` to `out[1]`, so the result region is `[0, 2, 0]` — exactly
    `mpnMul [2^63] [4,0]`.  Before the carry store this read back `[0, 0, 0]`. -/
example :
    let a : List (BitVec 64) := [(BitVec.ofNat 64 (2 ^ 63))]
    let b : List (BitVec 64) := [4, 0]
    let init : BignumState :=
      { mem := storeLimbs (storeLimbs (storeLimbs Mem.empty 0x1000 a) 0x4000 b)
                 0x8000 (List.replicate (a.length + b.length) 0)
      , regs := fun x =>
          if x = "ap" then 0x1000 else if x = "bp" then 0x4000
          else if x = "op" then 0x8000
          else if x = "n" then BitVec.ofNat 64 a.length else 0 }
    (match bignumExecFuel mulRegistry 100000 (mulBody b.length) init with
     | some s' => readLimbs s'.mem 0x8000 (a.length + b.length)
     | none => [])
    = mpnMul a b ∧ mpnMul a b = [0, 2, 0] := by native_decide

/-! ### Op-only frame for the `mpn_addmul_1` / `mpn_mul_1` loops

`mpnAddmul1_loop` / `mpnMul1_loop` expose a frame that *conservatively* excludes
both the `op` and `ap` regions.  But the kernels only ever **store** to `op`
(`bignumExec_loopBodyAddmul_step` / `…Mul…` give `s'.mem = s.mem.store64 op …`
each iteration), so memory outside the `op`-window is preserved — including the
`ap`-region.  The outer loop needs that (`a` lives at `ap` and must survive every
row).  We prove the op-only frame by the same limb induction as
`addmul_loop_op` / `mul_loop_op`, tracking the store-window instead of the
op-advance. -/

/-- **Op-only frame for the `mpn_addmul_1` loop.**  Any 8-byte block disjoint
    from the `op`-window `[op, op+8·|as|)` is preserved by the loop run (the loop
    stores only into that window). -/
theorem addmul_loop_frame_op :
    ∀ (out as : List (BitVec 64)) (s : BignumState) (cy : BitVec 64) (extra : Nat),
      out.length = as.length →
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "op") out →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAddmul] s
              = some s' ∧
        (∀ bb, MemoryModel.Disjoint (range bb 8) (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem bb = load64Mem s.mem bb) := by
  intro out
  induction out with
  | nil =>
    intro as s cy extra hlen hcy hn _ _ _
    cases as with
    | cons _ _ => simp at hlen
    | nil =>
      have hn0 : s.regs "n" = 0 := by simpa using hn
      refine ⟨s, ?_, ?_⟩
      · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
          simp only [List.length_nil]; omega
        rw [this]
        exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodyAddmul s
          (Mpn.Mul1Prototype.evalPExpr_loopCond_false s hn0)
      · intro bb _; rfl
  | cons o os ih =>
    intro as s cy extra hlen hcy hn hop hap hdoa
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hop_head, hop_tail⟩ := hop
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
        bignumExec_loopBodyAddmul_step s o a cy hcy hap_head hop_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      have hmem1 : s1.mem = s.mem.store64 op0
          (UInt64.ofNat (addmul1Step o a (s.regs "b") cy).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
          hdoa_store_aptail hap_tail
      have hsep_op : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
        range_op_head_tail_disjoint op0 as.length (by omega)
      have hop1 : memHoldsLimbs s1.mem (regAddr s1 "op") os := by
        rw [hra_op, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (op0 + 8) op0 _ os
          (by rw [hlen']; exact hsep_op) hop_tail
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "ap") (8 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hcy1 : s1.regs "cy" = (addmul1Step o a (s.regs "b") cy).2 := hs1_cy
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_frame⟩ :=
        ih as s1 (addmul1Step o a (s.regs "b") cy).2 extra hlen' hcy1 hn1 hop1 hap1 hdoa1
      refine ⟨s', ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_loopAddmul_step emptyRegistry (2 * as.length + 2 + extra) _
          s s1 s' (Mpn.Mul1Prototype.evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- Frame: bb disjoint from the whole op-window `[op0, op0+8(|as|+1))`.
        intro bb hbb
        have hbb_tail : MemoryModel.Disjoint (range bb 8) (range (regAddr s1 "op") (8 * as.length)) := by
          rw [hra_op]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        rw [hs'_frame bb hbb_tail, hmem1]
        have hbb_head : MemoryModel.Disjoint (range bb 8) (range op0 8) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        rw [load64Mem_store64_disjoint s.mem bb op0 _ hbb_head]

/-- **Op-only frame for the `mpn_mul_1` loop.**  Mirror of `addmul_loop_frame_op`
    for the single-buffer mul kernel. -/
theorem mul_loop_frame_op :
    ∀ (as : List (BitVec 64)) (s : BignumState) (cy : BitVec 64) (extra : Nat),
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) Mpn.Mul1Prototype.loopBodyMul] s
              = some s' ∧
        (∀ bb, MemoryModel.Disjoint (range bb 8) (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem bb = load64Mem s.mem bb) := by
  intro as
  induction as with
  | nil =>
    intro s cy extra hcy hn _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ Mpn.Mul1Prototype.loopBodyMul s
        (Mpn.Mul1Prototype.evalPExpr_loopCond_false s hn0)
    · intro bb _; rfl
  | cons a as ih =>
    intro s cy extra hcy hn hap hdoa
    have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
      simpa [List.length_cons] using
        disjoint_range_lt (regAddr s "op") (regAddr s "ap")
          (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
          (by simpa using hdoa)
    have hLsucc : as.length + 1 < 2 ^ 64 := by omega
    have hn_ne : s.regs "n" ≠ 0 := by
      rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
    obtain ⟨hap_head, hap_tail⟩ := hap
    obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
      Mpn.Mul1Prototype.bignumExec_loopBodyMul_step s a cy hcy hap_head
    set op0 : UInt64 := regAddr s "op" with hop0
    have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
      simp only [regAddr, hs1_ap]; exact regAddr_advance _
    have hra_op : regAddr s1 "op" = op0 + 8 := by
      simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
    have hmem1 : s1.mem = s.mem.store64 op0
        (UInt64.ofNat (Mpn.Mul1Prototype.mul1Step a (s.regs "b") cy).1.toNat) := by
      simpa [hop0, regAddr] using hs1_mem
    have hdoa_store_aptail :
        MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
      · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
      · exact range_shift_subset (regAddr s "ap") as.length x
          (by simpa [List.length_cons] using h)
    have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
      rw [hra_ap, hmem1]
      exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
        hdoa_store_aptail hap_tail
    have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
        (range (regAddr s1 "ap") (8 * as.length)) := by
      rw [hra_op, hra_ap]
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
      · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
      · exact range_shift_subset (regAddr s "ap") as.length x
          (by simpa [List.length_cons] using h)
    have hcy1 : s1.regs "cy" = (Mpn.Mul1Prototype.mul1Step a (s.regs "b") cy).2 := hs1_cy
    have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
      rw [hs1_n, hn]
      simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
    obtain ⟨s', hs', hs'_frame⟩ :=
      ih s1 (Mpn.Mul1Prototype.mul1Step a (s.regs "b") cy).2 extra hcy1 hn1 hap1 hdoa1
    refine ⟨s', ?_, ?_⟩
    · have hfuel : 2 * (a :: as).length + 3 + extra
          = (2 * as.length + 2 + extra) + 3 := by
        simp only [List.length_cons]; ring
      rw [hfuel]
      refine bignumExecFuel_loopMul_step emptyRegistry (2 * as.length + 2 + extra) _
        s s1 s' (Mpn.Mul1Prototype.evalPExpr_loopCond_true s hn_ne) hs1 ?_
      simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
              from by omega] using hs'
    · intro bb hbb
      have hbb_tail : MemoryModel.Disjoint (range bb 8) (range (regAddr s1 "op") (8 * as.length)) := by
        rw [hra_op]
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
      rw [hs'_frame bb hbb_tail, hmem1]
      have hbb_head : MemoryModel.Disjoint (range bb 8) (range op0 8) := by
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
      rw [load64Mem_store64_disjoint s.mem bb op0 _ hbb_head]

/-! ### The remaining refinement obligation, stated precisely

Two named `Prop`s capture exactly what the full Jasmin bridge still needs.  The
end-to-end `#eval`s above show the structure is *operationally* correct; these
are the *universal* (all-input) statements that an outer-loop induction would
prove. -/

/-- **Obligation 1 — registry independence of the inner kernel — PROVED.**
    Running `mpn_addmul_1`'s body under any registry equals running it under the
    empty registry: the body has no `Ccall`, so the registry is never consulted.
    This lets the outer `Ccall` reuse `MpnAddmul1JasminRefines` (stated over
    `emptyRegistry`).  A direct instance of the general
    `bignumExecFuel_registry_irrel` (§5.1) at `bodyAddmul` (`bodyAddmul_noCcall`),
    itself proved by induction over `bignumExecFuel`'s `(fuel, body.length)`
    recursion. -/
theorem addmul_registry_irrel
    (reg : BignumRegistry) (fuel : Nat) (s : BignumState) :
    bignumExecFuel reg fuel bodyAddmul s
      = bignumExecFuel emptyRegistry fuel bodyAddmul s :=
  bignumExecFuel_registry_irrel reg fuel bodyAddmul s bodyAddmul_noCcall

/-- The carry-storing `mpn_addmul_1` body has no `Ccall` (it is `bodyAddmul`
    followed by a single straight-line store). -/
theorem bodyAddmulCarry_noCcall : NoCcallBody bodyAddmulCarry := by
  refine append_noCcall bodyAddmul_noCcall (singleton_noCcall ?_)
  simp only [Mpn.Mul1Prototype.storeAt0, noCcallI]

/-- Registry independence of the carry-storing `mpn_addmul_1` body — a direct
    instance of the general `bignumExecFuel_registry_irrel`. -/
theorem addmulCarry_registry_irrel
    (reg : BignumRegistry) (fuel : Nat) (s : BignumState) :
    bignumExecFuel reg fuel bodyAddmulCarry s
      = bignumExecFuel emptyRegistry fuel bodyAddmulCarry s :=
  bignumExecFuel_registry_irrel reg fuel bodyAddmulCarry s bodyAddmulCarry_noCcall

/-! ### §5.1.5  Final `op` of the `mpn_addmul_1` loop (carry-store address)

The carry-storing kernel writes the carry-out to `out[|a|]` via the trailing
`[:u64 op + 0] = cy`.  For that store to hit `out[|a|]` we need the `op` register
at loop exit to be `op_init + 8·|a|` — the loop advances `op` by one limb per
iteration.  This is the per-iteration `op`-advance, threaded through the limb
induction (reusing `bignumExec_loopBodyAddmul_step`'s `op += 8` and the same
op/ap-frame bookkeeping as `mpnAddmul1_loop`).  It is the *address* half of
Residual A (the value half, `cy = carry-out`, is `MpnAddmul1JasminRefines`). -/

/-- **Final `op` of the `mpn_addmul_1` `Cwhile` loop.**  After `|as|` iterations
    the `op` register has advanced by `8·|as|` limbs. -/
theorem addmul_loop_op :
    ∀ (out as : List (BitVec 64)) (s : BignumState) (cy : BitVec 64) (extra : Nat),
      out.length = as.length →
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "op") out →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAddmul] s
              = some s' ∧
        s'.regs "op" = s.regs "op" + BitVec.ofNat 64 (8 * as.length) := by
  intro out
  induction out with
  | nil =>
    intro as s cy extra hlen hcy hn _ _ _
    cases as with
    | cons _ _ => simp at hlen
    | nil =>
      have hn0 : s.regs "n" = 0 := by simpa using hn
      refine ⟨s, ?_, ?_⟩
      · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
          simp only [List.length_nil]; omega
        rw [this]
        exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBodyAddmul s
          (Mpn.Mul1Prototype.evalPExpr_loopCond_false s hn0)
      · simp [List.length_nil]
  | cons o os ih =>
    intro as s cy extra hlen hcy hn hop hap hdoa
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hop_head, hop_tail⟩ := hop
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
        bignumExec_loopBodyAddmul_step s o a cy hcy hap_head hop_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      have hmem1 : s1.mem = s.mem.store64 op0
          (UInt64.ofNat (addmul1Step o a (s.regs "b") cy).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hsep_op : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
        range_op_head_tail_disjoint op0 as.length (by omega)
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
          hdoa_store_aptail hap_tail
      have hop1 : memHoldsLimbs s1.mem (regAddr s1 "op") os := by
        rw [hra_op, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (op0 + 8) op0 _ os
          (by rw [hlen']; exact hsep_op) hop_tail
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "ap") (8 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hcy1 : s1.regs "cy" = (addmul1Step o a (s.regs "b") cy).2 := hs1_cy
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_op⟩ :=
        ih as s1 (addmul1Step o a (s.regs "b") cy).2 extra hlen' hcy1 hn1 hop1 hap1 hdoa1
      refine ⟨s', ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_loopAddmul_step emptyRegistry (2 * as.length + 2 + extra) _
          s s1 s' (Mpn.Mul1Prototype.evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · rw [hs'_op, hs1_op]
        have hl : 8 * (a :: as).length = 8 * as.length + 8 := by
          simp only [List.length_cons]; ring
        rw [hl, BitVec.ofNat_add, show (BitVec.ofNat 64 8 : BitVec 64) = 8 from rfl]
        rw [BitVec.add_comm (BitVec.ofNat 64 (8 * as.length)) 8, ← BitVec.add_assoc]

/-! ### §5.2  The single `mpn_addmul_1`-`Ccall` discharge (nested-loop core)

The new ingredient for the nested loop: one outer-iteration `Ccall` to
`mpn_addmul_1(op, ap, [bp+0], n)` runs the verified inner kernel through
`bignumExecFuel`'s `Ccall` case and inherits its memory.  We reduce it to
`MpnAddmul1JasminRefines` (stated over `emptyRegistry`) using
`addmul_registry_irrel` (Obligation 1), after the parameter-binding bookkeeping
(`addmul_args_eval` + `addmul_callee_regs`).  This is the reusable per-row step
of the outer accumulation loop. -/

/-- The registry resolves `mpn_addmul_1` to the carry-storing kernel. -/
theorem mulRegistry_addmul : mulRegistry "mpn_addmul_1" = some mpnAddmul1CarryFd := by
  simp [mulRegistry]

/-- The four `Ccall` arguments `[op, ap, [bp+0], n]` evaluate to the register
    values plus the scalar `b[j]` loaded from `bp`. -/
theorem addmul_args_eval (s : BignumState) (bj : BitVec 64)
    (hbj : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat bj.toNat)) :
    [pv "op", pv "ap", PExpr.Pload .U64 { var := vr "bp" } (.Pconst 0), pv "n"].mapM (evalPExpr s)
      = some [s.regs "op", s.regs "ap", bj, s.regs "n"] := by
  have hload : evalPExpr s (.Pload .U64 { var := vr "bp" } (.Pconst 0)) = some bj := by
    simp only [evalPExpr]
    rw [CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype.resolveAddr_reg]
    simp only [hbj, bind, Option.bind, bv_uint_roundtrip]
  have hop : evalPExpr s (pv "op") = some (s.regs "op") := by simp [evalPExpr, pv, vr]
  have hap : evalPExpr s (pv "ap") = some (s.regs "ap") := by simp [evalPExpr, pv, vr]
  have hn : evalPExpr s (pv "n") = some (s.regs "n") := by simp [evalPExpr, pv, vr]
  rw [List.mapM_cons, hop, List.mapM_cons, hap, List.mapM_cons, hload, List.mapM_cons, hn,
      List.mapM_nil]
  rfl

/-- The callee's initial register file, built by `bignumExecFuel`'s `Ccall` case
    from `mpnAddmul1Fd.params = [op, ap, b, n]` and the argument vector, equals
    the explicit binding `op ↦ vop, ap ↦ vap, b ↦ vb, n ↦ vn`. -/
theorem addmul_callee_regs (vop vap vb vn : BitVec 64) :
    (fun name => match mpnAddmul1Fd.params.findIdx? (·.var.var.vname = name) with
                  | some idx => (([vop, vap, vb, vn] : List (BitVec 64))[idx]?).getD 0
                  | none => 0)
    = (fun name => if name = "op" then vop else if name = "ap" then vap
                   else if name = "b" then vb else if name = "n" then vn else 0) := by
  funext name
  simp only [mpnAddmul1Fd, vr, List.findIdx?, List.findIdx?.go]
  by_cases h0 : name = "op"
  · subst h0; simp
  · by_cases h1 : name = "ap"
    · subst h1; simp
    · by_cases h2 : name = "b"
      · subst h2; simp
      · by_cases h3 : name = "n"
        · subst h3; simp
        · simp only [eq_comm (a := name)] at *; simp [h0, h1, h2, h3]

/-- **Cross-call discharge of the `mpn_addmul_1` *body* (the low `|a|` limbs) —
    PROVED.**  Running the bare void kernel body `mpnAddmul1Fd.body` (= the
    `cy := 0; while …` *without* the trailing carry store) inside
    `bignumExecFuel`'s `Ccall` case (under `mulRegistry`, at fuel `f`) terminates
    with a memory whose `op`-window holds the multiply-accumulated low limbs
    `(mpnAddmul1 out a b[j] 0).1`.  The carry-storing kernel
    (`mpnAddmul1CarryFd`) runs *exactly this body* and then stores the carry-out
    `cy` to `out[|a|]`; this lemma discharges the body part.

    It composes the *verified* inner kernel (`MpnAddmul1JasminRefines`) through
    the cross-function call boundary, moving from the call-site registry
    `mulRegistry` to the kernel's `emptyRegistry` statement via
    `addmul_registry_irrel` (Obligation 1). -/
theorem addmul_ccall_step (f : Nat) (s : BignumState) (bj : BitVec 64)
    (out a : List (BitVec 64))
    (hlen : out.length = a.length)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (hout : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hf : f > 2 * a.length + 2) :
    ∃ cf, bignumExecFuel mulRegistry f mpnAddmul1Fd.body
        { regs := fun name => match mpnAddmul1Fd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) (mpnAddmul1 out a bj 0).1 := by
  -- The Ccall-built callee register file (raw `findIdx?` form) is the explicit binding.
  rw [addmul_callee_regs (s.regs "op") (s.regs "ap") bj (s.regs "n")]
  set ci : BignumState :=
    { regs := fun name => if name = "op" then s.regs "op"
                          else if name = "ap" then s.regs "ap"
                          else if name = "b" then bj
                          else if name = "n" then s.regs "n" else 0
    , mem := s.mem } with hci
  have hci_n : ci.regs "n" = BitVec.ofNat 64 a.length := by rw [hci]; simp; exact hn
  have hci_b : ci.regs "b" = bj := by rw [hci]; simp
  have hci_op : ci.regs "op" = s.regs "op" := by rw [hci]; simp
  have hci_ap : ci.regs "ap" = s.regs "ap" := by rw [hci]; simp
  have hci_mem : ci.mem = s.mem := by rw [hci]
  have hci_out : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "op").toNat) out := by
    rw [hci_mem, hci_op]; exact hout
  have hci_a : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) a := by
    rw [hci_mem, hci_ap]; exact ha
  have hci_doa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * a.length)) := by
    rw [hci_op, hci_ap]; exact hdoa
  obtain ⟨cf, hcf, hcf_mem, _⟩ :=
    MpnAddmul1JasminRefines ci out a f hlen hci_n hci_out hci_a hci_doa hf
  refine ⟨cf, ?_, ?_⟩
  · rw [show mpnAddmul1Fd.body = bodyAddmul from rfl, addmul_registry_irrel mulRegistry f ci]
    exact hcf
  · rw [hci_b, hci_op] at hcf_mem
    exact hcf_mem

/-- Peel the two straight-line pointer bumps `op += 8; bp += 8` off the front of
    a body at the *same* fuel (they flow through `bignumExecFuel`'s catch-all
    arm, which does not decrement fuel): the run on `[bumps] ++ rest` from `s1`
    equals the run on `rest` from the post-bump state. -/
theorem bumps_peel (f : Nat) (rest : List InstrR) (s1 : BignumState) :
    bignumExecFuel mulRegistry (f + 1)
        ([binImm "op" (.Oadd .U64) 8, binImm "bp" (.Oadd .U64) 8] ++ rest) s1
      = bignumExecFuel mulRegistry (f + 1) rest
          (setReg (setReg s1 "op" (s1.regs "op" + 8)) "bp" (s1.regs "bp" + 8)) := by
  simp only [List.cons_append, List.nil_append, bignumExecFuel, execInstr, binImm, evalPExpr, pv,
    vr, setReg, bind, Option.bind,
    show (BitVec.ofInt 64 8 : BitVec 64) = 8 from rfl,
    show ("bp" = "op") = False from by simp, if_false]

/-- The `Ccall mpn_addmul_1` reduction: discharged through `bignumExecFuel`'s
    `Ccall` case, running `mulOuterBody ++ rest` from `s` equals running
    `[op += 8; bp += 8] ++ rest` from the callee's post-state `{regs := s.regs,
    mem := cf.mem}` (the void return inherits the callee memory).  `cf` is the
    callee final state supplied by `addmul_ccall_step`. -/
theorem outer_ccall_reduce (f : Nat) (rest : List InstrR) (s : BignumState) (bj : BitVec 64)
    (cf : BignumState)
    (hbj : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat bj.toNat))
    (hcf : bignumExecFuel mulRegistry f mpnAddmul1CarryFd.body
        { regs := fun name => match mpnAddmul1CarryFd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf) :
    bignumExecFuel mulRegistry (f + 1) (mulOuterBody ++ rest) s
      = bignumExecFuel mulRegistry (f + 1)
          ([binImm "op" (.Oadd .U64) 8, binImm "bp" (.Oadd .U64) 8] ++ rest)
          { regs := s.regs, mem := cf.mem } := by
  rw [mulOuterBody, List.cons_append, bignumExecFuel, mulRegistry_addmul,
      addmul_args_eval s bj hbj]
  simp only [List.isEmpty_nil, if_true]
  -- `split` case-splits the callee-run `match`; `hcf` rules out `none`, the
  -- `some` branch matches the RHS (robust against `rw`'s match-motive restriction).
  split
  · -- none branch: `hrun` and `hcf` share the LHS, so `some cf = none` — absurd.
    rename_i hrun; exact absurd (hcf.symm.trans hrun) (by simp)
  · -- some branch: `cf' = cf` by injectivity on the shared LHS; both sides agree.
    rename_i cf' hrun
    have : cf' = cf := Option.some.inj (hrun.symm.trans hcf)
    rw [this]

/-- **One full outer-iteration body `mulOuterBody`, given the carry-kernel run —
    PROVED (pure plumbing).**  Parameterised by the carry-storing-kernel callee
    final state `cf` (whose `op`-window holds the full `|a|+1`-limb row
    `row = (mpnAddmul1 out a b[j] 0).1 ++ [(mpnAddmul1 out a b[j] 0).2]`), running
    `mulOuterBody ++ rest` (the `mpn_addmul_1` `Ccall` to `mpnAddmul1CarryFd`,
    followed by the pointer advances `op += 8; bp += 8`) equals continuing on
    `rest` from a state `s'` whose `op`-window holds `row`, with `op` and `bp`
    advanced one limb and all other registers untouched.

    This composes the cross-call reduction (`outer_ccall_reduce`) with the
    straight-line pointer bumps (`bumps_peel`).  Its *only* input is the
    carry-kernel callee run `hcf` + window `hcf_row` — that is exactly the
    per-row carry-window step factored into `mpnMul_per_row_carry_obligation`
    below (the part blocked on a forward control-flow append-join /
    fuel-monotonicity lemma absent from `BignumExec`). -/
theorem mulOuterBody_step (f : Nat) (rest : List InstrR) (s : BignumState) (bj : BitVec 64)
    (row : List (BitVec 64)) (cf : BignumState)
    (hbj : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat bj.toNat))
    (hcf : bignumExecFuel mulRegistry f mpnAddmul1CarryFd.body
        { regs := fun name => match mpnAddmul1CarryFd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf)
    (hcf_row : memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) row) :
    ∃ s',
      bignumExecFuel mulRegistry (f + 1) (mulOuterBody ++ rest) s
        = bignumExecFuel mulRegistry (f + 1) rest s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) row ∧
      s'.regs "op" = s.regs "op" + 8 ∧ s'.regs "bp" = s.regs "bp" + 8 ∧
      (∀ x, x ≠ "op" → x ≠ "bp" → s'.regs x = s.regs x) ∧
      s'.mem = cf.mem := by
  -- The callee's post-state (void return inherits `cf.mem`).
  set s1 : BignumState := { regs := s.regs, mem := cf.mem } with hs1
  -- The post-bump state.
  refine ⟨setReg (setReg s1 "op" (s1.regs "op" + 8)) "bp" (s1.regs "bp" + 8), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- run equality: Ccall reduction then bump-peel.
    rw [outer_ccall_reduce f rest s bj cf hbj hcf, ← hs1, bumps_peel f rest s1]
  · -- `op`-window memory: `cf.mem` (= `s1.mem`) unchanged by register-only bumps.
    rw [show (setReg (setReg s1 "op" (s1.regs "op" + 8)) "bp" (s1.regs "bp" + 8)).mem = cf.mem
          from rfl]
    exact hcf_row
  · -- `op` advanced (the `bp` bump leaves `op` alone).
    simp only [setReg, hs1, show ("op" = "bp") = False from by simp, if_false, if_true]
  · -- `bp` advanced.
    simp only [setReg, hs1, if_true]
  · -- frame: other registers untouched by the two bumps.
    intro x hop hbp
    simp only [setReg, hs1, if_neg hbp, if_neg hop]
  · -- memory: the register-only bumps preserve `cf.mem`.
    rfl

/-! ### §5.3  The carry-drop bug, fixed; the per-row residual, now closed

The dropped-carry bug recorded in the previous revision of this file (the
emitted body advanced `op`/`bp` after each kernel call but never stored the
kernel's carry-out into the high result limb `out[j+|a|]`) is **fixed**: the
`Ccall`s in `mulOuterBody`/`mulBody` now target the *carry-storing* kernels
`mpnAddmul1CarryFd` / `mpnMul1CarryFd`, whose bodies run the verified kernel and
then emit the trailing `[:u64 op + 0] = cy` store at `op = op_init + 8·|a|`,
landing the carry-out at `out[|a|]` — exactly the `rp[i+n] = …` store of GMP's
`mpn_mul_basecase`.  The positive end-to-end checks above (in particular the
carry-crossing `[2^63]·[4,0] = [0,2,0]`) confirm the fix operationally: the
result region now holds `mpnMul a b` rather than dropping the row carry.

The **per-row carry-window step** (Residual A) — the interpreter obligation that
broke the two prior attempts — is now a closed theorem (`mpnMul_per_row_carry`,
§5.3a): one `Ccall` to the carry-storing kernel writes the full `|a|+1`-limb row.
The enabling ingredient was a pair of fuel-monotonicity sequencing lemmas
(`bignumExecFuel_mono` / `bignumExecFuel_seq`) added to `BignumExec`, which let
the trailing carry store be sequenced after the addmul `Cwhile` (the continuation
runs at a different fuel than the loop body; the join aligns them).

What remains for the *universal* closed refinement theorem (Residual B,
`mpnMul_outer_loop_obligation`) is the outer-loop interpreter induction wiring
Residual A, the result-window frame, and the pure uniqueness lemma `toNat_inj`
together; it is recorded as a sorry-free `Prop`. -/

/-! ### §5.3a  Memory algebra for the carry-window: `memHoldsLimbs` snoc + the
    head/tail disjointness with the carry limb at the *end* of the window. -/

/-- General pointer-advance: adding `w` (`BitVec`) to a pointer register advances
    its resolved `UInt64` address by `UInt64.ofNat w.toNat` (both reductions mod
    `2^64` agree).  Generalises `regAddr_advance` (the `w = 8` case). -/
theorem regAddr_add (bv w : BitVec 64) :
    UInt64.ofNat (bv + w).toNat = UInt64.ofNat bv.toNat + UInt64.ofNat w.toNat := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add, BitVec.toNat_add]
  omega

/-- **`memHoldsLimbs` snoc.**  If the low limbs `low` sit at `base` and the word
    `w` sits one limb past them (at `base + 8·|low|`), then the window
    `low ++ [w]` is held at `base`.  Proved by induction on `low`, re-associating
    the per-limb base offset `(base + 8) + 8·|low'|  =  base + 8·(|low'|+1)`. -/
theorem memHoldsLimbs_snoc (m : Mem) (base : UInt64) (low : List (BitVec 64))
    (w : BitVec 64)
    (hlow : memHoldsLimbs m base low)
    (hw : load64Mem m (base + UInt64.ofNat (8 * low.length)) = some (UInt64.ofNat w.toNat)) :
    memHoldsLimbs m base (low ++ [w]) := by
  induction low generalizing base with
  | nil =>
    refine ⟨?_, True.intro⟩
    simpa using hw
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := hlow
    refine ⟨hhead, ?_⟩
    apply ih (base + 8) htail
    rw [show base + 8 + UInt64.ofNat (8 * xs.length)
          = base + UInt64.ofNat (8 * (xs.length + 1)) from by
        rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length from by ring,
            UInt64.ofNat_add, show (UInt64.ofNat 8 : UInt64) = 8 from rfl]; ac_rfl]
    simpa [List.length_cons] using hw

/-- **Asymmetric range-length bound.**  If `range op m1` is disjoint from a
    *nonempty* range `range ap m2` (`0 < m2`), then `m1 < 2^64`: a width
    `m1 ≥ 2^64` would make `range op m1` cover the whole address space (hence
    contain `ap`), contradicting disjointness with the nonempty second range. -/
theorem disjoint_range_lt_left (op ap : UInt64) (m1 m2 : Nat) (hm2 : 0 < m2)
    (h : MemoryModel.Disjoint (MemoryModel.range op m1) (MemoryModel.range ap m2)) :
    m1 < 2 ^ 64 := by
  by_contra hge
  rw [Nat.not_lt] at hge
  refine h ap ⟨⟨(ap - op).toNat, by have := (ap - op).toNat_lt; omega, ?_⟩,
    ⟨0, by omega, by simp⟩⟩
  rw [UInt64.ofNat_toNat]; bv_decide

/-- **Carry-limb head/tail disjointness.**  The carry-store block
    `[base + 8·k, base + 8·k + 8)` (the high limb at index `k`) is disjoint from
    the low-limb region `[base, base + 8·k)`, provided the whole `k+1`-limb window
    fits in the address space (`8·(k+1) ≤ 2^64`). -/
theorem range_tail_head_disjoint (base : UInt64) (k : Nat)
    (hbound : 8 * (k + 1) ≤ 2 ^ 64) :
    MemoryModel.Disjoint
      (MemoryModel.range (base + UInt64.ofNat (8 * k)) 8)
      (MemoryModel.range base (8 * k)) := by
  intro a ⟨⟨i, hi, hai⟩, ⟨j, hj, haj⟩⟩
  -- a = (base + ofNat (8k)) + ofNat i = base + ofNat (8k + i),  i < 8
  -- a = base + ofNat j,  j < 8k
  rw [show base + UInt64.ofNat (8 * k) + UInt64.ofNat i
        = base + UInt64.ofNat (8 * k + i) from by
      rw [UInt64.ofNat_add]; ac_rfl] at hai
  rw [haj] at hai
  have hcancel := uint64_add_left_cancel base _ _ hai
  have h2 := congrArg UInt64.toNat hcancel
  simp only [UInt64.toNat_ofNat'] at h2
  omega

/-- **Residual A — the per-row carry-window step — PROVED.**  Running the
    carry-storing kernel body `mpnAddmul1CarryFd.body`
    (= `bodyAddmul ++ [storeAt0 "op" "cy"]`) from the callee init state writes the
    *full* `|a|+1`-limb row `(mpnAddmul1 out a b[j] 0).1 ++ [(mpnAddmul1 out a b[j]
    0).2]` to the `op`-window: the verified void kernel (`MpnAddmul1JasminRefines`)
    fills the low `|a|` limbs and leaves the carry-out in `cy`, the loop advances
    `op` to `op_init + 8·|a|` (`addmul_loop_op`), and the trailing
    `storeAt0 "op" "cy"` lands that carry-out at `out[|a|]`.

    The store is sequenced after the loop's `Cwhile` via the new
    `bignumExecFuel_seq` (no control-flow restriction; the continuation's fuel is
    aligned to the loop's by `bignumExecFuel_mono`), and the registry is bridged
    `mulRegistry → emptyRegistry` by `addmulCarry_registry_irrel`.  The low limbs
    survive the high store by the result-window frame (`range_tail_head_disjoint`
    + `memHoldsLimbs_store64_frame`); the carry lands by `load64Mem_store64_same`;
    the window is reassembled by `memHoldsLimbs_snoc`. -/
theorem mpnMul_per_row_carry
    (f : Nat) (s : BignumState) (bj : BitVec 64) (out a : List (BitVec 64))
    (hlen : out.length = a.length)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (hout : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hf : f > 2 * a.length + 3) :
    ∃ cf, bignumExecFuel mulRegistry f mpnAddmul1CarryFd.body
        { regs := fun name => match mpnAddmul1CarryFd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat)
        ((mpnAddmul1 out a bj 0).1 ++ [(mpnAddmul1 out a bj 0).2]) := by
  -- mpnAddmul1CarryFd.params = mpnAddmul1Fd.params; identify the callee reg file.
  rw [show mpnAddmul1CarryFd.params = mpnAddmul1Fd.params from rfl,
      addmul_callee_regs (s.regs "op") (s.regs "ap") bj (s.regs "n")]
  -- The callee init state (after the parameter binding).
  set ci : BignumState :=
    { regs := fun name => if name = "op" then s.regs "op"
                          else if name = "ap" then s.regs "ap"
                          else if name = "b" then bj
                          else if name = "n" then s.regs "n" else 0
    , mem := s.mem } with hci
  have hci_n : ci.regs "n" = BitVec.ofNat 64 a.length := by rw [hci]; simp; exact hn
  have hci_b : ci.regs "b" = bj := by rw [hci]; simp
  have hci_op : ci.regs "op" = s.regs "op" := by rw [hci]; simp
  have hci_ap : ci.regs "ap" = s.regs "ap" := by rw [hci]; simp
  have hci_mem : ci.mem = s.mem := by rw [hci]
  have hci_out : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "op").toNat) out := by
    rw [hci_mem, hci_op]; exact hout
  have hci_a : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) a := by
    rw [hci_mem, hci_ap]; exact ha
  -- Window bound: 8·(|a|+1) < 2^64.  The full op-window is disjoint from the
  -- ap-window (`hdoa`); when `|a| > 0` the ap-window is nonempty, so the
  -- asymmetric length bound applies.  When `|a| = 0` the window is one limb.
  have hsize : 8 * (a.length + 1) ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos a.length with h0 | hpos
    · rw [h0]; norm_num
    · exact le_of_lt (disjoint_range_lt_left (UInt64.ofNat (s.regs "op").toNat)
        (UInt64.ofNat (s.regs "ap").toNat) (8 * (a.length + 1)) (8 * a.length)
        (by omega) hdoa)
  -- Disjointness on the low window (width `8·|a|`), needed by the kernel bridge.
  have hdoa_low : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * a.length)) := by
    rw [hci_op, hci_ap]
    refine disjoint_mono (fun x h => ?_) (fun x h => h) hdoa
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by omega, rfl⟩
  -- Run the verified void kernel body `bodyAddmul` on `ci` at fuel `f - 1`,
  -- reserving the last unit of fuel for the trailing carry store.
  set f1 : Nat := f - 1 with hf1
  have hf1_gt : f1 > 2 * a.length + 2 := by rw [hf1]; omega
  obtain ⟨extra, hextra⟩ : ∃ extra, f1 = 2 * a.length + 3 + extra :=
    ⟨f1 - (2 * a.length + 3), by omega⟩
  obtain ⟨s1, hs1, hs1_mem, hs1_cy⟩ :=
    MpnAddmul1JasminRefines ci out a f1 hlen hci_n hci_out hci_a hdoa_low hf1_gt
  rw [hci_b] at hs1_mem
  -- The cy-initialised state (`bodyAddmul = [cy := 0; Cwhile ...]`).
  set ci0 : BignumState := setReg ci "cy" 0 with hci0
  have hexec0 : execInstr ci
      (.Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64) (.Pconst 0))
      = some ci0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hci0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  -- The loop run, isolated from `bodyAddmul`'s leading `cy := 0`.
  have hloop : bignumExecFuel emptyRegistry f1
      [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAddmul] ci0 = some s1 := by
    obtain ⟨F, hF⟩ : ∃ F, f1 = F + 1 := ⟨f1 - 1, by omega⟩
    have : bignumExecFuel emptyRegistry (F + 1) bodyAddmul ci
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAddmul] ci0 := by
      conv_lhs => rw [bodyAddmul]
      simp only [bignumExecFuel, hexec0]
    rw [hF] at hs1 ⊢
    rw [← this]; exact hs1
  -- The op-advance: `addmul_loop_op` on `ci0`, identified with `s1` by determinism.
  have hci0_cy : ci0.regs "cy" = 0 := by rw [hci0]; simp [setReg]
  have hci0_n : ci0.regs "n" = BitVec.ofNat 64 a.length := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]; exact hci_n
  have hci0_op_reg : regAddr ci0 "op" = UInt64.ofNat (ci.regs "op").toNat := by
    rw [hci0]; simp only [regAddr, setReg]; rw [if_neg (by decide)]
  have hci0_ap_reg : regAddr ci0 "ap" = UInt64.ofNat (ci.regs "ap").toNat := by
    rw [hci0]; simp only [regAddr, setReg]; rw [if_neg (by decide)]
  have hci0_out : memHoldsLimbs ci0.mem (regAddr ci0 "op") out := by
    rw [show ci0.mem = ci.mem from rfl, hci0_op_reg]; exact hci_out
  have hci0_a : memHoldsLimbs ci0.mem (regAddr ci0 "ap") a := by
    rw [show ci0.mem = ci.mem from rfl, hci0_ap_reg]; exact hci_a
  have hci0_doa : MemoryModel.Disjoint (range (regAddr ci0 "op") (8 * a.length))
      (range (regAddr ci0 "ap") (8 * a.length)) := by
    rw [hci0_op_reg, hci0_ap_reg]; exact hdoa_low
  obtain ⟨s1', hs1', hs1'_op⟩ :=
    addmul_loop_op out a ci0 0 extra hlen hci0_cy hci0_n hci0_out hci0_a hci0_doa
  -- Determinism: same fuel, same body, same start state ⇒ `s1' = s1`.
  rw [show 2 * a.length + 3 + extra = f1 from by omega] at hs1'
  have hs1'_eq : s1' = s1 := Option.some.inj (hs1'.symm.trans hloop)
  rw [hs1'_eq] at hs1'_op
  -- So `s1.regs "op" = ci0.regs "op" + ofNat (8·|a|)`, hence its address is the
  -- carry-store address `op_init + 8·|a|`.
  have hci0_op_bv : ci0.regs "op" = ci.regs "op" := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]
  have hs1_op_reg : regAddr s1 "op"
      = UInt64.ofNat (ci.regs "op").toNat + UInt64.ofNat (8 * a.length) := by
    rw [regAddr, hs1'_op, hci0_op_bv, regAddr_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * a.length < 2 ^ 64)]
  -- Run the trailing carry store `[storeAt0 "op" "cy"]` from `s1`.
  set s2 : BignumState :=
    storeMem s1 (regAddr s1 "op") (UInt64.ofNat (s1.regs "cy").toNat) with hs2
  have hstep : execInstr s1 (Mpn.Mul1Prototype.storeAt0 "op" "cy") = some s2 := by
    rw [Mpn.Mul1Prototype.storeAt0]
    simp only [execInstr, evalPExpr, resolveAddr, vr, bind, Option.bind,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl,
      show s1.regs "op" + 0 = s1.regs "op" from by bv_decide, regAddr, hs2]
  have hstore : bignumExecFuel emptyRegistry 1
      [Mpn.Mul1Prototype.storeAt0 "op" "cy"] s1 = some s2 := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine emptyRegistry 0
        [Mpn.Mul1Prototype.storeAt0 "op" "cy"] s1
        ⟨by simp [Mpn.Mul1Prototype.storeAt0, InstrR.isStraightLine], True.intro⟩]
    simp only [bignumExec, hstep]
  -- Sequence loop + store via `bignumExecFuel_seq` (fuel `f1 + 1 = f`).
  have hseq : bignumExecFuel emptyRegistry f bodyAddmulCarry ci = some s2 := by
    rw [show f = f1 + 1 from by omega, bodyAddmulCarry]
    exact bignumExecFuel_seq emptyRegistry f1 1 bodyAddmul
      [Mpn.Mul1Prototype.storeAt0 "op" "cy"] ci s1 s2 hs1 hstore
  -- Bridge the registry `mulRegistry → emptyRegistry`; `mpnAddmul1CarryFd.body
  -- = bodyAddmulCarry` has no `Ccall`.
  refine ⟨s2, ?_, ?_⟩
  · rw [show mpnAddmul1CarryFd.body = bodyAddmulCarry from rfl,
        addmulCarry_registry_irrel mulRegistry f ci]
    exact hseq
  · -- The op-window holds the full row `low ++ [carry]`.
    -- Base = op_init address (= `ci.regs "op"` address, via `hci_op`).
    rw [← hci_op]
    -- Length of the low limbs = |a| = |out|.
    have hlow_len : (mpnAddmul1 out a bj 0).1.length = a.length := by
      rw [mpnAddmul1_length out a bj 0 hlen, hlen]
    -- `s2.mem = s1.mem.store64 (regAddr s1 "op") (ofNat (s1.cy).toNat)`.
    have hs2_mem : s2.mem = s1.mem.store64 (regAddr s1 "op")
        (UInt64.ofNat (s1.regs "cy").toNat) := by rw [hs2]; rfl
    -- The stored carry value = `(mpnAddmul1 out a bj 0).2`.
    have hcy_val : s1.regs "cy" = (mpnAddmul1 out a bj 0).2 := by
      rw [hs1_cy, hci_b]
    -- The carry-store block, by `hs1_op_reg`.
    set base : UInt64 := UInt64.ofNat (ci.regs "op").toNat with hbase
    have hstore_addr : regAddr s1 "op" = base + UInt64.ofNat (8 * a.length) := by
      rw [hs1_op_reg, hbase]
    -- Low limbs survive the high carry store (store block disjoint from low region).
    have hlow_survive : memHoldsLimbs s2.mem base (mpnAddmul1 out a bj 0).1 := by
      rw [hs2_mem, hstore_addr]
      refine memHoldsLimbs_store64_frame s1.mem base
        (base + UInt64.ofNat (8 * a.length)) _ (mpnAddmul1 out a bj 0).1 ?_ hs1_mem
      rw [hlow_len]
      exact range_tail_head_disjoint base a.length hsize
    -- The carry lands at `base + 8·|a| = base + 8·|low|` by read-back.
    have hcarry_at : load64Mem s2.mem (base + UInt64.ofNat (8 * (mpnAddmul1 out a bj 0).1.length))
        = some (UInt64.ofNat (mpnAddmul1 out a bj 0).2.toNat) := by
      rw [hlow_len, hs2_mem, hstore_addr, hcy_val,
          load64Mem_store64_same s1.mem (base + UInt64.ofNat (8 * a.length))]
    -- Reassemble the window `low ++ [carry]` via `memHoldsLimbs_snoc`.
    exact memHoldsLimbs_snoc s2.mem base (mpnAddmul1 out a bj 0).1
      (mpnAddmul1 out a bj 0).2 hlow_survive hcarry_at

/-- **Residual A — the per-row carry-window step.**  One `Ccall` to the
    carry-storing kernel `mpnAddmul1CarryFd` writes the *full* `|a|+1`-limb row
    `(mpnAddmul1 out a b[j] 0).1 ++ [(mpnAddmul1 out a b[j] 0).2]` to the
    `op`-window (the multiply-accumulated low limbs **plus** the stored carry-out).

    Discharged in full by `mpnMul_per_row_carry`. -/
def mpnMul_per_row_carry_obligation : Prop :=
  ∀ (f : Nat) (s : BignumState) (bj : BitVec 64) (out a : List (BitVec 64)),
    out.length = a.length →
    s.regs "n" = BitVec.ofNat 64 a.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    f > 2 * a.length + 3 →
    ∃ cf, bignumExecFuel mulRegistry f mpnAddmul1CarryFd.body
        { regs := fun name => match mpnAddmul1CarryFd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat)
        ((mpnAddmul1 out a bj 0).1 ++ [(mpnAddmul1 out a bj 0).2])

/-- Residual A holds — `mpnMul_per_row_carry` discharges
    `mpnMul_per_row_carry_obligation` in full. -/
theorem mpnMul_per_row_carry_obligation_holds : mpnMul_per_row_carry_obligation :=
  fun f s bj out a hlen hn hout ha hdoa hf =>
    mpnMul_per_row_carry f s bj out a hlen hn hout ha hdoa hf

/-! ### §5.3b  Row 0 — the `mpn_mul_1` carry-storing kernel

Row 0 of the schoolbook accumulation runs `mpn_mul_1` (not `mpn_addmul_1`): the
result window is initially zero, so `a · b[0]` is *written*, not accumulated.
The carry-storing kernel `mpnMul1CarryFd` runs the verified `mpn_mul_1` body
(`bodyMul`) and then stores the carry-out at `out[|a|]`.  We mirror
`mpnMul_per_row_carry` exactly: a `mul`-flavoured op-advance lemma, then the
full `|a|+1`-limb row step. -/

/-- **Final `op` of the `mpn_mul_1` `Cwhile` loop.**  After `|as|` iterations
    the `op` register has advanced by `8·|as|` limbs.  Mirror of
    `addmul_loop_op`, single-buffer (`mpn_mul_1` reads only `ap`). -/
theorem mul_loop_op :
    ∀ (as : List (BitVec 64)) (s : BignumState) (cy : BitVec 64) (extra : Nat),
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) Mpn.Mul1Prototype.loopBodyMul] s
              = some s' ∧
        s'.regs "op" = s.regs "op" + BitVec.ofNat 64 (8 * as.length) := by
  intro as
  induction as with
  | nil =>
    intro s cy extra hcy hn _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ Mpn.Mul1Prototype.loopBodyMul s
        (Mpn.Mul1Prototype.evalPExpr_loopCond_false s hn0)
    · simp [List.length_nil]
  | cons a as ih =>
    intro s cy extra hcy hn hap hdoa
    have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
      simpa [List.length_cons] using
        disjoint_range_lt (regAddr s "op") (regAddr s "ap")
          (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
          (by simpa using hdoa)
    have hLsucc : as.length + 1 < 2 ^ 64 := by omega
    have hn_ne : s.regs "n" ≠ 0 := by
      rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
    obtain ⟨hap_head, hap_tail⟩ := hap
    obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
      Mpn.Mul1Prototype.bignumExec_loopBodyMul_step s a cy hcy hap_head
    set op0 : UInt64 := regAddr s "op" with hop0
    have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
      simp only [regAddr, hs1_ap]; exact regAddr_advance _
    have hra_op : regAddr s1 "op" = op0 + 8 := by
      simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
    have hmem1 : s1.mem = s.mem.store64 op0
        (UInt64.ofNat (Mpn.Mul1Prototype.mul1Step a (s.regs "b") cy).1.toNat) := by
      simpa [hop0, regAddr] using hs1_mem
    have hdoa_store_aptail :
        MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
      · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
      · exact range_shift_subset (regAddr s "ap") as.length x
          (by simpa [List.length_cons] using h)
    have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
      rw [hra_ap, hmem1]
      exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
        hdoa_store_aptail hap_tail
    have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
        (range (regAddr s1 "ap") (8 * as.length)) := by
      rw [hra_op, hra_ap]
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
      · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
      · exact range_shift_subset (regAddr s "ap") as.length x
          (by simpa [List.length_cons] using h)
    have hcy1 : s1.regs "cy" = (Mpn.Mul1Prototype.mul1Step a (s.regs "b") cy).2 := hs1_cy
    have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
      rw [hs1_n, hn]
      simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
    obtain ⟨s', hs', hs'_op⟩ :=
      ih s1 (Mpn.Mul1Prototype.mul1Step a (s.regs "b") cy).2 extra hcy1 hn1 hap1 hdoa1
    refine ⟨s', ?_, ?_⟩
    · have hfuel : 2 * (a :: as).length + 3 + extra
          = (2 * as.length + 2 + extra) + 3 := by
        simp only [List.length_cons]; ring
      rw [hfuel]
      refine bignumExecFuel_loopMul_step emptyRegistry (2 * as.length + 2 + extra) _
        s s1 s' (Mpn.Mul1Prototype.evalPExpr_loopCond_true s hn_ne) hs1 ?_
      simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
              from by omega] using hs'
    · rw [hs'_op, hs1_op]
      have hl : 8 * (a :: as).length = 8 * as.length + 8 := by
        simp only [List.length_cons]; ring
      rw [hl, BitVec.ofNat_add, show (BitVec.ofNat 64 8 : BitVec 64) = 8 from rfl]
      rw [BitVec.add_comm (BitVec.ofNat 64 (8 * as.length)) 8, ← BitVec.add_assoc]

/-- The carry-storing `mpn_mul_1` body has no `Ccall`. -/
theorem bodyMulCarry_noCcall : NoCcallBody bodyMulCarry := by
  refine append_noCcall bodyMul_noCcall (singleton_noCcall ?_)
  simp only [Mpn.Mul1Prototype.storeAt0, noCcallI]

/-- Registry independence of the carry-storing `mpn_mul_1` body — a direct
    instance of the general `bignumExecFuel_registry_irrel`. -/
theorem mulCarry_registry_irrel
    (reg : BignumRegistry) (fuel : Nat) (s : BignumState) :
    bignumExecFuel reg fuel bodyMulCarry s
      = bignumExecFuel emptyRegistry fuel bodyMulCarry s :=
  bignumExecFuel_registry_irrel reg fuel bodyMulCarry s bodyMulCarry_noCcall

/-- The registry resolves `mpn_mul_1` to the carry-storing kernel. -/
theorem mulRegistry_mul : mulRegistry "mpn_mul_1" = some mpnMul1CarryFd := by
  simp [mulRegistry]

/-- **Row 0 — the per-row carry-window step for `mpn_mul_1`.**  Running the
    carry-storing kernel body `mpnMul1CarryFd.body` (= `bodyMul ++ [storeAt0
    "op" "cy"]`) from the callee init state writes the *full* `|a|+1`-limb row
    `(mpnMul1 a b[0] 0).1 ++ [(mpnMul1 a b[0] 0).2]` to the `op`-window: the
    verified void kernel (`MpnMul1JasminRefines`) writes the low `|a|` limbs and
    leaves the carry-out in `cy`, the loop advances `op` to `op_init + 8·|a|`
    (`mul_loop_op`), and the trailing `storeAt0 "op" "cy"` lands that carry-out
    at `out[|a|]`.  Mirror of `mpnMul_per_row_carry` (Residual A). -/
theorem mpnMul1_per_row_carry
    (f : Nat) (s : BignumState) (bj : BitVec 64) (a : List (BitVec 64))
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hf : f > 2 * a.length + 3) :
    ∃ cf, bignumExecFuel mulRegistry f mpnMul1CarryFd.body
        { regs := fun name => match mpnMul1CarryFd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat)
        ((mpnMul1 a bj 0).1 ++ [(mpnMul1 a bj 0).2]) := by
  -- mpnMul1CarryFd.params = mpnMul1Fd.params = mpnAddmul1Fd.params; identify regs.
  rw [show mpnMul1CarryFd.params = mpnAddmul1Fd.params from rfl,
      addmul_callee_regs (s.regs "op") (s.regs "ap") bj (s.regs "n")]
  -- The callee init state (after the parameter binding).
  set ci : BignumState :=
    { regs := fun name => if name = "op" then s.regs "op"
                          else if name = "ap" then s.regs "ap"
                          else if name = "b" then bj
                          else if name = "n" then s.regs "n" else 0
    , mem := s.mem } with hci
  have hci_n : ci.regs "n" = BitVec.ofNat 64 a.length := by rw [hci]; simp; exact hn
  have hci_b : ci.regs "b" = bj := by rw [hci]; simp
  have hci_op : ci.regs "op" = s.regs "op" := by rw [hci]; simp
  have hci_ap : ci.regs "ap" = s.regs "ap" := by rw [hci]; simp
  have hci_mem : ci.mem = s.mem := by rw [hci]
  have hci_a : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) a := by
    rw [hci_mem, hci_ap]; exact ha
  -- Window bound: 8·(|a|+1) ≤ 2^64.
  have hsize : 8 * (a.length + 1) ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos a.length with h0 | hpos
    · rw [h0]; norm_num
    · exact le_of_lt (disjoint_range_lt_left (UInt64.ofNat (s.regs "op").toNat)
        (UInt64.ofNat (s.regs "ap").toNat) (8 * (a.length + 1)) (8 * a.length)
        (by omega) hdoa)
  -- Low-window disjointness for the kernel bridge.
  have hdoa_low : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * a.length)) := by
    rw [hci_op, hci_ap]
    refine disjoint_mono (fun x h => ?_) (fun x h => h) hdoa
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by omega, rfl⟩
  -- Run the verified void kernel body `bodyMul` on `ci` at fuel `f - 1`.
  set f1 : Nat := f - 1 with hf1
  have hf1_gt : f1 > 2 * a.length + 2 := by rw [hf1]; omega
  obtain ⟨extra, hextra⟩ : ∃ extra, f1 = 2 * a.length + 3 + extra :=
    ⟨f1 - (2 * a.length + 3), by omega⟩
  obtain ⟨s1, hs1, hs1_mem, hs1_cy⟩ :=
    MpnMul1JasminRefines ci a f1 hci_n hci_a hdoa_low hf1_gt
  rw [hci_b] at hs1_mem hs1_cy
  -- The cy-initialised state (`bodyMul = [cy := 0; Cwhile ...]`).
  set ci0 : BignumState := setReg ci "cy" 0 with hci0
  have hexec0 : execInstr ci
      (.Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64) (.Pconst 0))
      = some ci0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hci0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  -- The loop run, isolated from `bodyMul`'s leading `cy := 0`.
  have hloop : bignumExecFuel emptyRegistry f1
      [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) Mpn.Mul1Prototype.loopBodyMul] ci0
        = some s1 := by
    obtain ⟨F, hF⟩ : ∃ F, f1 = F + 1 := ⟨f1 - 1, by omega⟩
    have : bignumExecFuel emptyRegistry (F + 1) Mpn.Mul1Prototype.bodyMul ci
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) Mpn.Mul1Prototype.loopBodyMul] ci0 := by
      conv_lhs => rw [Mpn.Mul1Prototype.bodyMul]
      simp only [bignumExecFuel, hexec0]
    rw [hF] at hs1 ⊢
    rw [← this]; exact hs1
  -- The op-advance: `mul_loop_op` on `ci0`, identified with `s1` by determinism.
  have hci0_cy : ci0.regs "cy" = 0 := by rw [hci0]; simp [setReg]
  have hci0_n : ci0.regs "n" = BitVec.ofNat 64 a.length := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]; exact hci_n
  have hci0_op_reg : regAddr ci0 "op" = UInt64.ofNat (ci.regs "op").toNat := by
    rw [hci0]; simp only [regAddr, setReg]; rw [if_neg (by decide)]
  have hci0_ap_reg : regAddr ci0 "ap" = UInt64.ofNat (ci.regs "ap").toNat := by
    rw [hci0]; simp only [regAddr, setReg]; rw [if_neg (by decide)]
  have hci0_a : memHoldsLimbs ci0.mem (regAddr ci0 "ap") a := by
    rw [show ci0.mem = ci.mem from rfl, hci0_ap_reg]; exact hci_a
  have hci0_doa : MemoryModel.Disjoint (range (regAddr ci0 "op") (8 * a.length))
      (range (regAddr ci0 "ap") (8 * a.length)) := by
    rw [hci0_op_reg, hci0_ap_reg]; exact hdoa_low
  obtain ⟨s1', hs1', hs1'_op⟩ :=
    mul_loop_op a ci0 0 extra hci0_cy hci0_n hci0_a hci0_doa
  -- Determinism: same fuel, same body, same start state ⇒ `s1' = s1`.
  rw [show 2 * a.length + 3 + extra = f1 from by omega] at hs1'
  have hs1'_eq : s1' = s1 := Option.some.inj (hs1'.symm.trans hloop)
  rw [hs1'_eq] at hs1'_op
  have hci0_op_bv : ci0.regs "op" = ci.regs "op" := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]
  have hs1_op_reg : regAddr s1 "op"
      = UInt64.ofNat (ci.regs "op").toNat + UInt64.ofNat (8 * a.length) := by
    rw [regAddr, hs1'_op, hci0_op_bv, regAddr_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * a.length < 2 ^ 64)]
  -- Run the trailing carry store `[storeAt0 "op" "cy"]` from `s1`.
  set s2 : BignumState :=
    storeMem s1 (regAddr s1 "op") (UInt64.ofNat (s1.regs "cy").toNat) with hs2
  have hstep : execInstr s1 (Mpn.Mul1Prototype.storeAt0 "op" "cy") = some s2 := by
    rw [Mpn.Mul1Prototype.storeAt0]
    simp only [execInstr, evalPExpr, resolveAddr, vr, bind, Option.bind,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl,
      show s1.regs "op" + 0 = s1.regs "op" from by bv_decide, regAddr, hs2]
  have hstore : bignumExecFuel emptyRegistry 1
      [Mpn.Mul1Prototype.storeAt0 "op" "cy"] s1 = some s2 := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine emptyRegistry 0
        [Mpn.Mul1Prototype.storeAt0 "op" "cy"] s1
        ⟨by simp [Mpn.Mul1Prototype.storeAt0, InstrR.isStraightLine], True.intro⟩]
    simp only [bignumExec, hstep]
  -- Sequence loop + store via `bignumExecFuel_seq` (fuel `f1 + 1 = f`).
  have hseq : bignumExecFuel emptyRegistry f bodyMulCarry ci = some s2 := by
    rw [show f = f1 + 1 from by omega, bodyMulCarry]
    exact bignumExecFuel_seq emptyRegistry f1 1 Mpn.Mul1Prototype.bodyMul
      [Mpn.Mul1Prototype.storeAt0 "op" "cy"] ci s1 s2 hs1 hstore
  -- Bridge the registry `mulRegistry → emptyRegistry`.
  refine ⟨s2, ?_, ?_⟩
  · rw [show mpnMul1CarryFd.body = bodyMulCarry from rfl,
        mulCarry_registry_irrel mulRegistry f ci]
    exact hseq
  · -- The op-window holds the full row `low ++ [carry]`.
    rw [← hci_op]
    have hlow_len : (mpnMul1 a bj 0).1.length = a.length := by
      rw [mpnMul1_length a bj 0]
    have hs2_mem : s2.mem = s1.mem.store64 (regAddr s1 "op")
        (UInt64.ofNat (s1.regs "cy").toNat) := by rw [hs2]; rfl
    have hcy_val : s1.regs "cy" = (mpnMul1 a bj 0).2 := hs1_cy
    set base : UInt64 := UInt64.ofNat (ci.regs "op").toNat with hbase
    have hstore_addr : regAddr s1 "op" = base + UInt64.ofNat (8 * a.length) := by
      rw [hs1_op_reg, hbase]
    have hlow_survive : memHoldsLimbs s2.mem base (mpnMul1 a bj 0).1 := by
      rw [hs2_mem, hstore_addr]
      refine memHoldsLimbs_store64_frame s1.mem base
        (base + UInt64.ofNat (8 * a.length)) _ (mpnMul1 a bj 0).1 ?_ ?_
      · rw [hlow_len]
        exact range_tail_head_disjoint base a.length hsize
      · -- s1.mem holds the low limbs at `base` (= `ci.regs "op"` address).
        exact hs1_mem
    have hcarry_at : load64Mem s2.mem (base + UInt64.ofNat (8 * (mpnMul1 a bj 0).1.length))
        = some (UInt64.ofNat (mpnMul1 a bj 0).2.toNat) := by
      rw [hlow_len, hs2_mem, hstore_addr, hcy_val,
          load64Mem_store64_same s1.mem (base + UInt64.ofNat (8 * a.length))]
    exact memHoldsLimbs_snoc s2.mem base (mpnMul1 a bj 0).1
      (mpnMul1 a bj 0).2 hlow_survive hcarry_at

/-! ### §5.3c  Frame-carrying per-row steps (for the outer-loop induction)

The committed `mpnMul_per_row_carry` / `mpnMul1_per_row_carry` give the row's
*window content* but not a frame for memory *outside* the row window — and the
outer loop needs that frame to keep already-finalized result limbs alive across
later rows.  We re-derive each per-row kernel run through the frame-carrying
loop lemmas (`mpnAddmul1_loop` / `mpnMul1_loop`, both of which expose a frame
clause `bb` disjoint from the write region ⇒ memory unchanged), adding the
frame conclusion: any block `bb` disjoint from the row window `[op, op+8(|a|+1))`
and from `[ap, ap+8|a|)` is preserved by the kernel run. -/

/-- **Frame-carrying addmul per-row step.**  Same as `mpnMul_per_row_carry`,
    plus: any 8-byte block `bb` disjoint from the row window `[op, op+8·(|a|+1))`
    reads the same in `cf.mem` as in the start memory `s.mem` (the kernel writes
    only the row window — established via the op-only loop frame
    `addmul_loop_frame_op` and the carry-store frame). -/
theorem mpnMul_per_row_carry_frame
    (f : Nat) (s : BignumState) (bj : BitVec 64) (out a : List (BitVec 64))
    (hlen : out.length = a.length)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (hout : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hf : f > 2 * a.length + 3) :
    ∃ cf, bignumExecFuel mulRegistry f mpnAddmul1CarryFd.body
        { regs := fun name => match mpnAddmul1CarryFd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat)
        ((mpnAddmul1 out a bj 0).1 ++ [(mpnAddmul1 out a bj 0).2]) ∧
      (∀ bb, MemoryModel.Disjoint (MemoryModel.range bb 8)
              (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1))) →
            load64Mem cf.mem bb = load64Mem s.mem bb) := by
  rw [show mpnAddmul1CarryFd.params = mpnAddmul1Fd.params from rfl,
      addmul_callee_regs (s.regs "op") (s.regs "ap") bj (s.regs "n")]
  set ci : BignumState :=
    { regs := fun name => if name = "op" then s.regs "op"
                          else if name = "ap" then s.regs "ap"
                          else if name = "b" then bj
                          else if name = "n" then s.regs "n" else 0
    , mem := s.mem } with hci
  have hci_n : ci.regs "n" = BitVec.ofNat 64 a.length := by rw [hci]; simp; exact hn
  have hci_b : ci.regs "b" = bj := by rw [hci]; simp
  have hci_op : ci.regs "op" = s.regs "op" := by rw [hci]; simp
  have hci_ap : ci.regs "ap" = s.regs "ap" := by rw [hci]; simp
  have hci_mem : ci.mem = s.mem := by rw [hci]
  have hci_out : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "op").toNat) out := by
    rw [hci_mem, hci_op]; exact hout
  have hci_a : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) a := by
    rw [hci_mem, hci_ap]; exact ha
  have hsize : 8 * (a.length + 1) ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos a.length with h0 | hpos
    · rw [h0]; norm_num
    · exact le_of_lt (disjoint_range_lt_left (UInt64.ofNat (s.regs "op").toNat)
        (UInt64.ofNat (s.regs "ap").toNat) (8 * (a.length + 1)) (8 * a.length)
        (by omega) hdoa)
  have hdoa_low : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * a.length)) := by
    rw [hci_op, hci_ap]
    refine disjoint_mono (fun x h => ?_) (fun x h => h) hdoa
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by omega, rfl⟩
  set f1 : Nat := f - 1 with hf1
  obtain ⟨extra, hextra⟩ : ∃ extra, f1 = 2 * a.length + 3 + extra :=
    ⟨f1 - (2 * a.length + 3), by omega⟩
  -- The cy-initialised state.
  set ci0 : BignumState := setReg ci "cy" 0 with hci0
  have hexec0 : execInstr ci
      (.Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64) (.Pconst 0))
      = some ci0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hci0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hci0_cy : ci0.regs "cy" = 0 := by rw [hci0]; simp [setReg]
  have hci0_n : ci0.regs "n" = BitVec.ofNat 64 a.length := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]; exact hci_n
  have hci0_op_reg : regAddr ci0 "op" = UInt64.ofNat (ci.regs "op").toNat := by
    rw [hci0]; simp only [regAddr, setReg]; rw [if_neg (by decide)]
  have hci0_ap_reg : regAddr ci0 "ap" = UInt64.ofNat (ci.regs "ap").toNat := by
    rw [hci0]; simp only [regAddr, setReg]; rw [if_neg (by decide)]
  have hci0_b : ci0.regs "b" = bj := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]; exact hci_b
  have hci0_mem : ci0.mem = s.mem := by rw [hci0]; simp only [setReg]; exact hci_mem
  have hci0_out : memHoldsLimbs ci0.mem (regAddr ci0 "op") out := by
    rw [show ci0.mem = ci.mem from rfl, hci0_op_reg]; exact hci_out
  have hci0_a : memHoldsLimbs ci0.mem (regAddr ci0 "ap") a := by
    rw [show ci0.mem = ci.mem from rfl, hci0_ap_reg]; exact hci_a
  have hci0_doa : MemoryModel.Disjoint (range (regAddr ci0 "op") (8 * a.length))
      (range (regAddr ci0 "ap") (8 * a.length)) := by
    rw [hci0_op_reg, hci0_ap_reg]; exact hdoa_low
  -- Run the verified loop with its frame, via `mpnAddmul1_loop` on `ci0`.
  obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_b, hs1_frame⟩ :=
    mpnAddmul1_loop out a ci0 0 extra hlen hci0_cy hci0_n hci0_out hci0_a hci0_doa
  rw [show 2 * a.length + 3 + extra = f1 from by omega] at hs1
  rw [hci0_b] at hs1_mem hs1_cy
  -- The op-advance, identified with `s1` by determinism (`addmul_loop_op`).
  obtain ⟨s1', hs1', hs1'_op⟩ :=
    addmul_loop_op out a ci0 0 extra hlen hci0_cy hci0_n hci0_out hci0_a hci0_doa
  rw [show 2 * a.length + 3 + extra = f1 from by omega] at hs1'
  have hs1'_eq : s1' = s1 := Option.some.inj (hs1'.symm.trans hs1)
  rw [hs1'_eq] at hs1'_op
  -- The op-only frame, identified with `s1` by determinism (`addmul_loop_frame_op`).
  obtain ⟨s1'', hs1'', hs1''_frame⟩ :=
    addmul_loop_frame_op out a ci0 0 extra hlen hci0_cy hci0_n hci0_out hci0_a hci0_doa
  rw [show 2 * a.length + 3 + extra = f1 from by omega] at hs1''
  have hs1''_eq : s1'' = s1 := Option.some.inj (hs1''.symm.trans hs1)
  rw [hs1''_eq] at hs1''_frame
  -- `addmul_loop_frame_op` frames over `[ci0.op, 8|a|)` relative to `ci0.mem = s.mem`.
  rw [hci0_op_reg, hci_op, hci0_mem] at hs1''_frame
  -- bodyAddmul = [cy:=0; Cwhile ...], so its run on `ci` matches the loop on `ci0`.
  have hbody : bignumExecFuel emptyRegistry f1 bodyAddmul ci = some s1 := by
    obtain ⟨F, hF⟩ : ∃ F, f1 = F + 1 := ⟨f1 - 1, by omega⟩
    have : bignumExecFuel emptyRegistry (F + 1) bodyAddmul ci
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodyAddmul] ci0 := by
      conv_lhs => rw [bodyAddmul]
      simp only [bignumExecFuel, hexec0]
    rw [hF] at hs1 ⊢
    rw [this]; exact hs1
  have hci0_op_bv : ci0.regs "op" = ci.regs "op" := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]
  have hs1_op_reg : regAddr s1 "op"
      = UInt64.ofNat (ci.regs "op").toNat + UInt64.ofNat (8 * a.length) := by
    rw [regAddr, hs1'_op, hci0_op_bv, regAddr_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * a.length < 2 ^ 64)]
  -- Trailing carry store.
  set s2 : BignumState :=
    storeMem s1 (regAddr s1 "op") (UInt64.ofNat (s1.regs "cy").toNat) with hs2
  have hstep : execInstr s1 (Mpn.Mul1Prototype.storeAt0 "op" "cy") = some s2 := by
    rw [Mpn.Mul1Prototype.storeAt0]
    simp only [execInstr, evalPExpr, resolveAddr, vr, bind, Option.bind,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl,
      show s1.regs "op" + 0 = s1.regs "op" from by bv_decide, regAddr, hs2]
  have hstore : bignumExecFuel emptyRegistry 1
      [Mpn.Mul1Prototype.storeAt0 "op" "cy"] s1 = some s2 := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine emptyRegistry 0
        [Mpn.Mul1Prototype.storeAt0 "op" "cy"] s1
        ⟨by simp [Mpn.Mul1Prototype.storeAt0, InstrR.isStraightLine], True.intro⟩]
    simp only [bignumExec, hstep]
  have hseq : bignumExecFuel emptyRegistry f bodyAddmulCarry ci = some s2 := by
    rw [show f = f1 + 1 from by omega, bodyAddmulCarry]
    exact bignumExecFuel_seq emptyRegistry f1 1 bodyAddmul
      [Mpn.Mul1Prototype.storeAt0 "op" "cy"] ci s1 s2 hbody hstore
  refine ⟨s2, ?_, ?_, ?_⟩
  · rw [show mpnAddmul1CarryFd.body = bodyAddmulCarry from rfl,
        addmulCarry_registry_irrel mulRegistry f ci]
    exact hseq
  · -- The op-window holds the full row `low ++ [carry]`.
    rw [← hci_op]
    have hlow_len : (mpnAddmul1 out a bj 0).1.length = a.length := by
      rw [mpnAddmul1_length out a bj 0 hlen, hlen]
    have hs2_mem : s2.mem = s1.mem.store64 (regAddr s1 "op")
        (UInt64.ofNat (s1.regs "cy").toNat) := by rw [hs2]; rfl
    have hcy_val : s1.regs "cy" = (mpnAddmul1 out a bj 0).2 := hs1_cy
    set base : UInt64 := UInt64.ofNat (ci.regs "op").toNat with hbase
    have hstore_addr : regAddr s1 "op" = base + UInt64.ofNat (8 * a.length) := by
      rw [hs1_op_reg, hbase]
    have hs1_mem' : memHoldsLimbs s1.mem base (mpnAddmul1 out a bj 0).1 := by
      have : regAddr ci0 "op" = base := by rw [hci0_op_reg, hbase]
      rw [← this]; exact hs1_mem
    have hlow_survive : memHoldsLimbs s2.mem base (mpnAddmul1 out a bj 0).1 := by
      rw [hs2_mem, hstore_addr]
      refine memHoldsLimbs_store64_frame s1.mem base
        (base + UInt64.ofNat (8 * a.length)) _ (mpnAddmul1 out a bj 0).1 ?_ hs1_mem'
      rw [hlow_len]
      exact range_tail_head_disjoint base a.length hsize
    have hcarry_at : load64Mem s2.mem (base + UInt64.ofNat (8 * (mpnAddmul1 out a bj 0).1.length))
        = some (UInt64.ofNat (mpnAddmul1 out a bj 0).2.toNat) := by
      rw [hlow_len, hs2_mem, hstore_addr, hcy_val,
          load64Mem_store64_same s1.mem (base + UInt64.ofNat (8 * a.length))]
    exact memHoldsLimbs_snoc s2.mem base (mpnAddmul1 out a bj 0).1
      (mpnAddmul1 out a bj 0).2 hlow_survive hcarry_at
  · -- The frame (op-window only).
    intro bb hbb_op
    have hs2_mem : s2.mem = s1.mem.store64 (regAddr s1 "op")
        (UInt64.ofNat (s1.regs "cy").toNat) := by rw [hs2]; rfl
    set base : UInt64 := UInt64.ofNat (ci.regs "op").toNat with hbase
    have hstore_addr : regAddr s1 "op" = base + UInt64.ofNat (8 * a.length) := by
      rw [hs1_op_reg, hbase]
    have hbase_s : base = UInt64.ofNat (s.regs "op").toNat := by rw [hbase, hci_op]
    -- `bb` disjoint from the carry-store block `[op+8|a|, +8)` (⊆ row window).
    have hbb_store : MemoryModel.Disjoint (range bb 8)
        (range (regAddr s1 "op") 8) := by
      rw [hstore_addr, hbase_s]
      refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
      obtain ⟨k, hk, rfl⟩ := h
      refine ⟨8 * a.length + k, by omega, ?_⟩
      rw [UInt64.ofNat_add, ← UInt64.add_assoc]
    -- `bb` disjoint from the loop write region `[op, op+8|a|)`.
    have hbb_loop_op : MemoryModel.Disjoint (range bb 8)
        (range (UInt64.ofNat (s.regs "op").toNat) (8 * a.length)) := by
      refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
      obtain ⟨k, hk, rfl⟩ := h
      exact ⟨k, by omega, rfl⟩
    -- Chain: store frame, then op-only loop frame (already relative to `s.mem`).
    rw [hs2_mem, load64Mem_store64_disjoint s1.mem bb (regAddr s1 "op") _ hbb_store]
    exact hs1''_frame bb hbb_loop_op

/-- **Frame-carrying row-0 (`mpn_mul_1`) per-row step.**  Same as
    `mpnMul1_per_row_carry`, plus the frame conclusion (block `bb` disjoint from
    the row window `[op, op+8·(|a|+1))` is preserved).  Row 0 reads only `ap`. -/
theorem mpnMul1_per_row_carry_frame
    (f : Nat) (s : BignumState) (bj : BitVec 64) (a : List (BitVec 64))
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hf : f > 2 * a.length + 3) :
    ∃ cf, bignumExecFuel mulRegistry f mpnMul1CarryFd.body
        { regs := fun name => match mpnMul1CarryFd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat)
        ((mpnMul1 a bj 0).1 ++ [(mpnMul1 a bj 0).2]) ∧
      (∀ bb, MemoryModel.Disjoint (MemoryModel.range bb 8)
              (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1))) →
            load64Mem cf.mem bb = load64Mem s.mem bb) := by
  rw [show mpnMul1CarryFd.params = mpnAddmul1Fd.params from rfl,
      addmul_callee_regs (s.regs "op") (s.regs "ap") bj (s.regs "n")]
  set ci : BignumState :=
    { regs := fun name => if name = "op" then s.regs "op"
                          else if name = "ap" then s.regs "ap"
                          else if name = "b" then bj
                          else if name = "n" then s.regs "n" else 0
    , mem := s.mem } with hci
  have hci_n : ci.regs "n" = BitVec.ofNat 64 a.length := by rw [hci]; simp; exact hn
  have hci_b : ci.regs "b" = bj := by rw [hci]; simp
  have hci_op : ci.regs "op" = s.regs "op" := by rw [hci]; simp
  have hci_ap : ci.regs "ap" = s.regs "ap" := by rw [hci]; simp
  have hci_mem : ci.mem = s.mem := by rw [hci]
  have hci_a : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) a := by
    rw [hci_mem, hci_ap]; exact ha
  have hsize : 8 * (a.length + 1) ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos a.length with h0 | hpos
    · rw [h0]; norm_num
    · exact le_of_lt (disjoint_range_lt_left (UInt64.ofNat (s.regs "op").toNat)
        (UInt64.ofNat (s.regs "ap").toNat) (8 * (a.length + 1)) (8 * a.length)
        (by omega) hdoa)
  have hdoa_low : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * a.length)) := by
    rw [hci_op, hci_ap]
    refine disjoint_mono (fun x h => ?_) (fun x h => h) hdoa
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by omega, rfl⟩
  set f1 : Nat := f - 1 with hf1
  obtain ⟨extra, hextra⟩ : ∃ extra, f1 = 2 * a.length + 3 + extra :=
    ⟨f1 - (2 * a.length + 3), by omega⟩
  set ci0 : BignumState := setReg ci "cy" 0 with hci0
  have hexec0 : execInstr ci
      (.Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64) (.Pconst 0))
      = some ci0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hci0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hci0_cy : ci0.regs "cy" = 0 := by rw [hci0]; simp [setReg]
  have hci0_n : ci0.regs "n" = BitVec.ofNat 64 a.length := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]; exact hci_n
  have hci0_op_reg : regAddr ci0 "op" = UInt64.ofNat (ci.regs "op").toNat := by
    rw [hci0]; simp only [regAddr, setReg]; rw [if_neg (by decide)]
  have hci0_ap_reg : regAddr ci0 "ap" = UInt64.ofNat (ci.regs "ap").toNat := by
    rw [hci0]; simp only [regAddr, setReg]; rw [if_neg (by decide)]
  have hci0_b : ci0.regs "b" = bj := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]; exact hci_b
  have hci0_mem : ci0.mem = s.mem := by rw [hci0]; simp only [setReg]; exact hci_mem
  have hci0_a : memHoldsLimbs ci0.mem (regAddr ci0 "ap") a := by
    rw [show ci0.mem = ci.mem from rfl, hci0_ap_reg]; exact hci_a
  have hci0_doa : MemoryModel.Disjoint (range (regAddr ci0 "op") (8 * a.length))
      (range (regAddr ci0 "ap") (8 * a.length)) := by
    rw [hci0_op_reg, hci0_ap_reg]; exact hdoa_low
  -- Run the verified loop with its frame, via `mpnMul1_loop` on `ci0`.
  obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_b, hs1_frame⟩ :=
    Mpn.Mul1Prototype.mpnMul1_loop a ci0 0 extra hci0_cy hci0_n hci0_a hci0_doa
  rw [show 2 * a.length + 3 + extra = f1 from by omega] at hs1
  rw [hci0_b] at hs1_mem hs1_cy
  -- op-advance via `mul_loop_op`, identified with `s1` by determinism.
  obtain ⟨s1', hs1', hs1'_op⟩ :=
    mul_loop_op a ci0 0 extra hci0_cy hci0_n hci0_a hci0_doa
  rw [show 2 * a.length + 3 + extra = f1 from by omega] at hs1'
  have hs1'_eq : s1' = s1 := Option.some.inj (hs1'.symm.trans hs1)
  rw [hs1'_eq] at hs1'_op
  -- The op-only frame via `mul_loop_frame_op`, identified with `s1`.
  obtain ⟨s1'', hs1'', hs1''_frame⟩ :=
    mul_loop_frame_op a ci0 0 extra hci0_cy hci0_n hci0_a hci0_doa
  rw [show 2 * a.length + 3 + extra = f1 from by omega] at hs1''
  have hs1''_eq : s1'' = s1 := Option.some.inj (hs1''.symm.trans hs1)
  rw [hs1''_eq] at hs1''_frame
  rw [hci0_op_reg, hci_op, hci0_mem] at hs1''_frame
  have hbody : bignumExecFuel emptyRegistry f1 Mpn.Mul1Prototype.bodyMul ci = some s1 := by
    obtain ⟨F, hF⟩ : ∃ F, f1 = F + 1 := ⟨f1 - 1, by omega⟩
    have : bignumExecFuel emptyRegistry (F + 1) Mpn.Mul1Prototype.bodyMul ci
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) Mpn.Mul1Prototype.loopBodyMul] ci0 := by
      conv_lhs => rw [Mpn.Mul1Prototype.bodyMul]
      simp only [bignumExecFuel, hexec0]
    rw [hF] at hs1 ⊢
    rw [this]; exact hs1
  have hci0_op_bv : ci0.regs "op" = ci.regs "op" := by
    rw [hci0]; simp only [setReg]; rw [if_neg (by decide)]
  have hs1_op_reg : regAddr s1 "op"
      = UInt64.ofNat (ci.regs "op").toNat + UInt64.ofNat (8 * a.length) := by
    rw [regAddr, hs1'_op, hci0_op_bv, regAddr_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * a.length < 2 ^ 64)]
  set s2 : BignumState :=
    storeMem s1 (regAddr s1 "op") (UInt64.ofNat (s1.regs "cy").toNat) with hs2
  have hstep : execInstr s1 (Mpn.Mul1Prototype.storeAt0 "op" "cy") = some s2 := by
    rw [Mpn.Mul1Prototype.storeAt0]
    simp only [execInstr, evalPExpr, resolveAddr, vr, bind, Option.bind,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl,
      show s1.regs "op" + 0 = s1.regs "op" from by bv_decide, regAddr, hs2]
  have hstore : bignumExecFuel emptyRegistry 1
      [Mpn.Mul1Prototype.storeAt0 "op" "cy"] s1 = some s2 := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine emptyRegistry 0
        [Mpn.Mul1Prototype.storeAt0 "op" "cy"] s1
        ⟨by simp [Mpn.Mul1Prototype.storeAt0, InstrR.isStraightLine], True.intro⟩]
    simp only [bignumExec, hstep]
  have hseq : bignumExecFuel emptyRegistry f bodyMulCarry ci = some s2 := by
    rw [show f = f1 + 1 from by omega, bodyMulCarry]
    exact bignumExecFuel_seq emptyRegistry f1 1 Mpn.Mul1Prototype.bodyMul
      [Mpn.Mul1Prototype.storeAt0 "op" "cy"] ci s1 s2 hbody hstore
  refine ⟨s2, ?_, ?_, ?_⟩
  · rw [show mpnMul1CarryFd.body = bodyMulCarry from rfl,
        mulCarry_registry_irrel mulRegistry f ci]
    exact hseq
  · rw [← hci_op]
    have hlow_len : (mpnMul1 a bj 0).1.length = a.length := by rw [mpnMul1_length a bj 0]
    have hs2_mem : s2.mem = s1.mem.store64 (regAddr s1 "op")
        (UInt64.ofNat (s1.regs "cy").toNat) := by rw [hs2]; rfl
    have hcy_val : s1.regs "cy" = (mpnMul1 a bj 0).2 := hs1_cy
    set base : UInt64 := UInt64.ofNat (ci.regs "op").toNat with hbase
    have hstore_addr : regAddr s1 "op" = base + UInt64.ofNat (8 * a.length) := by
      rw [hs1_op_reg, hbase]
    have hs1_mem' : memHoldsLimbs s1.mem base (mpnMul1 a bj 0).1 := by
      have : regAddr ci0 "op" = base := by rw [hci0_op_reg, hbase]
      rw [← this]; exact hs1_mem
    have hlow_survive : memHoldsLimbs s2.mem base (mpnMul1 a bj 0).1 := by
      rw [hs2_mem, hstore_addr]
      refine memHoldsLimbs_store64_frame s1.mem base
        (base + UInt64.ofNat (8 * a.length)) _ (mpnMul1 a bj 0).1 ?_ hs1_mem'
      rw [hlow_len]
      exact range_tail_head_disjoint base a.length hsize
    have hcarry_at : load64Mem s2.mem (base + UInt64.ofNat (8 * (mpnMul1 a bj 0).1.length))
        = some (UInt64.ofNat (mpnMul1 a bj 0).2.toNat) := by
      rw [hlow_len, hs2_mem, hstore_addr, hcy_val,
          load64Mem_store64_same s1.mem (base + UInt64.ofNat (8 * a.length))]
    exact memHoldsLimbs_snoc s2.mem base (mpnMul1 a bj 0).1
      (mpnMul1 a bj 0).2 hlow_survive hcarry_at
  · intro bb hbb_op
    have hs2_mem : s2.mem = s1.mem.store64 (regAddr s1 "op")
        (UInt64.ofNat (s1.regs "cy").toNat) := by rw [hs2]; rfl
    set base : UInt64 := UInt64.ofNat (ci.regs "op").toNat with hbase
    have hstore_addr : regAddr s1 "op" = base + UInt64.ofNat (8 * a.length) := by
      rw [hs1_op_reg, hbase]
    have hbase_s : base = UInt64.ofNat (s.regs "op").toNat := by rw [hbase, hci_op]
    have hbb_store : MemoryModel.Disjoint (range bb 8)
        (range (regAddr s1 "op") 8) := by
      rw [hstore_addr, hbase_s]
      refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
      obtain ⟨k, hk, rfl⟩ := h
      refine ⟨8 * a.length + k, by omega, ?_⟩
      rw [UInt64.ofNat_add, ← UInt64.add_assoc]
    have hbb_loop_op : MemoryModel.Disjoint (range bb 8)
        (range (UInt64.ofNat (s.regs "op").toNat) (8 * a.length)) := by
      refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
      obtain ⟨k, hk, rfl⟩ := h
      exact ⟨k, by omega, rfl⟩
    rw [hs2_mem, load64Mem_store64_disjoint s1.mem bb (regAddr s1 "op") _ hbb_store]
    exact hs1''_frame bb hbb_loop_op

/-! ### §5.4  Memory-algebra glue + control-flow peel for the outer loop -/

/-- Peel a `set j := k` (the `Cfor` loop-counter assignment) off the front of a
    body at the *same* fuel (it flows through the catch-all arm). -/
theorem setj_peel (f : Nat) (k : Nat) (rest : List InstrR) (s : BignumState) :
    bignumExecFuel mulRegistry (f + 1) (mkSetVarConst { var := vr "j" } k :: rest) s
      = bignumExecFuel mulRegistry (f + 1) rest (setReg s "j" (BitVec.ofInt 64 (Int.ofNat k))) := by
  simp only [mkSetVarConst, bignumExecFuel, execInstr, evalPExpr, vr, setReg, bind, Option.bind]

/-- `memHoldsLimbs` over a concatenation splits at the `8·|xs|` byte offset. -/
theorem memHoldsLimbs_append (m : Mem) (base : UInt64) (xs ys : List (BitVec 64)) :
    memHoldsLimbs m base (xs ++ ys)
      ↔ memHoldsLimbs m base xs ∧ memHoldsLimbs m (base + UInt64.ofNat (8 * xs.length)) ys := by
  induction xs generalizing base with
  | nil => simp [memHoldsLimbs]
  | cons x xs ih =>
    have haddr : base + 8 + UInt64.ofNat (8 * xs.length)
        = base + UInt64.ofNat (8 * (xs.length + 1)) := by
      rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length from by ring, UInt64.ofNat_add,
        show (UInt64.ofNat 8 : UInt64) = 8 from rfl]; ac_rfl
    simp only [List.cons_append, memHoldsLimbs, ih, List.length_cons]
    constructor
    · rintro ⟨hh, ht, hy⟩
      exact ⟨⟨hh, ht⟩, by rw [← haddr]; exact hy⟩
    · rintro ⟨⟨hh, ht⟩, hy⟩
      exact ⟨hh, ht, by rw [haddr]; exact hy⟩

/-- Transfer `memHoldsLimbs` across a memory change that agrees on every limb
    address of the window. -/
theorem memHoldsLimbs_frame_eq (m m' : Mem) (base : UInt64) (ws : List (BitVec 64))
    (heq : ∀ k, k < ws.length → load64Mem m' (base + UInt64.ofNat (8 * k)) = load64Mem m (base + UInt64.ofNat (8 * k)))
    (h : memHoldsLimbs m base ws) :
    memHoldsLimbs m' base ws := by
  induction ws generalizing base with
  | nil => exact True.intro
  | cons w ws ih =>
    obtain ⟨hh, ht⟩ := h
    refine ⟨?_, ?_⟩
    · have h0 := heq 0 (by simp)
      rw [show base + UInt64.ofNat (8 * 0) = base from by simp] at h0
      rw [h0]; exact hh
    · refine ih (base + 8) (fun k hk => ?_) ht
      have := heq (k+1) (by simp only [List.length_cons]; omega)
      rw [show base + UInt64.ofNat (8 * (k+1)) = base + 8 + UInt64.ofNat (8 * k) from by
        rw [show 8 * (k+1) = 8 + 8 * k from by ring, UInt64.ofNat_add, show (UInt64.ofNat 8 : UInt64) = 8 from rfl]; ac_rfl] at this
      exact this

/-- Transfer `memHoldsLimbs` across a memory change framed *outside* a region
    `R`, provided the window `[base, base+8·|ws|)` is disjoint from `R`. -/
theorem memHoldsLimbs_frame_disjoint (m m' : Mem) (base R0 : UInt64) (Rn : Nat)
    (ws : List (BitVec 64))
    (hframe : ∀ bb, MemoryModel.Disjoint (MemoryModel.range bb 8) (MemoryModel.range R0 Rn) →
        load64Mem m' bb = load64Mem m bb)
    (hdisj : MemoryModel.Disjoint (MemoryModel.range base (8 * ws.length)) (MemoryModel.range R0 Rn))
    (h : memHoldsLimbs m base ws) :
    memHoldsLimbs m' base ws := by
  refine memHoldsLimbs_frame_eq m m' base ws (fun k hk => ?_) h
  apply hframe
  -- `[base + 8k, base + 8k + 8)` ⊆ `[base, base + 8|ws|)`, hence disjoint from `R`.
  refine disjoint_mono (fun x hx => ?_) (fun x hx => hx) hdisj
  obtain ⟨i, hi, rfl⟩ := hx
  refine ⟨8 * k + i, by omega, ?_⟩
  rw [UInt64.ofNat_add, ← UInt64.add_assoc]

/-! ### §5.5  The outer-loop induction

`mulOuterRows vs` is the flattened body of the `Cfor`: for each set-counter
value `v` in `vs` it emits `set j := v` followed by one `mulOuterBody`.  (The
counter `j` is irrelevant to the computation — it's loaded into a register that
`mulOuterBody` never reads — so the values `vs` are immaterial; we keep them to
match the exact shape `unrollFor` produces.)  The core induction
`mulOuter_rows` shows: starting from a state whose `op`-region holds the
accumulator `acc` (with zero high-suffix), running `mulOuterRows vs ++ rest`
for `|vs| = |bs|` rows reaches `rest` from a state whose `op`-region holds
`mulAcc a bs acc`, with `op`/`bp` advanced and memory outside the active region
preserved. -/

/-- The flattened `Cfor` body: `(set j := v; mulOuterBody)` for each `v ∈ vs`. -/
def mulOuterRows : List Nat → List InstrR
  | []      => []
  | v :: vs => mkSetVarConst { var := vr "j" } v :: mulOuterBody ++ mulOuterRows vs

/-- **Core outer-loop induction.**  Process `|bsv|` rows (each `mpn_addmul_1`).
    The `op`-region holds the accumulator `acc` (length `|a|+|bsv|`, zero high
    suffix); the b-limbs `bsv` are held at `bp`; `a` at `ap`; `n=|a|`.
    Disjointness: the active region `[op, op+8(|a|+|bsv|))` is separated from
    `[ap, ap+8|a|)` and `[bp, bp+8|bsv|)`, and the whole layout fits.  Running
    `mulOuterRows vs ++ rest` (for `|vs| = |bsv|`) reaches `rest` from `s'` whose
    `op`-region holds `mulAcc a bsv acc`, with `op`/`bp` advanced `8|bsv|`, and
    memory outside `[op, op+8(|a|+|bsv|))` preserved.  By induction on `bsv`:
    each step extracts the current window `acc.take |a|`, runs one row via
    `mpnMul_per_row_carry_frame` + `mulOuterBody_step`, then re-establishes the
    invariant on the slid window. -/
theorem mulOuter_rows :
    ∀ (bsv : List (BitVec 64)) (vs : List Nat) (a acc : List (BitVec 64))
      (rest : List InstrR) (s : BignumState) (F : Nat),
      vs.length = bsv.length →
      acc.length = a.length + bsv.length →
      acc.drop a.length = List.replicate bsv.length 0 →
      s.regs "n" = BitVec.ofNat 64 a.length →
      memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) acc →
      memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
      memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bsv →
      MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + bsv.length)))
        (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
      MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + bsv.length)))
        (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * bsv.length)) →
      MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
        (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * bsv.length)) →
      8 * (a.length + bsv.length) ≤ 2 ^ 64 →
      F > 2 * a.length + 3 →
      ∃ s', bignumExecFuel mulRegistry (F + 1) (mulOuterRows vs ++ rest) s
            = bignumExecFuel mulRegistry (F + 1) rest s' ∧
        memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mulAcc a bsv acc) ∧
        s'.regs "op" = s.regs "op" + BitVec.ofNat 64 (8 * bsv.length) ∧
        s'.regs "bp" = s.regs "bp" + BitVec.ofNat 64 (8 * bsv.length) ∧
        s'.regs "n" = s.regs "n" ∧ s'.regs "ap" = s.regs "ap" ∧
        (∀ bb, MemoryModel.Disjoint (MemoryModel.range bb 8)
              (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + bsv.length))) →
            load64Mem s'.mem bb = load64Mem s.mem bb) := by
  intro bsv
  induction bsv with
  | nil =>
    intro vs a acc rest s F hvs hacclen _ hn hacc ha hbp _ _ _ _ hF
    have hvs0 : vs = [] := List.length_eq_zero_iff.mp (by simpa using hvs)
    subst hvs0
    refine ⟨s, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [mulOuterRows, List.nil_append]
    · simpa [mulAcc] using! hacc
    · simp
    · simp
    · intro bb _; rfl
  | cons b0 bsv' ih =>
    intro vs a acc rest s F hvs hacclen hacczero hn hacc ha hbp hdoa_ap hdoa_bp hap_bp hfit hF
    -- Split `vs = v :: vs'`.
    cases vs with
    | nil => simp at hvs
    | cons v vs' =>
    have hvs' : vs'.length = bsv'.length := by simpa using hvs
    -- Window content `acc.take |a|` and the head/tail split of `acc`.
    have hacc_take_len : (acc.take a.length).length = a.length := by
      rw [List.length_take]; omega
    have hacc_split := (memHoldsLimbs_append s.mem (UInt64.ofNat (s.regs "op").toNat)
      (acc.take a.length) (acc.drop a.length)).mp (by rw [List.take_append_drop]; exact hacc)
    obtain ⟨hwin0, hrest0⟩ := hacc_split
    rw [hacc_take_len] at hrest0
    -- The b-limb `b0` is at `bp`.
    obtain ⟨hbp_head, hbp_tail⟩ := hbp
    -- Abbreviations matching the `mulAcc` recursion.
    set p := mpnAddmul1 (acc.take a.length) a b0 0 with hp
    set row : List (BitVec 64) := p.1 ++ [p.2] with hrow
    have hp1_len : p.1.length = a.length := by
      rw [hp, mpnAddmul1_length (acc.take a.length) a b0 0 (by rw [hacc_take_len]), hacc_take_len]
    have hrow_len : row.length = a.length + 1 := by rw [hrow, List.length_append, hp1_len]; simp
    set acc' : List (BitVec 64) := row.tail ++ acc.drop (a.length + 1) with hacc'
    -- The active-region length facts.
    have hlen_cons : (b0 :: bsv').length = bsv'.length + 1 := by simp
    -- Peel `set j := v`; the post-set state agrees with `s` on op/ap/bp/n and memory.
    obtain ⟨F0, hF0⟩ : ∃ F0, F = F0 + 1 := ⟨F - 1, by omega⟩
    set s0 : BignumState := setReg s "j" (BitVec.ofInt 64 (Int.ofNat v)) with hs0
    -- The run on the row block reduces (peel `set j`) to a run from `s0`.
    have hpeel : bignumExecFuel mulRegistry (F + 1)
        (mulOuterRows (v :: vs') ++ rest) s
        = bignumExecFuel mulRegistry (F + 1)
            (mulOuterBody ++ (mulOuterRows vs' ++ rest)) s0 := by
      rw [hs0]
      simp only [mulOuterRows, List.cons_append, setj_peel, List.append_assoc]
    have hs0_reg : ∀ x, x ≠ "j" → s0.regs x = s.regs x := by
      intro x hx; rw [hs0]; simp [setReg, hx]
    have hs0_mem : s0.mem = s.mem := by rw [hs0]; rfl
    have hs0_op : s0.regs "op" = s.regs "op" := hs0_reg "op" (by decide)
    have hs0_ap : s0.regs "ap" = s.regs "ap" := hs0_reg "ap" (by decide)
    have hs0_bp : s0.regs "bp" = s.regs "bp" := hs0_reg "bp" (by decide)
    have hs0_n : s0.regs "n" = s.regs "n" := hs0_reg "n" (by decide)
    -- The `(|a|+1)`-window disjointness from `[ap, 8|a|)`.
    have hwin_doa : MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (s0.regs "op").toNat) (8 * (a.length + 1)))
        (MemoryModel.range (UInt64.ofNat (s0.regs "ap").toNat) (8 * a.length)) := by
      rw [hs0_op, hs0_ap]
      refine disjoint_mono (fun x h => ?_) (fun x h => h) hdoa_ap
      obtain ⟨k, hk, rfl⟩ := h
      exact ⟨k, by simp only [hlen_cons]; omega, rfl⟩
    -- Per-row carry-window step (frame-carrying) at `s0`.
    obtain ⟨cf, hcf, hcf_row, hcf_frame⟩ :=
      mpnMul_per_row_carry_frame F s0 b0 (acc.take a.length) a hacc_take_len
        (by rw [hs0_n]; exact hn)
        (by rw [hs0_op, hs0_mem]; exact hwin0)
        (by rw [hs0_ap, hs0_mem]; exact ha)
        hwin_doa hF
    rw [← hp] at hcf_row
    -- One full outer-iteration body via `mulOuterBody_step`.
    have hbj0 : load64Mem s0.mem (regAddr s0 "bp") = some (UInt64.ofNat b0.toNat) := by
      rw [show regAddr s0 "bp" = UInt64.ofNat (s.regs "bp").toNat from by
        rw [regAddr, hs0_bp], hs0_mem]; exact hbp_head
    obtain ⟨s1, hs1_run, hs1_row, hs1_op, hs1_bp, hs1_other, hs1_mem⟩ :=
      mulOuterBody_step F (mulOuterRows vs' ++ rest) s0 b0 row cf hbj0
        (by rw [hs0_op]; exact hcf) (by rw [hs0_op]; exact hcf_row)
    -- `s1` registers: op/bp advanced; ap/n preserved.
    have hs1_ap : s1.regs "ap" = s.regs "ap" := by rw [hs1_other "ap" (by decide) (by decide), hs0_ap]
    have hs1_n : s1.regs "n" = s.regs "n" := by rw [hs1_other "n" (by decide) (by decide), hs0_n]
    have hs1_op' : s1.regs "op" = s.regs "op" + 8 := by rw [hs1_op, hs0_op]
    have hs1_bp' : s1.regs "bp" = s.regs "bp" + 8 := by rw [hs1_bp, hs0_bp]
    -- The frame relating `s1.mem` to `s.mem` (outside the row window [s.op, 8(|a|+1))).
    have hframe1 : ∀ bb, MemoryModel.Disjoint (range bb 8)
        (range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1))) →
        load64Mem s1.mem bb = load64Mem s.mem bb := by
      intro bb hbb
      rw [hs1_mem, hcf_frame bb (by rw [hs0_op]; exact hbb), hs0_mem]
    -- Address facts: `regAddr s1 "op" = ofNat(s.op) + ofNat 8`, etc.
    have hs1_op_addr : UInt64.ofNat (s1.regs "op").toNat
        = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat 8 := by
      rw [hs1_op', regAddr_add]; rfl
    have hs1_ap_addr : UInt64.ofNat (s1.regs "ap").toNat = UInt64.ofNat (s.regs "ap").toNat := by
      rw [hs1_ap]
    have hs1_bp_addr : UInt64.ofNat (s1.regs "bp").toNat
        = UInt64.ofNat (s.regs "bp").toNat + UInt64.ofNat 8 := by
      rw [hs1_bp', regAddr_add]; rfl
    -- The new accumulator length / zero-suffix.
    have hacc'_len : acc'.length = a.length + bsv'.length := by
      rw [hacc', List.length_append, List.length_tail, hrow_len, List.length_drop]
      simp only [List.length_cons] at hacclen
      omega
    have hrowtail_len : row.tail.length = a.length := by rw [List.length_tail, hrow_len]; omega
    have hacc'_zero : acc'.drop a.length = List.replicate bsv'.length 0 := by
      have hdrop1 : acc.drop (a.length + 1) = List.replicate bsv'.length 0 := by
        rw [← List.drop_drop, hacczero, List.length_cons, List.drop_replicate]; simp
      rw [hacc', List.drop_left' (by rw [hrowtail_len]), hdrop1]
    -- `row.tail` sits at `s.op + 8`, `acc.drop(|a|+1)` at `s.op + 8(|a|+1)`.
    have hdrop1_addr : acc.drop (a.length + 1) = List.replicate bsv'.length 0 := by
      rw [← List.drop_drop, hacczero, List.length_cons, List.drop_replicate]; simp
    have hrow_at_s1 : memHoldsLimbs s1.mem (UInt64.ofNat (s.regs "op").toNat) row := by
      rw [hs0_op] at hs1_row; exact hs1_row
    -- `memHoldsLimbs s1.mem (s.op) (row.headI :: row.tail) = row`, so its tail at s.op+8.
    have hrow_cons : row.headI :: row.tail = row := by rw [hrow]; cases p.1 <;> simp
    have hrowtail_at : memHoldsLimbs s1.mem (UInt64.ofNat (s.regs "op").toNat + 8) row.tail := by
      have := hrow_at_s1
      rw [← hrow_cons] at this
      exact this.2
    -- `acc.drop(|a|+1)` at `s.op + 8(|a|+1)` preserved (outside the row window).
    have hhigh_at : memHoldsLimbs s1.mem
        (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)))
        (acc.drop (a.length + 1)) := by
      -- In `s.mem`, the high suffix sits there (from `hrest0` split further).
      have hrest_split := (memHoldsLimbs_append s.mem
        (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * a.length))
        (acc.drop a.length |>.take 1) (acc.drop a.length |>.drop 1)).mp
        (by rw [List.take_append_drop]; exact hrest0)
      -- `acc.drop |a| = w0 :: acc.drop(|a|+1)` with `w0 = 0`; its tail at +8(|a|+1).
      have hdd : acc.drop a.length = (0 : BitVec 64) :: acc.drop (a.length + 1) := by
        rw [show a.length + 1 = a.length + 1 from rfl, ← List.drop_drop,
          show acc.drop a.length = (acc.drop a.length).headI :: (acc.drop a.length).tail from by
            rw [hacczero]; cases bsv' <;> simp [List.replicate_succ]]
        rw [hacczero]; cases bsv' <;> simp [List.replicate_succ, List.drop_replicate]
      have hin_s : memHoldsLimbs s.mem
          (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)))
          (acc.drop (a.length + 1)) := by
        have h2 := (memHoldsLimbs_append s.mem (UInt64.ofNat (s.regs "op").toNat)
          (acc.take a.length) (acc.drop a.length)).mp (by rw [List.take_append_drop]; exact hacc)
        rw [hacc_take_len] at h2
        rw [hdd] at h2
        obtain ⟨_, _, htail⟩ := h2
        rw [show UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * a.length) + 8
              = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)) from by
            rw [show 8 * (a.length + 1) = 8 * a.length + 8 from by ring, UInt64.ofNat_add,
              show (UInt64.ofNat 8 : UInt64) = 8 from rfl, ← UInt64.add_assoc]] at htail
        exact htail
      -- Transfer to `s1.mem` via the frame (the high suffix is past the row window).
      refine memHoldsLimbs_frame_disjoint s.mem s1.mem _ (UInt64.ofNat (s.regs "op").toNat)
        (8 * (a.length + 1)) _ (fun bb hbb => hframe1 bb hbb) ?_ hin_s
      -- `[s.op+8(|a|+1), s.op+8(|a|+1)+8|...|)` disjoint from `[s.op, 8(|a|+1))`.
      intro x ⟨⟨i, hi, hxi⟩, ⟨j, hj, hxj⟩⟩
      rw [show UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)) + UInt64.ofNat i
            = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1) + i) from by
          rw [UInt64.ofNat_add, ← UInt64.add_assoc]] at hxi
      rw [hxj] at hxi
      have hcancel := uint64_add_left_cancel (UInt64.ofNat (s.regs "op").toNat) _ _ hxi
      have heq := congrArg UInt64.toNat hcancel
      simp only [UInt64.toNat_ofNat'] at heq
      -- `i < 8·|acc.drop(|a|+1)| = 8·|bsv'|`, so `8(|a|+1)+i < 2^64`.
      have hi_len : (acc.drop (a.length + 1)).length = bsv'.length := by
        rw [hdrop1_addr, List.length_replicate]
      rw [hi_len] at hi
      have hfit' : 8 * (a.length + (b0 :: bsv').length) ≤ 2 ^ 64 := hfit
      simp only [List.length_cons] at hfit'
      have hlt1 : 8 * (a.length + 1) + i < 2 ^ 64 := by omega
      have hlt2 : j < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at heq
      omega
    -- Assemble `acc'` at `s1.op = s.op + 8`.
    have hacc'_at : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "op").toNat) acc' := by
      rw [hacc', hs1_op_addr]
      refine (memHoldsLimbs_append s1.mem _ row.tail (acc.drop (a.length + 1))).mpr ⟨?_, ?_⟩
      · rw [show (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat 8)
              = UInt64.ofNat (s.regs "op").toNat + 8 from by
            rw [show (UInt64.ofNat 8 : UInt64) = 8 from rfl]]
        exact hrowtail_at
      · rw [show row.tail.length = a.length from by rw [List.length_tail, hrow_len]; omega,
          show UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat 8 + UInt64.ofNat (8 * a.length)
            = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)) from by
            rw [show 8 * (a.length + 1) = 8 + 8 * a.length from by ring, UInt64.ofNat_add,
              show (UInt64.ofNat 8 : UInt64) = 8 from rfl, ← UInt64.add_assoc]]
        exact hhigh_at
    -- A shift-by-8 subset map: `[base+8, base+8+8m) ⊆ [base, base+8(m+1))`.
    have hshift8 : ∀ (base : UInt64) (m : Nat) (x : UInt64),
        range (base + UInt64.ofNat 8) (8 * m) x → range base (8 * (m + 1)) x := by
      intro base m x h
      obtain ⟨k, hk, rfl⟩ := h
      refine ⟨8 + k, by omega, ?_⟩
      rw [UInt64.ofNat_add, ← UInt64.add_assoc]
    have hlc8a : 8 * (a.length + (b0 :: bsv').length) = 8 * (a.length + bsv'.length + 1) := by
      simp only [List.length_cons]; omega
    have hlc8b : 8 * (b0 :: bsv').length = 8 * (bsv'.length + 1) := by
      simp only [List.length_cons]
    -- IH disjointness hypotheses at `s1` (op'=s.op+8, ap=s.ap, bp'=s.bp+8).
    have hdoa_ap' : MemoryModel.Disjoint
        (range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + bsv'.length)))
        (range (UInt64.ofNat (s1.regs "ap").toNat) (8 * a.length)) := by
      rw [hs1_op_addr, hs1_ap_addr]
      refine disjoint_mono (fun x h => ?_) (fun x h => h) hdoa_ap
      rw [hlc8a]; exact hshift8 _ (a.length + bsv'.length) x h
    have hdoa_bp' : MemoryModel.Disjoint
        (range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + bsv'.length)))
        (range (UInt64.ofNat (s1.regs "bp").toNat) (8 * bsv'.length)) := by
      rw [hs1_op_addr, hs1_bp_addr]
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa_bp
      · rw [hlc8a]; exact hshift8 _ (a.length + bsv'.length) x h
      · rw [hlc8b]; exact hshift8 _ bsv'.length x h
    have hap_bp' : MemoryModel.Disjoint
        (range (UInt64.ofNat (s1.regs "ap").toNat) (8 * a.length))
        (range (UInt64.ofNat (s1.regs "bp").toNat) (8 * bsv'.length)) := by
      rw [hs1_ap_addr, hs1_bp_addr]
      refine disjoint_mono (fun x h => h) (fun x h => ?_) hap_bp
      rw [hlc8b]; exact hshift8 _ bsv'.length x h
    have hfit' : 8 * (a.length + bsv'.length) ≤ 2 ^ 64 := by
      simp only [List.length_cons] at hfit; omega
    -- The row window `[s.op, 8(|a|+1))` ⊆ the active region `[s.op, 8(|a|+|b0::bsv'|))`.
    have hwin_sub_active : ∀ x, range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)) x →
        range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + (b0 :: bsv').length)) x := by
      intro x h; obtain ⟨k, hk, rfl⟩ := h
      exact ⟨k, by simp only [List.length_cons]; omega, rfl⟩
    -- `a` preserved at `s1.ap` (disjoint from the row window) and `bsv'` at `s1.bp`.
    have ha1 : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "ap").toNat) a := by
      rw [hs1_ap_addr]
      refine memHoldsLimbs_frame_disjoint s.mem s1.mem _ (UInt64.ofNat (s.regs "op").toNat)
        (8 * (a.length + 1)) _ (fun bb hbb => hframe1 bb hbb) ?_ ha
      -- ap-region disjoint from row window (⊆ active region disjoint from ap).
      exact disjoint_mono (fun x h => h) hwin_sub_active (MemoryModel.Disjoint.symm hdoa_ap)
    have hbp1 : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "bp").toNat) bsv' := by
      rw [hs1_bp_addr,
        show UInt64.ofNat (s.regs "bp").toNat + UInt64.ofNat 8
          = UInt64.ofNat (s.regs "bp").toNat + 8 from by
          rw [show (UInt64.ofNat 8 : UInt64) = 8 from rfl]]
      refine memHoldsLimbs_frame_disjoint s.mem s1.mem _ (UInt64.ofNat (s.regs "op").toNat)
        (8 * (a.length + 1)) _ (fun bb hbb => hframe1 bb hbb) ?_ hbp_tail
      -- `[bp+8, bp+8+8|bsv'|)` disjoint from row window.
      refine disjoint_mono (fun x h => ?_) hwin_sub_active (MemoryModel.Disjoint.symm hdoa_bp)
      -- `[bp+8, …8|bsv'|) ⊆ [bp, …8|b0::bsv'|)`.
      obtain ⟨k, hk, rfl⟩ := h
      refine ⟨8 + k, by simp only [List.length_cons]; omega, ?_⟩
      rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, UInt64.ofNat_add, ← UInt64.add_assoc]
    -- Apply the IH.
    obtain ⟨s2, hs2_run, hs2_acc, hs2_op, hs2_bp, hs2_n, hs2_ap, hs2_frame⟩ :=
      ih vs' a acc' rest s1 F hvs' hacc'_len hacc'_zero (by rw [hs1_n]; exact hn)
        hacc'_at ha1 hbp1 hdoa_ap' hdoa_bp' hap_bp' hfit' hF
    -- Assemble the conclusion.
    refine ⟨s2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpeel, hs1_run, hs2_run]
    · -- The result region holds `mulAcc a (b0 :: bsv') acc`.
      show memHoldsLimbs s2.mem (UInt64.ofNat (s.regs "op").toNat) (mulAcc a (b0 :: bsv') acc)
      have hmulacc_unfold : mulAcc a (b0 :: bsv') acc = row.headI :: mulAcc a bsv' acc' := by
        rw [mulAcc]
      rw [hmulacc_unfold]
      refine ⟨?_, ?_⟩
      · -- `row.headI` at `s.op`: from `hrow_at_s1` head, preserved by IH frame.
        have hhead_s1 : load64Mem s1.mem (UInt64.ofNat (s.regs "op").toNat)
            = some (UInt64.ofNat row.headI.toNat) := by
          have := hrow_at_s1; rw [← hrow_cons] at this; exact this.1
        rw [hs2_frame (UInt64.ofNat (s.regs "op").toNat) ?_]
        · exact hhead_s1
        · -- `[s.op, 8)` disjoint from `[s1.op = s.op+8, 8(|a|+|bsv'|))`.
          rw [hs1_op_addr]
          intro x ⟨⟨i, hi, hxi⟩, ⟨j, hj, hxj⟩⟩
          rw [show UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat 8 + UInt64.ofNat j
                = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 + j) from by
              rw [UInt64.ofNat_add, ← UInt64.add_assoc]] at hxj
          rw [hxi] at hxj
          have hcancel := uint64_add_left_cancel (UInt64.ofNat (s.regs "op").toNat) _ _ hxj
          have := congrArg UInt64.toNat hcancel
          simp only [UInt64.toNat_ofNat'] at this
          omega
      · -- `mulAcc a bsv' acc'` at `s.op + 8 = s1.op`.
        rw [show UInt64.ofNat (s.regs "op").toNat + 8
              = UInt64.ofNat (s1.regs "op").toNat from by
            rw [hs1_op_addr, show (UInt64.ofNat 8 : UInt64) = 8 from rfl]]
        exact hs2_acc
    · -- `op` advanced by `8 * (b0 :: bsv').length`.
      rw [hs2_op, hs1_op']
      rw [show 8 * (b0 :: bsv').length = 8 + 8 * bsv'.length from by simp only [List.length_cons]; ring,
        BitVec.ofNat_add, show (BitVec.ofNat 64 8 : BitVec 64) = 8 from rfl, ← BitVec.add_assoc]
    · rw [hs2_bp, hs1_bp']
      rw [show 8 * (b0 :: bsv').length = 8 + 8 * bsv'.length from by simp only [List.length_cons]; ring,
        BitVec.ofNat_add, show (BitVec.ofNat 64 8 : BitVec 64) = 8 from rfl, ← BitVec.add_assoc]
    · rw [hs2_n, hs1_n]
    · rw [hs2_ap, hs1_ap]
    · -- Frame: compose IH frame (over [s1.op, ...)) with `hframe1` (over [s.op, 8(|a|+1))).
      intro bb hbb
      -- `bb` disjoint from `[s.op, 8(|a|+|b0::bsv'|))` ⟹ disjoint from `[s1.op, 8(|a|+|bsv'|))`
      -- and from `[s.op, 8(|a|+1))`.
      have hbb_s1 : MemoryModel.Disjoint (range bb 8)
          (range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + bsv'.length))) := by
        rw [hs1_op_addr]
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        obtain ⟨k, hk, rfl⟩ := h
        refine ⟨8 + k, by simp only [List.length_cons]; omega, ?_⟩
        rw [UInt64.ofNat_add, ← UInt64.add_assoc]
      have hbb_win : MemoryModel.Disjoint (range bb 8)
          (range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1))) := by
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        obtain ⟨k, hk, rfl⟩ := h
        exact ⟨k, by simp only [List.length_cons]; omega, rfl⟩
      rw [hs2_frame bb hbb_s1, hframe1 bb hbb_win]

/-! ### §5.6  Row 0 (`mpn_mul_1` Ccall) + `Cfor`-unroll glue -/

/-- The `Ccall mpn_mul_1` reduction (row 0): mirror of `outer_ccall_reduce` for
    the `mpn_mul_1` kernel.  Running `mulBody`'s prefix `[Ccall mpn_mul_1 …]` then
    the bumps `[op += 8; bp += 8]` from `s` equals running `rest` from the
    callee's post-state with `op`/`bp` advanced. -/
theorem mulRow0_step (f : Nat) (rest : List InstrR) (s : BignumState) (bj : BitVec 64)
    (row : List (BitVec 64)) (cf : BignumState)
    (hbj : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat bj.toNat))
    (hcf : bignumExecFuel mulRegistry f mpnMul1CarryFd.body
        { regs := fun name => match mpnMul1CarryFd.params.findIdx? (·.var.var.vname = name) with
                              | some idx =>
                                  (([s.regs "op", s.regs "ap", bj, s.regs "n"] : List (BitVec 64))[idx]?).getD 0
                              | none => 0
        , mem := s.mem } = some cf)
    (hcf_row : memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) row) :
    ∃ s',
      bignumExecFuel mulRegistry (f + 1)
        (.Ccall .DoNotInline [] { name := "mpn_mul_1" }
          [ pv "op", pv "ap", .Pload .U64 { var := vr "bp" } (.Pconst 0), pv "n" ]
          :: [binImm "op" (.Oadd .U64) 8, binImm "bp" (.Oadd .U64) 8] ++ rest) s
        = bignumExecFuel mulRegistry (f + 1) rest s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) row ∧
      s'.regs "op" = s.regs "op" + 8 ∧ s'.regs "bp" = s.regs "bp" + 8 ∧
      (∀ x, x ≠ "op" → x ≠ "bp" → s'.regs x = s.regs x) ∧
      s'.mem = cf.mem := by
  set s1 : BignumState := { regs := s.regs, mem := cf.mem } with hs1
  refine ⟨setReg (setReg s1 "op" (s1.regs "op" + 8)) "bp" (s1.regs "bp" + 8), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Ccall reduction (mul1) then bump-peel.
    rw [List.cons_append, bignumExecFuel, mulRegistry_mul, addmul_args_eval s bj hbj]
    simp only [List.isEmpty_nil, if_true]
    split
    · rename_i hrun; exact absurd (hcf.symm.trans hrun) (by simp)
    · rename_i cf' hrun
      have hcf'_eq : cf' = cf := Option.some.inj (hrun.symm.trans hcf)
      rw [hcf'_eq, ← hs1, bumps_peel f rest s1]
  · rw [show (setReg (setReg s1 "op" (s1.regs "op" + 8)) "bp" (s1.regs "bp" + 8)).mem = cf.mem
          from rfl]
    exact hcf_row
  · simp only [setReg, hs1, show ("op" = "bp") = False from by simp, if_false, if_true]
  · simp only [setReg, hs1, if_true]
  · intro x hop hbp
    simp only [setReg, hs1, if_neg hbp, if_neg hop]
  · rfl

/-- The `Cfor` body `unrollFor {j} {UpTo,1,m} mulOuterBody` is exactly
    `mulOuterRows` of the counter values `1, 2, …, m-1`. -/
theorem unrollFor_eq_mulOuterRows (m : Nat) :
    unrollFor { var := vr "j" } { dir := .UpTo, lo := 1, hi := m } mulOuterBody
      = mulOuterRows ((List.range (m - 1)).map (1 + ·)) := by
  have hmor : ∀ l : List Nat, mulOuterRows l
      = l.flatMap (fun k => mkSetVarConst { var := vr "j" } k :: mulOuterBody) := by
    intro l
    induction l with
    | nil => rfl
    | cons k ks ih =>
      simp only [mulOuterRows, List.flatMap_cons, ih, List.cons_append, List.append_assoc]
  rw [hmor, List.flatMap_map]
  simp only [unrollFor]

/-- **Residual B — the full outer-loop refinement (`MpnMulJasminRefines`).**
    Starting from a state whose memory holds `a` at `ap`, `b` at `bp`, a zeroed
    `|a|+|b|`-limb result region at `op`, with `n=|a|`, and the three regions
    pairwise disjoint, running `mulBody |b|` under `mulRegistry` lands in a
    state whose result region holds the pure product `mpnMul a b`.

    With the carry-drop bug fixed this statement is **true** (the positive
    end-to-end checks above witness it on concrete carry-crossing inputs).  The
    per-row interpreter blocker is now **gone**: Residual A
    (`mpnMul_per_row_carry`) is fully proved — one carry-storing-kernel `Ccall`
    writes the full `|a|+1`-limb row — using the new fuel-monotonicity
    sequencing lemmas (`bignumExecFuel_mono` / `bignumExecFuel_seq`) added to
    `BignumExec`.  A closed proof of this outer refinement composes, by induction
    over `b`'s limbs:
      * row 0 via the `mpn_mul_1` `Ccall` (a `mpnMul1`-flavoured analogue of
        `mpnMul_per_row_carry`, identical in shape);
      * rows `1 .. |b|-1` via `mulOuterBody_step` (proved) fed by
        `mpnMul_per_row_carry` (Residual A, proved);
      * the **result-window frame**: the finalized prefix `[op, op+8·j)` is
        disjoint from the active window `[op+8·j, op+8·j+8·(|a|+1))`, so earlier
        rows survive later stores (the dual of the input-region frame the
        single-loop bridges carry);
      * the **value computation**: the windowed in-place accumulation lands a
        `|a|+|b|`-limb result with `toNat = toNat a · toNat b`.  By `toNat_inj`
        (proved) that result *is* `mpnMul a b` (which `mpnMul_contract` certifies
        has exactly that length and value) — so no structural match against
        `mpnMul`'s `mpnAddN` form is needed, only the partial-product value
        tracked through the loop.

    What remains is purely the outer-loop interpreter induction wiring these
    proved pieces together (the per-row blocker that broke prior attempts is
    resolved); no new interpreter lemma is missing. -/
def mpnMul_outer_loop_obligation : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    0 < b.length →
    8 * (a.length + b.length) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ s' fuel, bignumExecFuel mulRegistry fuel (mulBody b.length) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnMul a b)

/-! **`MpnMulJasminRefines`** is the canonical bridge goal for the carry-fixed
    `mpn_mul` body, identified with the outer-loop refinement
    `mpnMul_outer_loop_obligation` (Residual B), now discharged as the theorem
    `mpnMul_outer_loop_holds` below. -/
/-- **The full outer-loop refinement — PROVED.**  `mpnMul_outer_loop_obligation`
    holds: running the carry-fixed `mpn_mul` body `mulBody |b|` (row 0 via the
    `mpn_mul_1` `Ccall`, rows `1..|b|-1` via the `mpn_addmul_1` `Cfor`) under
    `mulRegistry` lands a result region holding the pure product `mpnMul a b`.

    Assembled from: row 0 (`mpnMul1_per_row_carry_frame` + `mulRow0_step`,
    using `mpnMul1_eq_mpnAddmul1_replicate` to identify it with `mulAcc`'s first
    step), the `Cfor` over rows `1..|b|-1` (`unrollFor_eq_mulOuterRows` +
    `mulOuter_rows`), and the value identification (`mulAcc_zero_eq_mpnMul` via
    `toNat_inj` + `mpnMul_contract`).  Requires the GMP precondition `m = |b| ≥ 1`
    and a non-wraparound layout (`8·(|a|+|b|) ≤ 2^64`). -/
theorem mpnMul_outer_loop_holds : mpnMul_outer_loop_obligation := by
  intro s a b hbpos hfit hn ha hb hres hdoa_ap hdoa_bp hap_bp
  -- `b = b0 :: brest`.
  cases b with
  | nil => simp at hbpos
  | cons b0 brest =>
  -- Window content of row 0 is the (zeroed) low `|a|` limbs.
  set acc0 : List (BitVec 64) := List.replicate (a.length + (b0 :: brest).length) 0 with hacc0
  have hacc0_len : acc0.length = a.length + (b0 :: brest).length := by
    rw [hacc0, List.length_replicate]
  have hacc0_zero : acc0.drop a.length = List.replicate (b0 :: brest).length 0 := by
    rw [hacc0, List.drop_replicate]; congr 1; omega
  -- The op-region currently holds `acc0` (= `hres`).
  have hres' : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) acc0 := hres
  -- Window `acc0.take |a|` and high suffix.
  have htake0 : acc0.take a.length = List.replicate a.length 0 := by
    rw [hacc0, List.take_replicate]; congr 1; omega
  have hwin0 : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) (acc0.take a.length) := by
    have := (memHoldsLimbs_append s.mem (UInt64.ofNat (s.regs "op").toNat)
      (acc0.take a.length) (acc0.drop a.length)).mp (by rw [List.take_append_drop]; exact hres')
    exact this.1
  -- `b0` at `bp`.
  obtain ⟨hbp_head, hbp_tail⟩ := hb
  -- Row-0 window disjointness from `[ap, 8|a|)`.
  have hwin_doa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) := by
    refine disjoint_mono (fun x h => ?_) (fun x h => h) hdoa_ap
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by simp only [List.length_cons]; omega, rfl⟩
  -- Choose fuel.  Row 0 needs `F > 2|a|+3`; the Cfor needs the same `F` per row.
  set F : Nat := 2 * a.length + 4 with hF
  have hFgt : F > 2 * a.length + 3 := by omega
  -- Row 0: the carry-storing `mpn_mul_1` kernel writes the full `|a|+1`-limb row.
  have hFgt1 : F + 1 > 2 * a.length + 3 := by omega
  obtain ⟨cf0, hcf0, hcf0_row, hcf0_frame⟩ :=
    mpnMul1_per_row_carry_frame (F + 1) s b0 a hn ha hwin_doa hFgt1
  -- The row-0 window content is `mpnMul1 a b0 0` (= `mpnAddmul1 (replicate |a| 0) …`).
  -- This matches `mulAcc`'s first step `p = mpnAddmul1 (acc0.take|a|) a b0 0`.
  set p0 : List (BitVec 64) × BitVec 64 := mpnMul1 a b0 0 with hp0
  set row0 : List (BitVec 64) := p0.1 ++ [p0.2] with hrow0
  have hbj0 : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b0.toNat) := hbp_head
  -- Run row 0 + the bumps via `mulRow0_step`.
  obtain ⟨s1, hs1_run, hs1_row, hs1_op, hs1_bp, hs1_other, hs1_mem⟩ :=
    mulRow0_step (F + 1) [.Cfor { var := vr "j" } { dir := .UpTo, lo := 1, hi := (b0 :: brest).length }
        mulOuterBody] s b0 row0 cf0 hbj0 (by rw [hp0, ← hrow0] at *; exact hcf0)
      (by rw [hp0, ← hrow0] at *; exact hcf0_row)
  -- `s1` registers.
  have hs1_ap : s1.regs "ap" = s.regs "ap" := by rw [hs1_other "ap" (by decide) (by decide)]
  have hs1_n : s1.regs "n" = s.regs "n" := by rw [hs1_other "n" (by decide) (by decide)]
  -- The mulAcc first step: `p = mpnAddmul1 (acc0.take|a|) a b0 0 = mpnMul1 a b0 0 = p0`.
  have hmulacc1 : mulAcc a (b0 :: brest) acc0 = row0.headI ::
      mulAcc a brest (row0.tail ++ acc0.drop (a.length + 1)) := by
    have hp_eq : mpnAddmul1 (acc0.take a.length) a b0 0 = p0 := by
      rw [htake0, ← mpnMul1_eq_mpnAddmul1_replicate, hp0]
    rw [mulAcc]
    simp only [hp_eq, ← hrow0]
  -- The new accumulator after row 0.
  set acc1 : List (BitVec 64) := row0.tail ++ acc0.drop (a.length + 1) with hacc1
  -- Length / zero-suffix / lengths of `acc1`.
  have hrow0_len : row0.length = a.length + 1 := by
    rw [hrow0, List.length_append, hp0, mpnMul1_length]; simp
  have hrowtail0_len : row0.tail.length = a.length := by rw [List.length_tail, hrow0_len]; omega
  have hacc1_len : acc1.length = a.length + brest.length := by
    rw [hacc1, List.length_append, hrowtail0_len, List.length_drop, hacc0_len]
    simp only [List.length_cons]; omega
  have hdrop0 : acc0.drop (a.length + 1) = List.replicate brest.length 0 := by
    rw [← List.drop_drop, hacc0_zero, List.length_cons, List.drop_replicate]; simp
  have hacc1_zero : acc1.drop a.length = List.replicate brest.length 0 := by
    rw [hacc1, List.drop_left' (by rw [hrowtail0_len]), hdrop0]
  -- The result region after row 0 holds `acc1` at `op+8`, with `a`/`brest` framed.
  have hs1_op_addr : UInt64.ofNat (s1.regs "op").toNat
      = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat 8 := by
    rw [hs1_op, regAddr_add]; rfl
  have hs1_bp_addr : UInt64.ofNat (s1.regs "bp").toNat
      = UInt64.ofNat (s.regs "bp").toNat + UInt64.ofNat 8 := by
    rw [hs1_bp, regAddr_add]; rfl
  -- The frame `s1.mem` vs `s.mem` outside the row-0 window.
  have hframe0 : ∀ bb, MemoryModel.Disjoint (range bb 8)
      (range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1))) →
      load64Mem s1.mem bb = load64Mem s.mem bb := by
    intro bb hbb; rw [hs1_mem]; exact hcf0_frame bb hbb
  -- `row0.tail` at `s.op+8`; `acc0.drop(|a|+1)` at `s.op+8(|a|+1)` framed.
  have hrowtail0_at : memHoldsLimbs s1.mem (UInt64.ofNat (s.regs "op").toNat + 8) row0.tail := by
    have hrc : row0.headI :: row0.tail = row0 := by rw [hrow0]; cases p0.1 <;> simp
    have := hs1_row; rw [← hrc] at this; exact this.2
  have hhigh0_at : memHoldsLimbs s1.mem
      (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)))
      (acc0.drop (a.length + 1)) := by
    -- In `s.mem`, the high suffix sits there; transfer via `hframe0`.
    have hin_s : memHoldsLimbs s.mem
        (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)))
        (acc0.drop (a.length + 1)) := by
      have hsplit := (memHoldsLimbs_append s.mem (UInt64.ofNat (s.regs "op").toNat)
        (acc0.take (a.length + 1)) (acc0.drop (a.length + 1))).mp
        (by rw [List.take_append_drop]; exact hres')
      have htk1 : (acc0.take (a.length + 1)).length = a.length + 1 := by
        rw [List.length_take, hacc0_len]; simp only [List.length_cons]; omega
      rw [htk1] at hsplit
      exact hsplit.2
    refine memHoldsLimbs_frame_disjoint s.mem s1.mem _ (UInt64.ofNat (s.regs "op").toNat)
      (8 * (a.length + 1)) _ (fun bb hbb => hframe0 bb hbb) ?_ hin_s
    intro x ⟨⟨i, hi, hxi⟩, ⟨j, hj, hxj⟩⟩
    rw [show UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)) + UInt64.ofNat i
          = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1) + i) from by
        rw [UInt64.ofNat_add, ← UInt64.add_assoc]] at hxi
    rw [hxj] at hxi
    have hcancel := uint64_add_left_cancel (UInt64.ofNat (s.regs "op").toNat) _ _ hxi
    have heq := congrArg UInt64.toNat hcancel
    simp only [UInt64.toNat_ofNat'] at heq
    have hi_len : (acc0.drop (a.length + 1)).length = brest.length := by
      rw [hdrop0, List.length_replicate]
    rw [hi_len] at hi
    have hfit' : 8 * (a.length + (b0 :: brest).length) ≤ 2 ^ 64 := hfit
    simp only [List.length_cons] at hfit'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
    omega
  have hacc1_at : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "op").toNat) acc1 := by
    rw [hacc1, hs1_op_addr]
    refine (memHoldsLimbs_append s1.mem _ row0.tail (acc0.drop (a.length + 1))).mpr ⟨?_, ?_⟩
    · rw [show UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat 8
            = UInt64.ofNat (s.regs "op").toNat + 8 from by
          rw [show (UInt64.ofNat 8 : UInt64) = 8 from rfl]]
      exact hrowtail0_at
    · rw [hrowtail0_len,
        show UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat 8 + UInt64.ofNat (8 * a.length)
          = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (a.length + 1)) from by
          rw [show 8 * (a.length + 1) = 8 + 8 * a.length from by ring, UInt64.ofNat_add,
            show (UInt64.ofNat 8 : UInt64) = 8 from rfl, ← UInt64.add_assoc]]
      exact hhigh0_at
  -- `a` / `brest` preserved at `s1`.
  have hwin_sub_active0 : ∀ x, range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)) x →
      range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + (b0 :: brest).length)) x := by
    intro x h; obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by simp only [List.length_cons]; omega, rfl⟩
  have ha1 : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "ap").toNat) a := by
    rw [hs1_ap]
    refine memHoldsLimbs_frame_disjoint s.mem s1.mem _ (UInt64.ofNat (s.regs "op").toNat)
      (8 * (a.length + 1)) _ (fun bb hbb => hframe0 bb hbb) ?_ ha
    exact disjoint_mono (fun x h => h) hwin_sub_active0 (MemoryModel.Disjoint.symm hdoa_ap)
  have hbp1 : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "bp").toNat) brest := by
    rw [hs1_bp_addr,
      show UInt64.ofNat (s.regs "bp").toNat + UInt64.ofNat 8
        = UInt64.ofNat (s.regs "bp").toNat + 8 from by
        rw [show (UInt64.ofNat 8 : UInt64) = 8 from rfl]]
    refine memHoldsLimbs_frame_disjoint s.mem s1.mem _ (UInt64.ofNat (s.regs "op").toNat)
      (8 * (a.length + 1)) _ (fun bb hbb => hframe0 bb hbb) ?_ hbp_tail
    refine disjoint_mono (fun x h => ?_) hwin_sub_active0 (MemoryModel.Disjoint.symm hdoa_bp)
    obtain ⟨k, hk, rfl⟩ := h
    refine ⟨8 + k, by simp only [List.length_cons]; omega, ?_⟩
    rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, UInt64.ofNat_add, ← UInt64.add_assoc]
  -- IH-shape disjointness at `s1` for the `Cfor` (rows 1..).
  have hlc8a : 8 * (a.length + (b0 :: brest).length) = 8 * (a.length + brest.length + 1) := by
    simp only [List.length_cons]; omega
  have hlc8b : 8 * (b0 :: brest).length = 8 * (brest.length + 1) := by simp only [List.length_cons]
  have hshift8 : ∀ (base : UInt64) (m : Nat) (x : UInt64),
      range (base + UInt64.ofNat 8) (8 * m) x → range base (8 * (m + 1)) x := by
    intro base m x h; obtain ⟨k, hk, rfl⟩ := h
    refine ⟨8 + k, by omega, ?_⟩; rw [UInt64.ofNat_add, ← UInt64.add_assoc]
  have hdoa_ap1 : MemoryModel.Disjoint
      (range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + brest.length)))
      (range (UInt64.ofNat (s1.regs "ap").toNat) (8 * a.length)) := by
    rw [hs1_op_addr, hs1_ap]
    refine disjoint_mono (fun x h => ?_) (fun x h => h) hdoa_ap
    rw [hlc8a]; exact hshift8 _ (a.length + brest.length) x h
  have hdoa_bp1 : MemoryModel.Disjoint
      (range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + brest.length)))
      (range (UInt64.ofNat (s1.regs "bp").toNat) (8 * brest.length)) := by
    rw [hs1_op_addr, hs1_bp_addr]
    refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa_bp
    · rw [hlc8a]; exact hshift8 _ (a.length + brest.length) x h
    · rw [hlc8b]; exact hshift8 _ brest.length x h
  have hap_bp1 : MemoryModel.Disjoint
      (range (UInt64.ofNat (s1.regs "ap").toNat) (8 * a.length))
      (range (UInt64.ofNat (s1.regs "bp").toNat) (8 * brest.length)) := by
    rw [hs1_ap, hs1_bp_addr]
    refine disjoint_mono (fun x h => h) (fun x h => ?_) hap_bp
    rw [hlc8b]; exact hshift8 _ brest.length x h
  have hfit1 : 8 * (a.length + brest.length) ≤ 2 ^ 64 := by
    simp only [List.length_cons] at hfit; omega
  -- Apply the `Cfor` outer-loop induction (`mulOuter_rows`), `rest = []`.
  set vs : List Nat := (List.range (brest.length)).map (1 + ·) with hvs
  have hvs_len : vs.length = brest.length := by rw [hvs, List.length_map, List.length_range]
  obtain ⟨s2, hs2_run, hs2_acc, _, _, _, _, hs2_frame⟩ :=
    mulOuter_rows brest vs a acc1 [] s1 F hvs_len hacc1_len hacc1_zero (by rw [hs1_n]; exact hn)
      hacc1_at ha1 hbp1 hdoa_ap1 hdoa_bp1 hap_bp1 hfit1 hFgt
  -- Connect the run: row 0 + bumps + Cfor unroll + mulOuter_rows.
  refine ⟨s2, F + 2, ?_, ?_⟩
  · -- The full `mulBody` run = row0 + bumps + Cfor(unroll) + mulOuter_rows.
    rw [show F + 2 = (F + 1) + 1 from by omega, mulBody]
    -- `mulBody` = `Ccall :: [bump, bump] ++ [Cfor]`; apply `mulRow0_step` (= `hs1_run`).
    rw [show ([.Ccall .DoNotInline [] { name := "mpn_mul_1" }
            [ pv "op", pv "ap", .Pload .U64 { var := vr "bp" } (.Pconst 0), pv "n" ],
          binImm "op" (.Oadd .U64) 8, binImm "bp" (.Oadd .U64) 8,
          .Cfor { var := vr "j" } { dir := .UpTo, lo := 1, hi := (b0 :: brest).length } mulOuterBody]
        : List InstrR)
        = (.Ccall .DoNotInline [] { name := "mpn_mul_1" }
            [ pv "op", pv "ap", .Pload .U64 { var := vr "bp" } (.Pconst 0), pv "n" ]
          :: [binImm "op" (.Oadd .U64) 8, binImm "bp" (.Oadd .U64) 8]
          ++ [.Cfor { var := vr "j" } { dir := .UpTo, lo := 1, hi := (b0 :: brest).length } mulOuterBody])
        from rfl]
    rw [hs1_run]
    -- The `Cfor` arm: `(F+1)+1` → run `unrollFor ++ []` at `F+1`.
    rw [show (F + 1) + 1 = F + 1 + 1 from rfl, bignumExecFuel]
    rw [show unrollFor { var := vr "j" }
          { dir := .UpTo, lo := 1, hi := (b0 :: brest).length } mulOuterBody
          = mulOuterRows vs from by
        rw [unrollFor_eq_mulOuterRows, hvs, show (b0 :: brest).length - 1 = brest.length from by
          simp only [List.length_cons]; omega]]
    rw [hs2_run]
    -- `bignumExecFuel _ (F+1) [] s2 = some s2`.
    simp only [bignumExecFuel]
  · -- The result region holds `mpnMul a (b0 :: brest)`.
    -- `mulAcc a (b0::brest) acc0 = mpnMul a (b0::brest)` (zeroed region).
    have hmpn : mpnMul a (b0 :: brest) = mulAcc a (b0 :: brest) acc0 := by
      rw [hacc0]
      exact (mulAcc_zero_eq_mpnMul a (b0 :: brest)).symm
    rw [hmpn, hmulacc1]
    -- `s2.mem` holds `row0.headI :: mulAcc a brest acc1` at `s.op`.
    refine ⟨?_, ?_⟩
    · -- `row0.headI` at `s.op` survives the rest (via `mulOuter_rows` frame).
      have hrc : row0.headI :: row0.tail = row0 := by rw [hrow0]; cases p0.1 <;> simp
      have hhead_s1 : load64Mem s1.mem (UInt64.ofNat (s.regs "op").toNat)
          = some (UInt64.ofNat row0.headI.toNat) := by
        have := hs1_row; rw [← hrc] at this; exact this.1
      rw [hs2_frame (UInt64.ofNat (s.regs "op").toNat) ?_]
      · exact hhead_s1
      · -- `[s.op, 8)` disjoint from `[s1.op = s.op+8, 8(|a|+|brest|))`.
        rw [hs1_op_addr]
        intro x ⟨⟨i, hi, hxi⟩, ⟨j, hj, hxj⟩⟩
        rw [show UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat 8 + UInt64.ofNat j
              = UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 + j) from by
            rw [UInt64.ofNat_add, ← UInt64.add_assoc]] at hxj
        rw [hxi] at hxj
        have hcancel := uint64_add_left_cancel (UInt64.ofNat (s.regs "op").toNat) _ _ hxj
        have := congrArg UInt64.toNat hcancel
        simp only [UInt64.toNat_ofNat'] at this
        omega
    · -- `mulAcc a brest acc1` at `s.op + 8 = s1.op`.
      rw [show UInt64.ofNat (s.regs "op").toNat + 8 = UInt64.ofNat (s1.regs "op").toNat from by
          rw [hs1_op_addr, show (UInt64.ofNat 8 : UInt64) = 8 from rfl]]
      exact hs2_acc

abbrev MpnMulJasminRefines : Prop := mpnMul_outer_loop_obligation

/-- **`MpnMulJasminRefines` holds — the full Jasmin bridge for `mpn_mul`.**
    The carry-fixed emitted `mpn_mul` body refines the pure schoolbook product
    `mpnMul a b` over byte memory (GMP precondition `m = |b| ≥ 1`, non-wraparound
    layout `8·(|a|+|b|) ≤ 2^64`).  Discharged by `mpnMul_outer_loop_holds`. -/
theorem MpnMulJasminRefines_holds : MpnMulJasminRefines := mpnMul_outer_loop_holds

/-! ### Axiom audit

No `sorryAx` anywhere in this file.

  * The pure correctness theorems (`mpnMul_toNat`, `mpnMul_contract`) and the
    registry-independence lemmas (`bignumExecFuel_registry_irrel`,
    `addmul_registry_irrel`) depend only on the standard kernel axioms
    `propext`, `Classical.choice`, `Quot.sound`.
  * `addmul_ccall_step` (the cross-call discharge of the void kernel body's low
    `|a|` limbs), the loop-final-`op` lemma `addmul_loop_op`, and the per-row
    carry-window step `mpnMul_per_row_carry` (Residual A) additionally inherit the
    `bv_decide` native axioms (`disjoint_range_lt._native.bv_decide.ax_*`,
    `load64Mem_store64_same._native.bv_decide.ax_*`) that the *imported*
    single-loop bridge `MpnAddmul1JasminRefines` and the memory lemmas already
    carry — no new trust is introduced.  The per-row plumbing step
    `mulOuterBody_step` and the pure uniqueness lemma `toNat_inj` are pure
    (`propext`, `Quot.sound` only).
  * The fuel-monotonicity sequencing lemmas `bignumExecFuel_mono` /
    `bignumExecFuel_seq` (in `BignumExec`) that enable Residual A are axiom-clean
    (`propext`, `Quot.sound`).
  * The carry-drop fix is exercised by the end-to-end `native_decide` checks
    (including the carry-crossing `[2^63]·[4,0] = [0,2,0]`). -/

#print axioms bignumExecFuel_registry_irrel
#print axioms addmul_registry_irrel
#print axioms addmul_ccall_step
#print axioms addmul_loop_op
#print axioms mulOuterBody_step
#print axioms toNat_inj
#print axioms mpnMul_per_row_carry
#print axioms mpnMul_per_row_carry_obligation_holds
#print axioms mulOuter_rows
#print axioms mpnMul_outer_loop_holds
#print axioms MpnMulJasminRefines_holds

end CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
