/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Group

/-!
# Binary (square-and-multiply) exponentiation over a monoid

The multiplicative analogue of the additive double-and-add ladder
(`binaryLadder` in `RelationalFrontBls377G2Scalar`): given a base `g` in a
monoid `M` and the binary digits of an exponent `n`, compute `g ^ n` by a
left-to-right schedule of *squarings* interleaved with conditional
*multiplications*.

The single-step primitive is the monoid's multiplication; exponentiation
`g ^ n` — the operation pairing **final exponentiation** and **field
exponentiation** actually invoke — is built from it by this **square-and-multiply
ladder**: a sequence of squarings interleaved with conditional multiplications,
driven by the binary digits of the exponent (MSB first).

This module verifies that ladder.  The exponentiation *algorithm* is purely
monoid-theoretic (it uses only `*`, squaring, and the monoid's `Monoid.npow`),
so we develop it generically over an arbitrary `[Monoid M]` — exactly the right
altitude: correctness is independent of which monoid `M` is (the multiplicative
group of a finite field for field exponentiation, the target group `G_T` for
pairing final exponentiation, …).

## What this module proves

* `powLadder : List Bool → M → M` — the MSB-first square-and-multiply ladder:
  fold the exponent's bit list left-to-right, each step squaring the accumulator
  and conditionally multiplying by the base when the current bit is set.
* `bitsToNat : List Bool → ℕ` — the MSB-first bit-list decode (`[b₀,…,bₖ]` is
  the integer `∑ bᵢ · 2^(k−i)`), with the Horner recurrence
  `bitsToNat (bs ++ [b]) = 2 · bitsToNat bs + cond b 1 0`.
* `powLadder_correct` — **the square-and-multiply correctness theorem**:
  `powLadder bs g = g ^ (bitsToNat bs)` for *every* bit list, over any
  `[Monoid M]`.  Equivalently: the ladder driven by the bits of `n` computes
  `g ^ n`.
* The two ladder identities the algorithm rests on, isolated as named lemmas
  over `[Monoid M]`:
  - `pow_two_mul` — `g ^ (2·n) = g ^ n * g ^ n`  (the *squaring* step);
  - `pow_succ`    — `g ^ (n+1) = g ^ n * g`        (the *multiply* step, from
    Mathlib).

## Worked example

`powLadderNatMul` instantiates the ladder to the *multiplicative* monoid of `ℕ`
(`Multiplicative ℕ`-free: we just reuse `Monoid ℕ`), checking on a concrete
small exponent that the ladder reproduces ordinary natural-number power.

## Honesty boundary

`powLadder_correct` is the verified *algorithm*; it says the square-and-multiply
schedule computes `g ^ n` in any monoid.  Wiring each ladder *step* to a concrete
multiplication (the `Fp12`/`G_T` arithmetic of final exponentiation, or a field's
Montgomery multiply) is the realization done at the use site, under whatever side
conditions that arithmetic carries; the ladder itself is the new construction and
is unconditional.

0 sorries; no custom axioms; correctness holds over any `[Monoid M]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.MonoidPowLadder

/-! ## 1. The two ladder identities over an abstract monoid

Exponentiation is built from exactly two monoid identities: a *squaring* step
`g ^ (2n) = g ^ n * g ^ n` and a *multiply* step `g ^ (n+1) = g ^ n * g`.  Both
are immediate from Mathlib's `Monoid.npow` arithmetic; we isolate the squaring
identity as a named lemma so the ladder's recursion has an explicit hook (the
multiply step is Mathlib's `pow_succ`). -/

variable {M : Type*}

/-- **The squaring identity.**  Doubling the exponent squares the power:
    `g ^ (2·n) = g ^ n * g ^ n`.  This is the *square* half of
    square-and-multiply. -/
theorem pow_two_mul [Monoid M] (n : ℕ) (g : M) :
    g ^ (2 * n) = g ^ n * g ^ n := by
  rw [two_mul, pow_add]

/-! ## 2. The MSB-first bit-list decode

`bitsToNat [b₀, b₁, …, bₖ]` is the natural number with binary digits
`b₀ b₁ … bₖ` read most-significant-bit first.  The key fact for the ladder is
the Horner recurrence on `++ [b]`, which a left fold makes definitional. -/

/-- **MSB-first bit-list decode.**  `bitsToNat [b₀, b₁, …, bₖ]` is the natural
    number with binary digits `b₀ b₁ … bₖ` read most-significant-bit first:
    `bitsToNat [] = 0` and each appended bit Horner-shifts:
    `bitsToNat (bs ++ [b]) = 2 · bitsToNat bs + cond b 1 0`.  Implemented by a
    left fold so the recurrence is definitional on `++ [b]`. -/
def bitsToNat (bs : List Bool) : ℕ :=
  bs.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0

/-- `bitsToNat` of the empty bit list is `0`. -/
@[simp] theorem bitsToNat_nil : bitsToNat [] = 0 := rfl

/-- **The Horner recurrence for `bitsToNat`.**  Appending a least-significant
    bit `b` doubles the running value and adds `b`:
    `bitsToNat (bs ++ [b]) = 2 · bitsToNat bs + cond b 1 0`. -/
theorem bitsToNat_append_one (bs : List Bool) (b : Bool) :
    bitsToNat (bs ++ [b]) = 2 * bitsToNat bs + (if b then 1 else 0) := by
  simp only [bitsToNat, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## 3. The square-and-multiply ladder and its correctness

`powLadder` folds the exponent's bits MSB-first, squaring the accumulator and
conditionally multiplying by the base.  `powLadder_correct` proves the fold
computes `g ^ (bitsToNat bs)` — the verified exponentiation algorithm. -/

/-- **The MSB-first square-and-multiply ladder.**  Starting from `1`, process
    each exponent bit left-to-right: square the accumulator, then multiply by the
    base `g` iff the bit is set.  This is the standard left-to-right binary
    exponentiation schedule.  Generic over any `[Monoid M]`. -/
def powLadder [Monoid M] (bs : List Bool) (g : M) : M :=
  bs.foldl (fun acc b => (acc * acc) * (if b then g else 1)) 1

/-- `powLadder` on the empty bit list is the monoid identity `1`. -/
@[simp] theorem powLadder_nil [Monoid M] (g : M) :
    powLadder [] g = 1 := rfl

/-- **The ladder's append recurrence.**  Processing one more (least-significant)
    bit `b` squares the accumulated power and conditionally multiplies by `g`. -/
theorem powLadder_append_one [Monoid M] (bs : List Bool) (b : Bool) (g : M) :
    powLadder (bs ++ [b]) g
      = (powLadder bs g * powLadder bs g) * (if b then g else 1) := by
  simp only [powLadder, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Square-and-multiply correctness.**  The MSB-first ladder driven by the bit
    list `bs` computes `g ^ (bitsToNat bs)`: the accumulator after the fold
    equals the base raised to the exponent (decoded from its bits).
    Equivalently, feeding the binary digits of `n` to `powLadder` yields `g ^ n`.

    Proof: induction on `bs` from the right (`List.reverseRecOn`); the base case
    is `g ^ 0 = 1`, and the inductive step combines the ladder's append
    recurrence (`powLadder_append_one`) with `bitsToNat`'s Horner recurrence
    (`bitsToNat_append_one`), closed by the squaring identity `pow_two_mul` and
    the multiply identity `pow_succ`. -/
theorem powLadder_correct [Monoid M] (bs : List Bool) (g : M) :
    powLadder bs g = g ^ (bitsToNat bs) := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs b ih =>
    rw [powLadder_append_one, bitsToNat_append_one, ih]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, mul_one, add_zero]
      rw [pow_two_mul]
    | true =>
      simp only [if_true]
      rw [pow_succ, pow_two_mul]

/-! ## 4. Worked example: the multiplicative monoid of `ℕ`

`ℕ` is a `Monoid` under ordinary multiplication, so the verified ladder applies
directly: `powLadder bs n` computes `n ^ (bitsToNat bs)`.  We check it on the
exponent `13 = 0b1101 = bitsToNat [true, true, false, true]` with base `3`,
confirming the ladder reproduces `3 ^ 13`. -/

/-- **Ladder over the multiplicative monoid of `ℕ`** (worked instantiation).
    A direct specialization of `powLadder_correct` to `[Monoid ℕ]`: the
    square-and-multiply ladder computes `g ^ (bitsToNat bs)` for natural
    numbers. -/
theorem powLadderNat_correct (bs : List Bool) (g : ℕ) :
    powLadder bs g = g ^ (bitsToNat bs) :=
  powLadder_correct bs g

/-- The bits `[true, true, false, true]` decode (MSB-first) to `13`. -/
example : bitsToNat [true, true, false, true] = 13 := by decide

/-- The square-and-multiply ladder over `ℕ` computes `3 ^ 13 = 1594323`. -/
example : powLadder [true, true, false, true] (3 : ℕ) = 1594323 := by decide

/-- The ladder's result matches the abstract power, exhibited concretely:
    `powLadder [true,true,false,true] 3 = 3 ^ 13`. -/
example : powLadder [true, true, false, true] (3 : ℕ)
    = (3 : ℕ) ^ bitsToNat [true, true, false, true] :=
  powLadderNat_correct _ _

end CatCrypt.Crypto.Optimizer.Rewrite.MonoidPowLadder
