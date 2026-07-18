/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

/-!
# Fixed-window (2^w-ary) scalar multiplication, generic over `[AddCommGroup G]`

This file develops the **fixed-window** (a.k.a. `2^w`-ary) scalar-multiplication
schedule and proves it computes `n • P` in any abelian group.  It is the
windowed optimization of the binary double-and-add ladder
(`binaryLadder` / `binaryLadder_correct` in
`CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377G2Scalar`): instead of
processing one scalar bit per step, it processes a whole window of `w` bits per
step, doubling the accumulator `w` times (one `(2^w)•·` shift) and adding the
precomputed multiple `d • P` for the current base-`2^w` digit `d`.

Like the binary ladder, the optimization is purely group-theoretic — it relies
on nothing about the underlying group beyond the abelian-group axioms — so we
develop it generically over an arbitrary `[AddCommGroup G]`.  It then
instantiates to any elliptic-curve point group realized as an `AddCommGroup`.

## Main definitions

* `digitsToNat (w) : List ℕ → ℕ` — MSB-first decode of a base-`2^w` digit list,
  `digitsToNat w [d₀, …, dₖ] = ((…(d₀·2^w + d₁)·2^w + …)·2^w + dₖ)`, with the
  Horner recurrence `digitsToNat w (ds ++ [d]) = 2^w · digitsToNat w ds + d`.
* `windowDigits (w) (n) : List ℕ` — the base-`2^w` digits of `n`, MSB-first, such
  that `digitsToNat w (windowDigits w n) = n` (`windowDigits_decode`).
* `windowedSmul (w) : List ℕ → G → G` — the fixed-window ladder: fold the digit
  list MSB-first, each step shifting the accumulator by `(2^w)•·` (= `w`
  doublings) and adding `d • P`.

## Main theorems

* `windowedSmul_correct` — **the keystone**:
  `windowedSmul w (windowDigits w n) P = n • P`.  The `2^w`-ary windowed ladder
  driven by the base-`2^w` digits of `n` computes `n • P`, over any
  `[AddCommGroup G]`.
* `windowedSmul_decode` — the per-list form `windowedSmul w ds P =
  (digitsToNat w ds) • P` for *every* digit list, from which the keystone
  follows by `windowDigits_decode`.

## Relation to the binary ladder (base-`2^w` vs base-`2` Horner)

The binary ladder is the `w = 1` special case.  The single structural change is
the Horner base: where the binary recurrence is
`bitsToNat (bs ++ [b]) = 2 · bitsToNat bs + b` and the ladder step doubles
*once* (`acc + acc = 2•acc`), here the base-`2^w` recurrence is
`digitsToNat w (ds ++ [d]) = 2^w · digitsToNat w ds + d` and the ladder step
shifts by `(2^w)•·`.  Correctness therefore rests on the *windowed* doubling
identity `nsmul_window`: `(2^w · n) • P = (2^w) • (n • P)`, the base-`2^w`
analogue of the binary `nsmul_double`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.WindowedScalarMulGeneric

variable {G : Type*}

/-! ## 1. The windowed group identities over an abstract abelian group

Two identities drive the windowed ladder: a *window-shift* step
`(2^w · n) • P = (2^w) • (n • P)` (the base-`2^w` analogue of binary doubling)
and an *add-digit* step `(n + d) • P = n • P + d • P`. -/

/-- **The window-shift identity.**  Shifting the scalar by a full window
    multiplies it by `2^w`, which is `(2^w)•·` applied to the point:
    `(2^w · n) • P = (2^w) • (n • P)`.  This is the base-`2^w` analogue of the
    binary doubling step `(2·n)•P = n•P + n•P` and is realized in the ladder by
    `w` repeated doublings. -/
theorem nsmul_window [AddCommGroup G] (w n : ℕ) (P : G) :
    (2 ^ w * n) • P = (2 ^ w) • (n • P) := by
  rw [mul_nsmul']

/-- **The add-digit identity.**  Adding a base-`2^w` digit `d` to the scalar adds
    the precomputed multiple `d • P`: `(n + d) • P = n • P + d • P`. -/
theorem nsmul_add_digit [AddCommGroup G] (n d : ℕ) (P : G) :
    (n + d) • P = n • P + d • P := add_nsmul P n d

/-! ## 2. The MSB-first base-`2^w` digit decode and its Horner recurrence -/

/-- **MSB-first base-`2^w` decode.**  `digitsToNat w [d₀, d₁, …, dₖ]` is the
    natural number with base-`2^w` digits `d₀ d₁ … dₖ` read most-significant
    digit first: `digitsToNat w [] = 0` and each appended digit Horner-shifts:
    `digitsToNat w (ds ++ [d]) = 2^w · digitsToNat w ds + d`.  Implemented by a
    left fold so the recurrence is definitional on `++ [d]`. -/
def digitsToNat (w : ℕ) (ds : List ℕ) : ℕ :=
  ds.foldl (fun acc d => 2 ^ w * acc + d) 0

/-- `digitsToNat` of the empty digit list is `0`. -/
@[simp] theorem digitsToNat_nil (w : ℕ) : digitsToNat w [] = 0 := rfl

/-- **The Horner recurrence for `digitsToNat`.**  Appending a least-significant
    digit `d` shifts the running value by a window and adds `d`:
    `digitsToNat w (ds ++ [d]) = 2^w · digitsToNat w ds + d`. -/
theorem digitsToNat_append_one (w : ℕ) (ds : List ℕ) (d : ℕ) :
    digitsToNat w (ds ++ [d]) = 2 ^ w * digitsToNat w ds + d := by
  simp only [digitsToNat, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## 3. The base-`2^w` digits of a natural number

`windowDigits w n` produces the MSB-first base-`2^w` digit list of `n` so that
`digitsToNat w (windowDigits w n) = n`.  We build it by repeatedly stripping the
least-significant window via `% 2^w` / `/ 2^w` (`Nat.div_add_mod`), appending the
stripped digit at the end so the list stays MSB-first. -/

set_option linter.unusedVariables false in
/-- **The base-`2^w` digits of `n`, MSB-first.**  Strips the high part `n / 2^w`
    recursively (on the quotient, which strictly decreases for `2^w ≥ 2` and
    `n ≠ 0`) and appends the low window `n % 2^w` last, keeping the list
    most-significant-digit first.  Uses window size `2^(w+1)` so the base is
    always `≥ 2`; this is the value passed by `windowedSmul_correct` and matches
    a window of `w+1` bits. -/
def windowDigits (w : ℕ) (n : ℕ) : List ℕ :=
  if h : n = 0 then []
  else
    windowDigits w (n / 2 ^ (w + 1)) ++ [n % 2 ^ (w + 1)]
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (Nat.one_lt_two_pow (by omega))

/-- **Decode is a left inverse of `windowDigits`** (at window size `2^(w+1)`):
    `digitsToNat (w+1) (windowDigits w n) = n`.  Proof by strong induction on `n`
    via the recursion of `windowDigits`, using the Horner recurrence
    `digitsToNat_append_one` and `Nat.div_add_mod`. -/
theorem windowDigits_decode (w : ℕ) (n : ℕ) :
    digitsToNat (w + 1) (windowDigits w n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [windowDigits]
    split
    · simp_all
    · rename_i h
      rw [digitsToNat_append_one,
        ih (n / 2 ^ (w + 1))
          (Nat.div_lt_self (Nat.pos_of_ne_zero h)
            (Nat.one_lt_two_pow (by omega)))]
      rw [Nat.div_add_mod]

/-! ## 4. The fixed-window ladder and its correctness

`windowedSmul` folds the base-`2^w` digits MSB-first: each step shifts the
accumulated point by a full window `(2^w)•·` (realized as `w` doublings) and adds
the precomputed multiple `d • P` of the current digit.  `windowedSmul_decode`
proves the fold computes `(digitsToNat w ds) • P`, and `windowedSmul_correct`
specializes it to the digits of `n`, giving `n • P`. -/

/-- **The MSB-first fixed-window (`2^w`-ary) ladder.**  Starting from `0`, process
    each base-`2^w` digit left-to-right: shift the accumulator by one window
    (`(2^w)•·`, i.e. `w` doublings of a verified group element) and add the
    precomputed multiple `d • P` of the current digit.  This is the standard
    left-to-right windowed scalar-multiplication schedule.  Generic over any
    `[AddCommGroup G]`. -/
def windowedSmul [AddCommGroup G] (w : ℕ) (ds : List ℕ) (P : G) : G :=
  ds.foldl (fun acc d => (2 ^ w) • acc + d • P) 0

/-- `windowedSmul` on the empty digit list is the group identity `0`. -/
@[simp] theorem windowedSmul_nil [AddCommGroup G] (w : ℕ) (P : G) :
    windowedSmul w [] P = 0 := rfl

/-- **The ladder's append recurrence.**  Processing one more (least-significant)
    digit `d` shifts the accumulated point by a window and adds `d • P`. -/
theorem windowedSmul_append_one [AddCommGroup G] (w : ℕ) (ds : List ℕ) (d : ℕ)
    (P : G) :
    windowedSmul w (ds ++ [d]) P
      = (2 ^ w) • (windowedSmul w ds P) + d • P := by
  simp only [windowedSmul, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Windowed decode correctness.**  The fixed-window ladder driven by the
    base-`2^w` digit list `ds` computes `(digitsToNat w ds) • P`: the accumulator
    after the fold equals the scalar (decoded from its base-`2^w` digits) times
    the base point.

    Proof: induction on `ds` from the right (`List.reverseRecOn`); the base case
    is `0 • P = 0`, and the inductive step combines the ladder's append
    recurrence (`windowedSmul_append_one`) with `digitsToNat`'s Horner recurrence
    (`digitsToNat_append_one`), closed by the window-shift identity
    `nsmul_window` and the add-digit identity `nsmul_add_digit`. -/
theorem windowedSmul_decode [AddCommGroup G] (w : ℕ) (ds : List ℕ) (P : G) :
    windowedSmul w ds P = (digitsToNat w ds) • P := by
  induction ds using List.reverseRecOn with
  | nil => simp
  | append_singleton ds d ih =>
    rw [windowedSmul_append_one, digitsToNat_append_one, ih,
      nsmul_add_digit, nsmul_window]

/-- **Fixed-window scalar-multiplication correctness (the keystone).**  Feeding
    the base-`2^(w+1)` digits of `n` to the windowed ladder computes `n • P`:
    `windowedSmul (w+1) (windowDigits w n) P = n • P`, over any
    `[AddCommGroup G]`.  This is the windowed optimization of double-and-add
    proved equal to `n • P` — the verified `2^w`-ary scalar-multiplication
    algorithm.

    Proof: `windowedSmul_decode` reduces the ladder to
    `(digitsToNat (w+1) (windowDigits w n)) • P`, and `windowDigits_decode`
    rewrites the decoded scalar back to `n`. -/
theorem windowedSmul_correct [AddCommGroup G] (w : ℕ) (n : ℕ) (P : G) :
    windowedSmul (w + 1) (windowDigits w n) P = n • P := by
  rw [windowedSmul_decode, windowDigits_decode]

/-! ## 5. Worked example and elliptic-curve instantiation -/

section Example

variable {G2 : Type*} [AddCommGroup G2]

/-- **Worked example.**  At window size `2^2 = 4` (`w = 1`), the windowed ladder
    on the scalar `13` computes `13 • P` in any abelian group: `13` decomposes
    MSB-first into base-`4` digits `[3, 1]` (`3·4 + 1 = 13`), and the ladder
    reproduces `13 • P` from those digits.  Stated via the general keystone so it
    holds for every `[AddCommGroup G2]`, in particular any elliptic-curve point
    group. -/
example (P : G2) : windowedSmul 2 (windowDigits 1 13) P = 13 • P :=
  windowedSmul_correct 1 13 P

/-- **Elliptic-curve `G`-group fixed-window scalar multiplication**
    (instantiation).  For any point group realized as an `AddCommGroup` (e.g. the
    `bls12-377` `G2` group of `RelationalFrontBls377G2Scalar`, whose affine law is
    `g2AffineAdd` / `g2AffineDbl`), the fixed-window ladder is the verified
    scalar-multiplication routine, computing `n • P` from the base-`2^(w+1)`
    digits of `n`. -/
theorem windowedSmulG_correct (w n : ℕ) (P : G2) :
    windowedSmul (w + 1) (windowDigits w n) P = n • P :=
  windowedSmul_correct w n P

end Example

end CatCrypt.Crypto.Optimizer.Rewrite.WindowedScalarMulGeneric
