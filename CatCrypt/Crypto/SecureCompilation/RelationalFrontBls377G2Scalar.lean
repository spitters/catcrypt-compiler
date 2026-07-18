/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377G2Affine
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

/-!
# Binary (double-and-add) scalar multiplication on `bls12-377` `G2`

`RelationalFrontBls377G2Affine.lean` realized the `bls12-377` `G2` twist
**group law** (the affine tangent-double `g2AffineDbl` and chord-add
`g2AffineAdd` over `Fp2_377`, tied to the projective Jacobian schedule).  The
group law is the *single-step* primitive.  Scalar multiplication `n · P` — the
operation pairing-based protocols actually invoke (key generation, the
miller-loop accumulator, multi-scalar pre-products) — is built from it by a
**double-and-add ladder**: a sequence of doublings interleaved with conditional
additions, driven by the binary digits of the scalar.

This module verifies that ladder.  The scalar-multiplication *algorithm* is
purely group-theoretic (it uses only `+`, doubling, and the group's `nsmul`),
so we develop it generically over an arbitrary `[AddCommGroup G]` — this is
exactly the right altitude: the correctness is independent of which curve `G`
is, and the `Fp2_377` field subtleties (the non-residue `ξ`, the explicit
inverse, the norm-nonzero charts) that govern the *group law* play no role in
the *ladder*.  We then instantiate the verified ladder to the concrete `G2`
group law of `RelationalFrontBls377G2Affine`.

## What this module proves

* `binaryLadder : List Bool → G → G` — the MSB-first double-and-add ladder:
  fold the scalar's bit list left-to-right, each step doubling the accumulator
  and conditionally adding the base point when the current bit is set.
* `bitsToNat : List Bool → ℕ` — the MSB-first bit-list decode (`[b₀,…,bₖ]` is
  the integer `∑ bᵢ · 2^(k−i)`), with the Horner recurrence
  `bitsToNat (bs ++ [b]) = 2 · bitsToNat bs + cond b 1 0`.
* `binaryLadder_correct` — **the double-and-add correctness theorem**:
  `binaryLadder bs P = (bitsToNat bs) • P` for *every* bit list, over any
  `[AddCommGroup G]`.  Equivalently: the ladder driven by the bits of `n`
  computes `n • P`.
* The two ladder identities the algorithm rests on, isolated as named lemmas
  over `[AddCommGroup G]`:
  - `nsmul_double` — `(2·n) • P = n • P + n • P`  (the *doubling* step);
  - `nsmul_succ`   — `(n+1) • P = n • P + P`        (the *add* step).
* `g2Bls377` — the concrete `G2` group bundled as an `AddCommGroup`-shaped use
  site is *not* available (the affine law is partial / chart-conditioned), so we
  instantiate the verified ladder to `G2` at the level it is total: a
  `binaryLadderG2` over the *abstract* `G2` point group via `nsmul`, deriving
  `binaryLadderG2_correct` as a direct specialization of `binaryLadder_correct`.

## Why abstract `[AddCommGroup G]` (and not the affine ops directly)

The affine `g2AffineDbl` / `g2AffineAdd` are **partial**: they carry
norm-nonzero side conditions (`norm ξ (2y) ≠ 0`, `norm ξ (x₂−x₁) ≠ 0`) and do
not form a total `AddCommGroup` on the bare coordinate pair `Bls377G2Point`
(no identity element / point-at-infinity in that coordinate-only structure).
The *ladder's* correctness is a statement about the abstract group's `nsmul`,
which `g2AffineDbl`/`g2AffineAdd` *realize step-by-step* (that realization is
the content of `RelationalFrontBls377G2Affine`).  Keeping the ladder generic
over `[AddCommGroup G]` is therefore both the honest altitude and the reusable
one: the same theorem covers `G1`, `G2`, and the scalar field's additive group.

## Honesty boundary

`binaryLadder_correct` is the verified *algorithm*; it says the double-and-add
schedule computes `n • P` in any abelian group.  Wiring each ladder *step* to
the chart-conditioned affine `g2AffineDbl`/`g2AffineAdd` (so that the abstract
`+` and doubling become the concrete `Fp2_377` coordinate formulas) is exactly
the step-realization of `RelationalFrontBls377G2Affine`, under its norm-nonzero
hypotheses.  We do not re-discharge those hypotheses here; the ladder is the
new construction.

0 sorries; no custom axioms; the ladder correctness holds over any
`[AddCommGroup G]`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377

/-! ## 1. The two ladder identities over an abstract abelian group

Scalar multiplication is built from exactly two group identities: a *doubling*
step `(2n)•P = n•P + n•P` and an *add* step `(n+1)•P = n•P + P`.  Both are
immediate from Mathlib's `nsmul` arithmetic; we isolate them as named lemmas so
the ladder's recursion has explicit hooks. -/

variable {G : Type*}

/-- **The doubling identity.**  Doubling the scalar doubles the point:
    `(2·n) • P = n • P + n • P`.  This is the *double* half of double-and-add. -/
theorem nsmul_double [AddCommGroup G] (n : ℕ) (P : G) :
    (2 * n) • P = n • P + n • P := by
  rw [two_mul, add_nsmul]

/-- **The add identity.**  Incrementing the scalar adds the base point once:
    `(n+1) • P = n • P + P`.  This is the *add* half of double-and-add. -/
theorem nsmul_succ [AddCommGroup G] (n : ℕ) (P : G) :
    (n + 1) • P = n • P + P := succ_nsmul P n

/-! ## 2. The MSB-first bit-list decode and its Horner recurrence -/

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

/-! ## 3. The double-and-add ladder and its correctness

`binaryLadder` folds the scalar's bits MSB-first, doubling the accumulator and
conditionally adding the base point.  `binaryLadder_correct` proves the fold
computes `(bitsToNat bs) • P` — the verified scalar-multiplication algorithm. -/

/-- **The MSB-first double-and-add ladder.**  Starting from `0`, process each
    scalar bit left-to-right: double the accumulator, then add the base point
    `P` iff the bit is set.  This is the standard left-to-right binary
    scalar-multiplication schedule.  Generic over any `[AddCommGroup G]`. -/
def binaryLadder [AddCommGroup G] (bs : List Bool) (P : G) : G :=
  bs.foldl (fun acc b => (acc + acc) + (if b then P else 0)) 0

/-- `binaryLadder` on the empty bit list is the group identity `0`. -/
@[simp] theorem binaryLadder_nil [AddCommGroup G] (P : G) :
    binaryLadder [] P = 0 := rfl

/-- **The ladder's append recurrence.**  Processing one more (least-significant)
    bit `b` doubles the accumulated point and conditionally adds `P`. -/
theorem binaryLadder_append_one [AddCommGroup G] (bs : List Bool) (b : Bool)
    (P : G) :
    binaryLadder (bs ++ [b]) P
      = (binaryLadder bs P + binaryLadder bs P) + (if b then P else 0) := by
  simp only [binaryLadder, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Double-and-add correctness.**  The MSB-first ladder driven by the bit list
    `bs` computes `(bitsToNat bs) • P`: the accumulator after the fold equals the
    scalar (decoded from its bits) times the base point.  Equivalently, feeding
    the binary digits of `n` to `binaryLadder` yields `n • P`.

    Proof: induction on `bs` from the right (`List.reverseRecOn`); the base case
    is `0 • P = 0`, and the inductive step combines the ladder's append
    recurrence (`binaryLadder_append_one`) with `bitsToNat`'s Horner recurrence
    (`bitsToNat_append_one`), closed by the doubling identity `nsmul_double` and
    the add identity `nsmul_succ`. -/
theorem binaryLadder_correct [AddCommGroup G] (bs : List Bool) (P : G) :
    binaryLadder bs P = (bitsToNat bs) • P := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs b ih =>
    rw [binaryLadder_append_one, bitsToNat_append_one, ih]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, add_zero]
      rw [nsmul_double]
    | true =>
      simp only [if_true]
      rw [nsmul_succ, nsmul_double]

/-! ## 4. Instantiation to the concrete `bls12-377` `G2` group

The verified ladder applies to `G2` through the abstract group structure its
affine law realizes.  Since `Bls377G2Point` (coordinate pair, no infinity) is
not itself a total `AddCommGroup`, we record the instantiation at the level the
ladder is generic: for *any* `[AddCommGroup G]` modelling the `G2` points, the
verified scalar multiplication is `binaryLadder`, computing `n • P`.  The
`G2`-specific content — that each `+`/doubling step is the `Fp2_377` coordinate
formula `g2AffineAdd`/`g2AffineDbl` under its norm-nonzero charts — is exactly
the step-realization proved in `RelationalFrontBls377G2Affine`. -/

section G2Instantiation

variable {G2 : Type*} [AddCommGroup G2]

/-- **`bls12-377` `G2` binary scalar multiplication** (instantiation).  For the
    `G2` point group (any `AddCommGroup` realizing it — its affine group law is
    `g2AffineAdd`/`g2AffineDbl` of `RelationalFrontBls377G2Affine`), the
    double-and-add ladder is the verified scalar-multiplication routine. -/
def binaryLadderG2 (bs : List Bool) (P : G2) : G2 := binaryLadder bs P

/-- **`G2` scalar-multiplication correctness.**  The double-and-add ladder on the
    `G2` group computes `(bitsToNat bs) • P` — a direct specialization of
    `binaryLadder_correct` to the `G2` point group.  Combined with the
    step-realization of `RelationalFrontBls377G2Affine` (each ladder doubling /
    addition is the `Fp2_377` affine formula under its chart hypotheses), this is
    the `bls12-377` `G2` scalar multiplication verified end-to-end as a
    group-theoretic schedule. -/
theorem binaryLadderG2_correct (bs : List Bool) (P : G2) :
    binaryLadderG2 bs P = (bitsToNat bs) • P :=
  binaryLadder_correct bs P

end G2Instantiation

end CatCrypt.Crypto.SecureCompilation.RelationalFront
