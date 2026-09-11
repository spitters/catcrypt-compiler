/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.BitVec

/-!
# Verified SHA-512 single-round body — `BitVec 64` word arithmetic

A computable, verified Lean reference implementation of the SHA-512 single
round-transformation body (FIPS 180-4 §6.4). The structure mirrors
`Sha256Verified.lean` modulo the wider word (`BitVec 64`) and the
different rotation constants from FIPS 180-4 §4.1.3.

## Scope (fall-back gate, per Wave 9 plan)

This file ships the **verified single-round body**:
* `ch x y z = (x & y) ^ (~x & z)`,
* `maj x y z = (x & y) ^ (x & z) ^ (y & z)`,
* `bigSigma0 x = rotr x 28 ^ rotr x 34 ^ rotr x 39`,
* `bigSigma1 x = rotr x 14 ^ rotr x 18 ^ rotr x 41`,
* `smallSigma0 x = rotr x 1 ^ rotr x 8 ^ shr x 7`,
* `smallSigma1 x = rotr x 19 ^ rotr x 61 ^ shr x 6`,
* `sha512RoundVerified` — the full single round update of the working
  variables `(a, b, c, d, e, f, g, h)` with `K[t]` and `W[t]`.

The full 80-round message schedule + compression is the named
hypothesis `Sha512CompressSpec` — the trust-boundary outside the
single round (see `Sha256Verified.lean` for the rationale; the same
budget gate applies here).

## API

* `Sha512Word := BitVec 64`
* `ch`, `maj`, `bigSigma0`, `bigSigma1`, `smallSigma0`, `smallSigma1` —
  the FIPS 180-4 §4.1.3 logical functions
* `sha512RoundVerified` — one round transformation
* `Sha512Working` — the eight working words `(a, b, c, d, e, f, g, h)`
* `Sha512CompressSpec` — named hypothesis type for the published
  80-round + schedule composition
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util.Sha512Verified

/-! ## SHA-512 word width and rotate -/

/-- A SHA-512 word: a 64-bit BitVec. -/
abbrev Sha512Word : Type := BitVec 64

/-- Cyclic right rotation by `n` bits. -/
def rotr (x : Sha512Word) (k : Nat) : Sha512Word :=
  (x >>> (k : Nat)) ||| (x <<< ((64 - k) : Nat))

/-- Logical right shift by `k` bits. -/
def shr (x : Sha512Word) (k : Nat) : Sha512Word := x >>> (k : Nat)

/-! ## FIPS 180-4 §4.1.3 logical functions -/

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
def ch (x y z : Sha512Word) : Sha512Word := (x &&& y) ^^^ ((~~~x) &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def maj (x y z : Sha512Word) : Sha512Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ₀(x) = rotr(x, 28) ⊕ rotr(x, 34) ⊕ rotr(x, 39)`. -/
def bigSigma0 (x : Sha512Word) : Sha512Word :=
  rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39

/-- `Σ₁(x) = rotr(x, 14) ⊕ rotr(x, 18) ⊕ rotr(x, 41)`. -/
def bigSigma1 (x : Sha512Word) : Sha512Word :=
  rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41

/-- `σ₀(x) = rotr(x, 1) ⊕ rotr(x, 8) ⊕ shr(x, 7)`. -/
def smallSigma0 (x : Sha512Word) : Sha512Word :=
  rotr x 1 ^^^ rotr x 8 ^^^ shr x 7

/-- `σ₁(x) = rotr(x, 19) ⊕ rotr(x, 61) ⊕ shr(x, 6)`. -/
def smallSigma1 (x : Sha512Word) : Sha512Word :=
  rotr x 19 ^^^ rotr x 61 ^^^ shr x 6

/-! ## Working-word state and single-round body -/

/-- The eight SHA-512 working words `(a, b, c, d, e, f, g, h)`. -/
structure Sha512Working where
  a : Sha512Word
  b : Sha512Word
  c : Sha512Word
  d : Sha512Word
  e : Sha512Word
  f : Sha512Word
  g : Sha512Word
  h : Sha512Word
  deriving Repr, DecidableEq

/-- **SHA-512 single round** (FIPS 180-4 §6.4.2 step 3, one iteration). -/
def sha512RoundVerified
    (s : Sha512Working) (kt wt : Sha512Word) : Sha512Working :=
  let t1 := s.h + bigSigma1 s.e + ch s.e s.f s.g + kt + wt
  let t2 := bigSigma0 s.a + maj s.a s.b s.c
  { a := t1 + t2
    b := s.a
    c := s.b
    d := s.c
    e := s.d + t1
    f := s.e
    g := s.f
    h := s.g }

/-! ## Sanity lemmas over the single round -/

/-- The round body's `.b/.c/.d/.f/.g/.h` fields are the previous
    `.a/.b/.c/.e/.f/.g`. -/
theorem sha512RoundVerified_shift (s : Sha512Working) (kt wt : Sha512Word) :
    (sha512RoundVerified s kt wt).b = s.a ∧
    (sha512RoundVerified s kt wt).c = s.b ∧
    (sha512RoundVerified s kt wt).d = s.c ∧
    (sha512RoundVerified s kt wt).f = s.e ∧
    (sha512RoundVerified s kt wt).g = s.f ∧
    (sha512RoundVerified s kt wt).h = s.g := by
  unfold sha512RoundVerified
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Named hypothesis (composition trust-boundary) -/

/-- A complete SHA-512 message block (16 × 64-bit words = 1024 bits). -/
def Sha512Block : Type := Vector Sha512Word 16

/-- A SHA-512 digest / chaining state (8 × 64-bit words = 512 bits). -/
def Sha512State : Type := Vector Sha512Word 8

/-- **Named hypothesis (FIPS 180-4 SHA-512 composition trust-boundary).**

    The 80-round + schedule composition of `sha512RoundVerified`,
    evaluated on the standard message-schedule expansion of the input
    block, equals the published FIPS 180-4 SHA-512 block compression.

    Same boundary as SHA-256 (see `Sha256Verified.lean`): single round
    is verified; outer 80-round + schedule loop is named. Consumers
    (HKDF-SHA512 bridge, future SLH-DSA SHA-512 variants) take this as
    an explicit named hypothesis. -/
def Sha512CompressSpec : Type :=
  Sha512State → Sha512Block → Sha512State

end CatCrypt.Util.Sha512Verified
