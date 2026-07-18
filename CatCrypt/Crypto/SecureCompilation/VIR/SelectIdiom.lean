/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

set_option autoImplicit false

/-!
# C6 Select Instruction-Selection Bridge (SelectIdiom)

This file proves the constant-time-SELECT instruction-selection bridge lemma:
that the dialect's efficient `selectW` op equals the homogeneous branchless
mask-blend idiom built from `xor`/`and`/`sub` only.

## Context

In the Jasmin VIR dialect (`JasminDialect.lean`), the `selectW` function
implements a constant-time conditional select:

    selectW cond a b = if cond = 1#1 then a else b

Its docstring notes the value equals the branchless mask idiom
`(a & mask) | (b & ~mask)` with `mask = 0 - cond`. The algebraically-equivalent
XOR form is `((a ^^^ b) &&& mask) ^^^ b`.

## Theorem

`selectW_eq_maskBlend` (general `w`): for any bit-width `w`, condition
`cond : BitVec 1`, and operands `a b : BitVec w`,

    selectW cond a b = (((a ^^^ b) &&& (0#w - BitVec.ofNat w cond.toNat)) ^^^ b)

## Proof approach

Case-split on `cond.toNat ∈ {0, 1}` (derived by `omega` from `cond.isLt`),
then `BitVec.eq_of_toNat_eq` lifts to `cond = 0#1 ∨ cond = 1#1`.
- `cond = 0#1`: mask = `0 - 0 = 0`; `(a ^^^ b) &&& 0 = 0`; `0 ^^^ b = b`;
  LHS `selectW 0#1 a b = b`. ✓
- `cond = 1#1`: mask = `0 - 1 = −1 = allOnes` (`BitVec.neg_one_eq_allOnes`);
  `(a ^^^ b) &&& allOnes = a ^^^ b` (`BitVec.and_allOnes`);
  `(a ^^^ b) ^^^ b = a` (`BitVec.xor_assoc` + `BitVec.xor_self`);
  LHS `selectW 1#1 a b = a`. ✓

General `w` — no width restriction needed.

## Role (C6)

A verified pass can detect the mask-blend idiom in homogeneous front output
and rewrite it to the efficient `select`/CMOV op — this lemma is the
denotation-preservation justification: both sides compute the same `BitVec w`
value for every `cond`, `a`, `b`, and `w`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open JasminDialect

/-! ## Main theorem: general-width selectW = mask-blend idiom -/

/-- **SELECT instruction-selection bridge (C6).**

    For any bit-width `w`, the dialect's `selectW` op equals the branchless
    mask-blend idiom `((a ^^^ b) &&& mask) ^^^ b` with `mask = 0 - cond`
    (the two's-complement all-ones mask when `cond = 1`, zero when `cond = 0`).

    This is the `BitVec`-algebra fact that licenses collapsing the
    `xor`/`and`/`sub` mask-blend triple emitted by the homogeneous front into
    the single `select` op (data effect of x86 `CMOVcc`) without changing the
    denotation.

    Proof: case-split on `cond.toNat ∈ {0, 1}` (derived by `omega` from
    `cond.isLt : cond.toNat < 2`), convert to `cond = 0#1 ∨ cond = 1#1` via
    `BitVec.eq_of_toNat_eq`, then `simp` closes each branch using:
    - `cond = 0#1`: `BitVec.and_zero` (mask = 0, so `_ &&& 0 = 0` and `0 ^^^ b = b`)
    - `cond = 1#1`: `BitVec.neg_one_eq_allOnes` (mask = −1 = allOnes),
      `BitVec.and_allOnes`, `BitVec.xor_assoc`, `BitVec.xor_self` (xor self-cancels)
    General `w` — no width restriction. -/
theorem selectW_eq_maskBlend {w : Nat} (cond : BitVec 1) (a b : BitVec w) :
    selectW cond a b = (((a ^^^ b) &&& (0#w - BitVec.ofNat w cond.toNat)) ^^^ b) := by
  have hcond : cond = 0#1 ∨ cond = 1#1 := by
    have : cond.toNat = 0 ∨ cond.toNat = 1 := by
      have := cond.isLt; omega
    rcases this with h | h
    · left; exact BitVec.eq_of_toNat_eq (by simpa)
    · right; exact BitVec.eq_of_toNat_eq (by simpa)
  rcases hcond with rfl | rfl
  · simp [selectW, BitVec.and_zero]
  · simp [selectW, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
          BitVec.xor_assoc, BitVec.xor_self]

end CatCrypt.Crypto.SecureCompilation.VIR
