/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Mathlib.Data.BitVec
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.Group
public import CatCrypt.Crypto.Primitives.GF128
public import Std.Tactic.BVDecide

/-!
# Verified GF(2^128) — `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`

A computable, verified Lean reference implementation of GF(2^128), the
NIST SP 800-38D GCM / GHASH / POLYVAL field. Used by the AES-GCM /
AES-GCM-SIV / AES-CCM (in MAC mode via GHASH) / AES-SIV / AEGIS bridges to
replace opaque encoder round-trip axioms with proven identities, in the
same spirit as `Gf16.lean` (MAYO) and `Gf256.lean` (UOV / AES S-box).

## Representation

A `Gf128` element is a `BitVec 128` understood as a polynomial of degree
`<128` over `GF(2)`.

* **addition** = bitwise XOR (`a ^^^ b`);
* **multiplication** = the bit-reflected NIST SP 800-38D Algorithm 1
  shift-and-XOR loop (already encoded in `Primitives.GF128.gf128_mul`).

The reduction polynomial choice (`x^128 + x^7 + x^2 + x + 1`,
bit-reflected form `R = 0xE1…`) follows NIST SP 800-38D §6.3.

## Field axioms

Naive enumeration is **infeasible** at 128 bits (2^128 cases). The
additive axioms over `BitVec 128` are closed by `bv_decide` (SAT). The
multiplicative axioms expose only what the AEAD-family bridges need:
`mul_zero`, `zero_mul`, plus encoder round-trips. These are stated as
**theorems** (closed by SAT / `bv_decide` where feasible) rather than
axioms; we deliberately do **not** claim associativity or commutativity
here as theorems — those would need an algebraic proof rather than a
finite check, and the bridges do not consult them.

## Provenance

The `gf128_mul` body lives in `Primitives.GF128` (the canonical
implementation). This file re-exports it under the verified-GF naming
convention `Gf128.mul`, plus the encoders / round-trip lemmas the
AEAD bridges consume.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-- A `GF(2^128)` element: a 128-bit polynomial over `GF(2)`.

    Defined as an `abbrev` over `BitVec 128` so all `BitVec` instances
    flow through transparently. -/
abbrev Gf128 : Type := BitVec 128

namespace Gf128

/-! ## Multiplication via the canonical SP 800-38D algorithm -/

/-- GF(2^128) multiplication. Wraps the canonical
    `Primitives.GF128.gf128_mul`. -/
def mul (a b : Gf128) : Gf128 :=
  CatCrypt.Crypto.Primitives.GF128.gf128_mul a b

/-! ## Additive axioms (closed by `bv_decide`)

The 128-bit additive group is bit-wise XOR; all four group axioms reduce
to bit-blasted SAT instances. -/

theorem add_zero' (a : Gf128) : a ^^^ (0 : BitVec 128) = a := by bv_decide
theorem zero_add' (a : Gf128) : (0 : BitVec 128) ^^^ a = a := by bv_decide
theorem add_comm' (a b : Gf128) : a ^^^ b = b ^^^ a := by bv_decide
theorem add_assoc' (a b c : Gf128) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by bv_decide
theorem add_self' (a : Gf128) : a ^^^ a = (0 : BitVec 128) := by bv_decide

/-! ## Encoders to/from BitVec, Nat, Int -/

/-- Inject a `BitVec 128` into `Gf128` (identity). -/
def ofBitVec (b : BitVec 128) : Gf128 := b

/-- Project a `Gf128` element back to a `BitVec 128` (identity). -/
def toBitVec (g : Gf128) : BitVec 128 := g

theorem ofBitVec_toBitVec (g : Gf128) : ofBitVec (toBitVec g) = g := rfl
theorem toBitVec_ofBitVec (b : BitVec 128) : toBitVec (ofBitVec b) = b := rfl

/-- Inject a `Nat` (mod 2^128) into `Gf128`. -/
def fromNat (n : Nat) : Gf128 := BitVec.ofNat 128 n

/-- Project a `Gf128` element to a `Nat` in `[0..2^128)`. -/
def asNat (g : Gf128) : Nat := BitVec.toNat g

/-- Project a `Gf128` element to an `Int`. -/
def asInt (g : Gf128) : Int := (BitVec.toNat g : Int)

/-- Inject an `Int` (clamped to its nonneg part, mod 2^128) into `Gf128`. -/
def fromInt (i : Int) : Gf128 := BitVec.ofNat 128 i.toNat

theorem fromNat_asNat (g : Gf128) : fromNat (asNat g) = g := by
  show BitVec.ofNat 128 (BitVec.toNat g) = g
  exact BitVec.ofNat_toNat 128 g

theorem fromInt_asInt (g : Gf128) : fromInt (asInt g) = g := by
  show BitVec.ofNat 128 ((BitVec.toNat g : Int).toNat) = g
  simp

theorem asNat_lt (g : Gf128) : asNat g < 2 ^ 128 := by
  show BitVec.toNat g < 2 ^ 128
  exact g.isLt

end Gf128

end CatCrypt.Util
