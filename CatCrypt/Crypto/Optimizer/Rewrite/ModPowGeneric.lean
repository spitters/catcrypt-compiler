/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import CatCrypt.Crypto.Optimizer.Rewrite.MonoidPowLadderPass

/-!
# Modular exponentiation by square-and-multiply (generic)

This module composes the generic monoid square-and-multiply ladder
(`powLadder`, from `MonoidPowLadderPass`) with **modular reduction** to obtain
verified *modular* exponentiation `g ^ n mod m` — the abstract operation the
`mpz_powm`-style kernels realize.

## The clean generic phrasing: work in `ZMod m`

The ladder `powLadder` is proved correct over an arbitrary `[Monoid M]`:
`powLadder bs g = g ^ (bitsToNat bs)`.  To turn it into *modular* exponentiation
we do not reimplement the reduction step; instead we instantiate the **monoid**
to the quotient ring `ZMod m`.  In `ZMod m`, the power `(g : ZMod m) ^ n` is
**already reduced** — `ZMod m` *is* the quotient by `m`, so multiplication
carries the reduction with it.  Therefore:

* `powLadder bs (g : ZMod m) = (g : ZMod m) ^ (bitsToNat bs)` is just
  `powLadder_correct` at `M := ZMod m` — the square-and-multiply ladder run in
  `ZMod m` computes the reduced power; and
* `((g : ZMod m)) ^ n = ((g ^ n : ℕ) : ZMod m)` is the ring-hom commutation
  `Nat.cast_pow` (a `push_cast`), i.e. casting the natural-number power into
  `ZMod m` reduces it mod `m`.

Composing the two gives `modPow_correct`:
`powLadder bs ((g : ℕ) : ZMod m) = ((g ^ bitsToNat bs : ℕ) : ZMod m)` —
**the square-and-multiply ladder in `ZMod m` computes `g ^ n mod m`.**

## Honesty boundary

`modPow_correct` is the verified composition: it says the generic ladder, run in
the quotient ring `ZMod m`, equals the integer power `g ^ n` reduced mod `m`.
The reduction is supplied *for free* by working in `ZMod m`; a concrete bignum
`mpz_powm` realizes each `ZMod m` multiply by an explicit reduce-after-multiply
(Barrett/Montgomery) at the use site, under that arithmetic's side conditions.
The composition here — generic ladder ∘ modular reduction — is unconditional.

## Worked example

`3 ^ 13 mod 7` in `ZMod 7`: the ladder driven by the bits of `13`
(`[true, true, false, true]`) applied to `(3 : ZMod 7)` equals
`(3 ^ 13 : ℕ)` cast into `ZMod 7`, which is `3`.

0 sorries; no custom axioms; correctness holds over every modulus `m`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.ModPowGeneric

open CatCrypt.Crypto.Optimizer.Rewrite.MonoidPowLadder

variable {m : ℕ}

/-! ## 1. Casting a natural-number power into `ZMod m` reduces it

The bridge between the abstract integer power and its modular image: the
canonical ring hom `ℕ → ZMod m` commutes with `npow`, so casting `g ^ n` to
`ZMod m` is the same as raising the cast of `g`.  This is exactly the modular
reduction, supplied by the quotient structure of `ZMod m`. -/

/-- **Casting commutes with power (modular reduction).**  The natural-number
    power `g ^ n`, cast into `ZMod m`, equals the cast of `g` raised to `n`:
    `((g ^ n : ℕ) : ZMod m) = ((g : ℕ) : ZMod m) ^ n`.  Reading right-to-left,
    `ZMod m` already reduces the power mod `m`. -/
theorem cast_pow_zmod (g n : ℕ) :
    ((g ^ n : ℕ) : ZMod m) = ((g : ℕ) : ZMod m) ^ n := by
  push_cast
  ring

/-! ## 2. The modular square-and-multiply ladder and its correctness

Instantiating `powLadder_correct` at the monoid `ZMod m` gives the modular
correctness theorem: the generic ladder, run in `ZMod m`, computes the reduced
power.  Composing with `cast_pow_zmod` expresses it as the integer power reduced
mod `m`. -/

/-- **The ladder in `ZMod m` computes the reduced power.**  A direct
    specialization of `powLadder_correct` to the monoid `ZMod m`: the
    square-and-multiply ladder driven by `bs` on a base in `ZMod m` equals that
    base raised to `bitsToNat bs`, already reduced mod `m`. -/
theorem powLadder_zmod_correct (bs : List Bool) (g : ZMod m) :
    powLadder bs g = g ^ (bitsToNat bs) :=
  powLadder_correct bs g

/-- **Modular square-and-multiply correctness.**  The generic ladder, run in the
    quotient ring `ZMod m` on the cast base `(g : ZMod m)`, computes the
    integer power `g ^ (bitsToNat bs)` reduced mod `m`:
    `powLadder bs ((g : ℕ) : ZMod m) = ((g ^ bitsToNat bs : ℕ) : ZMod m)`.

    Equivalently, feeding the binary digits of `n` (MSB-first) to `powLadder`
    over `ZMod m` yields `g ^ n mod m`.  This composes the *generic*
    `powLadder_correct` (the verified algorithm over any `[Monoid M]`) with
    *modular reduction*, the latter supplied for free by the quotient structure
    of `ZMod m` (via `cast_pow_zmod`). -/
theorem modPow_correct (bs : List Bool) (g : ℕ) :
    powLadder bs ((g : ℕ) : ZMod m) = ((g ^ bitsToNat bs : ℕ) : ZMod m) := by
  rw [powLadder_zmod_correct, cast_pow_zmod]

/-! ## 3. Worked example: `3 ^ 13 mod 7`

The bits `[true, true, false, true]` decode (MSB-first) to `13` (checked in
`MonoidPowLadderPass`).  Running the ladder on `(3 : ZMod 7)` reproduces
`3 ^ 13 mod 7 = 1594323 mod 7 = 3`. -/

/-- The modular ladder over `ZMod 7` computes `3 ^ 13 mod 7 = 3`. -/
example : powLadder [true, true, false, true] (3 : ZMod 7) = 3 := by decide

/-- The modular ladder's result matches the integer power reduced mod `7`,
    exhibited concretely:
    `powLadder [true,true,false,true] (3 : ZMod 7) = ((3 ^ 13 : ℕ) : ZMod 7)`.
    A direct instance of `modPow_correct` at `m := 7`, `g := 3`. -/
example : powLadder [true, true, false, true] ((3 : ℕ) : ZMod 7)
    = (((3 : ℕ) ^ bitsToNat [true, true, false, true] : ℕ) : ZMod 7) :=
  modPow_correct _ _

end CatCrypt.Crypto.Optimizer.Rewrite.ModPowGeneric
