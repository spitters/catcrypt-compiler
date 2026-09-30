/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelFlatten
public import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelFlatten
public import CatCrypt.Crypto.SecureCompilation.BigNatBitwise
public import CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba
public import CatCrypt.Crypto.SecureCompilation.BigNatShift
public import CatCrypt.Crypto.SecureCompilation.BigNatPow
public import CatCrypt.Crypto.SecureCompilation.BigNatGcd

/-!
# Limb kernels lowered to `natKernelDialect`

The little-endian base-`2^64` limb carrier `List (BitVec 64)` carries an
operation set — addition, subtraction, multiplication, the three bitwise
operations, the two shifts and exponentiation — each with a value
specification stated through the
abstraction function `bignumVal`. Each of those specifications says that the
limb operation is the corresponding `Nat` operation on the abstracted values,
and each of those `Nat` operations is an instruction of `natKernelDialect`.

This module states that correspondence as a lowering: `toNatOp` maps a limb
operation to its dialect instruction, and `lower_sound` says that abstracting
the limb result equals the dialect instruction applied to the abstracted
arguments. A limb loop over the carrier therefore has a single dialect
instruction as its image.

The operations split by the type of their second argument. `LimbOp` collects
the six whose second argument is a limb list, and `LimbNatOp` the three whose
second argument is a `Nat` (the two shift amounts and the exponent); both land
in `NatKernelOp`, whose arguments are two `Nat`s either way.

## Side conditions

There are none. `bnSub` is exact truncating subtraction and `Nat.sub`
truncates; the bitwise
operations zero-pad the shorter operand, matching the zero-extension in the
bit-indexed `Nat` operations. Carrier addition `BigNat.add` is `bnAdd` at
carry-in `0`, so the carry-in of `bnAdd` does not appear.

## Main results

* `limbDenote` / `limbNatDenote` — the two limb-operation denotations.
* `toNatOp` / `toNatOpN` — the maps into `NatKernelOp`.
* `lower_add`, `lower_sub`, `lower_mul`, `lower_land`, `lower_lor`,
  `lower_xor`, `lower_shiftLeft`, `lower_shiftRight`, `lower_pow` — the
  per-operation statements.
* `lower_sound` / `lower_sound_nat` — the combined statements.
* `lower_karatsuba` — the recursive Karatsuba multiply lowers to `.mul` too.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LimbToNat

open CatCrypt.Crypto.SecureCompilation
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NatKernel

/-! ## 1. The limb operations -/

/-- The limb operations whose second argument is a limb list. -/
inductive LimbOp where
  /-- Carrier addition `BigNat.add`. -/
  | add
  /-- Exact truncating carrier subtraction `BigNatKaratsuba.bnSub`. -/
  | sub
  /-- Schoolbook carrier multiplication `BigNat.mul`. -/
  | mul
  /-- Limb-wise AND with zero padding. -/
  | land
  /-- Limb-wise OR with zero padding. -/
  | lor
  /-- Limb-wise XOR with zero padding. -/
  | xor
  /-- Truncating carrier division `BigNatDivMod.div`, zero at a zero divisor. -/
  | div
  /-- Carrier remainder `BigNatDivMod.mod`, the dividend at a zero divisor. -/
  | mod
  /-- The Euclidean algorithm on the carrier, `BigNatGcd.gcd`. -/
  | gcd
  deriving DecidableEq, Repr

/-- The limb operations whose second argument is a `Nat`. -/
inductive LimbNatOp where
  /-- Bit shift left by a `Nat` amount, `BigNatShift.shl`. -/
  | shiftLeft
  /-- Bit shift right by a `Nat` amount, `BigNatShift.shr`. -/
  | shiftRight
  /-- Exponentiation by a `Nat` exponent, `BigNat.pow`. -/
  | pow
  deriving DecidableEq, Repr

/-- The denotation of a two-limb-list operation. -/
def limbDenote : LimbOp → List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | .add => BigNat.add
  | .sub => BigNatKaratsuba.bnSub
  | .mul => BigNat.mul
  | .land => BigNatBitwise.land
  | .lor => BigNatBitwise.lor
  | .xor => BigNatBitwise.xor
  | .div => BigNatDivMod.div
  | .mod => BigNatDivMod.mod
  | .gcd => BigNatGcd.gcd

/-- The denotation of a limb operation with a `Nat` second argument. -/
def limbNatDenote : LimbNatOp → List (BitVec 64) → Nat → List (BitVec 64)
  | .shiftLeft => BigNatShift.shl
  | .shiftRight => BigNatShift.shr
  | .pow => BigNat.pow

/-! ## 2. The maps into the dialect -/

/-- The dialect instruction a two-limb-list operation lowers to. -/
def toNatOp : LimbOp → NatKernelOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .land => .land
  | .lor => .lor
  | .xor => .xor
  | .div => .div
  | .mod => .mod
  | .gcd => .gcd

/-- The dialect instruction a `Nat`-argument limb operation lowers to. -/
def toNatOpN : LimbNatOp → NatKernelOp
  | .shiftLeft => .shiftLeft
  | .shiftRight => .shiftRight
  | .pow => .pow

/-! ## 3. Per-operation soundness

Each statement is the operation's value specification read as an equation
between the abstracted limb result and the dialect denotation of the
abstracted arguments. -/

theorem lower_add (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .add xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .add)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNat.add_val xs ys

theorem lower_sub (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .sub xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .sub)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNatKaratsuba.bnSub_val xs ys

theorem lower_mul (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .mul xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .mul)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNat.mul_val xs ys

theorem lower_land (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .land xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .land)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNatBitwise.land_val xs ys

theorem lower_lor (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .lor xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .lor)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNatBitwise.lor_val xs ys

theorem lower_xor (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .xor xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .xor)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNatBitwise.xor_val xs ys

theorem lower_shiftLeft (xs : List (BitVec 64)) (k : Nat) :
    bignumVal (limbNatDenote .shiftLeft xs k)
      = DialectDenote.denote (d := natKernelDialect) (toNatOpN .shiftLeft)
          (args2 (bignumVal xs) k) :=
  BigNatShift.shl_shiftLeft xs k

theorem lower_shiftRight (xs : List (BitVec 64)) (k : Nat) :
    bignumVal (limbNatDenote .shiftRight xs k)
      = DialectDenote.denote (d := natKernelDialect) (toNatOpN .shiftRight)
          (args2 (bignumVal xs) k) :=
  BigNatShift.shr_shiftRight xs k

theorem lower_pow (xs : List (BitVec 64)) (k : Nat) :
    bignumVal (limbNatDenote .pow xs k)
      = DialectDenote.denote (d := natKernelDialect) (toNatOpN .pow)
          (args2 (bignumVal xs) k) :=
  BigNat.pow_natPow xs k

/-- Abstracting the carrier quotient is the `Nat` quotient. -/
theorem lower_div (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .div xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .div)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNatDivMod.div_val xs ys

/-- Abstracting the carrier remainder is the `Nat` remainder. -/
theorem lower_mod (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .mod xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .mod)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNatDivMod.mod_val xs ys

/-- Abstracting the carrier gcd is the `Nat` gcd. -/
theorem lower_gcd (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote .gcd xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .gcd)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNatGcd.gcd_val xs ys

/-! ## 4. The combined statements -/

/-- **Lowering soundness, two-limb-list operations.** Abstracting the limb
    result of `op` equals the dialect instruction `toNatOp op` applied to the
    abstracted arguments.

    The instruction acts through `evalFlatOp` rather than
    `DialectDenote.denote`: for a variable `op` the argument-vector type
    `HVector _ (DialectSignature.sig (toNatOp op))` does not reduce to
    `HVector _ [.nat, .nat]`, so the denotation form of this statement needs a
    transport along `sig (toNatOp op) = [.nat, .nat]`. `evalFlatOp` is the
    instruction's action on two naturals, and the per-operation theorems above
    give the denotation form at each literal operation. -/
theorem lower_sound (op : LimbOp) (xs ys : List (BitVec 64)) :
    bignumVal (limbDenote op xs ys)
      = evalFlatOp (toNatOp op) (bignumVal xs) (bignumVal ys) := by
  cases op with
  | add => exact lower_add xs ys
  | sub => exact lower_sub xs ys
  | mul => exact lower_mul xs ys
  | land => exact lower_land xs ys
  | lor => exact lower_lor xs ys
  | xor => exact lower_xor xs ys
  | div => exact lower_div xs ys
  | mod => exact lower_mod xs ys
  | gcd => exact lower_gcd xs ys

/-- **Lowering soundness, `Nat`-argument operations.** Stated through
    `evalFlatOp` for the reason given at `lower_sound`. -/
theorem lower_sound_nat (op : LimbNatOp) (xs : List (BitVec 64)) (k : Nat) :
    bignumVal (limbNatDenote op xs k)
      = evalFlatOp (toNatOpN op) (bignumVal xs) k := by
  cases op with
  | shiftLeft => exact lower_shiftLeft xs k
  | shiftRight => exact lower_shiftRight xs k
  | pow => exact lower_pow xs k

/-- The recursive Karatsuba multiply has the same dialect image as
    `limbDenote .mul`. -/
theorem lower_karatsuba (xs ys : List (BitVec 64)) :
    bignumVal (BigNatKaratsuba.karatsuba xs ys)
      = DialectDenote.denote (d := natKernelDialect) (toNatOp .mul)
          (args2 (bignumVal xs) (bignumVal ys)) :=
  BigNatKaratsuba.karatsuba_val xs ys

end CatCrypt.Crypto.SecureCompilation.VIR.LimbToNat
