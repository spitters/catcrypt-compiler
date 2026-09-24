/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.Jasmin.BignumExec
public import Plausible


@[expose] public section
set_option autoImplicit false

/-!
# Property-based tests for BignumExec primitives

Plausible-driven tests for `BignumExec`'s low-level arithmetic
primitives (`addCarry`, `subBorrow`, `mulx`, `addCarryIn`, `subBorrowIn`).
These complement the existing in-file `native_decide` smoke tests:
* Smoke tests check fixed inputs.
* PBT tests check ~100 random inputs per property.

Rather than testing the full `bignumExec` interpreter (which would
need custom `Sampleable`/`Shrinkable` instances for `InstrR`,
`BignumState`, etc.), this file targets the **leaf primitives** —
the per-intrinsic functions whose correctness `bignumExec` composes.
The intrinsic primitives are the natural granularity for
property-based testing because:

1. Their domain is `BitVec 64` (already has `Sampleable` via `Nat`).
2. Their properties are first-order arithmetic identities.
3. The `bignumExec` body interpretation is a deterministic walk over
   them — failures at the primitive level surface bugs at the
   interpreter level too.

## Test inventory

| Property | Coverage |
|----------|----------|
| `addCarry` correctness | sum mod 2^64 + carry-out flag |
| `subBorrow` correctness | difference mod 2^64 + borrow-out flag |
| `addCarryIn` agreement | matches `addCarry a b` when carry_in = 0 |
| `subBorrowIn` agreement | matches `subBorrow a b` when borrow_in = 0 |
| `mulx` correctness | `(hi << 64) ∣ lo = a · b` (full 128-bit product) |
| XOR self-zero | `a ^^^ a = 0` (XOR-clear idiom) |
| 2-limb add chain | ADD + ADC produces correct sum mod 2^128 |

## Why `#eval Testable.check` (not `plausible`)

The `plausible` *tactic* closes the goal with an admitted proof term;
it runs as a runtime test, not a compile-time proof. An audit-clean
PBT file needs every goal closed: an admitted term counted by the
audit tools would be a regression signal.

`#eval Plausible.Testable.check (∀ ...` runs the same property
test at *elaboration time* (during `lake build`) without leaving an
admitted proof in any term. If the property fails, build output shows the
counter-example; if it passes, build output shows
"Unable to find a counter-example".

Build-time cost: each `#eval` runs ~100 random trials per
property. Total elaboration ~2-3s for the file.
-/

namespace CatCrypt.Crypto.Jasmin.BignumExec.Pbt

open CatCrypt.Crypto.Jasmin.BignumExec

/-! ## addCarry / subBorrow leaf-primitive tests -/

/-! `addCarry a b = (cf, r)` where `r = (a + b) mod 2^64` and
    `cf = 1 ↔ a.toNat + b.toNat ≥ 2^64`. -/
#eval Plausible.Testable.check (∀ (a b : BitVec 64),
    let (cf, r) := addCarry a b
    r = a + b ∧ (cf.toNat = 1 ↔ a.toNat + b.toNat ≥ 2^64))

/-! `subBorrow a b = (cf, r)` where `r = (a - b) mod 2^64` and
    `cf = 1 ↔ a.toNat < b.toNat`. -/
#eval Plausible.Testable.check (∀ (a b : BitVec 64),
    let (cf, r) := subBorrow a b
    r = a - b ∧ (cf.toNat = 1 ↔ a.toNat < b.toNat))

/-! `addCarryIn a b 0 = addCarry a b` (with-carry-in degenerates to
    no-carry-in when carry_in = 0). -/
#eval Plausible.Testable.check (∀ (a b : BitVec 64),
    addCarryIn a b 0 = addCarry a b)

/-! `subBorrowIn a b 0 = subBorrow a b` (with-borrow-in degenerates). -/
#eval Plausible.Testable.check (∀ (a b : BitVec 64),
    subBorrowIn a b 0 = subBorrow a b)

/-! ## mulx leaf-primitive tests -/

/-! `mulx a b = (hi, lo)` where `(hi.toNat <<< 64) ||| lo.toNat =
    a.toNat * b.toNat` (full 128-bit product split into hi/lo). -/
#eval Plausible.Testable.check (∀ (a b : BitVec 64),
    let (hi, lo) := mulx a b
    hi.toNat * 2^64 + lo.toNat = a.toNat * b.toNat)

/-! ## XOR-clear idiom -/

/-! `XOR_64`'s self-clear: any value XORed with itself yields 0. The
    bignum interpreter relies on this for the standard `xor x, x` →
    `x = 0` assembler idiom. -/
#eval Plausible.Testable.check (∀ (a : BitVec 64), a ^^^ a = 0)

/-! ## addCarry chain (2-limb addition) -/

/-! 2-limb addition via ADD + ADC produces the correct sum mod 2^128. -/
#eval Plausible.Testable.check (∀ (a0 a1 b0 b1 : BitVec 64),
    let (cf0, r0) := addCarry a0 b0
    let (_cf1, r1) := addCarryIn a1 b1 cf0
    r1.toNat * 2^64 + r0.toNat =
      (a1.toNat * 2^64 + a0.toNat + b1.toNat * 2^64 + b0.toNat) % 2^128)

end CatCrypt.Crypto.Jasmin.BignumExec.Pbt
