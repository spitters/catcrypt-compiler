/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.Optimizer

/-!
# Dialect backend testing harness

Runs a canonical set of test programs through the **`catCryptDialect`** SSA
backend and verifies they produce the expected outputs (KAT-style).

The test programs are authored **directly** as `Com catCryptDialect` (the
MLIR-aligned `Com` dialect) and run through `Com.denote`.  Each case asserts
`denote input = expected` by `rfl`; failures surface as Lean type-check / `rfl`
errors.

## Harness shape

```
structure TestCase (Γ : Ctx) (t : CryptoTy) where
  prog : Com catCryptDialect Γ t   -- the dialect program
  input : Ctxt.Valuation Γ         -- initial valuation
  expected : t.denote              -- expected output value
  name : String                    -- for reporting
```
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.TestHarness

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Core

/-! ## 1. TestCase structure -/

/-- A dialect-backend test: program, input valuation, expected output. -/
structure TestCase (Γ : Ctxt catCryptDialect) (t : CryptoTy) where
  prog : Com catCryptDialect Γ t
  input : Ctxt.Valuation Γ
  expected : t.denote
  name : String := "<unnamed>"

/-! ## 2. Backend runner -/

/-- Run a `TestCase` under the `catCryptDialect` backend. -/
def runDialect {Γ : Ctxt catCryptDialect} {t : CryptoTy} (tc : TestCase Γ t) : t.denote :=
  tc.prog.denote tc.input

/-! ## 3. Test-case assertion -/

/-- Assert that a test case produces its expected value on the dialect
    backend. A type-level assertion: failures are compile-time errors. -/
def assertDialect {Γ : Ctxt catCryptDialect} {t : CryptoTy} (tc : TestCase Γ t) : Prop :=
  runDialect tc = tc.expected

/-! ## 4. Test suite

Each test is a theorem: if it type-checks, the test passes. -/

namespace Tests

/-- `const_3` — simplest test: a program that returns the constant `3`. -/
def const_3 : TestCase [] (.sword 8) where
  prog := .var { op := .bvConst 8 (3 : BitVec 8), retTy_eq := rfl, args := .nil } (.ret .here)
  input := HVector.nil
  expected := 3
  name := "const_3"

theorem const_3_ok : assertDialect const_3 := by
  show runDialect const_3 = (3 : BitVec 8)
  rfl

/-- `add_3_4` — straight-line addition: `let x=3; let y=4; let z=x+y; ret z`. -/
def add_3_4 : TestCase [] (.sword 8) where
  prog :=
    .var { op := .bvConst 8 (3 : BitVec 8), retTy_eq := rfl, args := .nil }
      (.var { op := .bvConst 8 (4 : BitVec 8), retTy_eq := rfl, args := .nil }
        (.var { op := .bvAdd 8, retTy_eq := rfl,
                args := .cons (.there .here) (.cons .here .nil) }
          (.ret .here)))
  input := HVector.nil
  expected := 7
  name := "add_3_4"

theorem add_3_4_ok : assertDialect add_3_4 := by
  show runDialect add_3_4 = (7 : BitVec 8)
  rfl

/-- `xor_5_3` — bitvec XOR: `let a=5; let b=3; ret a^^^b`. Expected: `6`. -/
def xor_5_3 : TestCase [] (.sword 8) where
  prog :=
    .var { op := .bvConst 8 (5 : BitVec 8), retTy_eq := rfl, args := .nil }
      (.var { op := .bvConst 8 (3 : BitVec 8), retTy_eq := rfl, args := .nil }
        (.var { op := .bvXor 8, retTy_eq := rfl,
                args := .cons (.there .here) (.cons .here .nil) }
          (.ret .here)))
  input := HVector.nil
  expected := 6
  name := "xor_5_3"

theorem xor_5_3_ok : assertDialect xor_5_3 := by
  show runDialect xor_5_3 = (6 : BitVec 8)
  rfl

/-- `ite_demo` — conditional: `let c=true; let a=10; let b=20; ret if c then a else b`. -/
def ite_demo : TestCase [] (.sword 8) where
  prog :=
    .var { op := .constBit true, retTy_eq := rfl, args := .nil }
      (.var { op := .bvConst 8 (10 : BitVec 8), retTy_eq := rfl, args := .nil }
        (.var { op := .bvConst 8 (20 : BitVec 8), retTy_eq := rfl, args := .nil }
          (.var { op := .ite (.sword 8), retTy_eq := rfl,
                  args := .cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil)) }
            (.ret .here))))
  input := HVector.nil
  expected := 10
  name := "ite_demo"

theorem ite_demo_ok : assertDialect ite_demo := by
  show runDialect ite_demo = (10 : BitVec 8)
  rfl

/-- `ite_demo_false` — ite branches the other way. -/
def ite_demo_false : TestCase [] (.sword 8) where
  prog :=
    .var { op := .constBit false, retTy_eq := rfl, args := .nil }
      (.var { op := .bvConst 8 (10 : BitVec 8), retTy_eq := rfl, args := .nil }
        (.var { op := .bvConst 8 (20 : BitVec 8), retTy_eq := rfl, args := .nil }
          (.var { op := .ite (.sword 8), retTy_eq := rfl,
                  args := .cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil)) }
            (.ret .here))))
  input := HVector.nil
  expected := 20
  name := "ite_demo_false"

theorem ite_demo_false_ok : assertDialect ite_demo_false := by
  show runDialect ite_demo_false = (20 : BitVec 8)
  rfl

/-- `memref_store_and_get` — store limb 0 = 42, read back, return. -/
def memref_store_and_get : TestCase [] (.sword 64) where
  prog :=
    .var { op := .memrefZero 3, retTy_eq := rfl, args := .nil }
      (.var { op := .bvConst 64 (42 : BitVec 64), retTy_eq := rfl, args := .nil }
        (.var { op := .memrefSet 3 0, retTy_eq := rfl,
                args := .cons (.there .here) (.cons .here .nil) }
          (.var { op := .memrefGet 3 0, retTy_eq := rfl, args := .cons .here .nil }
            (.ret .here))))
  input := HVector.nil
  expected := 42
  name := "memref_store_and_get"

theorem memref_store_and_get_ok : assertDialect memref_store_and_get := by
  show runDialect memref_store_and_get = (42 : BitVec 64)
  rfl

/-- `chained_arith` — mixed ops: `let a=2; let b=3; let c=a*b; let d=c+a; ret d`. -/
def chained_arith : TestCase [] (.sword 8) where
  prog :=
    .var { op := .bvConst 8 (2 : BitVec 8), retTy_eq := rfl, args := .nil }        -- a = 2
      (.var { op := .bvConst 8 (3 : BitVec 8), retTy_eq := rfl, args := .nil }     -- b = 3
        (.var { op := .bvMul 8, retTy_eq := rfl,
                args := .cons (.there .here) (.cons .here .nil) }                  -- c = a*b = 6
          (.var { op := .bvAdd 8, retTy_eq := rfl,
                  args := .cons .here (.cons (.there (.there .here)) .nil) }       -- d = c+a = 8
            (.ret .here))))
  input := HVector.nil
  expected := 8
  name := "chained_arith"

theorem chained_arith_ok : assertDialect chained_arith := by
  show runDialect chained_arith = (8 : BitVec 8)
  rfl

end Tests

/-! ## 5. Aggregate test reporter

A summary theorem: "all dialect tests pass" — type-checks iff every individual
test passes. Useful as a single CI sentinel. -/

/-- All dialect-backend tests produce their expected outputs. -/
theorem all_dialect_tests_pass :
    assertDialect Tests.const_3 ∧
    assertDialect Tests.add_3_4 ∧
    assertDialect Tests.xor_5_3 ∧
    assertDialect Tests.ite_demo ∧
    assertDialect Tests.ite_demo_false ∧
    assertDialect Tests.memref_store_and_get ∧
    assertDialect Tests.chained_arith :=
  ⟨Tests.const_3_ok, Tests.add_3_4_ok, Tests.xor_5_3_ok,
   Tests.ite_demo_ok, Tests.ite_demo_false_ok,
   Tests.memref_store_and_get_ok, Tests.chained_arith_ok⟩

end CatCrypt.Crypto.SecureCompilation.VIR.TestHarness
