/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# VIR example: a tiny arithmetic dialect

Smoke-tests the VIR framework with a single-type, three-op dialect:
`add`, `mul`, `const`. Shows that `Dialect` / `DialectSignature` /
`DialectDenote` / `Expr` / `Com` work end-to-end.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.ExampleTest

open CatCrypt.Crypto.SecureCompilation.VIR

inductive ArithTy where
  | nat
  deriving DecidableEq

inductive ArithOp where
  | const (n : Nat)
  | add
  | mul
  deriving DecidableEq

@[reducible] instance : TyDenote ArithTy where
  denote
    | .nat => Nat

-- DEPRECATED: example-only, superseded by `mlirArithDialect`
-- (`VIR/MlirArithDialect.lean`). This dialect exists solely to smoke-test the
-- VIR framework end-to-end in this illustrative, unimported file; it is not on
-- any emit/lowering path and has no consumer outside this module.
@[reducible] def arithDialect : Dialect := { Op := ArithOp, Ty := ArithTy }

instance : DialectSignature arithDialect where
  sig
    | .const _ => []
    | .add => [.nat, .nat]
    | .mul => [.nat, .nat]
  ret
    | .const _ => .nat
    | .add => .nat
    | .mul => .nat

instance : DialectDenote arithDialect where
  denote
    | .const n, .nil => (n : Nat)
    | .add, .cons (a : Nat) (.cons (b : Nat) .nil) => a + b
    | .mul, .cons (a : Nat) (.cons (b : Nat) .nil) => a * b

-- A program: let x = const 3; let y = const 4; let z = add x y; mul z z
-- = 49.
def prog : Com arithDialect [] .nat :=
  .var (.mk (.const 3) rfl .nil)
    (.var (.mk (.const 4) rfl .nil)
      (.var (.mk .add rfl (.cons (.there .here) (.cons .here .nil)))
        (.var (.mk .mul rfl (.cons .here (.cons .here .nil)))
          (.ret .here))))

example : prog.denote .nil = (49 : Nat) := by
  show (49 : Nat) = (49 : Nat); rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ExampleTest
