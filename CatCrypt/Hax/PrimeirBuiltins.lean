/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.ZMod.Basic
public meta import CatCrypt.Hax.Semantics
public import CatCrypt.Hax.Semantics

/-!
# Prime-field crypto-op builtins for the hax reference interpreter

`CatCrypt.Hax.Semantics` denotes an `ImpExpr` under a `Builtins` table
(`String → List Value → Option Value`). Its `defaultBuiltins` covers integer
arithmetic and comparisons but the bare `Field` heads that `haxpipeT` emits for a
`primeir-hax` `Field` call (`"mul"`, `"add"`, `"sub"`, `"neg"`, `"inv"` — see
`CompileFromHaxPrimeIrFront`) reduce over `ZMod p`, not over `ℤ`. This module
supplies the interpreter-side denotation of those prime-field ops.

## Value representation of a field element

A field element is carried by the interpreter as `Value.int (n : Int)`, the same
constructor `haxpipeT` produces for a `Field` variable. The element is the residue
class of `n`; `primeirBuiltins p` keeps the payload canonical in `[0, p)` for
`0 < p` by reducing with `Int.emod` (`%`). The correspondence to `ZMod p` is the
map `n ↦ (n : ZMod p)`; `primeirBuiltins_*_zmod` state that each op agrees with the
`ZMod p` operation under this map.

## Ops

* `"mul"`, `"add"`, `"sub"` — binary, `(a ⋆ b) % p`.
* `"neg"` — unary, `(-a) % p`.
* `"inv"` — unary modular inverse, `((a : ZMod p)⁻¹).val`. Expressible directly on
  the `Value.int` payload through `ZMod p`'s computable `Inv`.

Unrecognized heads fall through to `defaultBuiltins`, so comparisons, booleans,
option/result wrappers, and any non-field `"mul"`/`"add"` shapes keep their
default meaning.
-/

@[expose] public section

namespace CatCrypt.Hax

/-- Extend `defaultBuiltins` with the prime-field ops over the residue
    representation `Value.int n ↦ (n : ZMod p)`.

    The four ring ops reduce with `Int.emod` so the payload stays canonical in
    `[0, p)` when `0 < p`; `"inv"` uses `ZMod p`'s inverse. Any head or argument
    shape that is not a recognized field op falls through to `defaultBuiltins`. -/
def primeirBuiltins (p : Nat) : Builtins
  | "mul", [.int a, .int b] => some (.int ((a * b) % (p : Int)))
  | "add", [.int a, .int b] => some (.int ((a + b) % (p : Int)))
  | "sub", [.int a, .int b] => some (.int ((a - b) % (p : Int)))
  | "neg", [.int a]         => some (.int ((-a) % (p : Int)))
  | "inv", [.int a]         => some (.int (((a : ZMod p)⁻¹).val : Int))
  | f, args => defaultBuiltins f args

/-! ### Definitional characterizations -/

@[simp] theorem primeirBuiltins_mul (p : Nat) (a b : Int) :
    primeirBuiltins p "mul" [.int a, .int b] = some (.int ((a * b) % (p : Int))) := rfl

@[simp] theorem primeirBuiltins_add (p : Nat) (a b : Int) :
    primeirBuiltins p "add" [.int a, .int b] = some (.int ((a + b) % (p : Int))) := rfl

@[simp] theorem primeirBuiltins_sub (p : Nat) (a b : Int) :
    primeirBuiltins p "sub" [.int a, .int b] = some (.int ((a - b) % (p : Int))) := rfl

@[simp] theorem primeirBuiltins_neg (p : Nat) (a : Int) :
    primeirBuiltins p "neg" [.int a] = some (.int ((-a) % (p : Int))) := rfl

@[simp] theorem primeirBuiltins_inv (p : Nat) (a : Int) :
    primeirBuiltins p "inv" [.int a] = some (.int (((a : ZMod p)⁻¹).val : Int)) := rfl

/-- Comparisons and other non-field heads fall through unchanged. -/
theorem primeirBuiltins_le (p : Nat) (a b : Int) :
    primeirBuiltins p "le" [.int a, .int b] = some (.bool (a ≤ b)) := rfl

/-! ### `ZMod p` correspondence

Each recognized op agrees with the corresponding `ZMod p` operation under the
residue map `n ↦ (n : ZMod p)`. -/

theorem primeirBuiltins_mul_zmod (p : Nat) (a b : Int) :
    (((a * b) % (p : Int) : Int) : ZMod p) = (a : ZMod p) * (b : ZMod p) := by
  rw [ZMod.intCast_mod, Int.cast_mul]

theorem primeirBuiltins_add_zmod (p : Nat) (a b : Int) :
    (((a + b) % (p : Int) : Int) : ZMod p) = (a : ZMod p) + (b : ZMod p) := by
  rw [ZMod.intCast_mod, Int.cast_add]

theorem primeirBuiltins_sub_zmod (p : Nat) (a b : Int) :
    (((a - b) % (p : Int) : Int) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  rw [ZMod.intCast_mod, Int.cast_sub]

theorem primeirBuiltins_neg_zmod (p : Nat) (a : Int) :
    (((-a) % (p : Int) : Int) : ZMod p) = -(a : ZMod p) := by
  rw [ZMod.intCast_mod, Int.cast_neg]

/-! ### Concrete evaluation checks (p = 7) -/

#guard primeirBuiltins 7 "mul" [.int 3, .int 5] == some (.int 1)   -- 15 % 7 = 1
#guard primeirBuiltins 7 "add" [.int 4, .int 5] == some (.int 2)   -- 9  % 7 = 2
#guard primeirBuiltins 7 "sub" [.int 2, .int 5] == some (.int 4)   -- -3 % 7 = 4
#guard primeirBuiltins 7 "neg" [.int 3] == some (.int 4)           -- -3 % 7 = 4
-- non-field head falls through to defaultBuiltins:
#guard primeirBuiltins 7 "le" [.int 2, .int 5] == some (.bool true)

/-! ### End-to-end `denote` check

The `Field::mul x y` call node `haxpipeT` emits (`ImpExpr.app "mul" [x, y]`, per
`CompileFromHaxPrimeIrFront`) evaluates under `primeirBuiltins p` to the field
product of the bound operands. -/

/-- The bare-headed `Field::mul` call node, exactly as the front sees it. -/
def fieldMulCall : ImpExpr := .app "mul" [.var "x", .var "y"]

/-- Environment binding the two `Field` operands. -/
def demoEnv : Env := (Env.empty.extend "x" (.int 3)).extend "y" (.int 5)

/-- Result of running the interpreter on the emitted `Field::mul` node. -/
def demoResult : Outcome := (denote (primeirBuiltins 7) 100 fieldMulCall).run' demoEnv

-- Running the interpreter on the `Field::mul` node with `primeirBuiltins 7`
-- yields `3 * 5 = 15 ≡ 1 (mod 7)`.
#guard demoResult == .val (.int 1)

end CatCrypt.Hax
