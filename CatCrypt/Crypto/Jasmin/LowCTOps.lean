/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTSExpr
public import HaxLean.ScalarOp

/-!
# Semantics of the typed scalar operators

The meanings of the operators `Hax.ScalarOp` that the front's builtin tables
give by string, as total functions of the operator:

* `ScalarOp.natSem` — the operation on natural-number arguments: the untagged
  arithmetic of the hax runtime on non-negative arguments (`Sub` undefined
  below zero), and the Rust unsigned operation of the tagged width on the
  arguments modulo `2^w` (shifts defined for an amount below `w`, rotations by
  the amount modulo `w`);
* `ScalarCallOp.toSExpr` and `ScalarOp.toSExpr?` — the scalar expression of a
  `scalar#` call, and `ScalarCallOp.toSExpr_eval`, its value under
  `SExpr.eval`.

The string tables of the front agree with these functions on `ScalarOp.name`
(`scalarCallSExpr_name` in `CatCrypt.Crypto.Hax.HaxToLowCT`,
`arithOpNat_name` in `CatCrypt.Crypto.Hax.HaxToLowCT_ArithLeaves`).
-/

@[expose] public section

namespace Hax

open CatCrypt.Crypto.Jasmin.LowCT (SExpr)

/-- The natural-number value of a `scalar#` operation: `SSub` truncates at
    `0`, the shifts are the exact shifts on `Nat`, and a comparison is `0` or
    `1`. -/
def ScalarCallOp.natSem : ScalarCallOp → Nat → Nat → Nat
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .bitAnd, a, b => a &&& b
  | .bitXor, a, b => a ^^^ b
  | .shr, a, b => a >>> b
  | .shl, a, b => a <<< b
  | .cmp .lt, a, b => if a < b then 1 else 0
  | .cmp .gt, a, b => if b < a then 1 else 0
  | .cmp .le, a, b => 1 - (if b < a then 1 else 0)
  | .cmp .ge, a, b => 1 - (if a < b then 1 else 0)
  | .cmp .eq, a, b => 1 - (if a < b then 1 else 0) - (if b < a then 1 else 0)
  | .cmp .ne, a, b => (if a < b then 1 else 0) + (if b < a then 1 else 0)

/-- The scalar expression of a `scalar#` operation on the operands `a` and
    `b`. -/
def ScalarCallOp.toSExpr : ScalarCallOp → SExpr → SExpr → SExpr
  | .add, a, b => .SAdd a b
  | .sub, a, b => .SSub a b
  | .mul, a, b => .SMul a b
  | .bitAnd, a, b => .SAnd a b
  | .bitXor, a, b => .SXor a b
  | .shr, a, b => .SShr a b
  | .shl, a, b => .SShl a b
  | .cmp .lt, a, b => .SLt a b
  | .cmp .gt, a, b => .SLt b a
  | .cmp .le, a, b => .SSub (.SLit 1) (.SLt b a)
  | .cmp .ge, a, b => .SSub (.SLit 1) (.SLt a b)
  | .cmp .eq, a, b => .SSub (.SSub (.SLit 1) (.SLt a b)) (.SLt b a)
  | .cmp .ne, a, b => .SAdd (.SLt a b) (.SLt b a)

/-- The scalar expression of a `scalar#` operation evaluates to its
    natural-number value. -/
theorem ScalarCallOp.toSExpr_eval (s : ScalarCallOp) (σ : String → Nat) (a b : SExpr) :
    (s.toSExpr a b).eval σ = s.natSem (a.eval σ) (b.eval σ) := by
  cases s with
  | cmp c => cases c <;> rfl
  | _ => rfl

namespace ScalarOp

/-- A binary operation on an argument list of length two. -/
def natBin (g : Nat → Nat → Option Nat) : List Nat → Option Nat
  | [a, b] => g a b
  | _ => none

/-- A unary operation on an argument list of length one. -/
def natUn (g : Nat → Nat) : List Nat → Option Nat
  | [a] => some (g a)
  | _ => none

/-- A ternary operation on an argument list of length three. -/
def natTer (g : Nat → Nat → Nat → Option Nat) : List Nat → Option Nat
  | [a, b, c] => g a b c
  | _ => none

/-- The operation of an operator on natural-number arguments. With `n` the bit
    width of the tag (`64` for `size`):
    * `add`, `mul`, `div`, `rem` and the untagged bitwise operators are the
      operations on `Nat`; `sub` is undefined when the result would be
      negative;
    * a tagged bitwise operator, wrapping arithmetic and `cast` act on the
      arguments modulo `2^n`; `not` at a width is the complement below `2^n`;
    * `shl`, `shr` at a width and the trait methods `shlM`, `shrM` are defined
      for an amount below `n`; the untagged `shl`, `shr` and `not` are
      undefined;
    * `rotl`, `rotr` rotate by the amount modulo `n`;
    * `mulhi` is the high `n` bits of the product of the arguments modulo
      `2^n`, and `mulmod` the product modulo a positive third argument;
    * `scalar s` is `ScalarCallOp.natSem s`. -/
def natSem : ScalarOp → List Nat → Option Nat
  | .add => natBin fun a b => some (a + b)
  | .sub => natBin fun a b => if b ≤ a then some (a - b) else none
  | .mul => natBin fun a b => some (a * b)
  | .div => natBin fun a b => some (a / b)
  | .rem => natBin fun a b => some (a % b)
  | .bitAnd none => natBin fun a b => some (a &&& b)
  | .bitAnd (some w) => natBin fun a b => some ((a % 2 ^ w.bits) &&& (b % 2 ^ w.bits))
  | .bitOr none => natBin fun a b => some (a ||| b)
  | .bitOr (some w) => natBin fun a b => some ((a % 2 ^ w.bits) ||| (b % 2 ^ w.bits))
  | .bitXor none => natBin fun a b => some (a ^^^ b)
  | .bitXor (some w) => natBin fun a b => some ((a % 2 ^ w.bits) ^^^ (b % 2 ^ w.bits))
  | .not none => fun _ => none
  | .not (some w) => natUn fun a => 2 ^ w.bits - 1 - a % 2 ^ w.bits
  | .shl none => fun _ => none
  | .shl (some w) => natBin fun a b =>
      if b < w.bits then some (((a % 2 ^ w.bits) <<< b) % 2 ^ w.bits) else none
  | .shr none => fun _ => none
  | .shr (some w) => natBin fun a b =>
      if b < w.bits then some ((a % 2 ^ w.bits) >>> b) else none
  | .shlM w => natBin fun a b =>
      if b < w.bits then some (((a % 2 ^ w.bits) <<< b) % 2 ^ w.bits) else none
  | .shrM w => natBin fun a b =>
      if b < w.bits then some ((a % 2 ^ w.bits) >>> b) else none
  | .rotl w => natBin fun a n => some
      ((((a % 2 ^ w.bits) <<< (n % w.bits)) ||| ((a % 2 ^ w.bits) >>> (w.bits - n % w.bits)))
        % 2 ^ w.bits)
  | .rotr w => natBin fun a n => some
      ((((a % 2 ^ w.bits) >>> (n % w.bits)) ||| ((a % 2 ^ w.bits) <<< (w.bits - n % w.bits)))
        % 2 ^ w.bits)
  | .wrappingAdd w => natBin fun a b => some ((a + b) % 2 ^ w.bits)
  | .wrappingSub w => natBin fun a b =>
      some ((a % 2 ^ w.bits + 2 ^ w.bits - b % 2 ^ w.bits) % 2 ^ w.bits)
  | .wrappingMul w => natBin fun a b => some ((a * b) % 2 ^ w.bits)
  | .mulhi w => natBin fun a b => some (((a % 2 ^ w.bits) * (b % 2 ^ w.bits)) >>> w.bits)
  | .mulmod w => natTer fun a b p =>
      if 0 < p then some (((a % 2 ^ w.bits) * (b % 2 ^ w.bits)) % p) else none
  | .cast w => natUn fun a => a % 2 ^ w.bits
  | .scalar s => natBin fun a b => some (s.natSem a b)

/-- The scalar expression of an operator on the operands `a` and `b`: the
    `scalar#` operations by `ScalarCallOp.toSExpr`, and `none` for every other
    operator. -/
def toSExpr? : ScalarOp → SExpr → SExpr → Option SExpr
  | .scalar s, a, b => some (s.toSExpr a b)
  | _, _, _ => none

end ScalarOp

end Hax
