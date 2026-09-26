/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Program

/-!
# Word operations of the hax front computed in the scalar heap

Two passes around `haxToLowCT` that lower the `u64` word arithmetic of an
extracted kernel to scalar expressions.

`fuseMulHiIdiom` is a pass on hax terms.  It replaces the Rust multiply-high
idiom `((a as u128) * (b as u128) >> 64) as u64`, which hax extracts as the call
chain `cast#64(Shr#128(Mul(cast#128(a), cast#128(b)), 64))` (`mulHiChain`), by
the single call `mulhi#64(a, b)` in the right-hand side of every binding and
assignment of the program spine.

`scalarizeWordOps` is a pass on `LowCT`.  It lowers every binding
`RLetZero x _ (RSeq (RCall f x [a, b]) body)` of a word call `f` of
`wordOpNames` to `RLetU64Zero x (RSeq (RScalarSetExpr x e) body)`, where `e` is
the scalar expression of `f` on the scalar slots `a` and `b` (`wordOpSExpr`):
the wrapping `u64` addition, subtraction and multiplication as `SAdd`, `SSub`
and `SMul`, `mulhi#64` as `SMulHiU`, the `u64` bitwise operations and shifts as
`SAnd`, `SXor`, `SShr` and `SShl`, and `Add` as `SAdd`.

The scalar expressions are read in the wrapping `u64` semantics
`SExpr.evalBV`, in which `SAdd`, `SSub` and `SMul` wrap modulo `2^64` as the
Rust operations do.

## Main definitions

* `mulHiChain`, `mulHiChainArgs`, `fuseMulHiIdiom` — the multiply-high idiom,
  its recogniser and the pass.
* `wordOpNames`, `wordOpNat`, `wordOpSExpr` — the word calls, their
  natural-number operations and their scalar expressions.
* `scalarizeWordOps` — the pass on `LowCT`.

## Main results

* `denote_mulHiChain` — under `MulHiBuiltins bi`, the idiom on two variables
  holding words below `2^64` runs as the call `mulhi#64` on them.
* `wordOpSExpr_evalBV` — the scalar expression of a word call evaluates in
  `SExpr.evalBV` to the natural-number operation of the call on the values of
  its operands.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote denoteArgs)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr sexprMulHiU sexprMulHiU_lt)

/-! ### The multiply-high idiom -/

/-- The Rust multiply-high idiom `((a as u128) * (b as u128) >> 64) as u64` as
    hax extracts it. -/
def mulHiChain (a b : ImpExpr) : ImpExpr :=
  .app "cast#64" [.app "Shr#128" [.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]],
    .lit (.int 64)]]

/-- The operands of the multiply-high idiom, when `e` is `mulHiChain a b`. -/
def mulHiChainArgs : ImpExpr → Option (ImpExpr × ImpExpr)
  | .app "cast#64" [.app "Shr#128" [.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]],
      .lit (.int 64)]] => some (a, b)
  | _ => none

theorem mulHiChainArgs_mulHiChain (a b : ImpExpr) :
    mulHiChainArgs (mulHiChain a b) = some (a, b) := rfl

/-- The call name of the multiply-high builtin: the high 64 bits of the
    `128`-bit product of two `64`-bit words. -/
def mulHiCallName : String := "mulhi#64"

/-- A right-hand side with the multiply-high idiom replaced by the call
    `mulhi#64` on its operands. -/
def fuseMulHiRhs (v : ImpExpr) : ImpExpr :=
  match mulHiChainArgs v with
  | some (a, b) => .app mulHiCallName [a, b]
  | none => v

/-- The pass replacing the multiply-high idiom by `mulhi#64` in the right-hand
    side of every binding and assignment of the program spine (bindings,
    sequences, branches and loop bodies). -/
def fuseMulHiIdiom : ImpExpr → ImpExpr
  | .letBind x v b => .letBind x (fuseMulHiRhs v) (fuseMulHiIdiom b)
  | .assign x v => .assign x (fuseMulHiRhs v)
  | .seq a b => .seq (fuseMulHiIdiom a) (fuseMulHiIdiom b)
  | .ifThenElse c t e => .ifThenElse c (fuseMulHiIdiom t) (fuseMulHiIdiom e)
  | .whileLoop c b => .whileLoop c (fuseMulHiIdiom b)
  | .whileFold c b => .whileFold c (fuseMulHiIdiom b)
  | .forFold i lo hi b => .forFold i lo hi (fuseMulHiIdiom b)
  | .forFoldRev i lo hi b => .forFoldRev i lo hi (fuseMulHiIdiom b)
  | .typeAscription e ty => .typeAscription (fuseMulHiIdiom e) ty
  | e => e

/-- The builtin facts the multiply-high idiom evaluates by: the casts to and
    from `u128` and the `u128` product and shift on operands below `2^64`, and
    `mulhi#64` as `sexprMulHiU`. -/
structure MulHiBuiltins (bi : Builtins) : Prop where
  cast128 : ∀ n : Nat, n < 2 ^ 64 → bi "cast#128" [.int n] = some (.int n)
  mul : ∀ n m : Nat, n < 2 ^ 64 → m < 2 ^ 64 →
    bi "Mul" [.int n, .int m] = some (.int ((n * m : Nat) : Int))
  shr128 : ∀ n : Nat, n < 2 ^ 128 →
    bi "Shr#128" [.int n, .int 64] = some (.int ((n >>> 64 : Nat) : Int))
  cast64 : ∀ n : Nat, n < 2 ^ 64 → bi "cast#64" [.int n] = some (.int n)
  mulhi : ∀ n m : Nat, n < 2 ^ 64 → m < 2 ^ 64 →
    bi mulHiCallName [.int n, .int m] = some (.int (sexprMulHiU n m))

/-- On words below `2^64`, `sexprMulHiU` is the product shifted right by `64`. -/
theorem sexprMulHiU_of_lt {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) :
    sexprMulHiU n m = (n * m) >>> 64 := by
  unfold sexprMulHiU
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm]

/-- The multiply-high idiom on two variables holding words below `2^64` runs as
    the call `mulhi#64` on them. -/
theorem denote_mulHiChain {bi : Builtins} (hbi : MulHiBuiltins bi) (fuel : Nat) (env : Env)
    (a b : String) (n m : Nat) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (ha : env a = some (.int n)) (hb : env b = some (.int m)) :
    (denote bi fuel (mulHiChain (.var a) (.var b))).run env =
      (denote bi fuel (.app mulHiCallName [.var a, .var b])).run env := by
  have hNil : (denoteArgs bi fuel ([] : List ImpExpr)).run env = (some [], env) := by
    unfold denoteArgs; rfl
  have hnm : n * m < 2 ^ 128 := by
    have h := Nat.mul_lt_mul'' hn hm
    rwa [← Nat.pow_add] at h
  have hhi : (n * m) >>> 64 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hnm)
  simp only [mulHiChain, denote_app_run_eq, denoteArgs_cons_run_eq, denote_var_run_eq,
    denote_lit_eq, ha, hb, hNil, Option.map_some, Value.ofLit, hbi.cast128 n hn,
    hbi.cast128 m hm, hbi.mul n m hn hm, hbi.shr128 _ hnm, hbi.cast64 _ hhi,
    hbi.mulhi n m hn hm, sexprMulHiU_of_lt hn hm]

/-! ### Word operations computed in the scalar heap -/

/-- The two-operand word calls lowered to scalar expressions. -/
def wordOpNames : List String :=
  ["wrapping_add#64", "wrapping_sub#64", "wrapping_mul#64", "mulhi#64",
   "BitAnd#64", "BitXor#64", "Shr#64", "Shl#64", "Add"]

/-- The natural-number operation of a word call: the Rust `u64` operation of the
    tagged names on the operands modulo `2^64` (shifts defined for an amount
    below `64`), `mulhi#64` the high word of the product, and `Add` the sum. -/
def wordOpNat (f : String) (a b : Nat) : Option Nat :=
  match f with
  | "wrapping_add#64" => some ((a + b) % 2 ^ 64)
  | "wrapping_sub#64" => some ((a % 2 ^ 64 + 2 ^ 64 - b % 2 ^ 64) % 2 ^ 64)
  | "wrapping_mul#64" => some ((a * b) % 2 ^ 64)
  | "mulhi#64" => some (sexprMulHiU a b)
  | "BitAnd#64" => some ((a % 2 ^ 64) &&& (b % 2 ^ 64))
  | "BitXor#64" => some ((a % 2 ^ 64) ^^^ (b % 2 ^ 64))
  | "Shr#64" => if b < 64 then some ((a % 2 ^ 64) >>> b) else none
  | "Shl#64" => if b < 64 then some (((a % 2 ^ 64) <<< b) % 2 ^ 64) else none
  | "Add" => some (a + b)
  | _ => none

/-- The scalar expression of the word call `f` on the operands `a` and `b`. -/
def wordOpSExpr (f : String) (a b : SExpr) : Option SExpr :=
  match f with
  | "wrapping_add#64" => some (.SAdd a b)
  | "wrapping_sub#64" => some (.SSub a b)
  | "wrapping_mul#64" => some (.SMul a b)
  | "mulhi#64" => some (.SMulHiU a b)
  | "BitAnd#64" => some (.SAnd a b)
  | "BitXor#64" => some (.SXor a b)
  | "Shr#64" => some (.SShr a b)
  | "Shl#64" => some (.SShl a b)
  | "Add" => some (.SAdd a b)
  | _ => none

/-- The scalar expression of a call is defined exactly on the word calls. -/
theorem wordOpSExpr_isSome (f : String) (a b : SExpr) :
    (wordOpSExpr f a b).isSome = wordOpNames.contains f := by
  unfold wordOpSExpr wordOpNames
  split <;> simp_all

/-- The scalar expression of a word call evaluates, in the wrapping `u64`
    semantics `SExpr.evalBV`, to the natural-number operation of the call on the
    values of its operands, when that operation is defined and below `2^64`. -/
theorem wordOpSExpr_evalBV {f : String} {ea eb se : SExpr} {r : Nat}
    (β : String → BitVec 64) (hse : wordOpSExpr f ea eb = some se)
    (hr : wordOpNat f (ea.evalBV β).toNat (eb.evalBV β).toNat = some r) (hlt : r < 2 ^ 64) :
    (se.evalBV β).toNat = r := by
  have hA := (ea.evalBV β).isLt
  have hB := (eb.evalBV β).isLt
  unfold wordOpSExpr at hse
  unfold wordOpNat at hr
  split at hse <;> cases hse <;> simp only [Option.some.injEq] at hr
  all_goals
    try (split at hr <;> [simp only [Option.some.injEq] at hr; cases hr])
    subst hr
    simp only [SExpr.evalBV, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul,
      BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB,
      Nat.mod_eq_of_lt (sexprMulHiU_lt _ _)]
    try omega

/-! ### The lowering pass -/

/-- The pass lowering every binding `let x = f(a, b)` of a word call `f` of
    `wordOpNames` to the scalar assignment `RScalarSetExpr x e` of its scalar
    expression `e` on the scalar slots `a` and `b`, inside `RLetU64Zero x`. -/
def scalarizeWordOps : LowCT → LowCT
  | .RLetZero x t (.RSeq (.RCall f dest [a, b]) body) =>
      match wordOpSExpr f (.SVar a.locVar) (.SVar b.locVar) with
      | some se =>
          if dest.locVar = x then
            .RLetU64Zero x (.RSeq (.RScalarSetExpr x se) (scalarizeWordOps body))
          else .RLetZero x t (.RSeq (.RCall f dest [a, b]) (scalarizeWordOps body))
      | none => .RLetZero x t (.RSeq (.RCall f dest [a, b]) (scalarizeWordOps body))
  | .RSeq a b => .RSeq (scalarizeWordOps a) (scalarizeWordOps b)
  | .RLetZero x t b => .RLetZero x t (scalarizeWordOps b)
  | .RLetU64Zero x b => .RLetU64Zero x (scalarizeWordOps b)
  | .RIfNz v t e => .RIfNz v (scalarizeWordOps t) (scalarizeWordOps e)
  | .RWhileNz v b => .RWhileNz v (scalarizeWordOps b)
  | .RFor x n b => .RFor x n (scalarizeWordOps b)
  | .RForRuntime x bound b => .RForRuntime x bound (scalarizeWordOps b)
  | .RBlock b => .RBlock (scalarizeWordOps b)
  | c => c

end CatCrypt.Crypto.Hax
