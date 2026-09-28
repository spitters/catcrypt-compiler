/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Program
public import CatCrypt.Crypto.SecureCompilation.Ascent.SExprOrNot

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

The `u8`, `u16`, `u32` and `usize` word calls, the rotations at every width and
the `u64` bitwise OR (`narrowOpOf`), the casts to at most `64` bits
(`narrowCastOf`) and the complements `Not#w` (`narrowNotOf`) act on values held
in `u64` slots: their scalar expressions are the `u64` operations masked to the
width (`NarrowOp.sexpr`, `narrowMask`), OR and NOT expressed over `SXor` and
`SAnd` (`sOrExpr`, `sNotExpr`), a rotation as the OR of two shifts of the masked
operand by the amount modulo the width (`narrowRotSExpr`), and
`scalarizeNarrowIn` lowers their bindings.  A cast is lowered only when its
operand is a name the pass knows to hold a word below `2^64` (`bindsWord`): the
source width of a cast is not in its name, and a `u128` operand is not held in a
`u64` slot.

`fuseMulModIdiom` replaces the Rust modular-multiplication idiom
`((a as u128) * (b as u128) % (m as u128)) as u64`, inline (`mulModChain`) or with
the product bound first (`mulModLet`), by the call `mulmod#64(a, b, m)`.
`scalarizeMulMod m p` lowers a binding of that call whose modulus is the variable
`m` holding `p` to `mulModSExpr p a b`: Barrett reduction by the constant `p`
of the product of the Barrett reductions of `a` and `b`, exact for `1 < p < 2^32`.

## Main definitions

* `mulHiChain`, `mulHiChainArgs`, `fuseMulHiIdiom` — the multiply-high idiom,
  its recogniser and the pass.
* `wordOpNames`, `wordOpNat`, `wordOpSExpr` — the word calls, their
  natural-number operations and their scalar expressions.
* `scalarizeWordOps` — the pass on `LowCT`.
* `NarrowOp`, `narrowOpOf`, `narrowCastOf`, `narrowNotOf`, `narrowMask`,
  `narrowAmt`, `narrowRotSExpr`, `narrowNotSExpr`, `narrowOpSExpr` — the
  width-tagged word calls, casts and complements and their scalar expressions.
* `wordResultCall`, `bindsWord`, `narrowUnSExpr`, `narrowLetIn`,
  `scalarizeNarrowIn` — the names known to hold words, and the width-tracking
  lowering of the narrow bindings.
* `barrettRedSExpr`, `mulModSExpr` — reduction and modular multiplication by a
  constant modulus as scalar expressions.
* `mulModChain`, `mulModLet`, `fuseMulModIdiom`, `MulModBuiltins` — the
  modular-multiplication idiom, its fusion and the builtin facts it runs by.
* `mapLetZero`, `scalarizeNarrowOps`, `scalarizeMulMod` — the passes on `LowCT`.

## Main results

* `denote_mulHiChain` — under `MulHiBuiltins bi`, the idiom on two variables
  holding words below `2^64` runs as the call `mulhi#64` on them.
* `wordOpSExpr_evalBV` — the scalar expression of a word call evaluates in
  `SExpr.evalBV` to the natural-number operation of the call on the values of
  its operands.
* `NarrowOp.sexpr_evalBV`, `narrowMask_evalBV`, `narrowNotSExpr_evalBV` — the
  same for the width-tagged operations, casts and complements;
  `narrowRotr_evalBV`, `narrowRotl_evalBV` for the rotations.
* `narrowLetIn_op`, `narrowLetIn_cast`, `narrowLetIn_not` — the lowering of a
  binding is the scalar assignment the step lemmas of `HaxToLowCTWordOpsSim`
  are stated on.
* `barrett64_bound`, `barrettRedSExpr_evalBV`, `mulModSExpr_evalBV` — Barrett's
  estimate and the value of the modular scalar expressions.
* `denote_mulModChain`, `denote_mulModLet`, `denote_mulModCall` — both forms of
  the idiom run as the call `mulmod#64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote denoteArgs)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located sexprMulHiU sexprMulHiU_lt)

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

/-! ### Word operations of the narrow widths -/

/-- The two-operand operations of the unsigned widths held in `u64` slots. -/
inductive NarrowOp where
  | add | sub | mul | and | or | xor | shl | shr | rotr | rotl
  deriving DecidableEq, Repr

/-- The natural-number operation of `op` at width `w`: the Rust `u<w>` operation
    on the operands read modulo `2^w`, the shifts defined for an amount below
    `w`, the rotations by the amount modulo `w`. -/
def NarrowOp.nat (w : Nat) : NarrowOp → Nat → Nat → Option Nat
  | .add, a, b => some ((a + b) % 2 ^ w)
  | .sub, a, b => some ((a % 2 ^ w + 2 ^ w - b % 2 ^ w) % 2 ^ w)
  | .mul, a, b => some ((a * b) % 2 ^ w)
  | .and, a, b => some ((a % 2 ^ w) &&& (b % 2 ^ w))
  | .or, a, b => some ((a % 2 ^ w) ||| (b % 2 ^ w))
  | .xor, a, b => some ((a % 2 ^ w) ^^^ (b % 2 ^ w))
  | .shl, a, b => if b < w then some (((a % 2 ^ w) <<< b) % 2 ^ w) else none
  | .shr, a, b => if b < w then some ((a % 2 ^ w) >>> b) else none
  | .rotr, a, b => some (_root_.Hax.rotrNat w a b)
  | .rotl, a, b => some (_root_.Hax.rotlNat w a b)

/-- The scalar expression `e` masked to its low `w` bits. -/
def narrowMask (w : Nat) (e : SExpr) : SExpr := .SAnd e (.SLit (2 ^ w - 1))

/-- The rotation amount `b` modulo a width `w` that is a power of two:
    `b &&& (w - 1)`. -/
def narrowAmt (w : Nat) (b : SExpr) : SExpr := .SAnd b (.SLit (w - 1))

/-- The rotation of the `w`-bit word `x` by the amount `k < w`: the disjunction
    of the shift `sh₁ x k` and the shift `sh₂ x (w - k)`, masked to `w` bits.  For
    `k = 0` both halves are `x` or one is `0`, so the disjunction is `x`. -/
def narrowRotSExpr (w : Nat) (sh₁ sh₂ : SExpr → SExpr → SExpr) (x k : SExpr) : SExpr :=
  narrowMask w (SecureCompilation.Ascent.sOrExpr (sh₁ x k) (sh₂ x (.SSub (.SLit w) k)))

/-- The scalar expression of `op` at width `w` on the `u64` scalar expressions
    `a` and `b`: the `u64` operation masked to `w` bits, for `shr` the shift
    of the masked operand, and for the rotations `narrowRotSExpr` of the masked
    operand by the amount modulo `w`. -/
def NarrowOp.sexpr (w : Nat) : NarrowOp → SExpr → SExpr → SExpr
  | .add, a, b => narrowMask w (.SAdd a b)
  | .sub, a, b => narrowMask w (.SSub a b)
  | .mul, a, b => narrowMask w (.SMul a b)
  | .and, a, b => narrowMask w (.SAnd a b)
  | .or, a, b => narrowMask w (SecureCompilation.Ascent.sOrExpr a b)
  | .xor, a, b => narrowMask w (.SXor a b)
  | .shl, a, b => narrowMask w (.SShl a b)
  | .shr, a, b => .SShr (narrowMask w a) b
  | .rotr, a, b => narrowRotSExpr w .SShr .SShl (narrowMask w a) (narrowAmt w b)
  | .rotl, a, b => narrowRotSExpr w .SShl .SShr (narrowMask w a) (narrowAmt w b)

/-- The width and operation of a width-tagged word call: the `u8`, `u16`,
    `u32` and `usize` operations (`usize` of width `64`), the rotations at every
    width, and the `u64` bitwise OR. -/
def narrowOpOf : String → Option (Nat × NarrowOp)
  | "wrapping_add#8" => some (8, .add)
  | "wrapping_sub#8" => some (8, .sub)
  | "wrapping_mul#8" => some (8, .mul)
  | "BitAnd#8" => some (8, .and)
  | "BitOr#8" => some (8, .or)
  | "BitXor#8" => some (8, .xor)
  | "Shl#8" => some (8, .shl)
  | "Shr#8" => some (8, .shr)
  | "wrapping_add#16" => some (16, .add)
  | "wrapping_sub#16" => some (16, .sub)
  | "wrapping_mul#16" => some (16, .mul)
  | "BitAnd#16" => some (16, .and)
  | "BitOr#16" => some (16, .or)
  | "BitXor#16" => some (16, .xor)
  | "Shl#16" => some (16, .shl)
  | "Shr#16" => some (16, .shr)
  | "wrapping_add#32" => some (32, .add)
  | "wrapping_sub#32" => some (32, .sub)
  | "wrapping_mul#32" => some (32, .mul)
  | "BitAnd#32" => some (32, .and)
  | "BitOr#32" => some (32, .or)
  | "BitXor#32" => some (32, .xor)
  | "Shl#32" => some (32, .shl)
  | "Shr#32" => some (32, .shr)
  | "BitOr#64" => some (64, .or)
  | "wrapping_add#size" => some (64, .add)
  | "wrapping_sub#size" => some (64, .sub)
  | "wrapping_mul#size" => some (64, .mul)
  | "BitAnd#size" => some (64, .and)
  | "BitOr#size" => some (64, .or)
  | "BitXor#size" => some (64, .xor)
  | "Shl#size" => some (64, .shl)
  | "Shr#size" => some (64, .shr)
  | "rotate_right#8" => some (8, .rotr)
  | "rotate_right#16" => some (16, .rotr)
  | "rotate_right#32" => some (32, .rotr)
  | "rotate_right#64" => some (64, .rotr)
  | "rotate_right#size" => some (64, .rotr)
  | "rotate_left#8" => some (8, .rotl)
  | "rotate_left#16" => some (16, .rotl)
  | "rotate_left#32" => some (32, .rotl)
  | "rotate_left#64" => some (64, .rotl)
  | "rotate_left#size" => some (64, .rotl)
  | _ => none

/-- The width of a cast call to an unsigned width of at most `64` bits: the
    truncations to `8`, `16` and `32` bits, and the casts to `u64` and `usize`,
    which on a word below `2^64` are the identity. -/
def narrowCastOf : String → Option Nat
  | "cast#8" => some 8
  | "cast#16" => some 16
  | "cast#32" => some 32
  | "cast#64" => some 64
  | "cast#size" => some 64
  | _ => none

/-- The width of a complement call `Not#w`. -/
def narrowNotOf : String → Option Nat
  | "Not#8" => some 8
  | "Not#16" => some 16
  | "Not#32" => some 32
  | "Not#64" => some 64
  | "Not#size" => some 64
  | _ => none

/-- The widths of the width-tagged word calls are `8`, `16`, `32` and `64`. -/
theorem narrowOpOf_width {f : String} {w : Nat} {op : NarrowOp}
    (h : narrowOpOf f = some (w, op)) : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
  unfold narrowOpOf at h
  split at h <;> cases h <;> simp

/-- The casts are to `8`, `16`, `32` and `64` bits. -/
theorem narrowCastOf_width {f : String} {w : Nat} (h : narrowCastOf f = some w) :
    w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
  unfold narrowCastOf at h
  split at h <;> cases h <;> simp

/-- The complements are at `8`, `16`, `32` and `64` bits. -/
theorem narrowNotOf_width {f : String} {w : Nat} (h : narrowNotOf f = some w) :
    w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
  unfold narrowNotOf at h
  split at h <;> cases h <;> simp

/-- Masking to `w ≤ 64` bits evaluates to the value modulo `2^w`. -/
theorem narrowMask_evalBV {w : Nat} (hw : w ≤ 64) (β : String → BitVec 64) (e : SExpr) :
    ((narrowMask w e).evalBV β).toNat = (e.evalBV β).toNat % 2 ^ w := by
  have h1 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  simp only [narrowMask, SExpr.evalBV, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ 64), Nat.and_two_pow_sub_one_eq_mod]

/-- The rotation amount evaluates to the value of `b` modulo the width. -/
theorem narrowAmt_evalBV {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) (b : SExpr) :
    ((narrowAmt w b).evalBV β).toNat = (b.evalBV β).toNat % w := by
  simp only [narrowAmt, SExpr.evalBV, BitVec.toNat_and, BitVec.toNat_ofNat]
  rcases hw with rfl | rfl | rfl | rfl
  · exact Nat.and_two_pow_sub_one_eq_mod _ 3
  · exact Nat.and_two_pow_sub_one_eq_mod _ 4
  · exact Nat.and_two_pow_sub_one_eq_mod _ 5
  · exact Nat.and_two_pow_sub_one_eq_mod _ 6

/-- The rotation amount is below the width. -/
theorem narrowAmt_lt {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) (b : SExpr) : ((narrowAmt w b).evalBV β).toNat < w := by
  rw [narrowAmt_evalBV hw]
  exact Nat.mod_lt _ (by omega)

/-- `w - k` for an amount `k < w ≤ 64`, evaluated as `SSub (SLit w) k`. -/
theorem narrowRot_sub_evalBV {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) (k : SExpr) (hk : (k.evalBV β).toNat < w) :
    ((SExpr.SSub (.SLit w) k).evalBV β).toNat = w - (k.evalBV β).toNat := by
  simp only [SExpr.evalBV, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rcases hw with rfl | rfl | rfl | rfl <;> omega

/-- The right rotation of a `w`-bit word `x` by `k < w` evaluates to the
    disjunction of `x >>> k` and `x <<< (w - k)` modulo `2^w`. -/
theorem narrowRotr_evalBV {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) (x k : SExpr) (hk : (k.evalBV β).toNat < w) :
    ((narrowRotSExpr w .SShr .SShl x k).evalBV β).toNat =
      (((x.evalBV β).toNat >>> (k.evalBV β).toNat) |||
        ((x.evalBV β).toNat <<< (w - (k.evalBV β).toNat))) % 2 ^ w := by
  have hdvd : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  have hs := narrowRot_sub_evalBV hw β k hk
  simp only [SExpr.evalBV] at hs
  rw [narrowRotSExpr, narrowMask_evalBV (by omega), SecureCompilation.Ascent.evalBV_sOrExpr,
    BitVec.toNat_or]
  simp only [SExpr.evalBV, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  rw [hs, Nat.or_mod_two_pow, Nat.or_mod_two_pow, Nat.mod_mod_of_dvd _ hdvd]

/-- The left rotation of a `w`-bit word `x` by `k < w` evaluates to the
    disjunction of `x <<< k` and `x >>> (w - k)` modulo `2^w`. -/
theorem narrowRotl_evalBV {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) (x k : SExpr) (hk : (k.evalBV β).toNat < w) :
    ((narrowRotSExpr w .SShl .SShr x k).evalBV β).toNat =
      (((x.evalBV β).toNat <<< (k.evalBV β).toNat) |||
        ((x.evalBV β).toNat >>> (w - (k.evalBV β).toNat))) % 2 ^ w := by
  have hdvd : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  have hs := narrowRot_sub_evalBV hw β k hk
  simp only [SExpr.evalBV] at hs
  rw [narrowRotSExpr, narrowMask_evalBV (by omega), SecureCompilation.Ascent.evalBV_sOrExpr,
    BitVec.toNat_or]
  simp only [SExpr.evalBV, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  rw [hs, Nat.or_mod_two_pow, Nat.or_mod_two_pow, Nat.mod_mod_of_dvd _ hdvd]

/-- The scalar expression of a narrow operation evaluates, in the wrapping `u64`
    semantics `SExpr.evalBV`, to the natural-number operation on the values of
    its operands. -/
theorem NarrowOp.sexpr_evalBV {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (op : NarrowOp)
    {ea eb : SExpr} {r : Nat} (β : String → BitVec 64)
    (hr : op.nat w (ea.evalBV β).toNat (eb.evalBV β).toNat = some r) :
    ((op.sexpr w ea eb).evalBV β).toNat = r := by
  have hw64 : w ≤ 64 := by omega
  have hdvd : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw64
  have hA := (ea.evalBV β).isLt
  have hB := (eb.evalBV β).isLt
  cases op <;> simp only [NarrowOp.nat, NarrowOp.sexpr, Option.some.injEq] at hr ⊢
  · rw [narrowMask_evalBV hw64, ← hr]
    simp only [SExpr.evalBV, BitVec.toNat_add, Nat.mod_mod_of_dvd _ hdvd]
  · rw [narrowMask_evalBV hw64, ← hr]
    simp only [SExpr.evalBV, BitVec.toNat_sub]
    rcases hw with rfl | rfl | rfl | rfl <;> omega
  · rw [narrowMask_evalBV hw64, ← hr]
    simp only [SExpr.evalBV, BitVec.toNat_mul, Nat.mod_mod_of_dvd _ hdvd]
  · rw [narrowMask_evalBV hw64, ← hr]
    simp only [SExpr.evalBV, BitVec.toNat_and, Nat.and_mod_two_pow]
  · rw [narrowMask_evalBV hw64, ← hr]
    simp only [SecureCompilation.Ascent.evalBV_sOrExpr, BitVec.toNat_or, Nat.or_mod_two_pow]
  · rw [narrowMask_evalBV hw64, ← hr]
    simp only [SExpr.evalBV, BitVec.toNat_xor, Nat.xor_mod_two_pow]
  · split at hr
    · simp only [Option.some.injEq] at hr
      rw [narrowMask_evalBV hw64, ← hr]
      simp only [SExpr.evalBV, BitVec.toNat_shiftLeft, Nat.mod_mod_of_dvd _ hdvd,
        Nat.shiftLeft_eq, Nat.mod_mul_mod]
    · cases hr
  · split at hr
    · simp only [Option.some.injEq] at hr
      rw [← hr]
      simp only [SExpr.evalBV, BitVec.toNat_ushiftRight, narrowMask_evalBV hw64]
    · cases hr
  · rw [← hr, narrowRotr_evalBV hw β _ _ (narrowAmt_lt hw β eb), narrowMask_evalBV hw64,
      narrowAmt_evalBV hw]
    rfl
  · rw [← hr, narrowRotl_evalBV hw β _ _ (narrowAmt_lt hw β eb), narrowMask_evalBV hw64,
      narrowAmt_evalBV hw]
    rfl

/-- The complement of `a` in `w` bits: `sNotExpr a` masked to `w` bits. -/
def narrowNotSExpr (w : Nat) (a : SExpr) : SExpr :=
  narrowMask w (SecureCompilation.Ascent.sNotExpr a)

/-- The complement in `w` bits evaluates to `2^w - 1` minus the value modulo
    `2^w`. -/
theorem narrowNotSExpr_evalBV {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) (a : SExpr) :
    ((narrowNotSExpr w a).evalBV β).toNat = 2 ^ w - 1 - (a.evalBV β).toNat % 2 ^ w := by
  have hA := (a.evalBV β).isLt
  rw [narrowNotSExpr, narrowMask_evalBV (by omega), SecureCompilation.Ascent.evalBV_sNotExpr,
    BitVec.toNat_not]
  rcases hw with rfl | rfl | rfl | rfl <;> omega

/-- The scalar expression of a narrow word call `f` on the operands `a` and `b`. -/
def narrowOpSExpr (f : String) (a b : SExpr) : Option SExpr :=
  (narrowOpOf f).map fun p => p.2.sexpr p.1 a b

/-! ### Modular multiplication by a constant modulus -/

/-- Barrett's quotient estimate `⌊x·⌊2^64/p⌋ / 2^64⌋` for `x < 2^64` lies within
    two of `⌊x/p⌋` from below: `q·p ≤ x < q·p + 2p`. -/
theorem barrett64_bound {p x : Nat} (hp : 0 < p) (hp64 : p ≤ 2 ^ 64) (hx : x < 2 ^ 64) :
    x * (2 ^ 64 / p) / 2 ^ 64 * p ≤ x ∧ x < x * (2 ^ 64 / p) / 2 ^ 64 * p + 2 * p := by
  generalize hmu : 2 ^ 64 / p = mu
  generalize hq : x * mu / 2 ^ 64 = q
  have hq1 : q * 2 ^ 64 ≤ x * mu := hq ▸ Nat.div_mul_le_self _ _
  have hmp : mu * p ≤ 2 ^ 64 := hmu ▸ Nat.div_mul_le_self _ _
  have hmu0 : 0 < mu := hmu ▸ Nat.div_pos hp64 hp
  have hmp' : 2 ^ 64 < p * (mu + 1) := hmu ▸ Nat.lt_mul_div_succ _ hp
  have hxq : x * mu < 2 ^ 64 * (q + 1) := hq ▸ Nat.lt_mul_div_succ _ (by decide)
  have hqm : q < mu := hq ▸ Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right hx hmu0)
  constructor
  · have h : q * p * 2 ^ 64 ≤ x * 2 ^ 64 := by
      calc q * p * 2 ^ 64 = q * 2 ^ 64 * p := Nat.mul_right_comm _ _ _
        _ ≤ x * mu * p := Nat.mul_le_mul_right p hq1
        _ = x * (mu * p) := Nat.mul_assoc _ _ _
        _ ≤ x * 2 ^ 64 := Nat.mul_le_mul_left x hmp
    exact Nat.le_of_mul_le_mul_right h (by decide)
  · have h : x * mu < (q * p + 2 * p) * mu := by
      calc x * mu < 2 ^ 64 * (q + 1) := hxq
        _ ≤ p * (mu + 1) * (q + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt hmp')
        _ ≤ (q * p + 2 * p) * mu := by
          have e1 : (mu + 1) * (q + 1) = mu * q + mu + q + 1 := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega
          have e2 : (q + 2) * mu = mu * q + 2 * mu := by rw [Nat.add_mul, Nat.mul_comm q mu]
          have h3 : (mu + 1) * (q + 1) ≤ (q + 2) * mu := by omega
          calc p * (mu + 1) * (q + 1) = p * ((mu + 1) * (q + 1)) := Nat.mul_assoc _ _ _
            _ ≤ p * ((q + 2) * mu) := Nat.mul_le_mul_left p h3
            _ = (q * p + 2 * p) * mu := by
              rw [← Nat.mul_assoc, Nat.mul_comm p (q + 2), Nat.add_mul]
    exact Nat.lt_of_mul_lt_mul_right h

/-- Barrett reduction of the `u64` scalar expression `x` by the constant `p`:
    the estimate `t = x − ⌊x·μ/2^64⌋·p` with `μ = ⌊2^64/p⌋`, then the branchless
    conditional subtract `d + p·(d >> 63)` of `d = t − p`. -/
def barrettRedSExpr (p : Nat) (x : SExpr) : SExpr :=
  let t := SExpr.SSub x (.SMul (.SMulHiU x (.SLit (2 ^ 64 / p))) (.SLit p))
  let d := SExpr.SSub t (.SLit p)
  .SAdd d (.SMul (.SLit p) (.SShr d (.SLit 63)))

/-- For a modulus `1 < p < 2^32`, Barrett reduction evaluates to the value
    modulo `p`. -/
theorem barrettRedSExpr_evalBV {p : Nat} (hp1 : 1 < p) (hp : p < 2 ^ 32)
    (β : String → BitVec 64) (x : SExpr) :
    ((barrettRedSExpr p x).evalBV β).toNat = (x.evalBV β).toNat % p := by
  generalize hX : (x.evalBV β).toNat = X
  have hX64 : X < 2 ^ 64 := hX ▸ (x.evalBV β).isLt
  have hmu : 2 ^ 64 / p < 2 ^ 64 := Nat.div_lt_self (by decide) hp1
  obtain ⟨hqp, hlt⟩ := barrett64_bound (p := p) (x := X) (by omega) (by omega) hX64
  generalize hq : X * (2 ^ 64 / p) / 2 ^ 64 = q at hqp hlt
  have hmulhi : sexprMulHiU X (2 ^ 64 / p) = q := by
    rw [← hq, sexprMulHiU, Nat.mod_eq_of_lt hX64, Nat.mod_eq_of_lt hmu, Nat.shiftRight_eq_div_pow]
  have hq64 : q < 2 ^ 64 := by
    have : q ≤ q * p := Nat.le_mul_of_pos_right q (by omega)
    omega
  have hXmod : X % p = (X - q * p) % p := by
    conv_lhs => rw [show X = (X - q * p) + q * p by omega]
    exact Nat.add_mul_mod_self_right _ _ _
  simp only [barrettRedSExpr, SExpr.evalBV, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hX, Nat.mod_eq_of_lt hmu, hmulhi,
    Nat.mod_eq_of_lt hq64]
  rw [Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show q * p < 2 ^ 64 by omega),
    show (63 : Nat) % 2 ^ 64 = 63 from rfl, Nat.shiftRight_eq_div_pow, hXmod]
  generalize q * p = QP at hqp hlt ⊢
  have ht : (2 ^ 64 - QP + X) % 2 ^ 64 = X - QP := by omega
  rw [ht]
  generalize hD : (2 ^ 64 - p + (X - QP)) % 2 ^ 64 = D
  by_cases htp : X - QP < p
  · rw [Nat.mod_eq_of_lt htp]
    have h1 : D / 2 ^ 63 = 1 := by omega
    rw [h1, Nat.mul_one, Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (a := X - QP) (b := p) (by omega),
      Nat.mod_eq_of_lt (a := X - QP - p) (by omega)]
    have h0 : D / 2 ^ 63 = 0 := by omega
    rw [h0, Nat.mul_zero, Nat.zero_mod, Nat.add_zero]
    omega

/-- The scalar expression of `(a · b) mod p` for a constant modulus `1 < p < 2^32`:
    Barrett reduction of the product of the Barrett reductions of `a` and `b`,
    whose product is below `p² < 2^64`. -/
def mulModSExpr (p : Nat) (a b : SExpr) : SExpr :=
  barrettRedSExpr p (.SMul (barrettRedSExpr p a) (barrettRedSExpr p b))

/-- For a modulus `1 < p < 2^32`, `mulModSExpr p a b` evaluates to the product of
    the values of `a` and `b` modulo `p`. -/
theorem mulModSExpr_evalBV {p : Nat} (hp1 : 1 < p) (hp : p < 2 ^ 32)
    (β : String → BitVec 64) (a b : SExpr) :
    ((mulModSExpr p a b).evalBV β).toNat = (a.evalBV β).toNat * (b.evalBV β).toNat % p := by
  have ha := Nat.mod_lt (a.evalBV β).toNat (show 0 < p by omega)
  have hb := Nat.mod_lt (b.evalBV β).toNat (show 0 < p by omega)
  have hab : (a.evalBV β).toNat % p * ((b.evalBV β).toNat % p) < 2 ^ 64 :=
    calc _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' (by omega) (by omega)
      _ = 2 ^ 64 := by decide
  rw [mulModSExpr, barrettRedSExpr_evalBV hp1 hp, SExpr.evalBV, BitVec.toNat_mul,
    barrettRedSExpr_evalBV hp1 hp, barrettRedSExpr_evalBV hp1 hp, Nat.mod_eq_of_lt hab,
    ← Nat.mul_mod]

/-! ### The modular-multiplication idiom -/

/-- The Rust modular-multiplication idiom
    `((a as u128) * (b as u128) % (m as u128)) as u64` as hax extracts it. -/
def mulModChain (a b m : ImpExpr) : ImpExpr :=
  .app "cast#64" [.app "Rem" [.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]],
    .app "cast#128" [m]]]

/-- The operands of the modular-multiplication idiom, when `e` is
    `mulModChain a b m`. -/
def mulModChainArgs : ImpExpr → Option (ImpExpr × ImpExpr × ImpExpr)
  | .app "cast#64" [.app "Rem" [.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]],
      .app "cast#128" [m]]] => some (a, b, m)
  | _ => none

theorem mulModChainArgs_mulModChain (a b m : ImpExpr) :
    mulModChainArgs (mulModChain a b m) = some (a, b, m) := rfl

/-- The idiom with the product bound to `x` before the reduction, the form hax
    extracts from `let x = (a as u128) * (b as u128); (x % (m as u128)) as u64`. -/
def mulModLet (x : String) (a b : ImpExpr) (m : String) : ImpExpr :=
  .letBind x (.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]])
    (.app "cast#64" [.app "Rem" [.var x, .app "cast#128" [.var m]]])

/-- The operands of the bound form of the idiom, when `e` is `mulModLet x a b m`
    with `m ≠ x`. -/
def mulModLetArgs : ImpExpr → Option (ImpExpr × ImpExpr × String)
  | .letBind x (.app "Mul" [.app "cast#128" [a], .app "cast#128" [b]])
      (.app "cast#64" [.app "Rem" [.var y, .app "cast#128" [.var m]]]) =>
      if y = x ∧ m ≠ x then some (a, b, m) else none
  | _ => none

theorem mulModLetArgs_mulModLet (x : String) (a b : ImpExpr) (m : String) (h : m ≠ x) :
    mulModLetArgs (mulModLet x a b m) = some (a, b, m) := by
  unfold mulModLet mulModLetArgs
  exact if_pos ⟨rfl, h⟩

/-- The call name of the modular-multiplication builtin: the product of two
    `64`-bit words modulo a third. -/
def mulModCallName : String := "mulmod#64"

/-- A right-hand side with the modular-multiplication idiom replaced by the call
    `mulmod#64` on its operands. -/
def fuseMulModRhs (v : ImpExpr) : ImpExpr :=
  match mulModChainArgs v with
  | some (a, b, m) => .app mulModCallName [a, b, m]
  | none => v

/-- The pass replacing the modular-multiplication idiom by `mulmod#64` in the
    right-hand side of every binding and assignment of the program spine
    (bindings, sequences, branches and loop bodies). -/
def fuseMulModBody : ImpExpr → ImpExpr
  | .letBind x v b => .letBind x (fuseMulModRhs v) (fuseMulModBody b)
  | .assign x v => .assign x (fuseMulModRhs v)
  | .seq a b => .seq (fuseMulModBody a) (fuseMulModBody b)
  | .ifThenElse c t e => .ifThenElse c (fuseMulModBody t) (fuseMulModBody e)
  | .whileLoop c b => .whileLoop c (fuseMulModBody b)
  | .whileFold c b => .whileFold c (fuseMulModBody b)
  | .forFold i lo hi b => .forFold i lo hi (fuseMulModBody b)
  | .forFoldRev i lo hi b => .forFoldRev i lo hi (fuseMulModBody b)
  | .typeAscription e ty => .typeAscription (fuseMulModBody e) ty
  | e => fuseMulModRhs e

/-- The pass replacing the bound form `mulModLet` of the idiom by the call
    `mulmod#64` where it is the result of the program: along binding bodies, the
    second part of sequences and branches. -/
def fuseMulModTail : ImpExpr → ImpExpr
  | .letBind x v b =>
      match mulModLetArgs (.letBind x v b) with
      | some (a, b', m) => .app mulModCallName [a, b', .var m]
      | none => .letBind x v (fuseMulModTail b)
  | .seq a b => .seq a (fuseMulModTail b)
  | .ifThenElse c t e => .ifThenElse c (fuseMulModTail t) (fuseMulModTail e)
  | .typeAscription e ty => .typeAscription (fuseMulModTail e) ty
  | e => e

/-- The modular-multiplication fusion: `fuseMulModBody`, then `fuseMulModTail`. -/
def fuseMulModIdiom (e : ImpExpr) : ImpExpr := fuseMulModTail (fuseMulModBody e)

/-- The builtin facts the modular-multiplication idiom evaluates by, beside
    `MulHiBuiltins`: the `u128` remainder by a positive modulus, and `mulmod#64`
    as the product modulo the third operand. -/
structure MulModBuiltins (bi : Builtins) : Prop where
  rem : ∀ n q : Nat, n < 2 ^ 128 → 0 < q → q < 2 ^ 128 →
    bi "Rem" [.int n, .int q] = some (.int ((n % q : Nat) : Int))
  mulmod : ∀ n m q : Nat, n < 2 ^ 64 → m < 2 ^ 64 → 0 < q → q < 2 ^ 64 →
    bi mulModCallName [.int n, .int m, .int q] = some (.int ((n * m % q : Nat) : Int))

/-- The call `mulmod#64` on three variables holding words below `2^64`, the third
    positive, runs to the product modulo the third. -/
theorem denote_mulModCall {bi : Builtins} (hbi : MulModBuiltins bi) (fuel : Nat) (env : Env)
    (a b m : String) (n k q : Nat) (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) (hq0 : 0 < q)
    (hq : q < 2 ^ 64) (ha : env a = some (.int n)) (hb : env b = some (.int k))
    (hm : env m = some (.int q)) :
    (denote bi fuel (.app mulModCallName [.var a, .var b, .var m])).run env =
      (.val (.int ((n * k % q : Nat) : Int)), env) := by
  have hNil : (denoteArgs bi fuel ([] : List ImpExpr)).run env = (some [], env) := by
    unfold denoteArgs; rfl
  simp only [denote_app_run_eq, denoteArgs_cons_run_eq, denote_var_run_eq, ha, hb, hm, hNil,
    Option.map_some, hbi.mulmod n k q hn hk hq0 hq]

/-- The modular-multiplication idiom on three variables holding words below
    `2^64`, the third positive, runs as the call `mulmod#64` on them. -/
theorem denote_mulModChain {bi : Builtins} (hmh : MulHiBuiltins bi) (hbi : MulModBuiltins bi)
    (fuel : Nat) (env : Env) (a b m : String) (n k q : Nat) (hn : n < 2 ^ 64)
    (hk : k < 2 ^ 64) (hq0 : 0 < q) (hq : q < 2 ^ 64) (ha : env a = some (.int n))
    (hb : env b = some (.int k)) (hm : env m = some (.int q)) :
    (denote bi fuel (mulModChain (.var a) (.var b) (.var m))).run env =
      (denote bi fuel (.app mulModCallName [.var a, .var b, .var m])).run env := by
  have hNil : (denoteArgs bi fuel ([] : List ImpExpr)).run env = (some [], env) := by
    unfold denoteArgs; rfl
  have hnk : n * k < 2 ^ 128 := by
    have h := Nat.mul_lt_mul'' hn hk
    rwa [← Nat.pow_add] at h
  have hr : n * k % q < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ hq0) hq
  rw [denote_mulModCall hbi fuel env a b m n k q hn hk hq0 hq ha hb hm]
  simp only [mulModChain, denote_app_run_eq, denoteArgs_cons_run_eq, denote_var_run_eq, ha, hb,
    hm, hNil, Option.map_some, hmh.cast128 n hn, hmh.cast128 k hk, hmh.cast128 q hq,
    hmh.mul n k hn hk, hbi.rem _ q hnk hq0 (by omega), hmh.cast64 _ hr]

/-- The bound form of the idiom, on variables holding words below `2^64` with a
    positive modulus `m ≠ x`, runs to the product modulo the modulus, with `x`
    bound to the product. -/
theorem denote_mulModLet {bi : Builtins} (hmh : MulHiBuiltins bi) (hbi : MulModBuiltins bi)
    (fuel : Nat) (env : Env) (x a b m : String) (hmx : m ≠ x) (n k q : Nat) (hn : n < 2 ^ 64)
    (hk : k < 2 ^ 64) (hq0 : 0 < q) (hq : q < 2 ^ 64) (ha : env a = some (.int n))
    (hb : env b = some (.int k)) (hm : env m = some (.int q)) :
    (denote bi fuel (mulModLet x (.var a) (.var b) m)).run env =
      (.val (.int ((n * k % q : Nat) : Int)), env.extend x (.int ((n * k : Nat) : Int))) := by
  have hNil : ∀ e : Env, (denoteArgs bi fuel ([] : List ImpExpr)).run e = (some [], e) := by
    intro e; unfold denoteArgs; rfl
  have hnk : n * k < 2 ^ 128 := by
    have h := Nat.mul_lt_mul'' hn hk
    rwa [← Nat.pow_add] at h
  have hr : n * k % q < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ hq0) hq
  have hmx' : (env.extend x (.int ((n * k : Nat) : Int))) m = some (.int q) := by
    simp [Env.extend, hmx, hm]
  have hxx : (env.extend x (.int ((n * k : Nat) : Int))) x = some (.int ((n * k : Nat) : Int)) := by
    simp [Env.extend]
  simp only [mulModLet, denote_letBind_run_eq, denote_app_run_eq, denoteArgs_cons_run_eq,
    denote_var_run_eq, ha, hb, hNil, Option.map_some, hmh.cast128 n hn, hmh.cast128 k hk,
    hmh.mul n k hn hk, hmx', hxx, hmh.cast128 q hq, hbi.rem _ q hnk hq0 (by omega),
    hmh.cast64 _ hr]

/-! ### The lowering passes of the narrow and modular operations -/

/-- The program `c` with every binding `RLetZero x t b` replaced by `g x t b'`,
    where `b'` is `b` with its bindings replaced, through sequences, branches,
    loops and blocks. -/
def mapLetZero (g : String → TowerType → LowCT → LowCT) : LowCT → LowCT
  | .RLetZero x t b => g x t (mapLetZero g b)
  | .RSeq a b => .RSeq (mapLetZero g a) (mapLetZero g b)
  | .RLetU64Zero x b => .RLetU64Zero x (mapLetZero g b)
  | .RIfNz v t e => .RIfNz v (mapLetZero g t) (mapLetZero g e)
  | .RWhileNz v b => .RWhileNz v (mapLetZero g b)
  | .RFor x n b => .RFor x n (mapLetZero g b)
  | .RForRuntime x bound b => .RForRuntime x bound (mapLetZero g b)
  | .RBlock b => .RBlock (mapLetZero g b)
  | c => c

/-- The call names whose bound result is a word below `2^64`: the `u64` word
    calls, the width-tagged operations, casts and complements, and
    `mulmod#64`. -/
def wordResultCall (f : String) : Bool :=
  wordOpNames.contains f || (narrowOpOf f).isSome || (narrowCastOf f).isSome ||
    (narrowNotOf f).isSome || f == mulModCallName

/-- Whether the body `b` of a binding of `x` binds `x` to a word below `2^64`:
    its first command is a call of `wordResultCall` or an array load into `x`. -/
def bindsWord (x : String) : LowCT → Bool
  | .RSeq (.RCall f dest _) _ => dest.locVar == x && wordResultCall f
  | .RSeq (.RArrLoad dest _ _) _ => dest.locVar == x
  | _ => false

/-- The names `W` with `x` added when `word` holds, and removed otherwise. -/
def bindWord (W : List String) (x : String) (word : Bool) : List String :=
  if word then x :: W else W.filter (· != x)

/-- The scalar expression of the one-operand call `f` on the variable `a`, with
    `W` the names known to hold words below `2^64`: a cast `f` to `w` bits of a
    name of `W` is `a` masked to `w` bits, and a complement `Not#w` is
    `narrowNotSExpr w a`.  A cast of a name outside `W`, whose value may be a
    `u128` held outside the `u64` slots, has none. -/
def narrowUnSExpr (W : List String) (f a : String) : Option SExpr :=
  match narrowCastOf f with
  | some w => if a ∈ W then some (narrowMask w (.SVar a)) else none
  | none => (narrowNotOf f).map fun w => narrowNotSExpr w (.SVar a)

/-- The binding `RLetZero x t b` with a first call `f(a, b)` of a narrow word
    call `f` into `x` lowered to the scalar assignment of `narrowOpSExpr f a b`,
    and a first call `f(a)` into `x` with a scalar expression `narrowUnSExpr W f a`
    lowered to its scalar assignment, inside `RLetU64Zero x`. -/
def narrowLetIn (W : List String) (x : String) (t : TowerType) : LowCT → LowCT
  | .RSeq (.RCall f dest [a, b]) body =>
      match narrowOpSExpr f (.SVar a.locVar) (.SVar b.locVar) with
      | some se =>
          if dest.locVar = x then .RLetU64Zero x (.RSeq (.RScalarSetExpr x se) body)
          else .RLetZero x t (.RSeq (.RCall f dest [a, b]) body)
      | none => .RLetZero x t (.RSeq (.RCall f dest [a, b]) body)
  | .RSeq (.RCall f dest [a]) body =>
      match narrowUnSExpr W f a.locVar with
      | some se =>
          if dest.locVar = x then .RLetU64Zero x (.RSeq (.RScalarSetExpr x se) body)
          else .RLetZero x t (.RSeq (.RCall f dest [a]) body)
      | none => .RLetZero x t (.RSeq (.RCall f dest [a]) body)
  | b => .RLetZero x t b

/-- The pass lowering every binding `let x = f(a, b)` of a narrow word call `f`
    and every binding `let x = f(a)` of a cast or complement (`narrowLetIn`),
    tracking in `W` the names in scope known to hold words below `2^64`: those
    bound by `RLetU64Zero`, by a call of `wordResultCall` or an array load
    (`bindsWord`), and the loop indices.  A binding of any other value removes
    its name. -/
def scalarizeNarrowIn (W : List String) : LowCT → LowCT
  | .RLetZero x t b => narrowLetIn W x t (scalarizeNarrowIn (bindWord W x (bindsWord x b)) b)
  | .RSeq a b => .RSeq (scalarizeNarrowIn W a) (scalarizeNarrowIn W b)
  | .RLetU64Zero x b => .RLetU64Zero x (scalarizeNarrowIn (x :: W) b)
  | .RIfNz v t e => .RIfNz v (scalarizeNarrowIn W t) (scalarizeNarrowIn W e)
  | .RWhileNz v b => .RWhileNz v (scalarizeNarrowIn W b)
  | .RFor x n b => .RFor x n (scalarizeNarrowIn (x :: W) b)
  | .RForRuntime x bound b => .RForRuntime x bound (scalarizeNarrowIn (x :: W) b)
  | .RBlock b => .RBlock (scalarizeNarrowIn W b)
  | c => c

/-- `scalarizeNarrowIn` from no known words: the parameters of the program are
    not known to be words, so a cast of a parameter is not lowered. -/
def scalarizeNarrowOps : LowCT → LowCT := scalarizeNarrowIn []

/-- A binding of a narrow word call into `x` is lowered to the scalar assignment
    of `NarrowOp.sexpr`, the shape of `step_narrow`. -/
theorem narrowLetIn_op {W : List String} {x f : String} {t : TowerType} {dest a b : Located}
    {body : LowCT} {w : Nat} {op : NarrowOp} (hf : narrowOpOf f = some (w, op))
    (hd : dest.locVar = x) :
    narrowLetIn W x t (.RSeq (.RCall f dest [a, b]) body) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (op.sexpr w (.SVar a.locVar) (.SVar b.locVar)))
        body) := by
  simp [narrowLetIn, narrowOpSExpr, hf, hd]

/-- A binding of a cast into `x` of a name of `W` is lowered to the scalar
    assignment of the masked operand, the shape of `step_cast`. -/
theorem narrowLetIn_cast {W : List String} {x f : String} {t : TowerType} {dest a : Located}
    {body : LowCT} {w : Nat} (hf : narrowCastOf f = some w) (ha : a.locVar ∈ W)
    (hd : dest.locVar = x) :
    narrowLetIn W x t (.RSeq (.RCall f dest [a]) body) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (narrowMask w (.SVar a.locVar))) body) := by
  simp [narrowLetIn, narrowUnSExpr, hf, ha, hd]

/-- A binding of a complement into `x` is lowered to the scalar assignment of
    `narrowNotSExpr`, the shape of `step_not`. -/
theorem narrowLetIn_not {W : List String} {x f : String} {t : TowerType} {dest a : Located}
    {body : LowCT} {w : Nat} (hf : narrowNotOf f = some w) (hd : dest.locVar = x) :
    narrowLetIn W x t (.RSeq (.RCall f dest [a]) body) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (narrowNotSExpr w (.SVar a.locVar))) body) := by
  have hc : narrowCastOf f = none := by
    unfold narrowNotOf at hf
    split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf <;> rfl
  simp [narrowLetIn, narrowUnSExpr, hc, hf, hd]

/-- The binding `RLetZero x t b` with a first call `mulmod#64(a, b, m)` into `x`
    lowered to the scalar assignment of `mulModSExpr p a b` inside
    `RLetU64Zero x`. -/
def mulModLetAt (m : String) (p : Nat) (x : String) (t : TowerType) : LowCT → LowCT
  | .RSeq (.RCall f dest [a, b, c]) body =>
      if f = mulModCallName ∧ c.locVar = m ∧ dest.locVar = x then
        .RLetU64Zero x
          (.RSeq (.RScalarSetExpr x (mulModSExpr p (.SVar a.locVar) (.SVar b.locVar))) body)
      else .RLetZero x t (.RSeq (.RCall f dest [a, b, c]) body)
  | b => .RLetZero x t b

/-- The pass lowering every binding `let x = mulmod#64(a, b, m)` whose modulus is
    the variable `m` to the scalar assignment of `mulModSExpr p a b`; `p` is the
    value `m` holds. -/
def scalarizeMulMod (m : String) (p : Nat) : LowCT → LowCT := mapLetZero (mulModLetAt m p)


end CatCrypt.Crypto.Hax
