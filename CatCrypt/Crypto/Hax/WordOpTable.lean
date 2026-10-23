/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Semantics
public import CatCrypt.Crypto.Jasmin.LowCTSExpr
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

/-!
# The word-operation table of hax builtin calls

The names, natural-number meanings and builtin contracts of the width-tagged word
calls that hax extracts from Rust integer code, stated over hax-lean's `Builtins`
and independent of any lowering pass.

The `u64` word calls (`wordOpNames`) have the natural-number operations
`wordOpNat`: the wrapping `u64` addition, subtraction and multiplication, the
multiply-high `mulhi#64`, the bitwise AND and XOR, the shifts below `64`, and the
unbounded sum `Add`.  The `u8`, `u16`, `u32` and `usize` calls, the rotations at
every width and the `u64` OR are width-tagged operations (`narrowOpOf`, with the
operation `NarrowOp.nat`); the casts to at most `64` bits and the complements
`Not#w` have their widths in `narrowCastOf` and `narrowNotOf`.

The multiply-high idiom `((a as u128) * (b as u128) >> 64) as u64` is the call
chain `mulHiChain`, and its fused call is `mulhi#64` (`mulHiCallName`); the fused
modular multiplication is `mulmod#64` (`mulModCallName`).

A builtin table meets a contract when it evaluates these calls by their
natural-number operations: `MulHiBuiltins` and `MulModBuiltins` for the two
idioms, `WordBuiltins` and its bounded form `WordBuiltins'` for the `u64` word
calls with array `index` and `array_update`, and `NarrowBuiltins w` for the calls
of width `w`.

## Main definitions

* `mulHiChain`, `mulHiChainArgs`, `mulHiCallName`, `MulHiBuiltins` — the
  multiply-high idiom, its recogniser, the fused call and its builtin facts.
* `wordOpNames`, `wordOpNat` — the `u64` word calls and their natural-number
  operations.
* `NarrowOp`, `NarrowOp.nat`, `narrowOpOf`, `narrowCastOf`, `narrowNotOf` — the
  width-tagged word calls, casts and complements.
* `mulModCallName`, `MulModBuiltins` — the fused modular multiplication and its
  builtin facts.
* `WordOpsSim.WordBuiltins`, `WordOpsSim.WordBuiltins'`,
  `WordOpsSim.NarrowBuiltins` — the contracts of a builtin table on the word
  calls.

## Main results

* `sexprMulHiU_of_lt` — on words below `2^64`, `sexprMulHiU` is the product
  shifted right by `64`.
* `narrowOpOf_width`, `narrowCastOf_width`, `narrowNotOf_width` — the widths are
  `8`, `16`, `32` and `64`.
* `WordOpsSim.WordBuiltins.toBounded` — `WordBuiltins` implies `WordBuiltins'`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Builtins)
open CatCrypt.Crypto.Jasmin.LowCT (sexprMulHiU)

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

/-- The recogniser `mulHiChainArgs` returns the operands of `mulHiChain`. -/
theorem mulHiChainArgs_mulHiChain (a b : ImpExpr) :
    mulHiChainArgs (mulHiChain a b) = some (a, b) := rfl

/-- The call name of the multiply-high builtin: the high 64 bits of the
    `128`-bit product of two `64`-bit words. -/
def mulHiCallName : String := "mulhi#64"

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

/-! ### The `u64` word calls -/

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

/-! ### The width-tagged word calls -/

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

/-! ### Modular multiplication -/

/-- The call name of the modular-multiplication builtin: the product of two
    `64`-bit words modulo a third. -/
def mulModCallName : String := "mulmod#64"

/-- The builtin facts the modular-multiplication idiom evaluates by, beside
    `MulHiBuiltins`: the `u128` remainder by a positive modulus, and `mulmod#64`
    as the product modulo the third operand. -/
structure MulModBuiltins (bi : Builtins) : Prop where
  rem : ∀ n q : Nat, n < 2 ^ 128 → 0 < q → q < 2 ^ 128 →
    bi "Rem" [.int n, .int q] = some (.int ((n % q : Nat) : Int))
  mulmod : ∀ n m q : Nat, n < 2 ^ 64 → m < 2 ^ 64 → 0 < q → q < 2 ^ 64 →
    bi mulModCallName [.int n, .int m, .int q] = some (.int ((n * m % q : Nat) : Int))

end CatCrypt.Crypto.Hax

namespace CatCrypt.Crypto.Hax.WordOpsSim

open _root_.Hax (Value Builtins)

/-! ### Contracts of a builtin table on the word calls -/

/-- The facts the builtin table evaluates the straight-line bindings by: every
    word call of `wordOpNames` on two words below `2^64` as `wordOpNat`, an
    `index` read of an `.int` cell, and an in-range `array_update`. -/
structure WordBuiltins (bi : Builtins) : Prop where
  word : ∀ f ∈ wordOpNames, ∀ n m : Nat, n < 2 ^ 64 → m < 2 ^ 64 →
    bi f [.int n, .int m] = (wordOpNat f n m).map (fun r : Nat => Value.int r)
  index : ∀ (vs : List Value) (i w : Nat), vs[i]? = some (.int w) →
    bi "index" [.array vs, .int i] = some (.int w)
  update : ∀ (vs : List Value) (i : Nat) (v : Value), i < vs.length →
    bi "array_update" [.array vs, .int i, v] = some (.array (vs.set i v))

/-- The facts a builtin table evaluates the straight-line bindings by: every word
    call of `wordOpNames` on two words below `2^64` whose `wordOpNat` result is
    below `2^64` returns that result, an `index` read of an `.int` cell, and an
    in-range `array_update`. -/
structure WordBuiltins' (bi : Builtins) : Prop where
  word : ∀ f ∈ wordOpNames, ∀ n m r : Nat, n < 2 ^ 64 → m < 2 ^ 64 →
    wordOpNat f n m = some r → r < 2 ^ 64 → bi f [.int n, .int m] = some (.int r)
  index : ∀ (vs : List Value) (i w : Nat), vs[i]? = some (.int w) →
    bi "index" [.array vs, .int i] = some (.int w)
  update : ∀ (vs : List Value) (i : Nat) (v : Value), i < vs.length →
    bi "array_update" [.array vs, .int i, v] = some (.array (vs.set i v))

/-- `WordBuiltins` implies `WordBuiltins'`. -/
theorem WordBuiltins.toBounded {bi : Builtins} (h : WordBuiltins bi) : WordBuiltins' bi where
  word f hf n m r hn hm hr _ := by rw [h.word f hf n m hn hm, hr]; rfl
  index := h.index
  update := h.update

/-- The facts a builtin table evaluates the narrow word calls of width `w` by:
    every call of `narrowOpOf` at width `w` on two words below `2^64` returns
    its natural-number operation, every cast to `w` bits returns its operand
    modulo `2^w`, and every complement `Not#w` of a word below `2^64` returns
    `2^w - 1` minus the word modulo `2^w`. -/
structure NarrowBuiltins (w : Nat) (bi : Builtins) : Prop where
  op : ∀ (f : String) (op : NarrowOp), narrowOpOf f = some (w, op) → ∀ n m r : Nat,
    n < 2 ^ 64 → m < 2 ^ 64 → op.nat w n m = some r → bi f [.int n, .int m] = some (.int r)
  cast : ∀ f : String, narrowCastOf f = some w → ∀ n : Nat,
    bi f [.int n] = some (.int ((n % 2 ^ w : Nat) : Int))
  not : ∀ f : String, narrowNotOf f = some w → ∀ n : Nat, n < 2 ^ 64 →
    bi f [.int n] = some (.int ((2 ^ w - 1 - n % 2 ^ w : Nat) : Int))

end CatCrypt.Crypto.Hax.WordOpsSim
