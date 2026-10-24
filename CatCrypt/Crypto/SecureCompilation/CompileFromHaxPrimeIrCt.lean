/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrFront
public import Mathlib.Data.ZMod.Basic

/-!
# Front recognizer: `primeir-hax` `CtField` methods → constant-time field helpers over `ZMod p`

The `primeir-hax` `CtField` trait (`primeir-hax/src/ct.rs`; extracted class
`Primeir_hax.CtField`) names the field operations of RFC 9496 §2.1–2.2 beyond
the ring operations of `Field`: `ct_select`, `ct_eq`, `is_zero`, `is_negative`
and `ct_abs`. A truth value is a `u64` in `{0, 1}`. `Scalar::bit_u64` is the
inherent method that reads one little-endian bit of a scalar as such a truth
value. `haxpipeT` surfaces each call by its bare method name
(`.app "ct_select" [c, a, b]`, `.app "is_negative" [a]`, …), the field type
parameter erased to `Array Int`.

No prime-IR correspondence dialect carries these operations: `fieldDialect`
(`VIR/FieldDialect.lean`) and `derivedDialect` (`VIR/FieldDerivedOps.lean`)
have the single carrier `fp p` and no truth-value type, and the existing
selects (`jasminDialect`'s `select`, `thirDialect`'s `thSelect`,
`BranchlessSelectGoldenPath.ctSelectCom`) are word-level over `BitVec 64`. So
each recognized head is tied to a denotation over `ZMod p` defined here, in
the form the trait documents and RFC 9496 specifies, and the recognition is
keyed nominally on the method name, fail-closed, as in
`CompileFromHaxPrimeIrField`.

## Recognition table

| bare head     | `CtOp`        | denotation over `ZMod p` (`p` odd)                    |
|---------------|---------------|-------------------------------------------------------|
| `ct_select`   | `.ctSelect`   | `ctSelectDenote c a b = if c = 1 then a else b`       |
| `ct_eq`       | `.ctEq`       | `ctEqDenote a b = if a = b then 1 else 0`             |
| `is_zero`     | `.isZero`     | `isZeroDenote a = if a = 0 then 1 else 0`             |
| `is_negative` | `.isNegative` | `isNegativeDenote a = a.val % 2`                      |
| `ct_abs`      | `.ctAbs`      | `ctAbsDenote a = if a.val % 2 = 1 then -a else a`     |

`Scalar::bit_u64` is keyed separately by `recognizeScalarBitU64` and denotes to
`bitU64Denote k i = (k / 2 ^ i) % 2`, bit `i` of the scalar's integer value.

## Main definitions

* `CtOp`: the five `CtField` op tags.
* `recognizeCtField`: bare or qualified `CtField` method name → `CtOp`.
* `recognizeCtCall`: the `ImpExpr.app` node form of the same recognizer.
* `recognizeScalarBitU64`: the `Scalar::bit_u64` head.
* `ctSelectDenote`, `ctEqDenote`, `isZeroDenote`, `isNegativeDenote`,
  `ctAbsDenote`, `bitU64Denote`: the denotations.
* `ctAbsDemoImpExpr`, `ctEqUpToSignDemoImpExpr`, `scalarBitU64ImpExpr`: the
  `haxpipeT` literals for the two generic demo callers and for `bit_u64`.

## Main results

* `ctSelect_one` / `ctSelect_zero`, `ctEq_eq_one_iff`, `isZero_eq_ctEq_zero`,
  `isNegative_le_one`, `ctAbs_eq_select`: each denotation agrees with the
  trait's stated meaning.
* `isNegative_ctAbs`, `ctAbs_neg`, `ctAbs_mul_self`: `ct_abs` returns the
  non-negative one of `a`, `-a`, for odd `p`.
* `ctAbsDemo_denote`: the composed denotation of `ct_abs_demo`'s body, with the
  `neg` sub-call read through `fNegLeaf`, is `ctAbsDenote`.
* `ctEqUpToSignDemo_denote_eq_one_iff`: the composed denotation of
  `ct_eq_up_to_sign_demo`'s body is `1` iff `a = ±b` and `a ≠ 0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrCt

open _root_.Hax (ImpExpr)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrFront

/-! ## 1. The op tags and the recognition table -/

/-- The `CtField` op tags: the five constant-time field helpers of RFC 9496
    §2.1–2.2. -/
inductive CtOp where
  /-- `CT_SELECT`: `then_v` if the condition is `1`, `else_v` if it is `0`. -/
  | ctSelect
  /-- `CT_EQ`: `1` if the two elements are equal, `0` otherwise. -/
  | ctEq
  /-- `1` if the element is zero, `0` otherwise. -/
  | isZero
  /-- `IS_NEGATIVE`: the parity of the canonical representative. -/
  | isNegative
  /-- `CT_ABS`: the negation if the element is negative, else the element. -/
  | ctAbs
  deriving DecidableEq, Repr

/-- The arity of each `CtField` op. -/
def CtOp.arity : CtOp → Nat
  | .ctSelect => 3
  | .ctEq => 2
  | .isZero => 1
  | .isNegative => 1
  | .ctAbs => 1

/-- Recognize a `primeir-hax` `CtField` method name as its `CtOp`. The bare
    head `haxpipeT` emits (`ct_select`), the class-method form
    (`CtField.ct_select`) and the fully-qualified form
    (`Primeir_hax.CtField.ct_select`) are accepted. Any other head returns
    `none`. -/
def recognizeCtField (name : String) : Option CtOp :=
  if name = "ct_select" ∨ name = "CtField.ct_select" ∨
      name = "Primeir_hax.CtField.ct_select" then some .ctSelect
  else if name = "ct_eq" ∨ name = "CtField.ct_eq" ∨
      name = "Primeir_hax.CtField.ct_eq" then some .ctEq
  else if name = "is_zero" ∨ name = "CtField.is_zero" ∨
      name = "Primeir_hax.CtField.is_zero" then some .isZero
  else if name = "is_negative" ∨ name = "CtField.is_negative" ∨
      name = "Primeir_hax.CtField.is_negative" then some .isNegative
  else if name = "ct_abs" ∨ name = "CtField.ct_abs" ∨
      name = "Primeir_hax.CtField.ct_abs" then some .ctAbs
  else none

@[simp] theorem recognize_ct_select : recognizeCtField "ct_select" = some .ctSelect := rfl
@[simp] theorem recognize_ct_eq : recognizeCtField "ct_eq" = some .ctEq := rfl
@[simp] theorem recognize_is_zero : recognizeCtField "is_zero" = some .isZero := rfl
@[simp] theorem recognize_is_negative :
    recognizeCtField "is_negative" = some .isNegative := rfl
@[simp] theorem recognize_ct_abs : recognizeCtField "ct_abs" = some .ctAbs := rfl
@[simp] theorem recognize_ct_select_qualified :
    recognizeCtField "Primeir_hax.CtField.ct_select" = some .ctSelect := rfl

/-- A `Field` head is not a `CtField` head: `neg` is keyed by
    `CompileFromHaxPrimeIrField.recognizeFieldOp`. -/
theorem recognize_unknown : recognizeCtField "neg" = none := rfl

/-- Recognize a `haxpipeT`-extracted call node as a `CtField` op by its
    `ImpExpr.app` head; a non-`app` node or an unrecognized head is rejected. -/
def recognizeCtCall (e : ImpExpr) : Option CtOp :=
  match e with
  | .app f _ => recognizeCtField f
  | _ => none

/-- Recognize the `Scalar::bit_u64` head (`.app "bit_u64" [k, i]` in an
    extraction, or the resolved `Scalar.bit_u64`). Returns `true` on the head
    and `false` otherwise. -/
def recognizeScalarBitU64 (name : String) : Bool :=
  name = "bit_u64" ∨ name = "Scalar.bit_u64" ∨ name = "Primeir_hax.Scalar.bit_u64"

@[simp] theorem recognizeScalarBitU64_bit_u64 : recognizeScalarBitU64 "bit_u64" = true := rfl

theorem recognizeScalarBitU64_unknown : recognizeScalarBitU64 "ct_select" = false := rfl

/-! ## 2. The denotations over `ZMod p`

A truth value is a `Nat` in `{0, 1}`, the value of the `u64` the trait
returns. -/

/-- `CT_SELECT` (RFC 9496 §2.2): `a` if `c = 1`, else `b`. -/
def ctSelectDenote {p : Nat} (c : Nat) (a b : ZMod p) : ZMod p :=
  if c = 1 then a else b

/-- `CT_EQ` (RFC 9496 §2.2): `1` if `a = b`, else `0`. -/
def ctEqDenote {p : Nat} (a b : ZMod p) : Nat :=
  if a = b then 1 else 0

/-- `is_zero`: `1` if `a = 0`, else `0`. -/
def isZeroDenote {p : Nat} (a : ZMod p) : Nat :=
  if a = 0 then 1 else 0

/-- `IS_NEGATIVE` (RFC 9496 §2.1): the parity of the canonical representative
    of `a` in `[0, p)`; `sgn0` of RFC 9380 §4.1 at extension degree `1`. -/
def isNegativeDenote {p : Nat} (a : ZMod p) : Nat :=
  a.val % 2

/-- `CT_ABS` (RFC 9496 §2.2): `-a` if `a` is negative, else `a`. -/
def ctAbsDenote {p : Nat} (a : ZMod p) : ZMod p :=
  if a.val % 2 = 1 then -a else a

/-- `Scalar::bit_u64`: little-endian bit `i` of the scalar with integer value
    `k`, as a truth value. -/
def bitU64Denote (k i : Nat) : Nat :=
  (k / 2 ^ i) % 2

/-! ## 3. Agreement with the trait's stated meaning -/

/-- `ct_select` at condition `1` returns `then_v`. -/
@[simp] theorem ctSelect_one {p : Nat} (a b : ZMod p) : ctSelectDenote 1 a b = a := by
  simp [ctSelectDenote]

/-- `ct_select` at condition `0` returns `else_v`. -/
@[simp] theorem ctSelect_zero {p : Nat} (a b : ZMod p) : ctSelectDenote 0 a b = b := by
  simp [ctSelectDenote]

/-- `ct_eq` is a truth value. -/
theorem ctEq_le_one {p : Nat} (a b : ZMod p) : ctEqDenote a b ≤ 1 := by
  unfold ctEqDenote; split <;> omega

/-- `ct_eq a b = 1` exactly when `a = b`. -/
theorem ctEq_eq_one_iff {p : Nat} (a b : ZMod p) : ctEqDenote a b = 1 ↔ a = b := by
  unfold ctEqDenote; split <;> simp_all

/-- `is_zero a` is `ct_eq a 0`, as the trait states. -/
theorem isZero_eq_ctEq_zero {p : Nat} (a : ZMod p) : isZeroDenote a = ctEqDenote a 0 := rfl

/-- `is_zero a = 1` exactly when `a = 0`. -/
theorem isZero_eq_one_iff {p : Nat} (a : ZMod p) : isZeroDenote a = 1 ↔ a = 0 :=
  ctEq_eq_one_iff a 0

/-- `is_negative` is a truth value. -/
theorem isNegative_le_one {p : Nat} (a : ZMod p) : isNegativeDenote a ≤ 1 := by
  unfold isNegativeDenote; omega

/-- `is_negative a = 1` exactly when the canonical representative is odd. -/
theorem isNegative_eq_one_iff {p : Nat} (a : ZMod p) :
    isNegativeDenote a = 1 ↔ a.val % 2 = 1 := Iff.rfl

/-- Zero is not negative. -/
theorem isNegative_zero {p : Nat} : isNegativeDenote (0 : ZMod p) = 0 := by
  simp [isNegativeDenote]

/-- `bit_u64` is a truth value. -/
theorem bitU64_le_one (k i : Nat) : bitU64Denote k i ≤ 1 := by
  unfold bitU64Denote; omega

/-- `bit_u64` is `Nat.testBit`. -/
theorem bitU64_eq_testBit (k i : Nat) : bitU64Denote k i = (k.testBit i).toNat := by
  unfold bitU64Denote
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  generalize k / 2 ^ i = m
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [Nat.one_and_eq_mod_two, h]

/-- `ct_abs a` is `ct_select (is_negative a) (-a) a`, the RFC 9496 §2.2
    definition of `CT_ABS`. -/
theorem ctAbs_eq_select {p : Nat} (a : ZMod p) :
    ctAbsDenote a = ctSelectDenote (isNegativeDenote a) (-a) a := rfl

/-- The canonical representative of `-a` for `a ≠ 0` is `p - a.val`. -/
theorem neg_val_of_ne_zero {p : Nat} [NeZero p] {a : ZMod p} (ha : a ≠ 0) :
    (-a).val = p - a.val := by
  rw [ZMod.neg_val, ite_eq_right ha]

/-- For odd `p`, `ct_abs a` is not negative. -/
theorem isNegative_ctAbs {p : Nat} [NeZero p] (hp : p % 2 = 1) (a : ZMod p) :
    isNegativeDenote (ctAbsDenote a) = 0 := by
  unfold isNegativeDenote ctAbsDenote
  split
  · rename_i h
    have ha : a ≠ 0 := by
      rintro rfl
      simp at h
    rw [neg_val_of_ne_zero ha]
    have := ZMod.val_lt a
    omega
  · omega

/-- For odd `p`, `ct_abs (-a) = ct_abs a`. -/
theorem ctAbs_neg {p : Nat} [NeZero p] (hp : p % 2 = 1) (a : ZMod p) :
    ctAbsDenote (-a) = ctAbsDenote a := by
  by_cases ha : a = 0
  · subst ha; simp
  have hlt := ZMod.val_lt a
  have hpos : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha ((ZMod.val_eq_zero a).1 h))
  unfold ctAbsDenote
  rw [neg_val_of_ne_zero ha, neg_neg]
  split <;> split <;> first | rfl | omega

/-- `ct_abs a * ct_abs a = a * a`. -/
theorem ctAbs_mul_self {p : Nat} (a : ZMod p) : ctAbsDenote a * ctAbsDenote a = a * a := by
  unfold ctAbsDenote; split <;> simp

/-- `ct_abs a` is `a` or `-a`. -/
theorem ctAbs_eq_or {p : Nat} (a : ZMod p) : ctAbsDenote a = a ∨ ctAbsDenote a = -a := by
  unfold ctAbsDenote; split <;> simp

/-- For odd `p`, `ct_abs a = ct_abs b` exactly when `a = b` or `a = -b`. -/
theorem ctAbs_eq_ctAbs_iff {p : Nat} [NeZero p] (hp : p % 2 = 1) (a b : ZMod p) :
    ctAbsDenote a = ctAbsDenote b ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    rcases ctAbs_eq_or a with ha | ha <;> rcases ctAbs_eq_or b with hb | hb
    · left; rw [← ha, h, hb]
    · right; rw [← ha, h, hb]
    · right; rw [← neg_neg a, ← ha, h, hb]
    · left; rw [← neg_neg a, ← ha, h, hb, neg_neg]
  · rintro (rfl | rfl)
    · rfl
    · exact ctAbs_neg hp b

/-! ## 4. The `haxpipeT` literals of the demo callers, reproduced verbatim

The `ImpExpr` literals `haxpipeT --emit-certified --name Primeir` writes for
`ct_abs_demo`, `ct_eq_up_to_sign_demo` (`primeir-hax/src/ct.rs`) and
`Scalar::bit_u64`, pinned so the recognizer is keyed on the real extraction
heads. -/

/-- `ct_abs_demo`'s body as `haxpipeT` extracts it:
    `ct_select(is_negative(a), neg(a), a)`. -/
def ctAbsDemoImpExpr : ImpExpr :=
  .letBind "a" (.var "a")
    (.app "ct_select" [(.app "is_negative" [(.var "a")]), (.app "neg" [(.var "a")]), (.var "a")])

/-- `ct_eq_up_to_sign_demo`'s body as `haxpipeT` extracts it:
    `ct_eq(ct_abs(a), ct_abs(b)) & (1 - is_zero(a))`. -/
def ctEqUpToSignDemoImpExpr : ImpExpr :=
  .letBind "a" (.var "a")
    (.letBind "b" (.var "b")
      (.app "BitAnd#64"
        [(.app "ct_eq" [(.app "ct_abs" [(.var "a")]), (.app "ct_abs" [(.var "b")])]),
         (.app "Sub" [(.lit (.int 1)), (.app "is_zero" [(.var "a")])])]))

/-- `Scalar::bit_u64`'s body as `haxpipeT` extracts it:
    `cast_u64((self.0[i >> 3] >> (i & 7)) & 1)`. -/
def scalarBitU64ImpExpr : ImpExpr :=
  .letBind "self" (.var "self")
    (.letBind "i" (.var "i")
      (.letBind "byte"
        (.app "index" [(.app "::namedProj::Scalar" [(.var "self")]),
                       (.app "Shr#size" [(.var "i"), (.lit (.int 3))])])
        (.app "cast#64"
          [(.app "BitAnd#8"
            [(.app "Shr#8" [(.var "byte"), (.app "BitAnd#size" [(.var "i"), (.lit (.int 7))])]),
             (.lit (.int 1))])])))

/-- The `ct_select` call node of `ct_abs_demo`. -/
def ctAbsDemoCall : ImpExpr :=
  .app "ct_select" [(.app "is_negative" [(.var "a")]), (.app "neg" [(.var "a")]), (.var "a")]

/-- The `ct_select` node is the body of `ct_abs_demo`. -/
theorem ctAbsDemoCall_in_demo :
    ctAbsDemoImpExpr = .letBind "a" (.var "a") ctAbsDemoCall := rfl

/-- The `ct_eq` call node of `ct_eq_up_to_sign_demo`. -/
def ctEqUpToSignDemoEqCall : ImpExpr :=
  .app "ct_eq" [(.app "ct_abs" [(.var "a")]), (.app "ct_abs" [(.var "b")])]

/-- The `ct_eq` node is the first operand of `ct_eq_up_to_sign_demo`'s `&`. -/
theorem ctEqUpToSignDemoEqCall_in_demo :
    ctEqUpToSignDemoImpExpr =
      .letBind "a" (.var "a")
        (.letBind "b" (.var "b")
          (.app "BitAnd#64"
            [ctEqUpToSignDemoEqCall,
             (.app "Sub" [(.lit (.int 1)), (.app "is_zero" [(.var "a")])])])) := rfl

/-! ## 5. Recognition of the demo callers' heads -/

/-- Every head of `ct_abs_demo`'s body is recognized: the outer `ct_select` and
    the inner `is_negative` by `recognizeCtCall`, the inner `neg` by the `Field`
    front (`recognizePrimeirCall`). -/
theorem ctAbsDemo_heads_recognized (p : Nat) :
    recognizeCtCall ctAbsDemoCall = some .ctSelect ∧
    recognizeCtCall (.app "is_negative" [(.var "a")]) = some .isNegative ∧
    recognizePrimeirCall (.app "neg" [(.var "a")]) p = some (.fNeg p) :=
  ⟨rfl, rfl, rfl⟩

/-- Every `CtField` head of `ct_eq_up_to_sign_demo`'s body is recognized. -/
theorem ctEqUpToSignDemo_heads_recognized :
    recognizeCtCall ctEqUpToSignDemoEqCall = some .ctEq ∧
    recognizeCtCall (.app "ct_abs" [(.var "a")]) = some .ctAbs ∧
    recognizeCtCall (.app "is_zero" [(.var "a")]) = some .isZero :=
  ⟨rfl, rfl, rfl⟩

/-! ## 6. The composed denotations of the demo bodies

The body of each demo caller is a tree of recognized heads; composing the
denotations in that tree shape gives the value the caller computes. The `neg`
sub-call of `ct_abs_demo` is read through the `Field` front's `fNegLeaf`, tied
to `-a` by `primeir_field_neg_recognized_denote`. -/

/-- The composed denotation of `ct_abs_demo`'s body:
    `ct_select(is_negative(a), neg(a), a)` with `neg` the `fNegLeaf` leaf. -/
def ctAbsDemoDenote (p : Nat) (a : ZMod p) : ZMod p :=
  ctSelectDenote (isNegativeDenote a) ((fNegLeaf p).denote (.cons a .nil)) a

/-- `ct_abs_demo` computes `ct_abs`. -/
theorem ctAbsDemo_denote (p : Nat) (a : ZMod p) : ctAbsDemoDenote p a = ctAbsDenote a := by
  unfold ctAbsDemoDenote
  rw [primeir_field_neg_recognized_denote, ctAbs_eq_select]

/-- The composed denotation of `ct_eq_up_to_sign_demo`'s body:
    `ct_eq(ct_abs(a), ct_abs(b)) & (1 - is_zero(a))`. -/
def ctEqUpToSignDemoDenote {p : Nat} (a b : ZMod p) : Nat :=
  ctEqDenote (ctAbsDenote a) (ctAbsDenote b) &&& (1 - isZeroDenote a)

/-- For odd `p`, `ct_eq_up_to_sign_demo a b = 1` exactly when `a = ±b` and
    `a ≠ 0`. -/
theorem ctEqUpToSignDemo_denote_eq_one_iff {p : Nat} [NeZero p] (hp : p % 2 = 1)
    (a b : ZMod p) :
    ctEqUpToSignDemoDenote a b = 1 ↔ (a = b ∨ a = -b) ∧ a ≠ 0 := by
  unfold ctEqUpToSignDemoDenote
  rw [← ctAbs_eq_ctAbs_iff hp, ← ctEq_eq_one_iff, ne_eq, ← isZero_eq_one_iff]
  have h1 := ctEq_le_one (ctAbsDenote a) (ctAbsDenote b)
  have h2 : isZeroDenote a ≤ 1 := ctEq_le_one a 0
  generalize ctEqDenote (ctAbsDenote a) (ctAbsDenote b) = e at *
  generalize isZeroDenote a = z at *
  interval_cases e <;> interval_cases z <;> decide

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrCt
