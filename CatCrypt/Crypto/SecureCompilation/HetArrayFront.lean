/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import HaxLean.TExpr
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-!
# Heterogeneous array-input front pilot — runtime `arr[i]` reads (the §9 deferral)

The committed THIR→`Com jasminDialect` front (`ThirToComFront.lean`) is
**homogeneous**: `frontCtxt`/`FState`/`Atom`/`inputValuation` all model the
input file as `nIn` replicated `rW w` registers. That front can compile
`inp[i]` reads only when `i` is a *compile-time* literal (it resolves to a fixed
input register); a genuine runtime-indexed array read `arr[i]` — where the array
is one heterogeneous `stackArr w n` value and `i` is a runtime `reg 64` — cannot
be carried, because a stack-array value is not a `rW w` register. The §9 store
pilot and the §20 table-load demonstrator (`storeDemoCom` / `zetaLookupCom` in
`ThirToComFront.lean`) note this exact gap and defer it.

This module opens that deferral **additively**: it adds a *parallel*
heterogeneous front entry over the context `[.stackArr w n, .reg 64]` (one array
input + one runtime index register). Nothing in the committed homogeneous front
is touched — `frontCtxt`, `FState`, `Atom`, `inputValuation`, `thirToJasmin`,
and every σ₀ / round-component / load proof stay byte-identical. The dialect and
the emit back-half already support heterogeneous `Com` contexts (this is exactly
what `storeDemoCom`/`zetaLookupCom` exercise); the only missing piece was a
front that *recognises* an `index[arr, idx]` THIR-`TExpr` leaf and lowers it into
the dialect's `stackLoad` gather. That recogniser is what we add here.

## What carries the connecting theorem

* `arrReadFront` — the parallel heterogeneous front: a recogniser over
  `Hax.TExpr` that matches the real `index` app head (an array-typed `var` and an
  index `var`) and emits the `stackLoad` `Com` over `[.stackArr w n, .reg 64]`.
  This is the read dual of §9's `storeDemoCom`, built the way §20's
  `zetaLookupCom` builds its gather, but driven *from a recognised TExpr leaf*
  rather than hand-written.
* `arrReadModel` — the minimal `fn f(arr:&[u32;n], i:usize)->u32 { arr[i] }`
  body in real typed-`Hax.TExpr` form (the real `index` head over a
  `&[u32;n]`-typed `arr` var and a `usize`-typed `i` var).
* `arrRead_compiles` — the array read **compiles** (the recogniser fires) and its
  emitted `Com` **denotes** to the indexed element `stackGet arr i.toNat`, and on
  an in-range index `i : Fin n` reads exactly `arr i`. This is the first
  array-index read compiled through a (parallel) verified front.

The denotation is pinned to the dialect's total `stackGet` read (the same fact
`zetaLookupCom_denote` reuses), with the in-range `% n` ↔ direct-index bridge
discharged by `stackGet_id` (the same fact `zetaLookupCom_inrange` reuses).

## Constant-time note (inherited)

As for §20, the dialect's `JasminCTPredicate.opIndexPublic` admits the emitted
`stackLoad` as CT-safe **iff** its index register is `.Public`. A runtime
`arr[i]` with a *secret* `i` is a cache-timing leak and must instead use a
constant-time `select`-scan (the §17 idiom); this front lowers the gather
faithfully and leaves the public-index obligation to that predicate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HetArrayFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## §H.1  The heterogeneous front context and the gather `Com` builder

The front context for a single array input + a single runtime index register is
the two-element heterogeneous `Ctxt jasminDialect` `[.stackArr w n, .reg 64]`.
The compiled body is exactly one `stackLoad` binding (the runtime gather) whose
result is returned — the read dual of §9's `storeDemoCom`, structurally
identical to §20's `zetaLookupCom` but width-parameterized. -/

/-- The heterogeneous front context: one `w`-bit `n`-element array followed by a
    `64`-bit runtime index register. -/
abbrev arrCtxt (w n : Nat) : Ctxt jasminDialect := [.stackArr w n, .reg 64]

/-- The compiled gather `Com` over `arrCtxt w n`: `let v = stackLoad arr idx; ret v`.
    The single `stackLoad` binding (`[stackArr w n, reg 64] → reg w`) is the
    runtime gather; the loaded `reg w` value is returned. Structurally the read
    dual of §9's `storeDemoCom` and identical in shape to §20's `zetaLookupCom`. -/
def arrLoadCom (w n : Nat) :
    Com jasminDialect (arrCtxt w n) (.reg w) :=
  .var (.mk (.stackLoad w n) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The heterogeneous input valuation: an array value and a `64`-bit index, as a
    `Ctxt.Valuation` of `arrCtxt w n`. The array occupies slot 0, the index slot 1
    — matching the de-Bruijn variables `arrLoadCom` feeds to `stackLoad`. -/
def arrInputValuation (w n : Nat) (arr : Fin n → BitVec w) (idx : BitVec 64) :
    Ctxt.Valuation (arrCtxt w n) :=
  .cons arr (.cons idx .nil)

/-- `arrLoadCom` denotes the dialect's total gather `stackGet arr idx.toNat` —
    element `idx mod n` of the array. Reuses the `stackLoad` `.denote` fact the
    §20 `zetaLookupCom_denote` rests on (here it is `rfl`). -/
theorem arrLoadCom_denote (w n : Nat) (arr : Fin n → BitVec w) (idx : BitVec 64) :
    (arrLoadCom w n).denote (arrInputValuation w n arr idx)
      = stackGet arr idx.toNat := rfl

/-! ## §H.2  The recogniser: an `index[arr, idx]` TExpr leaf → the gather `Com`

The recogniser inspects a `Hax.TExpr` and fires on the real `index` app head
(the head `Generated/LoadU32LeTExpr.lean` carries: `app "index" [arr, idx]`,
`arr` an array-typed `var`, `idx` an index expr). On a match it returns the
heterogeneous gather `Com`; otherwise `none`. This is the front recogniser arm
the homogeneous front could not host (its `Atom`/`rhsExpr` surface has no
array-typed operand). -/

/-- Is this `Hax.ImpType` an array (or a reference to an array) of `w`-bit words
    of length `n`? Recognises both `&[uN;n]` and `[uN;n]` (the `index` head
    receiver is typed `ref (array ..) false` in real extractions, e.g.
    `LoadU32LeTExpr`). -/
def isArrTypeOfW (w n : Nat) : Hax.ImpType → Bool
  | .ref t _ => isArrTypeOfW w n t
  | .array (.uint iw) m => decide (iw.bits = w) && decide (m = n)
  | _ => false

/-- The heterogeneous array-read front: recognise an `arr[i]` `index` leaf and
    emit the gather `Com` over `arrCtxt w n`.

    Fires on `Hax.TExprKind.app "index" [arr, idx]` where `arr` is a `var` whose
    type is a `&[uw;n]` / `[uw;n]` array (matched by `isArrTypeOfW w n`) — i.e.
    the real `index` head shape. The index sub-expression is accepted as the
    runtime `reg 64` operand (it occupies the index slot of `arrCtxt`). Any other
    shape returns `none` (the recogniser does not fire). -/
def arrReadFront (w n : Nat) : Hax.TExpr → Option (Com jasminDialect (arrCtxt w n) (.reg w))
  | .mk (.app "index" [arr, _idx]) _ =>
      match arr with
      | .mk (.var _) arrTy =>
          if isArrTypeOfW w n arrTy then some (arrLoadCom w n) else none
      | _ => none
  | _ => none

/-! ## §H.3  The model body and the end-to-end compile + denote theorem

`arrReadModel` is the minimal `fn f(arr:&[u32;n], i:usize)->u32 { arr[i] }` body
in real typed-`Hax.TExpr` form: the `index` head over a `&[u32;n]`-typed `arr`
var and a `usize`-typed `i` var (`IntWidth.wsize`), exactly the index leaf shape
of `Generated/LoadU32LeTExpr.lean`. -/

/-- The array length used by the model (a length-1 `u32` array, the minimal
    `&[u32;1]` shape from the task; any `n` works — see `arrRead_compiles_n`). -/
abbrev modelLen : Nat := 1

/-- The minimal `arr[i]` body, `fn f(arr:&[u32;1], i:usize)->u32 { arr[i] }`, in
    real typed-`Hax.TExpr` form: `index[arr, i]` with `arr : &[u32;1]` (a `var`
    typed `ref (array (uint w32) 1) false`) and `i : usize` (a `var` typed
    `uint wsize`). The result type is `u32`. -/
def arrReadModel : Hax.TExpr :=
  Hax.TExpr.mk
    (Hax.TExprKind.app "index"
      [ Hax.TExpr.mk (Hax.TExprKind.var "arr")
          (Hax.ImpType.ref (Hax.ImpType.array (Hax.ImpType.uint Hax.IntWidth.w32) modelLen) false),
        Hax.TExpr.mk (Hax.TExprKind.var "i")
          (Hax.ImpType.uint Hax.IntWidth.wsize) ])
    (Hax.ImpType.uint Hax.IntWidth.w32)

/-- **The array read compiles and denotes to the indexed element.**

    The heterogeneous front `arrReadFront 32 1` fires on the real `arr[i]`
    `index`-leaf `arrReadModel`, producing a gather `Com`; that `Com` denotes,
    for every array `arr : Fin 1 → BitVec 32` and runtime index `idx : BitVec 64`,
    to the dialect's total indexed read `stackGet arr idx.toNat` (element
    `idx mod 1` of the array). This is the first runtime array-index read
    compiled through a (parallel) verified front — the §9 deferral, opened
    additively at `w = 32`, `n = 1`. -/
theorem arrRead_compiles :
    ∃ c, arrReadFront 32 modelLen arrReadModel = some c ∧
      ∀ (arr : Fin modelLen → BitVec 32) (idx : BitVec 64),
        c.denote (arrInputValuation 32 modelLen arr idx) = stackGet arr idx.toNat := by
  refine ⟨arrLoadCom 32 modelLen, rfl, ?_⟩
  intro arr idx
  exact arrLoadCom_denote 32 modelLen arr idx

/-- **In-range reads hit the underlying element.** On an in-range index
    `i : Fin modelLen` (its `u64` representative `BitVec.ofNat 64 i.val`), the
    compiled gather reads exactly `arr i`. The `% n` reduction of `stackGet` is
    the identity here (`stackGet_id`), closing the in-range ↔ direct-index gap —
    the same bridge §20's `zetaLookupCom_inrange` uses. -/
theorem arrRead_compiles_inrange :
    ∃ c, arrReadFront 32 modelLen arrReadModel = some c ∧
      ∀ (arr : Fin modelLen → BitVec 32) (i : Fin modelLen),
        c.denote (arrInputValuation 32 modelLen arr (BitVec.ofNat 64 i.val)) = arr i := by
  refine ⟨arrLoadCom 32 modelLen, rfl, ?_⟩
  intro arr i
  rw [arrLoadCom_denote]
  have hlt : i.val < 2 ^ 64 := by
    have h1 : i.val < modelLen := i.isLt
    have h2 : (modelLen : Nat) ≤ 2 ^ 64 := by norm_num [modelLen]
    omega
  rw [show (BitVec.ofNat 64 i.val).toNat = i.val from by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt]
  exact stackGet_id arr i

/-! ## §H.4  Width/length-general statement

The pilot is not specific to `w = 32`, `n = 1`: the front, the gather `Com`, and
the denotation work for any width `w` and length `n` (`n ≤ 2^64`, so a `Fin n`
index has a faithful `u64` representative). The general statement records that
the recogniser + gather denote uniformly. -/

/-- A length-`n` `u32` model body (general `n`): `index[arr, i]` with
    `arr : &[u32;n]`, `i : usize`. -/
def arrReadModelN (n : Nat) : Hax.TExpr :=
  Hax.TExpr.mk
    (Hax.TExprKind.app "index"
      [ Hax.TExpr.mk (Hax.TExprKind.var "arr")
          (Hax.ImpType.ref (Hax.ImpType.array (Hax.ImpType.uint Hax.IntWidth.w32) n) false),
        Hax.TExpr.mk (Hax.TExprKind.var "i")
          (Hax.ImpType.uint Hax.IntWidth.wsize) ])
    (Hax.ImpType.uint Hax.IntWidth.w32)

/-- **General-`n` compile + denote.** For any length `n ≤ 2^64`, the front fires
    on `arrReadModelN n` and the compiled gather reads `stackGet arr idx.toNat`,
    with the in-range case reading exactly `arr i`. -/
theorem arrRead_compiles_n (n : Nat) (hn : n ≤ 2 ^ 64) :
    ∃ c, arrReadFront 32 n (arrReadModelN n) = some c ∧
      (∀ (arr : Fin n → BitVec 32) (idx : BitVec 64),
        c.denote (arrInputValuation 32 n arr idx) = stackGet arr idx.toNat) ∧
      (∀ (arr : Fin n → BitVec 32) (i : Fin n),
        c.denote (arrInputValuation 32 n arr (BitVec.ofNat 64 i.val)) = arr i) := by
  refine ⟨arrLoadCom 32 n, ?_, ?_, ?_⟩
  · simp only [arrReadFront, arrReadModelN, isArrTypeOfW, Hax.IntWidth.bits,
      decide_true, Bool.and_self, if_true]
  · intro arr idx; exact arrLoadCom_denote 32 n arr idx
  · intro arr i
    rw [arrLoadCom_denote]
    have hlt : i.val < 2 ^ 64 := lt_of_lt_of_le i.isLt hn
    rw [show (BitVec.ofNat 64 i.val).toNat = i.val from by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt]
    exact stackGet_id arr i

end CatCrypt.Crypto.SecureCompilation.HetArrayFront
