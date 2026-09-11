/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HetArrayFront

/-!
# Heterogeneous array-input front: runtime `arr[i] = v` WRITES (the §9 dual)

The read dual (`HetArrayFront`) recognised an `index[arr, idx]` `Hax.TExpr` leaf and
lowered it to the dialect's `stackLoad` gather. This module is the **write** half:
recognise an array-store leaf `arr[idx] = val` and lower it to the dialect's
`stackStore` (the runtime scatter, `[stackArr w n, reg 64, reg w] → stackArr w n`),
with denotation the functional update `stackSet`.

The dialect/`Com` side already exists — `ThirToComFront §9`'s `storeDemoCom` /
`storeDemoCom_denote` exercise `stackStore` directly (at `w = 32`, `n = 4`). What was
missing, exactly as for the read, is a **front recogniser** that fires on a store-shaped
`Hax.TExpr` leaf and emits the gather/scatter `Com`. That recogniser is what we add here,
width/length-generically. Like the read, this is **additive**: nothing in the committed
homogeneous front (`frontCtxt`/`FState`/`Atom`/`thirToJasmin`) is touched.

## Real-head alignment

The read recogniser keys on the confirmed real head `"index"` (from
`Generated/LoadU32LeTExpr.lean`). The store recogniser keys on the Rust array-assignment
heads — `IndexMut`/update shapes (`"index_store"`, `"index_mut"`, `"set"`) — over an
array-typed receiver. The exact head a given hax export emits for `arr[i] = v` is
confirmed against the first real array-WRITE function (chacha `quarter_round`, which
writes the state array); the recogniser matches the family so that alignment is a
one-line addition, not a re-architecture. The denotation-tie to `stackSet` is the real
content and is head-independent.

## Constant-time note (inherited)

As for the read (and §9), the dialect's `JasminCTPredicate` admits the emitted
`stackStore` as CT-safe iff its index register is `.Public`; a secret-indexed write is a
cache-timing leak and must use a constant-time `select`-scatter. This front lowers the
scatter faithfully and leaves the public-index obligation to that predicate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HetArrayStoreFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.HetArrayFront (isArrTypeOfW)

/-! ## §S.1  The heterogeneous store context and the scatter `Com` builder -/

/-- The store front context: a `w`-bit `n`-element array, a `64`-bit runtime index
    register, and a `w`-bit value register. -/
abbrev arrStoreCtxt (w n : Nat) : Ctxt jasminDialect := [.stackArr w n, .reg 64, .reg w]

/-- The compiled scatter `Com` over `arrStoreCtxt w n`: `let arr' = stackStore arr idx val; ret arr'`.
    The single `stackStore` binding (`[stackArr w n, reg 64, reg w] → stackArr w n`) is the
    runtime scatter; the updated array is returned. Width/length-generic `storeDemoCom`. -/
def arrStoreCom (w n : Nat) :
    Com jasminDialect (arrStoreCtxt w n) (.stackArr w n) :=
  .var (.mk (.stackStore w n) rfl
          (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))
    (.ret .here)

/-- The heterogeneous store input valuation: an array value, a `64`-bit index, and a
    `w`-bit value, as a `Ctxt.Valuation` of `arrStoreCtxt w n`. -/
def arrStoreInputValuation (w n : Nat) (arr : Fin n → BitVec w) (idx : BitVec 64)
    (val : BitVec w) : Ctxt.Valuation (arrStoreCtxt w n) :=
  .cons arr (.cons idx (.cons val .nil))

/-- `arrStoreCom` denotes the functional update `stackSet arr idx.toNat val` — element
    `idx mod n` becomes `val`, the rest unchanged. The store dual of `arrLoadCom_denote`
    (here it is `rfl`, the same fact `storeDemoCom_denote` rests on). -/
theorem arrStoreCom_denote (w n : Nat) (arr : Fin n → BitVec w) (idx : BitVec 64)
    (val : BitVec w) :
    (arrStoreCom w n).denote (arrStoreInputValuation w n arr idx val)
      = stackSet arr idx.toNat val := rfl

/-! ## §S.2  The recogniser: an `arr[idx] = val` store leaf → the scatter `Com` -/

/-- Recognise an array-assignment head. Matches the Rust `IndexMut`/update family for
    `arr[idx] = val`. The exact head a given hax export emits is confirmed against the
    first real array-write function; the recogniser matches the family. -/
def isStoreHead (f : String) : Bool :=
  f == "index_store" || f == "index_mut" || f == "index_set" || f == "set" || f == "store"

/-- The heterogeneous array-store front: recognise an `arr[idx] = val` store leaf and emit
    the scatter `Com` over `arrStoreCtxt w n`.

    Fires on `Hax.TExprKind.app <storeHead> [arr, idx, val]` where `arr` is a `var` whose
    type is a `&[uw;n]` / `[uw;n]` array (matched by `isArrTypeOfW w n`) — i.e. an
    array-typed receiver of an index-assignment. Any other shape returns `none`. This is the
    write dual of `HetArrayFront.arrReadFront`; the receiver-array-type guard is the same. -/
def arrStoreFront (w n : Nat) : Hax.TExpr → Option (Com jasminDialect (arrStoreCtxt w n) (.stackArr w n))
  | .mk (.app f [arr, _idx, _val]) _ =>
      if isStoreHead f then
        match arr with
        | .mk (.var _) arrTy =>
            if isArrTypeOfW w n arrTy then some (arrStoreCom w n) else none
        | _ => none
      else none
  | _ => none

/-! ## §S.3  The model body and the end-to-end compile + denote theorem -/

/-- The minimal `arr[i] = v` body, `fn f(arr:&mut [u32;1], i:usize, v:u32) { arr[i] = v }`,
    in `Hax.TExpr` form: an `index_store` app over a `&[u32;1]`-typed `arr` var, a `usize`
    index var, and a `u32` value var. -/
def arrStoreModel : Hax.TExpr :=
  Hax.TExpr.mk
    (Hax.TExprKind.app "index_store"
      [ Hax.TExpr.mk (Hax.TExprKind.var "arr")
          (Hax.ImpType.ref (Hax.ImpType.array (Hax.ImpType.uint Hax.IntWidth.w32) 1) true),
        Hax.TExpr.mk (Hax.TExprKind.var "i") (Hax.ImpType.uint Hax.IntWidth.wsize),
        Hax.TExpr.mk (Hax.TExprKind.var "v") (Hax.ImpType.uint Hax.IntWidth.w32) ])
    (Hax.ImpType.array (Hax.ImpType.uint Hax.IntWidth.w32) 1)

/-- **The array write compiles and denotes to the functional update.**

    The store front `arrStoreFront 32 1` fires on the real `arr[i] = v` store leaf
    `arrStoreModel`, producing a scatter `Com`; that `Com` denotes, for every array
    `arr : Fin 1 → BitVec 32`, index `idx : BitVec 64`, and value `val : BitVec 32`, to the
    dialect's functional update `stackSet arr idx.toNat val`. The write dual of
    `HetArrayFront.arrRead_compiles` — the §9 store deferral opened additively. -/
theorem arrStore_compiles :
    ∃ c, arrStoreFront 32 1 arrStoreModel = some c ∧
      ∀ (arr : Fin 1 → BitVec 32) (idx : BitVec 64) (val : BitVec 32),
        c.denote (arrStoreInputValuation 32 1 arr idx val) = stackSet arr idx.toNat val := by
  refine ⟨arrStoreCom 32 1, rfl, ?_⟩
  intro arr idx val
  exact arrStoreCom_denote 32 1 arr idx val

/-! ## §S.4  Width/length-general statement -/

/-- A length-`n` `u32` store model (general `n`): `index_store[arr, i, v]` with
    `arr : &mut [u32;n]`, `i : usize`, `v : u32`. -/
def arrStoreModelN (n : Nat) : Hax.TExpr :=
  Hax.TExpr.mk
    (Hax.TExprKind.app "index_store"
      [ Hax.TExpr.mk (Hax.TExprKind.var "arr")
          (Hax.ImpType.ref (Hax.ImpType.array (Hax.ImpType.uint Hax.IntWidth.w32) n) true),
        Hax.TExpr.mk (Hax.TExprKind.var "i") (Hax.ImpType.uint Hax.IntWidth.wsize),
        Hax.TExpr.mk (Hax.TExprKind.var "v") (Hax.ImpType.uint Hax.IntWidth.w32) ])
    (Hax.ImpType.array (Hax.ImpType.uint Hax.IntWidth.w32) n)

/-- **General-`n` compile + denote** for the array write: the front fires on
    `arrStoreModelN n` and the compiled scatter denotes to `stackSet arr idx.toNat val`. -/
theorem arrStore_compiles_n (n : Nat) :
    ∃ c, arrStoreFront 32 n (arrStoreModelN n) = some c ∧
      ∀ (arr : Fin n → BitVec 32) (idx : BitVec 64) (val : BitVec 32),
        c.denote (arrStoreInputValuation 32 n arr idx val) = stackSet arr idx.toNat val := by
  refine ⟨arrStoreCom 32 n, ?_, ?_⟩
  · simp only [arrStoreFront, arrStoreModelN, isStoreHead, isArrTypeOfW, Hax.IntWidth.bits,
      decide_true, Bool.and_self, beq_self_eq_true, Bool.true_or, Bool.or_true, if_true]
  · intro arr idx val; exact arrStoreCom_denote 32 n arr idx val

end CatCrypt.Crypto.SecureCompilation.HetArrayStoreFront
