/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify

/-!
# `reifyAeneas%` at the array operations

An Aeneas array of words `Array (UScalar ty) n` is the NF array `arr n.val (word 64)` of the
`64`-bit words of its entries (`embA`). This module gives the embedding, its agreement with
the chain encoding (`enc_embA`, `dec_arrV`), the reading `aeCallV` of `index` and
`array_update` on encoded arrays (`aeCall2_index`, `aeCall3_update`), and the instances of
`ReifyE` at `Array.index_usize` and `Array.update`, with the literal index operands of
`LitOf`; the reader of `AeneasFront/Reify.lean` uses them as leaves.

## Main definitions

* `toU64`, `a64`: a word and an array of words as `u64` words
* `embA`: the NF value of an Aeneas array of words

## Main results

* `readArr_arrV`, `aeCall2_index`, `aeCall3_update`: the reading of the array calls
* `enc_embA`, `dec_arrV`: the embedding and the chain encoding
* `aeExpr_call`: the reading of a call expression
* `reifyE_index`, `reifyE_update`: the instances
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open _root_.Hax (Value)
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.ImpToNF (dec encAll)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

/-! ## Words and arrays as `u64` words -/

/-- A word as a `u64` word. -/
def toU64 {ty : UScalarTy} (x : UScalar ty) : U64 := ⟨BitVec.ofNat 64 x.val⟩

theorem toU64_val {ty : UScalarTy} [Le64 ty] (x : UScalar ty) : (toU64 x).val = x.val := by
  simp only [toU64, UScalar.val]
  exact Nat.mod_eq_of_lt (lt64 x)

theorem wordV_toU64 {ty : UScalarTy} [Le64 ty] (x : UScalar ty) : wordV (toU64 x) = wordV x := by
  simp only [wordV, toU64_val]

theorem readW_U64 {ty : UScalarTy} [Le64 ty] (x : UScalar ty) :
    readW .U64 (wordV x) = .ok (toU64 x) :=
  litA_ofNat (lt64 x)

theorem readWs_map {ty : UScalarTy} [Le64 ty] :
    ∀ xs : List (UScalar ty), readWs (xs.map wordV) = .ok (xs.map toU64)
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, readWs, readW_U64, bind_tc_ok, readWs_map xs, bind_tc_ok]
    rfl

theorem litA_usize (n : Usize) : litA .Usize (n.val : Int) = .ok n := by
  rw [litA_ofNat n.hBounds]
  cases n
  simp [UScalar.val]

/-- An array of words as an array of `u64` words. -/
def a64 {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) :
    Aeneas.Std.Array U64 n :=
  ⟨a.val.map toU64, by rw [List.length_map]; exact a.property⟩

theorem arrV_a64 {ty : UScalarTy} [Le64 ty] {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) :
    arrV (a64 a) = arrV a := by
  simp only [arrV, a64, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => wordV_toU64 x

theorem readArr_arrV {ty : UScalarTy} [Le64 ty] {n : Usize}
    (a : Aeneas.Std.Array (UScalar ty) n) :
    readArr (arrV a) = .ok ⟨n, a64 a⟩ := by
  have hl : (a.val.map toU64).length = n.val := by rw [List.length_map]; exact a.property
  have hn : litA .Usize ((a.val.map toU64).length : Int) = .ok n := by
    rw [hl]
    exact litA_usize n
  rw [arrV, readArr.eq_1, readWs_map, bind_tc_ok, hn, bind_tc_ok]
  split
  · rfl
  · contradiction

theorem index_a64 {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n)
    (i : Usize) :
    (a64 a).index_usize i = (a.index_usize i >>= fun z => .ok (toU64 z)) := by
  unfold Aeneas.Std.Array.index_usize
  have e : (a64 a).val = a.val.map toU64 := rfl
  rw [Aeneas.Std.Array.getElem?_Usize_eq, Aeneas.Std.Array.getElem?_Usize_eq, e,
    List.getElem?_map]
  cases a.val[i.val]? <;> rfl

theorem update_a64 {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n)
    (i : Usize) (x : UScalar ty) :
    (a64 a).update i (toU64 x) = (a.update i x >>= fun a' => .ok (a64 a')) := by
  unfold Aeneas.Std.Array.update
  have e : (a64 a).val = a.val.map toU64 := rfl
  rw [Aeneas.Std.Array.getElem?_Usize_eq, Aeneas.Std.Array.getElem?_Usize_eq]
  simp only [e, List.getElem?_map]
  cases a.val[i.val]? with
  | none => rfl
  | some _ =>
    simp only [Option.map_some]
    congr 1
    apply Subtype.ext
    simp [a64, List.map_set]

/-! ## The reading of the array calls -/

/-- `index` on an encoded array and an encoded `usize` index is the Aeneas `index_usize`. -/
theorem aeCall2_index {ty : UScalarTy} [Le64 ty] {n : Usize}
    (a : Aeneas.Std.Array (UScalar ty) n) (i : Usize) :
    aeCall2 "index" (arrV a) (wordV i) = (a.index_usize i >>= fun z => .ok (wordV z)) := by
  have h1 : wordOpAt? "index" = none := by decide +kernel
  have h2 : checkedAt? "index" = none := by decide +kernel
  have h3 : CmpOp.ofName? "index" = none := by decide +kernel
  have h4 : BoolOp.ofName? "index" = none := by decide +kernel
  unfold aeCall2
  rw [h1, h2, h3, h4]
  simp only [ite_true, readArr_arrV, readW_wordV, bind_tc_ok, index_a64]
  cases a.index_usize i with
  | ok z => simp only [bind_tc_ok, wordV_toU64]
  | fail _ => rfl
  | div => rfl

/-- `array_update` on an encoded array, index and value is the Aeneas `update`. -/
theorem aeCall3_update {ty : UScalarTy} [Le64 ty] {n : Usize}
    (a : Aeneas.Std.Array (UScalar ty) n) (i : Usize) (x : UScalar ty) :
    aeCall3 "array_update" (arrV a) (wordV i) (wordV x) =
      (a.update i x >>= fun a' => .ok (arrV a')) := by
  unfold aeCall3
  simp only [ite_true, readArr_arrV, readW_wordV, readW_U64, bind_tc_ok, update_a64]
  cases a.update i x with
  | ok a' => simp only [bind_tc_ok, arrV_a64]
  | fail _ => rfl
  | div => rfl

/-! ## The NF value of an array -/

/-- The NF value of an Aeneas array of words: the `64`-bit words of its entries. -/
def embA {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) :
    Fin n.val → BitVec 64 :=
  fun j => embW (a.val[j.1]'(by rw [a.property]; exact j.2))

/-- An Aeneas array of words is an NF array of `64`-bit words. -/
@[reducible] instance (ty : UScalarTy) (n : Usize) : AeVal (Aeneas.Std.Array (UScalar ty) n) :=
  ⟨.arr n.val (.word 64), embA⟩

theorem enc_embA {ty : UScalarTy} [Le64 ty] {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) :
    ImpToNF.enc (.arr n.val (.word 64)) (embA a) = arrV a := by
  simp only [ImpToNF.enc, arrV, Value.array.injEq]
  apply List.ext_getElem
  · simp [a.property]
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, embA]
    exact enc_embW _

theorem mapM_dec_wordV {ty : UScalarTy} [Le64 ty] :
    ∀ xs : List (UScalar ty), (xs.map wordV).mapM (dec (.word 64)) = some (xs.map embW)
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, List.mapM_cons, dec_wordV, mapM_dec_wordV xs]
    rfl

theorem dec_arrV {ty : UScalarTy} [Le64 ty] {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) :
    dec (.arr n.val (.word 64)) (arrV a) = some (embA a) := by
  have hl : (a.val.map embW).length = n.val := by rw [List.length_map]; exact a.property
  rw [arrV, dec, mapM_dec_wordV, Option.bind_some]
  split
  · congr 1
    funext j
    simp [embA]
  · contradiction

/-! ## Call expressions and the instances -/

/-- The reading of a call expression is the reading `aeCallV` of the call on the encodings of
    its arguments, decoded at its result type. -/
theorem aeExpr_call {Γ : Ctxt nfDialect} {as : List NfTy} {r : NfTy} (f : String)
    (args : HVector (fun t => Var Γ t) as) (V : Valuation Γ) {v : Value} {res : r.denote}
    (h : aeCallV f (encAll as (Expr.lookupArgs args V)) = .ok v) (hd : dec r v = some res) :
    aeExpr ⟨.call f as r, rfl, args⟩ V = .ok res := by
  change aeOp (.call f as r) (Expr.lookupArgs args V) = .ok res
  unfold aeOp
  rw [nfDenoteOp]
  unfold aeTable
  simp only [h, hd]

/-- `Array.index_usize` is the call `index`. -/
instance reifyE_index {ty : UScalarTy} [Le64 ty] {n : Usize} {Γ : Ctxt nfDialect}
    (a : Aeneas.Std.Array (UScalar ty) n) (i : Usize) (V : Valuation Γ)
    {va : Var Γ (.arr n.val (.word 64))} {vi : Var Γ (.word 64)}
    [ha : Lookup V (embA a) va] [hi : Lookup V (embW i) vi] :
    ReifyE (a.index_usize i) V
      ⟨.call "index" [.arr n.val (.word 64), .word 64] (.word 64), rfl,
        .cons va (.cons vi .nil)⟩ where
  sound z hz := by
    refine aeExpr_call _ _ V ?_ (dec_wordV z)
    change aeCall2 "index" (ImpToNF.enc _ (va.lookup V)) (ImpToNF.enc _ (vi.lookup V)) = _
    rw [ha.eq, hi.eq, enc_embA, enc_embW, aeCall2_index, hz]
    rfl

/-- `Array.update` is the call `array_update`. -/
instance reifyE_update {ty : UScalarTy} [Le64 ty] {n : Usize} {Γ : Ctxt nfDialect}
    (a : Aeneas.Std.Array (UScalar ty) n) (i : Usize) (x : UScalar ty) (V : Valuation Γ)
    {va : Var Γ (.arr n.val (.word 64))} {vi vx : Var Γ (.word 64)}
    [ha : Lookup V (embA a) va] [hi : Lookup V (embW i) vi] [hx : Lookup V (embW x) vx] :
    ReifyE (a.update i x) V
      ⟨.call "array_update" [.arr n.val (.word 64), .word 64, .word 64] (.arr n.val (.word 64)),
        rfl, .cons va (.cons vi (.cons vx .nil))⟩ where
  sound a' ha' := by
    refine aeExpr_call _ _ V ?_ (dec_arrV a')
    change aeCall3 "array_update" (ImpToNF.enc _ (va.lookup V)) (ImpToNF.enc _ (vi.lookup V))
      (ImpToNF.enc _ (vx.lookup V)) = _
    rw [ha.eq, hi.eq, hx.eq, enc_embA, enc_embW, enc_embW, aeCall3_update, ha']
    rfl

instance {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) (c : Usize) :
    LitOf (a.index_usize c) .Usize c := ⟨⟩

instance {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n) (c : Usize)
    (x : UScalar ty) : LitOf (a.update c x) .Usize c := ⟨⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront
