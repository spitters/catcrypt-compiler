/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyArrays

/-!
# `reifyAeneas%` at slices of words and arrays of arrays of words

An Aeneas slice of words `Slice (UScalar ty)` is the NF slice `slice (word 64)` of the `64`-bit
words of its entries (`embS`), encoded as the chain array of its entries (`sliceV`). A slice is
the array of its length (`sArr`), so `index` and `array_update` read `Slice.index_usize` and
`Slice.update` through the array readings of `AeneasFront/ReifyArrays.lean`
(`aeCall2_sindex`, `aeCall3_supdate`).

An Aeneas array of arrays of words `Array (Array (UScalar ty) n) m` is the NF array
`arr m (arr n (word 64))` (`embAA`); its `index_usize` and `update` are the NF operations
`index` and `update` at the element type `arr n (word 64)`.

## Main definitions

* `sliceV`, `embS`: the chain value and the NF value of a slice of words
* `sArr`: a slice of words as the array of its length
* `embAA`: the NF value of an array of arrays of words

## Main results

* `aeCall2_sindex`, `aeCall3_supdate`: the reading of the calls on encoded slices
* `enc_embS`, `dec_sliceV`: the embedding of a slice and the chain encoding
* `reifyE_sindex`, `reifyE_supdate`: the instances at `Slice.index_usize` and `Slice.update`
* `reifyE_aaIndex`, `reifyE_aaUpdate`: the instances at `Array.index_usize` and `Array.update`
  of an array of arrays
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

/-! ## Slices of words -/

/-- A slice of words as the array of its length. -/
def sArr {ty : UScalarTy} (s : Slice (UScalar ty)) : Aeneas.Std.Array (UScalar ty) s.len :=
  ⟨s.val, by simp⟩

/-- The chain value of an Aeneas slice of words: the chain value of the array of its length,
    the array of the encodings of its entries. -/
def sliceV {ty : UScalarTy} (s : Slice (UScalar ty)) : Value := arrV (sArr s)

/-- `Array.index_usize` of the array of a slice is `Slice.index_usize`: both read the list of
    entries at the index. -/
theorem index_sArr {ty : UScalarTy} (s : Slice (UScalar ty)) (i : Usize) :
    (sArr s).index_usize i = s.index_usize i := rfl

theorem update_sArr {ty : UScalarTy} (s : Slice (UScalar ty)) (i : Usize) (x : UScalar ty) :
    ((sArr s).update i x >>= fun a' => .ok (arrV a')) =
      (s.update i x >>= fun s' => .ok (sliceV s')) := by
  unfold Aeneas.Std.Array.update Slice.update
  rw [Aeneas.Std.Array.getElem?_Usize_eq]
  rcases h : s.val[i.val]? with _ | y
  · have h' : (sArr s).val[i.val]? = none := h
    simp only [h']
    rfl
  · have h' : (sArr s).val[i.val]? = some y := h
    simp only [h']
    rfl

/-- `index` on an encoded slice and an encoded `usize` index is the Aeneas
    `Slice.index_usize`. -/
theorem aeCall2_sindex {ty : UScalarTy} [Le64 ty] (s : Slice (UScalar ty)) (i : Usize) :
    aeCall2 "index" (sliceV s) (wordV i) = (s.index_usize i >>= fun z => .ok (wordV z)) := by
  rw [sliceV, aeCall2_index, index_sArr]

/-- `array_update` on an encoded slice, index and value is the Aeneas `Slice.update`. -/
theorem aeCall3_supdate {ty : UScalarTy} [Le64 ty] (s : Slice (UScalar ty)) (i : Usize)
    (x : UScalar ty) :
    aeCall3 "array_update" (sliceV s) (wordV i) (wordV x) =
      (s.update i x >>= fun s' => .ok (sliceV s')) := by
  rw [sliceV, aeCall3_update, update_sArr]

/-- The NF value of an Aeneas slice of words: the `64`-bit words of its entries. -/
def embS {ty : UScalarTy} (s : Slice (UScalar ty)) : List (BitVec 64) := s.val.map embW

/-- An Aeneas slice of words is an NF slice of `64`-bit words. -/
@[reducible] instance (ty : UScalarTy) : AeVal (Slice (UScalar ty)) := ⟨.slice (.word 64), embS⟩

theorem enc_embS {ty : UScalarTy} [Le64 ty] (s : Slice (UScalar ty)) :
    ImpToNF.enc (.slice (.word 64)) (embS s) = sliceV s := by
  simp only [ImpToNF.enc, embS, sliceV, arrV, sArr, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => enc_embW x

theorem dec_sliceV {ty : UScalarTy} [Le64 ty] (s : Slice (UScalar ty)) :
    dec (.slice (.word 64)) (sliceV s) = some (embS s) :=
  mapM_dec_wordV s.val

/-- `Slice.index_usize` is the call `index`. -/
instance reifyE_sindex {ty : UScalarTy} [Le64 ty] {Γ : Ctxt nfDialect}
    (s : Slice (UScalar ty)) (i : Usize) (V : Valuation Γ)
    {vs : Var Γ (.slice (.word 64))} {vi : Var Γ (.word 64)}
    [hs : Lookup V (embS s) vs] [hi : Lookup V (embW i) vi] :
    ReifyE (s.index_usize i) V
      ⟨.call "index" [.slice (.word 64), .word 64] (.word 64), rfl,
        .cons vs (.cons vi .nil)⟩ where
  sound z hz := by
    refine aeExpr_call _ _ V ?_ (dec_wordV z)
    change aeCall2 "index" (ImpToNF.enc _ (vs.lookup V)) (ImpToNF.enc _ (vi.lookup V)) = _
    rw [hs.eq, hi.eq, enc_embS, enc_embW, aeCall2_sindex, hz]
    rfl

/-- `Slice.update` is the call `array_update`. -/
instance reifyE_supdate {ty : UScalarTy} [Le64 ty] {Γ : Ctxt nfDialect}
    (s : Slice (UScalar ty)) (i : Usize) (x : UScalar ty) (V : Valuation Γ)
    {vs : Var Γ (.slice (.word 64))} {vi vx : Var Γ (.word 64)}
    [hs : Lookup V (embS s) vs] [hi : Lookup V (embW i) vi] [hx : Lookup V (embW x) vx] :
    ReifyE (s.update i x) V
      ⟨.call "array_update" [.slice (.word 64), .word 64, .word 64] (.slice (.word 64)),
        rfl, .cons vs (.cons vi (.cons vx .nil))⟩ where
  sound s' hs' := by
    refine aeExpr_call _ _ V ?_ (dec_sliceV s')
    change aeCall3 "array_update" (ImpToNF.enc _ (vs.lookup V)) (ImpToNF.enc _ (vi.lookup V))
      (ImpToNF.enc _ (vx.lookup V)) = _
    rw [hs.eq, hi.eq, hx.eq, enc_embS, enc_embW, enc_embW, aeCall3_supdate, hs']
    rfl

instance {ty : UScalarTy} (s : Slice (UScalar ty)) (c : Usize) :
    LitOf (s.index_usize c) .Usize c := ⟨⟩

instance {ty : UScalarTy} (s : Slice (UScalar ty)) (c : Usize) (x : UScalar ty) :
    LitOf (s.update c x) .Usize c := ⟨⟩

/-! ## Arrays of arrays of words -/

/-- The NF value of an Aeneas array of arrays of words: the NF values of its rows. -/
def embAA {ty : UScalarTy} {n m : Usize}
    (s : Aeneas.Std.Array (Aeneas.Std.Array (UScalar ty) n) m) :
    Fin m.val → Fin n.val → BitVec 64 :=
  fun j => embA (s.val[j.1]'(by rw [s.property]; exact j.2))

/-- An Aeneas array of arrays of words is an NF array of arrays of `64`-bit words. -/
@[reducible] instance (ty : UScalarTy) (n m : Usize) :
    AeVal (Aeneas.Std.Array (Aeneas.Std.Array (UScalar ty) n) m) :=
  ⟨.arr m.val (.arr n.val (.word 64)), embAA⟩

/-- The reading of an expression of an operation other than a call is the operation's NF
    meaning. -/
theorem aeExpr_op {Γ : Ctxt nfDialect} (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
    (V : Valuation Γ) {res : op.ret.denote}
    (h : nfDenoteOp aeTable op (Expr.lookupArgs args V) = some res) :
    aeExpr ⟨op, rfl, args⟩ V = .ok res := by
  change aeOp op (Expr.lookupArgs args V) = .ok res
  unfold aeOp
  rw [h]

theorem index_usize_ok {α : Type} {n : Usize} {a : Aeneas.Std.Array α n} {i : Usize} {z : α}
    (h : a.index_usize i = .ok z) : ∃ hi : i.val < a.val.length, a.val[i.val] = z := by
  unfold Aeneas.Std.Array.index_usize at h
  rw [Aeneas.Std.Array.getElem?_Usize_eq] at h
  rcases hx : a.val[i.val]? with _ | x
  · rw [hx] at h
    cases h
  · rw [hx] at h
    cases h
    exact List.getElem?_eq_some_iff.mp hx

theorem update_ok {α : Type} {n : Usize} {a a' : Aeneas.Std.Array α n} {i : Usize} {x : α}
    (h : a.update i x = .ok a') : i.val < a.val.length ∧ a'.val = a.val.set i.val x := by
  unfold Aeneas.Std.Array.update at h
  rw [Aeneas.Std.Array.getElem?_Usize_eq] at h
  rcases hx : a.val[i.val]? with _ | y
  · rw [hx] at h
    cases h
  · rw [hx] at h
    cases h
    exact ⟨(List.getElem?_eq_some_iff.mp hx).1, rfl⟩

theorem embW_toNat {ty : UScalarTy} [Le64 ty] (x : UScalar ty) : (embW x).toNat = x.val := by
  simp only [embW, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt64 x)

/-- `Array.index_usize` of an array of arrays is the NF operation `index`. -/
instance reifyE_aaIndex {ty : UScalarTy} [Le64 ty] {n m : Usize} {Γ : Ctxt nfDialect}
    (s : Aeneas.Std.Array (Aeneas.Std.Array (UScalar ty) n) m) (i : Usize) (V : Valuation Γ)
    {vs : Var Γ (.arr m.val (.arr n.val (.word 64)))} {vi : Var Γ (.word 64)}
    [hs : Lookup V (embAA s) vs] [hi : Lookup V (embW i) vi] :
    ReifyE (s.index_usize i) V
      ⟨.index m.val (.arr n.val (.word 64)), rfl, .cons vs (.cons vi .nil)⟩ where
  sound z hz := by
    obtain ⟨hlt, hz⟩ := index_usize_ok hz
    apply aeExpr_op
    change nfDenoteOp aeTable (.index m.val (.arr n.val (.word 64)))
      (.cons (vs.lookup V) (.cons (vi.lookup V) .nil)) = _
    rw [hs.eq, hi.eq, nfDenoteOp]
    have hlt' : (embW i).toNat < m.val := by
      rw [embW_toNat, ← s.property]
      exact hlt
    simp only [HVector.head, HVector.tail, hlt', ↓reduceDIte]
    simp only [embAA, embW_toNat, hz]
    rfl

/-- `Array.update` of an array of arrays is the NF operation `update`. -/
instance reifyE_aaUpdate {ty : UScalarTy} [Le64 ty] {n m : Usize} {Γ : Ctxt nfDialect}
    (s : Aeneas.Std.Array (Aeneas.Std.Array (UScalar ty) n) m) (i : Usize)
    (x : Aeneas.Std.Array (UScalar ty) n) (V : Valuation Γ)
    {vs : Var Γ (.arr m.val (.arr n.val (.word 64)))} {vi : Var Γ (.word 64)}
    {vx : Var Γ (.arr n.val (.word 64))}
    [hs : Lookup V (embAA s) vs] [hi : Lookup V (embW i) vi] [hx : Lookup V (embA x) vx] :
    ReifyE (s.update i x) V
      ⟨.update m.val (.arr n.val (.word 64)), rfl, .cons vs (.cons vi (.cons vx .nil))⟩ where
  sound s' hs' := by
    obtain ⟨hlt, hval⟩ := update_ok hs'
    apply aeExpr_op
    change nfDenoteOp aeTable (.update m.val (.arr n.val (.word 64)))
      (.cons (vs.lookup V) (.cons (vi.lookup V) (.cons (vx.lookup V) .nil))) = _
    rw [hs.eq, hi.eq, hx.eq, nfDenoteOp]
    have hlt' : (embW i).toNat < m.val := by
      rw [embW_toNat, ← s.property]
      exact hlt
    simp only [HVector.head, HVector.tail, hlt', ↓reduceDIte, Option.some.injEq]
    funext j
    change _ = embAA s' j
    simp only [Function.update_apply, embAA, hval, List.getElem_set, Fin.ext_iff, embW_toNat]
    split <;> grind

instance {ty : UScalarTy} {n m : Usize}
    (s : Aeneas.Std.Array (Aeneas.Std.Array (UScalar ty) n) m) (c : Usize) :
    LitOf (s.index_usize c) .Usize c := ⟨⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront
