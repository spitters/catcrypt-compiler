/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote

/-!
# The byte-offset array oracle satisfies the in-bounds array laws

`LowCTMemDenote.byteOffsetLeafSpec 8` stores element `i` of a `TArr n TU64` array
at bytes `8 i .. 8 i + 7` and loads it into word `0` of the destination slot.
`byteOffset_lawfulArr` states that it satisfies `GuardedAgree.LawfulArr`: at an
index below `n`, a load gives the word `memGetDyn (arrWords n a) idx` and a store
writes the word view `memSetDyn (arrWords n a) idx v`.

The one-word laws `ArrLoadWord` / `ArrStoreWord` of `RustExecSemScalarBridge`
quantify over every index, and this oracle does not satisfy them: an index at or
past `n` leaves the array unchanged and loads `0`, while `memGetDyn` and
`memSetDyn` reduce the index modulo `n`.

## Main results

* `getWord_eq_wordOfBytes8`: the little-endian word read of eight in-range bytes
* `setWord_apply_of_not_mem`: a word write leaves the bytes outside its range
* `byteOffset_lawfulArr`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.LawfulArrByteOffset

open CatCrypt.Crypto.Jasmin (JArray)
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy cryptoTyOfRustVal wordOfBytes8)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge (arrWords)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree (LawfulArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote
  (byteOffsetLeafSpec arrElem arrSetElem valWord getWord_setWord_same)

/-- The little-endian word read of the eight bytes at `off .. off + 7`, all in
    range, is `wordOfBytes8` of those bytes. -/
theorem getWord_eq_wordOfBytes8 {N : Nat} (a : JArray N) (off : Nat) (h : off + 8 ≤ N) :
    a.getWord .U64 off = wordOfBytes8 (fun j => a ⟨off + j.val, by omega⟩) := by
  unfold JArray.getWord wordOfBytes8
  dsimp only [Jasmin.WSize.bits, Jasmin.WSize.bytes]
  rw [show List.range 8 = [0,1,2,3,4,5,6,7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil,
    dif_pos (show off + 0 < N by omega), dif_pos (show off + 1 < N by omega),
    dif_pos (show off + 2 < N by omega), dif_pos (show off + 3 < N by omega),
    dif_pos (show off + 4 < N by omega), dif_pos (show off + 5 < N by omega),
    dif_pos (show off + 6 < N by omega), dif_pos (show off + 7 < N by omega)]
  simp

/-- A word write leaves every byte outside the range `off .. off + 7`. -/
theorem setWord_apply_of_not_mem {N : Nat} (a : JArray N) (off : Nat) (v : BitVec 64)
    (p : Fin N) (hp : p.val < off ∨ off + 8 ≤ p.val) :
    (a.setWord .U64 off v) p = a p := by
  have step : ∀ (arr : JArray N) (j : Nat) (w : BitVec 8), p.val ≠ off + j →
      (if h : off + j < N then arr.set ⟨off + j, h⟩ w else arr) p = arr p := by
    intro arr j w hne
    split
    · simp only [JArray.set]
      exact Function.update_of_ne (fun h => hne (congrArg Fin.val h)) _ _
    · rfl
  unfold JArray.setWord
  dsimp only [Jasmin.WSize.bytes]
  rw [show List.range 8 = [0,1,2,3,4,5,6,7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [step _ 7 _ (by omega), step _ 6 _ (by omega), step _ 5 _ (by omega),
    step _ 4 _ (by omega), step _ 3 _ (by omega), step _ 2 _ (by omega),
    step _ 1 _ (by omega), step _ 0 _ (by omega)]

private theorem memGetDyn_of_lt {m : Nat} (arr : Fin m → BitVec 64) {k : Nat} (hk : k < m) :
    memGetDyn arr k = arr ⟨k, hk⟩ := by
  cases m with
  | zero => omega
  | succ m' => simp only [memGetDyn, Nat.mod_eq_of_lt hk]

private theorem memSetDyn_apply_of_lt {m : Nat} (arr : Fin m → BitVec 64) {k : Nat} (hk : k < m)
    (v : BitVec 64) (j : Fin m) : memSetDyn arr k v j = if j.val = k then v else arr j := by
  cases m with
  | zero => omega
  | succ m' =>
      simp only [memSetDyn, Nat.mod_eq_of_lt hk, Fin.ext_iff]

private theorem cryptoTy_TU64_eq_getWord (v : RustVal .TU64) :
    cryptoTyOfRustVal .TU64 v = v.getWord .U64 0 := by
  rw [getWord_eq_wordOfBytes8 v 0 (by simp [TowerType.storageBytes])]
  simp only [Nat.zero_add]
  rfl

private theorem arrWords_apply (n : Nat) (a : RustVal (.TArr n .TU64))
    (j : Fin ((n * TowerType.TU64.storageBytes + 7) / 8)) :
    arrWords n a j = a.getWord .U64 (8 * j.val) := by
  have hj := j.isLt
  simp only [TowerType.storageBytes] at hj
  rw [getWord_eq_wordOfBytes8 a (8 * j.val) (by simp only [TowerType.storageBytes]; omega)]
  rfl

/-- The byte-offset oracle at element size `8` satisfies the in-bounds array laws. -/
theorem byteOffset_lawfulArr : LawfulArr (byteOffsetLeafSpec 8) where
  load := by
    intro d oldV n a idx hidx
    have hm : idx < (n * TowerType.TU64.storageBytes + 7) / 8 := by
      simp only [TowerType.storageBytes]; omega
    show cryptoTyOfRustVal .TU64 (oldV.setWord .U64 0 (arrElem a 8 idx)) = _
    rw [cryptoTy_TU64_eq_getWord,
      getWord_setWord_same oldV 0 _ (by simp [TowerType.storageBytes])]
    refine Eq.trans ?_ (memGetDyn_of_lt (arrWords n a) hm).symm
    exact (arrWords_apply n a ⟨idx, hm⟩).symm
  store := by
    intro arr n oldV idx sv hidx
    have hm : idx < (n * TowerType.TU64.storageBytes + 7) / 8 := by
      simp only [TowerType.storageBytes]; omega
    show arrWords n (arrSetElem oldV 8 idx (valWord sv)) = _
    funext j
    refine Eq.trans ?_ (memSetDyn_apply_of_lt (arrWords n oldV) hm _ j).symm
    have hj := j.isLt
    simp only [TowerType.storageBytes] at hj
    by_cases hji : j.val = idx
    · refine (arrWords_apply n _ j).trans (Eq.trans ?_ (if_pos hji).symm)
      rw [hji, cryptoTy_TU64_eq_getWord]
      exact getWord_setWord_same oldV (8 * idx) _
        (by simp only [TowerType.storageBytes]; omega)
    · refine (arrWords_apply n _ j).trans
        (Eq.trans ?_ ((if_neg hji).trans (arrWords_apply n oldV j)).symm)
      refine (getWord_eq_wordOfBytes8 (arrSetElem oldV 8 idx (valWord sv)) (8 * j.val) ?_).trans
        ((congrArg wordOfBytes8 (funext fun t => ?_)).trans
          (getWord_eq_wordOfBytes8 oldV (8 * j.val) ?_).symm)
      · simp only [TowerType.storageBytes]; omega
      · exact setWord_apply_of_not_mem _ _ _ _ (by have := t.isLt; simp only; omega)
      · simp only [TowerType.storageBytes]; omega

end CatCrypt.Crypto.SecureCompilation.Dialects.LawfulArrByteOffset
