/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFoldPosHyps

/-!
# The fold class from the names of an instruction

The theorem `fieldDom_foldPos_of_loadsChainK` takes the fold class `PosClass` of the code behind
the prefix of the parts (`hP`) and the absence of array self-moves (`hNP`) as hypotheses. This
module reduces both to facts about the names of single instructions.

A cell name `memName A o` begins with `m` (`memName_head`), so an instruction none of whose
names begins with `m` names no cell. The fold class of an instruction then asks only that its
scalar names are no cell arrays, that a store writes its own base, and that an access of a cell
array has the length of that array (`PosShape`). An array self-move `selfMoveB` is a load
directly followed by a store of the same array at the same index of the loaded value; code in
which no load is so followed has no pair of `selfPairB`.

## Main definitions

* `NoMName`: no name of an instruction begins with `m`.
* `PosShape`: the shape of an instruction of the fold class at the slot arrays.

## Main results

* `posClass_load`, `posClass_store`, `posClass_keepB`, `posClass_keepRegB`: the fold class of
  one instruction from its names.
* `posClass_of_posShape`: the fold class from `PosShape` and `NoMName`.
* `posClass_parts_of_posShape`: the hypothesis `hP` of `fieldDom_foldPos_of_loadsChainK` from
  `PosShape` and `NoMName` at every position of the code behind the prefix.
* `selfMoveB_eq_false_of_base_ne`, `selfMoveB_eq_false_of_not_load`: a pair whose arrays differ,
  or whose first instruction is no load, is no array self-move.
* `selfPairB_eq_false_of_selfMoveB`: code without an array self-move behind `k0` has no pair of
  `selfPairB`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames mulxFree
  mulxFree_of_lopn1)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots isArrB isCellB lenOf
  keepB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL (ctlB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg (keepRegB noArrB readNames)

/-! ## 1. The fold class of one instruction -/

/-- **No name of the instruction `i` begins with `m`.** -/
def NoMName (i : LinstrRM) : Prop :=
  ∀ x ∈ instrNames i.1, x.toList.head? ≠ some 'm'

/-- **A load of a slot array into a name that is no slot array**, at an index that is no slot
    array, of the length of the array when it is a slot array, is of the fold class. -/
theorem posClass_load {R : Slots} {d b x : String} {s n : Nat}
    (hm : NoMName (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load 64 n))
    (hd : isArrB R d = false) (hx : isArrB R x = false)
    (hn : isArrB R b = true → lenOf R b = some n) :
    PosClass R (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load 64 n) := by
  have hc : ∀ y ∈ [d, b, x], isCellB R y = false := fun y hy =>
    isCellB_of_head (hm y (by simpa [instrNames, JasminLsemExportRewrites.opNames] using hy)) R
  have hmx : mulxFree (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load 64 n) = true :=
    mulxFree_of_lopn1 ⟨.reg d, "LOADIDX", _, rfl⟩
  cases hb : isArrB R b
  · refine .inr (.inr (.inl ?_))
    simp_all [keepB, isLopnB, instrNames, JasminLsemExportRewrites.opNames]
  · exact .inl ⟨d, b, x, s, n, rfl, hb, hn hb, hc d (by simp), hd⟩

/-- **A store to a slot array of its own base**, at an index that is no slot array, of a value
    that is no slot array, of the length of the array when it is a slot array, is of the fold
    class. -/
theorem posClass_store {R : Slots} {b x v : String} {s n : Nat}
    (hm : NoMName (.Lopn [.reg b] "STOREIDX" [.arrIdx b x s, .reg v], .store 64 n))
    (hx : isArrB R x = false) (hv : isArrB R v = false)
    (hn : isArrB R b = true → lenOf R b = some n) :
    PosClass R (.Lopn [.reg b] "STOREIDX" [.arrIdx b x s, .reg v], .store 64 n) := by
  have hc : ∀ y ∈ [b, x, v], isCellB R y = false := fun y hy =>
    isCellB_of_head (hm y (by simpa [instrNames, JasminLsemExportRewrites.opNames] using hy)) R
  have hmx : mulxFree (.Lopn [.reg b] "STOREIDX" [.arrIdx b x s, .reg v], .store 64 n) = true :=
    mulxFree_of_lopn1 ⟨.reg b, "STOREIDX", _, rfl⟩
  cases hb : isArrB R b
  · refine .inr (.inr (.inl ?_))
    simp_all [keepB, isLopnB, instrNames, JasminLsemExportRewrites.opNames]
  · exact .inr (.inl ⟨b, x, s, v, n, rfl, hb, hn hb, hc v (by simp)⟩)

/-- **An operation that is no `MULX` and names no slot array** is of the fold class. -/
theorem posClass_keepB {R : Slots} {i : LinstrRM} (hm : NoMName i) (hl : isLopnB i = true)
    (hx : mulxFree i = true) (ha : ∀ y ∈ instrNames i.1, isArrB R y = false) :
    PosClass R i := by
  refine .inr (.inr (.inl ?_))
  simp only [keepB, hl, hx, Bool.and_self, Bool.true_and, List.all_eq_true, Bool.and_eq_true,
    Bool.not_eq_true']
  exact fun y hy => ⟨ha y hy, isCellB_of_head (hm y hy) R⟩

/-- **An operation without an array tag whose written and read names begin with no `m`** is of
    the fold class. -/
theorem posClass_keepRegB {R : Slots} {i : LinstrRM} (hl : isLopnB i = true)
    (ha : noArrB i = true) (hd : ∀ y ∈ dstNames i.1, y.toList.head? ≠ some 'm')
    (hr : ∀ y ∈ readNames i.1, y.toList.head? ≠ some 'm') : PosClass R i := by
  refine .inr (.inr (.inr (.inl ?_)))
  have hrdx : isCellB R "RDX" = false := isCellB_of_head (by decide) R
  simp only [keepRegB, hl, ha, Bool.true_or, Bool.true_and, hrdx, Bool.not_false,
    Bool.and_true, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  exact ⟨fun y hy => isCellB_of_head (hd y hy) R, fun y hy => isCellB_of_head (hr y hy) R⟩

/-! ## 2. The shape of the fold class -/

/-- **The shape of an instruction of the fold class** at the slot arrays `R`: a load into a
    name that is no slot array at an index that is no slot array; a store of its own base at an
    index and of a value that are no slot arrays; in both cases of the length of the array when
    it is a slot array; an operation that is no `MULX` and names no slot array; an operation
    without an array tag whose names begin with no `m`; or a control instruction of `ctlB`. -/
def PosShape (R : Slots) (i : LinstrRM) : Prop :=
  (∃ d b x s n, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load 64 n) ∧
      isArrB R d = false ∧ isArrB R x = false ∧ (isArrB R b = true → lenOf R b = some n))
  ∨ (∃ b x s v n, i = (.Lopn [.reg b] "STOREIDX" [.arrIdx b x s, .reg v], .store 64 n) ∧
      isArrB R x = false ∧ isArrB R v = false ∧ (isArrB R b = true → lenOf R b = some n))
  ∨ (isLopnB i = true ∧ mulxFree i = true ∧ ∀ y ∈ instrNames i.1, isArrB R y = false)
  ∨ (isLopnB i = true ∧ noArrB i = true ∧ (∀ y ∈ dstNames i.1, y.toList.head? ≠ some 'm')
      ∧ ∀ y ∈ readNames i.1, y.toList.head? ≠ some 'm')
  ∨ (isLopnB i = false ∧ ctlB i = true)

/-- **The fold class from the shape** of an instruction none of whose names begins with
    `m`. -/
theorem posClass_of_posShape {R : Slots} {i : LinstrRM} (hm : NoMName i) (h : PosShape R i) :
    PosClass R i := by
  rcases h with ⟨d, b, x, s, n, rfl, hd, hx, hn⟩ | ⟨b, x, s, v, n, rfl, hx, hv, hn⟩ |
      ⟨hl, hx, ha⟩ | ⟨hl, ha, hd, hr⟩ | h
  · exact posClass_load hm hd hx hn
  · exact posClass_store hm hx hv hn
  · exact posClass_keepB hm hl hx ha
  · exact posClass_keepRegB hl ha hd hr
  · exact .inr (.inr (.inr (.inr h)))

/-- **The hypothesis `hP` of `fieldDom_foldPos_of_loadsChainK`** from the shape of the fold
    class and names that begin with no `m` at every position of the code behind the prefix of
    the parts. -/
theorem posClass_parts_of_posShape (d : CoParts)
    (hm : ∀ (k : Nat) (i : LinstrRM), (d.fused.drop d.pre.length)[k]? = some i → NoMName i)
    (hs : ∀ (k : Nat) (i : LinstrRM), (d.fused.drop d.pre.length)[k]? = some i →
      PosShape d.cells i) :
    ∀ (k : Nat) (i : LinstrRM), (d.fused.drop d.pre.length)[k]? = some i → PosClass d.cells i :=
  fun k i hk => posClass_of_posShape (hm k i hk) (hs k i hk)

/-! ## 3. Array self-moves -/

/-- **A load and a store of different arrays are no array self-move.** -/
theorem selfMoveB_eq_false_of_base_ne {t a z a' b z' t' : String} {s s' w w' n n' : Nat}
    (h : a ≠ b) :
    selfMoveB (.Lopn [.reg t] "LOADIDX" [.arrIdx a z s], .load w n)
      (.Lopn [.reg a'] "STOREIDX" [.arrIdx b z' s', .reg t'], .store w' n') = false := by
  simp [selfMoveB, h]

/-- **A pair whose first instruction is no load is no array self-move.** -/
theorem selfMoveB_eq_false_of_not_load {i j : LinstrRM}
    (h : ∀ t a z s w n, i ≠ (.Lopn [.reg t] "LOADIDX" [.arrIdx a z s], .load w n)) :
    selfMoveB i j = false := by
  cases hm : selfMoveB i j
  · rfl
  · obtain ⟨t, a, z, s, w, n, hi, -⟩ := selfMoveB_shape hm
    exact absurd hi (h t a z s w n)

/-- **Code without an array self-move behind `k0` has no pair of `selfPairB`**, at every liveness
    table. -/
theorem selfPairB_eq_false_of_selfMoveB {k0 : Nat} {B : List LinstrRM}
    (h : ∀ k i j, k0 ≤ k → B[k]? = some i → B[k + 1]? = some j → selfMoveB i j = false)
    (Lr : Nat → List String) (k : Nat) : selfPairB k0 Lr B k = false := by
  unfold selfPairB
  by_cases hk : k0 ≤ k
  · rw [decide_eq_true hk, Bool.true_and]
    split
    · rename_i i j hi hj
      rw [h k i j hk hi hj, Bool.false_and]
    · rfl
  · rw [decide_eq_false hk, Bool.false_and]

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
