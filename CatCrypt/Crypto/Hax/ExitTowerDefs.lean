/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxCallNames
public import HaxLean.FieldTag

/-!
# Slots, admitted names and scalar operations of the typed exit lowering

The definitions of the typed exit lowering that a builtin table, a bridge and a leaf
semantics are stated over.

## Main definitions

* `ValueTowerBridge`: a relation between a hax value and a slot of each tower type;
* `exitCallName`: the tower slot a call or an element load writes;
* `exitAdmits`: the call names the typed lowering admits (every name except a wide field
  head);
* `exitElem`: the element type an element store writes into an array held at a type;
* `exitArrLen`: the number of elements of an array type;
* `scalarOpNatT`: hax-lean's scalar operation on two scalars, as `LowCT` computes it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (Value)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType RustVal)

/-- `ValueTowerBridge eq` packages a relation `eq : ∀ dt, Value → RustVal dt → Prop`
    that says "Hax Value `v` and RustVal of tower type `dt` represent the
    same logical value".  Per-protocol instances (BLS, Curve25519, etc.)
    populate this. -/
def ValueTowerBridge : Type :=
  ∀ (dt : TowerType), Value → RustVal dt → Prop

/-- The tower slot a call or an element load writes before its result is copied to
    the bound name. -/
def exitCallName : String := "__exit_call"

/-- A call name the typed lowering admits: every name except a wide field head, a tagged
    field head `m#p` (`Hax.FieldTag.fieldTag?`) at a modulus `p ≥ 2^64`, whose operands and
    result `Hax.FieldTag.fieldCall` holds as arrays of `Hax.FieldTag.fieldLimbs p` limbs. -/
def exitAdmits (f : String) : Bool :=
  match _root_.Hax.FieldTag.fieldTag? f with
  | some (_, p) => decide (p < 2 ^ 64)
  | none => true

/-- A name without `#` is admitted: it is no tagged field head. -/
theorem exitAdmits_of_not_hash {f : String} (h : f.contains '#' = false) :
    exitAdmits f = true := by
  unfold exitAdmits
  rcases ht : _root_.Hax.FieldTag.fieldTag? f with _ | ⟨m, p⟩
  · rfl
  · have hm := _root_.Hax.FieldTag.mem_toList_of_fieldTag? ht
    simp [String.contains_char_eq, hm] at h

/-- A call outside `exitScalarRes` is admitted: a tagged field head contains `#` and is a
    scalar call. -/
theorem exitAdmits_of_scalarRes_false {f : String} (h : exitScalarRes f = false) :
    exitAdmits f = true := by
  apply exitAdmits_of_not_hash
  simp only [exitScalarRes, exitScalarCall, Bool.or_eq_false_iff] at h
  exact h.1.2

/-- The element type of a container type: `TPolyMod q n` for `TPolyVec q n k` (`k`
    polynomials), `TPolyVec q n m` for `TPolyMat q n k m` (`k` polynomial vectors of length
    `m`), the coefficient type `TFp` for `TPolyMod q n`, the byte type `TU8` for `TBytes n`,
    `t` for `TArr n t`, and the type itself at every other type. -/
def _root_.CatCrypt.Crypto.Jasmin.LowCT.TowerType.elemType : TowerType → TowerType
  | .TPolyVec q n _k    => .TPolyMod q n
  | .TPolyMat q n _k m  => .TPolyVec q n m
  | .TPolyMod _q _n     => .TFp
  | .TBytes _           => .TU8
  | .TArr _ t           => t
  | t                   => t

/-- The type of the elements an element store writes into an array held at `t`: the
    element tower type of `exitElemTower`, and `t.elemType` for an array of words. -/
def exitElem (t : TowerType) : TowerType := (exitElemTower t).getD t.elemType

/-- The number of elements of an array type: `n` for `TArr n t`, and `2`, `3`, `2` for the
    containers `TFp2`, `TFp6`, `TFp12`. -/
def exitArrLen : TowerType → Option Nat
  | .TArr n _ => some n
  | .TFp2 => some 2
  | .TFp6 => some 3
  | .TFp12 => some 2
  | _ => none

/-- hax-lean's scalar operation `op` on scalars, as `LowCT` computes it: the value of
    `scalarOpExprT op` on the literals `a` and `b`, and `0` for an operation outside
    `scalarOpExprT`. -/
def scalarOpNatT (op : String) (a b : Nat) : Nat :=
  match scalarOpExprT op (.SLit a) (.SLit b) with
  | some se => se.eval fun _ => 0
  | none => 0

end CatCrypt.Crypto.Hax
