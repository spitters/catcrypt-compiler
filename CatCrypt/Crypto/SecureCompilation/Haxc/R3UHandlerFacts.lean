/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.Hax64Table
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgWiden

/-!
# The builtin table at reduce-multiply heads, and widening at 64-bit words

A reduce-multiply head (`montTag? f = some q`, a name `redc` followed by the tagged head of
the multiplication at `q`) is no name of the `u64` builtin table: `hax64Builtins f vals` is
`none`, and so are the admitted tables `hax64Exit` and `hax64WExit`. Every arm of
`hax64WordOps`, `hax64NarrowOps`, `hax64CmpOps` and `widthArrayOps` names a literal that does
not begin with `redc`, and the field heads `fieldTag?`, `fieldTagM?` read no such name.

The widening type map `wideTy` fixes `reg 64` and `stackArr 64 n`, and its value transport
`transTy` is the identity there.

## Main results

* `hax64Builtins_of_montTag?`, `hax64Exit_of_montTag?`, `hax64WExit_of_montTag?`.
* `wideTy_reg64`, `wideTy_stackArr64`, `transTy_stackArr64`.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify

open _root_.Hax (Value hax64Builtins hax64WordOps hax64NarrowOps hax64CmpOps widthArrayOps)

variable {f : String} {q : Nat}

/-- A reduce-multiply head differs from every name that `montTag?` does not read. -/
theorem eq_false_of_montTag? (hf : montTag? f = some q) (s : String) (hs : montTag? s = none) :
    (f = s) = False :=
  eq_false fun h => by subst h; simp_all

/-- `widthArrayOps` has no arm at a reduce-multiply head. -/
theorem widthArrayOps_of_montTag? (hf : montTag? f = some q) (args : List Value) :
    widthArrayOps f args = none := by
  unfold widthArrayOps
  split <;> first | rfl | cases hf

set_option linter.auxLemma false in
/-- `hax64CmpOps` has no arm at a reduce-multiply head. -/
theorem hax64CmpOps_of_montTag? (hf : montTag? f = some q) (args : List Value) :
    hax64CmpOps f args = none := by
  unfold hax64CmpOps Hax.hax64CmpOps.match_1
  simp (disch := decide) only [eq_false_of_montTag? hf, dite_false]

set_option linter.auxLemma false in
/-- `hax64NarrowOps` has no arm at a reduce-multiply head. -/
theorem hax64NarrowOps_of_montTag? (hf : montTag? f = some q) (args : List Value) :
    hax64NarrowOps f args = none := by
  unfold hax64NarrowOps Hax.hax64NarrowOps.match_1
  simp (disch := decide) only [eq_false_of_montTag? hf, dite_false, hax64CmpOps_of_montTag? hf]

set_option linter.auxLemma false in
/-- `hax64WordOps` has no arm at a reduce-multiply head. -/
theorem hax64WordOps_of_montTag? (hf : montTag? f = some q) (args : List Value) :
    hax64WordOps f args = none := by
  obtain ⟨h1, h2⟩ := _root_.Hax.FieldTag.fieldHeadB_eq_false_iff.mp (fieldHeadB_of_montTag? hf)
  unfold hax64WordOps
  rw [h1, h2]
  dsimp only
  unfold Hax.hax64WordOps.match_1
  simp (disch := decide) only [eq_false_of_montTag? hf, dite_false,
    hax64NarrowOps_of_montTag? hf]

/-- **The `u64` builtin table answers nothing at a reduce-multiply head.** -/
theorem hax64Builtins_of_montTag? (hf : montTag? f = some q) (args : List Value) :
    hax64Builtins f args = none := by
  rw [_root_.Hax.hax64Builtins_of_none (hax64WordOps_of_montTag? hf args)]
  exact widthArrayOps_of_montTag? hf args

/-- The admitted `u64` table answers nothing at a reduce-multiply head. -/
theorem hax64Exit_of_montTag? (hf : montTag? f = some q) (args : List Value) :
    CatCrypt.Crypto.Hax.hax64Exit f args = none := by
  cases h : CatCrypt.Crypto.Hax.hax64Exit f args with
  | none => rfl
  | some r =>
      have := CatCrypt.Crypto.Hax.hax64Exit_sub h
      rw [hax64Builtins_of_montTag? hf] at this
      cases this

/-- The widened admitted `u64` table answers nothing at a reduce-multiply head. -/
theorem hax64WExit_of_montTag? (hf : montTag? f = some q) (args : List Value) :
    CatCrypt.Crypto.Hax.hax64WExit f args = none := by
  cases h : CatCrypt.Crypto.Hax.hax64WExit f args with
  | none => rfl
  | some r =>
      have := CatCrypt.Crypto.Hax.hax64WExit_sub h
      rw [hax64Builtins_of_montTag? hf] at this
      cases this

end CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- `wideTy` fixes the 64-bit register. -/
@[simp] theorem wideTy_reg64 : wideTy (.reg 64) = .reg 64 := by
  simp [wideTy, wideW, narrowB]

/-- `wideTy` fixes a stack array of 64-bit words. -/
@[simp] theorem wideTy_stackArr64 (n : Nat) : wideTy (.stackArr 64 n) = .stackArr 64 n := by
  simp [wideTy, wideW, narrowB]

/-- A stack array of 64-bit words is held as itself. -/
theorem transTy_stackArr64 {n : Nat} (a : Fin n → BitVec 64) :
    transTy (t := .stackArr 64 n) a = a := by
  funext i
  exact BitVec.setWidth_eq (a i)

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords
