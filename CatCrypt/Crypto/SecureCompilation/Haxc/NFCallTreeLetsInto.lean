/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick
public import HaxLean.Phase.LetIntoBranches

/-!
# Bindings moved into statements at the level of call trees

The front moves a binding of an `if`-expression into its branches and a binding of a block past
its statements (`bindInto`, `letsInto`). The rewriting introduces no name, duplicates no
expression and reorders no evaluation, so the reading `denoteT` of the rewritten expression at
every tree table and fuel is the reading of the expression: the call trees are equal.

## Main results

* `denoteForLoopT_congr` and its companions: a loop reading depends on its body only through the
  readings of the body.
* `denoteT_bindInto`: the reading of `bindInto x v k` is that of `let x = v; k`.
* `denoteT_letsInto`: the reading of `letsInto e` is that of `e`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeLetsInto

open _root_.Hax
open _root_.Hax.LetIntoBranches (bindInto letsInto)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc denoteT_seq_run
  denoteT_ifThenElse_run denoteT_letBind_run')

variable {E : EventSig}

/-! ## Loops over bodies with equal readings -/

section Loops

variable {bt : TreeTable E} {b b' : ImpExpr} (hb : ∀ f, denoteT bt f b' = denoteT bt f b)
include hb

/-- The counted loop over bodies with equal readings. -/
theorem denoteForLoopT_congr (i : String) :
    ∀ fuel lo hi, denoteForLoopT bt fuel i lo hi b' = denoteForLoopT bt fuel i lo hi b := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoopT; simp
  | succ n ih =>
    intro lo hi
    unfold denoteForLoopT
    simp only [hb, Nat.add_sub_cancel, ih]

/-- The reversed counted loop over bodies with equal readings. -/
theorem denoteForLoopRevT_congr (i : String) :
    ∀ fuel lo hi, denoteForLoopRevT bt fuel i lo hi b' = denoteForLoopRevT bt fuel i lo hi b := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoopRevT; simp
  | succ n ih =>
    intro lo hi
    unfold denoteForLoopRevT
    simp only [hb, Nat.add_sub_cancel, ih]

/-- The counted loop with a return over bodies with equal readings. -/
theorem denoteForLoopReturnT_congr (i : String) :
    ∀ fuel lo hi,
      denoteForLoopReturnT bt fuel i lo hi b' = denoteForLoopReturnT bt fuel i lo hi b := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoopReturnT; simp
  | succ n ih =>
    intro lo hi
    unfold denoteForLoopReturnT
    simp only [hb, Nat.add_sub_cancel, ih]

/-- The reversed counted loop with a return over bodies with equal readings. -/
theorem denoteForLoopRevReturnT_congr (i : String) :
    ∀ fuel lo hi,
      denoteForLoopRevReturnT bt fuel i lo hi b' = denoteForLoopRevReturnT bt fuel i lo hi b := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoopRevReturnT; simp
  | succ n ih =>
    intro lo hi
    unfold denoteForLoopRevReturnT
    simp only [hb, Nat.add_sub_cancel, ih]

/-- The `while` loop over bodies with equal readings. -/
theorem denoteWhileT_congr (c : ImpExpr) :
    ∀ fuel, denoteWhileT bt fuel c b' = denoteWhileT bt fuel c b := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileT; simp
  | succ n ih =>
    unfold denoteWhileT
    simp only [hb, Nat.add_sub_cancel, ih]

/-- The `while` loop with a return over bodies with equal readings. -/
theorem denoteWhileReturnT_congr (c : ImpExpr) :
    ∀ fuel, denoteWhileReturnT bt fuel c b' = denoteWhileReturnT bt fuel c b := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileReturnT; simp
  | succ n ih =>
    unfold denoteWhileReturnT
    simp only [hb, Nat.add_sub_cancel, ih]

end Loops

/-! ## The rewriting keeps the call tree -/

/-- The reading of the unit value is a leaf. -/
theorem denoteT_unitVal_run (bt : TreeTable E) (fuel : Nat) (s : Env) :
    denoteT bt fuel .unitVal s = .ret (.val .unit, s) := by
  rw [denoteT]; rfl

/-- **`bindInto` keeps the call tree**: the reading of `bindInto x v k` is that of
    `let x = v; k`, at every tree table and fuel. -/
theorem denoteT_bindInto (bt : TreeTable E) (fuel : Nat) (x : String) (v k : ImpExpr) :
    denoteT bt fuel (bindInto x v k) = denoteT bt fuel (.letBind x v k) := by
  fun_induction bindInto x v k with
  | case1 x c t f k iht ihf =>
    funext env
    rw [denoteT_seq_run, denoteT_ifThenElse_run, denoteT_letBind_run', denoteT_ifThenElse_run,
      bind_assoc, bind_assoc]
    congr 1
    funext p
    rcases p with ⟨o, e1⟩
    rcases o with v | _ | _ | _ | _
    · cases v with
      | bool bb =>
        cases bb
        all_goals
          dsimp only
          simp only [ihf, iht]
          rw [denoteT_letBind_run', bind_assoc]
          congr 1
          funext q
          rcases q with ⟨o, e2⟩
          rcases o with w | _ | _ | _ | _
          · cases w <;> first | rfl | (dsimp only; rw [denoteT_unitVal_run]; rfl)
          all_goals rfl
      | _ => rfl
    all_goals rfl
  | case2 x a b k ih =>
    funext env
    rw [denoteT_seq_run, denoteT_letBind_run', denoteT_seq_run, bind_assoc]
    congr 1
    funext p
    rcases p with ⟨o, e1⟩
    rcases o with u | _ | _ | _ | _
    · cases u <;> first | rfl | (dsimp only; simp only [ih]; rw [denoteT_letBind_run'])
    all_goals rfl
  | case3 x y w b k ihb ihw =>
    funext env
    rw [ihw, denoteT_letBind_run', denoteT_letBind_run', denoteT_letBind_run', bind_assoc]
    congr 1
    funext p
    rcases p with ⟨o, e1⟩
    rcases o with u | _ | _ | _ | _
    · cases u <;> first | rfl | (dsimp only; simp only [ihb]; rw [denoteT_letBind_run'])
    all_goals rfl
  | case4 => rfl

/-- **`letsInto` keeps the call tree**: the reading of `letsInto e` is that of `e`, at every
    tree table and fuel. -/
theorem denoteT_letsInto (bt : TreeTable E) (e : ImpExpr) :
    ∀ fuel, denoteT bt fuel (letsInto e) = denoteT bt fuel e := by
  fun_induction letsInto e with
  | case1 x v k ihv ihk =>
    intro fuel
    rw [denoteT_bindInto]
    simp only [denoteT, ihv, ihk]
  | case2 a b iha ihb => intro fuel; simp only [denoteT, iha, ihb]
  | case3 c t f iht ihf => intro fuel; simp only [denoteT, iht, ihf]
  | case4 i lo hi b ih => intro fuel; simp only [denoteT, denoteForLoopT_congr ih]
  | case5 i lo hi b ih => intro fuel; simp only [denoteT, denoteForLoopRevT_congr ih]
  | case6 i lo hi b ih => intro fuel; simp only [denoteT, denoteForLoopReturnT_congr ih]
  | case7 i lo hi b ih => intro fuel; simp only [denoteT, denoteForLoopRevReturnT_congr ih]
  | case8 c b ih => intro fuel; simp only [denoteT, denoteWhileT_congr ih]
  | case9 c b ih => intro fuel; simp only [denoteT, denoteWhileReturnT_congr ih]
  | case10 => intro fuel; rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeLetsInto
