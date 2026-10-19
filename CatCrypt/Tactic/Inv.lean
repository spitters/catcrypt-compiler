/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import CatCrypt.Tactic.InvAttr

/-!
# `inv`: inversion of executable functions in hypotheses

`inv h` inverts a hypothesis `h : f x = some y` (or a Boolean checker `c x = true`) over an
executable function. It unfolds the named definitions, splits every `match` and `if` in
`h`, rewrites `h` with the simp set `ir_inv`, and then destructs the hypotheses it
produced: conjunctions and existentials are split, equations are solved by unification
(substitution of a variable, constructor injectivity, and closure of a branch whose
equation relates two distinct constructors, such as `none = some _`). Hypotheses that were
in the context before the call and are not `h` are left unchanged.

This is the procedure of CompCert's `monadInv` and Jasmin's `t_xrbindP` for `Option`.

## Main definitions

* `inv [f, g] h`: invert `h` after unfolding `f` and `g`; the hypotheses it introduces
  are inaccessible.
* `inv [f, g] h with pat`: the same, with `h` destructed by the `rcases` pattern `pat`
  after the rewriting and splitting.
* `inv`: destruct every hypothesis of the context by the same procedure.
* `ir_inv`: the simp set of inversion lemmas; `code_layout`: the simp set of
  instruction-list layout lemmas.

## Main results

The `example`s at the end of the module are regression checks of the inversion shapes:
a bind chain, an `if`-guard returning `none`, a `match` with a `none` arm, a Boolean
conjunction, a pair result and an append layout.
-/

@[expose] public section

set_option autoImplicit false

attribute [ir_inv] Option.bind_eq_some_iff Option.map_eq_some_iff Option.bind_eq_bind
  Option.pure_def Option.bind_some Option.bind_none Option.map_some Option.map_none
  Option.some.injEq Prod.mk.injEq Option.ite_none_right_eq_some
  Option.ite_none_left_eq_some Bool.and_eq_true beq_iff_eq decide_eq_true_eq
  exists_prop and_true true_and

attribute [code_layout] List.append_assoc List.cons_append List.nil_append List.append_nil
  List.singleton_append List.length_append List.length_cons List.length_nil
  List.length_singleton List.mem_append List.mem_cons List.mem_singleton
  List.getElem_append_left List.getElem_append_right List.getElem_cons_zero
  List.getElem_cons_succ

namespace CatCrypt.Tactic

open Lean Meta Elab Tactic

/-- A hypothesis is destructed by `inv` when it is not in `old` and is the inverted
    hypothesis `hName` or carries an inaccessible name. With `all`, every hypothesis is
    destructed. -/
meta def invTarget (all : Bool) (old : Std.HashSet FVarId) (hName : Name) (d : LocalDecl) :
    Bool :=
  !d.isImplementationDetail &&
    (all || (!old.contains d.fvarId && (d.userName.hasMacroScopes || d.userName == hName)))

/-- Destruct the target hypotheses of `g`: split conjunctions and existentials, close the
    goal on `False`, and solve equations by unification (`cases` on `Eq`). An equation
    that unification does not solve is kept. -/
meta partial def invClean (all : Bool) (old : Std.HashSet FVarId) (hName : Name)
    (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    unless invTarget all old hName d do continue
    let ty := (← instantiateMVars d.type).cleanupAnnotations
    if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isFalse then
      let subgoals ← g.cases d.fvarId
      return (← subgoals.toList.mapM fun s => invClean all old hName s.mvarId).flatten
    if ty.isAppOfArity ``Eq 3 then
      if let some g' ← observing? (subst g d.fvarId) then
        return ← invClean all old hName g'
      if let some subgoals ← observing? (g.cases d.fvarId) then
        return (← subgoals.toList.mapM fun s => invClean all old hName s.mvarId).flatten
  return [g]

/-- Run `invClean` on every goal. -/
meta def invCleanGoals (all : Bool) (old : Std.HashSet FVarId) (hName : Name) :
    TacticM Unit := do
  let gs ← getGoals
  let mut out : List MVarId := []
  for g in gs do
    if ← g.isAssigned then continue
    out := out ++ (← invClean all old hName g)
  setGoals out

/-- `inv [f, g] h` inverts `h : e = some v` (or a checker `c = true`): it unfolds the
    definitions `f` and `g` in `h`, reduces matches on constructors, splits every `match`
    and `if` of `h`, rewrites with the simp set `ir_inv`, and destructs the conjunctions,
    existentials and equations this produces, closing contradictory branches.
    `inv [f, g] h with pat` destructs `h` by the `rcases` pattern `pat` after the
    rewriting. `inv` alone destructs every hypothesis. -/
syntax (name := invTac) "inv" (" [" ident,* "]")? (ppSpace colGt ident)?
  (" with " Lean.Parser.Tactic.rcasesPatLo)? : tactic

/-- The simp arguments of `inv`: the simp set `ir_inv` and the simproc `reduceCtorEq`,
    which rewrites an equation between distinct constructors to `False`. -/
meta def invSimpArgs : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  return #[← `(Lean.Parser.Tactic.simpLemma| ir_inv),
    ← `(Lean.Parser.Tactic.simpLemma| reduceCtorEq)]

elab_rules : tactic
  | `(tactic| inv $[[$fs,*]]? $h:ident $[with $pat]?) => do
    let fs : Array Ident := (fs.map (·.getElems)).getD #[]
    let ls ← invSimpArgs
    let old ← withMainContext do
      return (← getLCtx).foldl (init := ({} : Std.HashSet FVarId)) fun s d => s.insert d.fvarId
    for f in fs do
      evalTactic (← `(tactic| (try unfold $f:ident at $h:ident)))
    evalTactic (← `(tactic| (try dsimp only at $h:ident)))
    evalTactic (← `(tactic| repeat' split at $h:ident))
    evalTactic (← `(tactic| all_goals (try simp only [$ls,*] at $h:ident)))
    evalTactic (← `(tactic| repeat' (split at $h:ident <;> (try simp only [$ls,*] at $h:ident))))
    if let some pat := pat then
      evalTactic (← `(tactic| all_goals rcases $h:ident with $pat))
    invCleanGoals false old h.getId
  | `(tactic| inv) => do
    let ls ← invSimpArgs
    evalTactic (← `(tactic| (try simp only [$ls,*] at *)))
    invCleanGoals true {} .anonymous

end CatCrypt.Tactic

/-! ## Regression checks -/

namespace CatCrypt.Tactic.InvExamples

/-- A two-step `Option` computation. -/
def pairUp (x y : Option Nat) : Option (Nat × Nat) :=
  x.bind fun a => y.map fun b => (a, b)

/-- A guarded `Option` computation. -/
def guardLt (a b : Nat) : Option Nat :=
  if a < b then some (b - a) else none

/-- A recognizer with a `none` arm. -/
def headPos : List Nat → Option Nat
  | (k + 1) :: _ => some k
  | _ => none

/-- A Boolean checker of two conjuncts. -/
def bothLt (a b c : Nat) : Bool :=
  decide (a < b) && (b == c)

example (x y : Option Nat) (p : Nat × Nat) (h : pairUp x y = some p) :
    x = some p.1 ∧ y = some p.2 := by
  inv [pairUp] h
  exact ⟨rfl, rfl⟩

example (x y : Option Nat) (a b : Nat) (h : pairUp x y = some (a, b)) : x = some a := by
  inv [pairUp] h with ⟨a', ha, b', hb, rfl, rfl⟩
  exact ha

example (a b r : Nat) (h : guardLt a b = some r) : a < b ∧ r = b - a := by
  inv [guardLt] h
  exact ⟨‹_›, rfl⟩

example (l : List Nat) (k : Nat) (h : headPos l = some k) : k + 1 ∈ l := by
  inv [headPos] h
  exact List.mem_cons_self

example (a b c : Nat) (h : bothLt a b c = true) : a < c := by
  inv [bothLt] h
  assumption

example (a b c : Nat) (h : (some (a, b) : Option (Nat × Nat)) = some (c, 3)) :
    a = c ∧ b = 3 := by
  inv h
  exact ⟨rfl, rfl⟩

example (x : Option Nat) (h : (x.bind fun _ => (none : Option Nat)) = some 0) : False := by
  inv h

example (p q : Prop) (h : p ∧ (q ∧ True)) : q := by
  inv
  assumption

example (xs ys : List Nat) (a : Nat) :
    (xs ++ [a] ++ ys).length = xs.length + ys.length + 1 := by
  simp only [code_layout]
  omega

example (xs ys : List Nat) (a : Nat) (h : a ∈ xs ++ ys) : a ∈ ys ∨ a ∈ xs := by
  simp only [code_layout] at h
  exact h.symm

end CatCrypt.Tactic.InvExamples
