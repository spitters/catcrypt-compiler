/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Std.Data.String.ToNat
public meta import HaxLean.AST
public import HaxLean.AST
public import HaxLean.Value
public meta import CatCrypt.Crypto.Hax.ImpExprVar
public import CatCrypt.Crypto.Hax.ImpExprVar

/-!
# The total A-normaliser: definitions and counter lemmas

`aNormalizeTotal` is a total A-normaliser for hax `ImpExpr`: the tail pass `bindTails`
followed by argument, condition and loop-bound hoisting. It is defined by structural
recursion on `ImpExpr`, with the fresh-name counter threaded as an explicit `Nat`.

This module holds the syntactic part of the normaliser: the passes, the fresh-name scheme
`__anorm_N`, the environment relation `EnvEqOff` and the monotonicity of the counter. The
predicate `isVar` comes from `ImpExprVar.lean`.

## Main definitions

* `prependBindings`, `splitLetBinds` — wrapping a body in `letBind`s and peeling the
  leading `letBind`s of an expression.
* `retName`, `isTailBindable`, `bindTails` — the tail pass, which binds a call or a
  literal in tail position to the `"_ret"` slot.
* `anormName`, `hoistAt`, `hoistsBound`, `hoistsLo`, `floatLet`, `bindRhs` — the fresh names, the
  loop bounds the hoisting pass binds, and the binding of a hoisted `letBind` right-hand
  side.
* `aNormTBody`, `aNormTArgs`, `aNormTArms` — the hoisting pass.
* `aNormalizeTotal`, `aNormalizeTotalCount` — the composed pass and the number of fresh
  names it mints.
* `AnormBelow`, `EnvEqOff` — the first `K` fresh names, and agreement of two
  environments off a set of names.

## Main results

* `anormName_inj` — distinct indices give distinct fresh names.
* `aNormTBody_le` — the fresh-name counter never decreases.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat Value Env)

/-! ## §1  Bindings and the tail pass -/

/-- Wrap a `body` ImpExpr with a list of letBind prefixes (outermost first
    in the list, so the first element binds the outermost scope). -/
def prependBindings (bs : List (String × ImpExpr)) (body : ImpExpr) : ImpExpr :=
  bs.foldr (fun (kv : String × ImpExpr) (acc : ImpExpr) =>
    ImpExpr.letBind kv.1 kv.2 acc) body

/-- Peel off leading `.letBind` constructors of an `ImpExpr`, returning the
    list of `(name, rhs)` pairs (outermost first) and the inner non-letBind
    core.  This is the inverse of `prependBindings`: for any input `e`,
    `prependBindings (splitLetBinds e).1 (splitLetBinds e).2 = e`. -/
def splitLetBinds : ImpExpr → List (String × ImpExpr) × ImpExpr
  | .letBind n v b =>
      let (bs, core) := splitLetBinds b
      ((n, v) :: bs, core)
  | e => ([], e)

/-- Fresh tail-slot name introduced by `bindTails`. -/
def retName : String := "_ret"

/-- A tail expression is *bindable* if `haxToLowCT` has a `letBind`-RHS
    arm for it (after argument hoisting): any `.app`, and the literal
    forms the scalar-set arms accept (nonneg `.int`, `.uintLit`,
    `.bool`).  `.var` and all-`var` `.tuple` tails are accepted by the
    translator directly and stay as they are; `.sintLit` has no
    `letBind` arm, so rewriting it would not help. -/
def isTailBindable : ImpExpr → Bool
  | .app _ _            => true
  | .lit (.int n)       => decide (0 ≤ n)
  | .lit (.uintLit _ _) => true
  | .lit (.bool _)      => true
  | _                   => false

/-- Rewrite bindable value-returning tails to
    `.letBind retName e (.var retName)`, recursing through tail
    positions only.  Idempotent: the rewritten tail is `.var retName`,
    which is not bindable. -/
def bindTails : ImpExpr → ImpExpr
  | .letBind n v b    => .letBind n v (bindTails b)
  | .seq a b          => .seq a (bindTails b)
  | .ifThenElse c t e => .ifThenElse c (bindTails t) (bindTails e)
  | e => if isTailBindable e then .letBind retName e (.var retName) else e

/-! ## §2  The normaliser -/

/-- The `j`-th fresh name, `__anorm_j`. -/
def anormName (j : Nat) : String := s!"__anorm_{j}"

theorem prependBindings_nil (body : ImpExpr) : prependBindings [] body = body := rfl

theorem prependBindings_cons (n : String) (v : ImpExpr) (bs : List (String × ImpExpr))
    (body : ImpExpr) :
    prependBindings ((n, v) :: bs) body = .letBind n v (prependBindings bs body) := rfl

theorem splitLetBinds_letBind (n : String) (v b : ImpExpr) :
    splitLetBinds (.letBind n v b) = ((n, v) :: (splitLetBinds b).1, (splitLetBinds b).2) := rfl

/-- Bind an already-normalised expression `e'` to the fresh name with index `k`:
    its leading `letBind`s become outer bindings and its core is bound to
    `anormName k`. -/
def hoistAt (e' : ImpExpr) (k : Nat) : List (String × ImpExpr) × ImpExpr :=
  ((splitLetBinds e').1 ++ [(anormName k, (splitLetBinds e').2)], .var (anormName k))

/-- A counted-loop bound that the hoisting pass binds to a fresh name: a call of
    a function other than the bound arithmetic `Add`, `Sub`, `Mul` and `min`. -/
def hoistsBound : ImpExpr → Bool
  | .app f _ => !(f == "Add" || f == "Sub" || f == "Mul" || f == "min")
  | _ => false

/-- A counted-loop lower bound `lo` that the hoisting pass binds to a fresh name, given the
    upper bound `hi`: every `lo` other than a literal or a variable, and a variable when
    `hoistsBound hi` holds, so that the lower bound is read before the upper bound runs. -/
def hoistsLo (lo hi : ImpExpr) : Bool :=
  match lo with
  | .lit _ => false
  | .var _ => hoistsBound hi
  | _ => true

/-- `let x = r; body` with the leading `letBind`s of `r` floated outwards. -/
def floatLet (x : String) (r body : ImpExpr) : ImpExpr :=
  prependBindings (splitLetBinds r).1 (.letBind x (splitLetBinds r).2 body)

/-- The binding of `x` to a hoisted right-hand side `r` before `body`.  A
    conditional `ifThenElse c t e` becomes the conditional whose branches bind
    `x` to the value of `t` and of `e` and return `unitVal`, followed by `body`;
    any other `r` is bound by `letBind x r body`. -/
def bindRhs (x : String) : ImpExpr → ImpExpr → ImpExpr
  | .ifThenElse c t e, body =>
      .seq (.ifThenElse c (floatLet x t .unitVal) (floatLet x e .unitVal)) body
  | r, body => .letBind x r body

mutual

/-- The hoisting pass in body position, from counter `k`; returns the normal
    form and the next counter.  Every non-`var` call or tuple argument and every
    non-`var` `ifThenElse` condition is bound to a fresh name, and so are the
    lower bound of a counted loop (`forLoop`, `forLoopRev`, `forFold`, `forFoldRev`) when
    `hoistsLo` holds of it and its upper bound when `hoistsBound` holds of it, the lower
    bound first.  The
    leading `letBind`s of a `letBind` right-hand side are floated outwards, and
    a right-hand side that is a conditional is bound in each branch
    (`bindRhs`). -/
def aNormTBody : ImpExpr → Nat → ImpExpr × Nat
  | .var n, k => (.var n, k)
  | .typeAscription e _, k => aNormTBody e k
  | .lit l, k => (.lit l, k)
  | .unitVal, k => (.unitVal, k)
  | .letBind name rhs body, k =>
      let r := aNormTBody rhs k
      let b := aNormTBody body r.2
      (prependBindings (splitLetBinds r.1).1 (bindRhs name (splitLetBinds r.1).2 b.1), b.2)
  | .lam ps body, k =>
      let b := aNormTBody body k
      (.lam ps b.1, b.2)
  | .app f args, k =>
      let a := aNormTArgs args k
      (prependBindings a.1 (.app f a.2.1), a.2.2)
  | .tuple elems, k =>
      let a := aNormTArgs elems k
      (prependBindings a.1 (.tuple a.2.1), a.2.2)
  | .proj e i, k =>
      let r := aNormTBody e k
      (.proj r.1 i, r.2)
  | .ifThenElse c t e, k =>
      let cr : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if isVar c then (([], c), k)
        else (hoistAt (aNormTBody c k).1 (aNormTBody c k).2, (aNormTBody c k).2 + 1)
      let t' := aNormTBody t cr.2
      let e' := aNormTBody e t'.2
      (prependBindings cr.1.1 (.ifThenElse cr.1.2 t'.1 e'.1), e'.2)
  | .match_ scrut arms, k =>
      let s := aNormTBody scrut k
      let a := aNormTArms arms s.2
      (.match_ s.1 a.1, a.2)
  | .seq e1 e2, k =>
      let a := aNormTBody e1 k
      let b := aNormTBody e2 a.2
      (.seq a.1 b.1, b.2)
  | .borrow e, k => let r := aNormTBody e k; (.borrow r.1, r.2)
  | .deref e, k => let r := aNormTBody e k; (.deref r.1, r.2)
  | .assign n rhs, k => let r := aNormTBody rhs k; (.assign n r.1, r.2)
  | .forLoop v lo hi body, k =>
      let l : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if hoistsLo lo hi then
          (hoistAt (aNormTBody lo k).1 (aNormTBody lo k).2, (aNormTBody lo k).2 + 1)
        else (([], lo), k)
      let h : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if hoistsBound hi then
          (hoistAt (aNormTBody hi l.2).1 (aNormTBody hi l.2).2, (aNormTBody hi l.2).2 + 1)
        else (([], hi), l.2)
      let r := aNormTBody body h.2
      (prependBindings (l.1.1 ++ h.1.1) (.forLoop v l.1.2 h.1.2 r.1), r.2)
  | .forLoopRev v lo hi body, k =>
      let l : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if hoistsLo lo hi then
          (hoistAt (aNormTBody lo k).1 (aNormTBody lo k).2, (aNormTBody lo k).2 + 1)
        else (([], lo), k)
      let h : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if hoistsBound hi then
          (hoistAt (aNormTBody hi l.2).1 (aNormTBody hi l.2).2, (aNormTBody hi l.2).2 + 1)
        else (([], hi), l.2)
      let r := aNormTBody body h.2
      (prependBindings (l.1.1 ++ h.1.1) (.forLoopRev v l.1.2 h.1.2 r.1), r.2)
  | .whileLoop c body, k =>
      let a := aNormTBody c k
      let b := aNormTBody body a.2
      (.whileLoop a.1 b.1, b.2)
  | .break_ none, k => (.break_ none, k)
  | .break_ (some e), k => let r := aNormTBody e k; (.break_ (some r.1), r.2)
  | .continue_, k => (.continue_, k)
  | .earlyReturn e, k => let r := aNormTBody e k; (.earlyReturn r.1, r.2)
  | .questionMark e, k => let r := aNormTBody e k; (.questionMark r.1, r.2)
  | .forFold v lo hi body, k =>
      let l : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if hoistsLo lo hi then
          (hoistAt (aNormTBody lo k).1 (aNormTBody lo k).2, (aNormTBody lo k).2 + 1)
        else (([], lo), k)
      let h : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if hoistsBound hi then
          (hoistAt (aNormTBody hi l.2).1 (aNormTBody hi l.2).2, (aNormTBody hi l.2).2 + 1)
        else (([], hi), l.2)
      let r := aNormTBody body h.2
      (prependBindings (l.1.1 ++ h.1.1) (.forFold v l.1.2 h.1.2 r.1), r.2)
  | .forFoldRev v lo hi body, k =>
      let l : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if hoistsLo lo hi then
          (hoistAt (aNormTBody lo k).1 (aNormTBody lo k).2, (aNormTBody lo k).2 + 1)
        else (([], lo), k)
      let h : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if hoistsBound hi then
          (hoistAt (aNormTBody hi l.2).1 (aNormTBody hi l.2).2, (aNormTBody hi l.2).2 + 1)
        else (([], hi), l.2)
      let r := aNormTBody body h.2
      (prependBindings (l.1.1 ++ h.1.1) (.forFoldRev v l.1.2 h.1.2 r.1), r.2)
  | .whileFold c body, k =>
      let a := aNormTBody c k
      let b := aNormTBody body a.2
      (.whileFold a.1 b.1, b.2)
  | .forFoldReturn v lo hi body, k =>
      let r := aNormTBody body k; (.forFoldReturn v lo hi r.1, r.2)
  | .forFoldRevReturn v lo hi body, k =>
      let r := aNormTBody body k; (.forFoldRevReturn v lo hi r.1, r.2)
  | .whileFoldReturn c body, k =>
      let a := aNormTBody c k
      let b := aNormTBody body a.2
      (.whileFoldReturn a.1 b.1, b.2)
  | .cfBreak e, k => let r := aNormTBody e k; (.cfBreak r.1, r.2)
  | .cfContinue e, k => let r := aNormTBody e k; (.cfContinue r.1, r.2)
  | .cfBreakContinue e, k => let r := aNormTBody e k; (.cfBreakContinue r.1, r.2)

/-- The hoisting pass over an argument list, from counter `k`: the hoisted
    bindings (left to right), the argument list with every non-`var` argument
    replaced by its fresh name, and the next counter. -/
def aNormTArgs : List ImpExpr → Nat → List (String × ImpExpr) × List ImpExpr × Nat
  | [], k => ([], [], k)
  | a :: rest, k =>
      let h : (List (String × ImpExpr) × ImpExpr) × Nat :=
        if isVar a then (([], a), k)
        else (hoistAt (aNormTBody a k).1 (aNormTBody a k).2, (aNormTBody a k).2 + 1)
      let t := aNormTArgs rest h.2
      (h.1.1 ++ t.1, h.1.2 :: t.2.1, t.2.2)

/-- The hoisting pass over match arms: each arm body in turn. -/
def aNormTArms : List (ImpPat × ImpExpr) → Nat → List (ImpPat × ImpExpr) × Nat
  | [], k => ([], k)
  | (p, e) :: rest, k =>
      let r := aNormTBody e k
      let t := aNormTArms rest r.2
      ((p, r.1) :: t.1, t.2)

end

/-- The hoisting pass on a counted loop built by `mk` (one of `forLoop`, `forLoopRev`,
    `forFold`, `forFoldRev`), from counter `k`: the lower bound bound to a fresh name when
    `hoistsLo` holds, then the upper bound when `hoistsBound` holds, then the body. -/
def loopNorm (mk : String → ImpExpr → ImpExpr → ImpExpr → ImpExpr) (v : String)
    (lo hi body : ImpExpr) (k : Nat) : ImpExpr × Nat :=
  let l : (List (String × ImpExpr) × ImpExpr) × Nat :=
    if hoistsLo lo hi then
      (hoistAt (aNormTBody lo k).1 (aNormTBody lo k).2, (aNormTBody lo k).2 + 1)
    else (([], lo), k)
  let h : (List (String × ImpExpr) × ImpExpr) × Nat :=
    if hoistsBound hi then
      (hoistAt (aNormTBody hi l.2).1 (aNormTBody hi l.2).2, (aNormTBody hi l.2).2 + 1)
    else (([], hi), l.2)
  let r := aNormTBody body h.2
  (prependBindings (l.1.1 ++ h.1.1) (mk v l.1.2 h.1.2 r.1), r.2)

theorem aNormTBody_forLoop_loopNorm (v : String) (lo hi body : ImpExpr) (k : Nat) :
    aNormTBody (.forLoop v lo hi body) k = loopNorm .forLoop v lo hi body k := by
  rw [aNormTBody]; rfl

theorem aNormTBody_forLoopRev_loopNorm (v : String) (lo hi body : ImpExpr) (k : Nat) :
    aNormTBody (.forLoopRev v lo hi body) k = loopNorm .forLoopRev v lo hi body k := by
  rw [aNormTBody]; rfl

theorem aNormTBody_forFold_loopNorm (v : String) (lo hi body : ImpExpr) (k : Nat) :
    aNormTBody (.forFold v lo hi body) k = loopNorm .forFold v lo hi body k := by
  rw [aNormTBody]; rfl

theorem aNormTBody_forFoldRev_loopNorm (v : String) (lo hi body : ImpExpr) (k : Nat) :
    aNormTBody (.forFoldRev v lo hi body) k = loopNorm .forFoldRev v lo hi body k := by
  rw [aNormTBody]; rfl

/-- The total A-normaliser: tail binding, then hoisting from counter `0`. -/
def aNormalizeTotal (e : ImpExpr) : ImpExpr :=
  (aNormTBody (bindTails e) 0).1

/-- The number of fresh names `aNormalizeTotal e` mints. -/
def aNormalizeTotalCount (e : ImpExpr) : Nat :=
  (aNormTBody (bindTails e) 0).2

/-! ## §3  Fresh names and the environment relation -/

/-- `n` is one of the first `K` fresh names. -/
def AnormBelow (K : Nat) (n : String) : Prop := ∃ j, j < K ∧ n = anormName j

/-- Two environments agree on every name outside `F`. -/
def EnvEqOff (F : String → Prop) (env₁ env₂ : Env) : Prop :=
  ∀ n, ¬ F n → env₁ n = env₂ n

/-- The fresh names are pairwise distinct: `anormName a = anormName b` implies `a = b`. -/
theorem anormName_inj {a b : Nat} (h : anormName a = anormName b) : a = b := by
  simp only [anormName] at h
  simpa [Nat.repr_inj] using h

theorem EnvEqOff.extend {F : String → Prop} {env₁ env₂ : Env} (h : EnvEqOff F env₁ env₂)
    (n : String) (v : Value) : EnvEqOff F (env₁.extend n v) (env₂.extend n v) := by
  intro m hm
  by_cases hmn : m = n
  · subst hmn; simp [Env.extend_same]
  · rw [Env.extend_other _ _ _ _ hmn, Env.extend_other _ _ _ _ hmn]; exact h m hm

theorem EnvEqOff.extend_right {F : String → Prop} {env₁ env₂ : Env}
    (h : EnvEqOff F env₁ env₂) {n : String} (hn : F n) (v : Value) :
    EnvEqOff F env₁ (env₂.extend n v) := by
  intro m hm
  have hmn : m ≠ n := fun h' => hm (h' ▸ hn)
  rw [Env.extend_other _ _ _ _ hmn]; exact h m hm

theorem EnvEqOff.trans {F G : String → Prop} {env₁ env₂ env₃ : Env}
    (h₁ : EnvEqOff F env₁ env₂) (h₂ : EnvEqOff G env₂ env₃) :
    EnvEqOff (fun n => F n ∨ G n) env₁ env₃ := by
  intro m hm
  simp only [not_or] at hm
  exact (h₁ m hm.1).trans (h₂ m hm.2)

theorem isVar_eq_true {e : ImpExpr} (h : isVar e = true) : ∃ n, e = .var n := by
  cases e <;> simp_all [isVar]

/-! ## §4  The counter is monotone -/

theorem aNormTArgs_le_of (args : List ImpExpr)
    (ih : ∀ a ∈ args, ∀ k, k ≤ (aNormTBody a k).2) :
    ∀ k, k ≤ (aNormTArgs args k).2.2 := by
  induction args with
  | nil => intro k; simp [aNormTArgs]
  | cons a rest ihr =>
    intro k
    have ha := ih a (List.mem_cons_self ..)
    have hr := ihr (fun b hb => ih b (List.mem_cons_of_mem _ hb))
    simp only [aNormTArgs]
    split
    · exact hr k
    · exact Nat.le_trans (Nat.le_trans (ha k) (Nat.le_succ _)) (hr _)

theorem aNormTArms_le_of (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa ∈ arms, ∀ k, k ≤ (aNormTBody pa.2 k).2) :
    ∀ k, k ≤ (aNormTArms arms k).2 := by
  induction arms with
  | nil => intro k; simp [aNormTArms]
  | cons pa rest ihr =>
    intro k
    obtain ⟨p, e⟩ := pa
    have ha := ih (p, e) (List.mem_cons_self ..)
    have hr := ihr (fun b hb => ih b (List.mem_cons_of_mem _ hb))
    simp only [aNormTArms]
    exact Nat.le_trans (ha k) (hr _)

/-- The fresh-name counter never decreases. -/
theorem aNormTBody_le (e : ImpExpr) : ∀ k, k ≤ (aNormTBody e k).2 := by
  induction e using ImpExpr.ind
  case letBind n v b ihv ihb =>
    intro k; simp only [aNormTBody]; exact Nat.le_trans (ihv k) (ihb _)
  case app f args ih =>
    intro k; simp only [aNormTBody]; exact aNormTArgs_le_of args ih k
  case tuple es ih =>
    intro k; simp only [aNormTBody]; exact aNormTArgs_le_of es ih k
  case ifThenElse c t e ihc iht ihe =>
    intro k; simp only [aNormTBody]
    split
    · exact Nat.le_trans (iht k) (ihe _)
    · exact Nat.le_trans (Nat.le_trans (ihc k) (Nat.le_succ _))
        (Nat.le_trans (iht _) (ihe _))
  case match_ s arms ihs iha =>
    intro k; simp only [aNormTBody]; exact Nat.le_trans (ihs k) (aNormTArms_le_of arms iha _)
  case seq a b iha ihb =>
    intro k; simp only [aNormTBody]; exact Nat.le_trans (iha k) (ihb _)
  case whileLoop c b ihc ihb =>
    intro k; simp only [aNormTBody]; exact Nat.le_trans (ihc k) (ihb _)
  case whileFold c b ihc ihb =>
    intro k; simp only [aNormTBody]; exact Nat.le_trans (ihc k) (ihb _)
  case whileFoldReturn c b ihc ihb =>
    intro k; simp only [aNormTBody]; exact Nat.le_trans (ihc k) (ihb _)
  case forLoop _ lo hi b ihlo ihhi ih | forLoopRev _ lo hi b ihlo ihhi ih
  | forFold _ lo hi b ihlo ihhi ih | forFoldRev _ lo hi b ihlo ihhi ih =>
    intro k; simp only [aNormTBody]
    have := ihlo k
    have := ihhi k
    have := ihhi ((aNormTBody lo k).2 + 1)
    split <;> split <;> refine Nat.le_trans ?_ (ih _) <;> (try dsimp only) <;> omega
  case forFoldReturn _ _ _ _ _ _ ih => intro k; simp only [aNormTBody]; exact ih k
  case forFoldRevReturn _ _ _ _ _ _ ih => intro k; simp only [aNormTBody]; exact ih k
  all_goals first
    | (intro k; simp only [aNormTBody]; done)
    | (intro k; simp only [aNormTBody]; omega)
    | (rename_i ih; intro k; simp only [aNormTBody]; exact ih k)

end CatCrypt.Crypto.Hax
