/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.AST

/-!
# Feature Predicates

Inductive predicates on `ImpExpr` that characterize which imperative
features have been eliminated. Each verified compiler phase establishes
one predicate as a post-condition and may require others as pre-conditions.

Follows the `IsDeterministic` pattern from `Deep/Deterministic.lean`.
-/

@[expose] public section

namespace CatCrypt.Hax

/-! ## NoReferences -/

/-- An expression contains no `borrow` or `deref` nodes. -/
inductive NoReferences : ImpExpr → Prop where
  | lit {v} : NoReferences (.lit v)
  | var {n} : NoReferences (.var n)
  | letBind {n val body} : NoReferences val → NoReferences body →
      NoReferences (.letBind n val body)
  | lam {ps body} : NoReferences body → NoReferences (.lam ps body)
  | app {f args} : (∀ a, a ∈ args → NoReferences a) →
      NoReferences (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoReferences a) →
      NoReferences (.tuple elems)
  | proj {e i} : NoReferences e → NoReferences (.proj e i)
  | ifThenElse {c t e} : NoReferences c → NoReferences t → NoReferences e →
      NoReferences (.ifThenElse c t e)
  | match_ {scrut arms} : NoReferences scrut →
      (∀ pa, pa ∈ arms → NoReferences pa.2) →
      NoReferences (.match_ scrut arms)
  | unitVal : NoReferences .unitVal
  | seq {e1 e2} : NoReferences e1 → NoReferences e2 →
      NoReferences (.seq e1 e2)
  | assign {n rhs} : NoReferences rhs →
      NoReferences (.assign n rhs)
  | forLoop {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forLoop v lo hi body)
  | forLoopRev {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forLoopRev v lo hi body)
  | whileLoop {c body} : NoReferences c → NoReferences body →
      NoReferences (.whileLoop c body)
  | break_none : NoReferences (.break_ none)
  | break_some {e} : NoReferences e → NoReferences (.break_ (some e))
  | continue_ : NoReferences .continue_
  | earlyReturn {e} : NoReferences e →
      NoReferences (.earlyReturn e)
  | questionMark {e} : NoReferences e →
      NoReferences (.questionMark e)
  | forFold {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forFold v lo hi body)
  | forFoldRev {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forFoldRev v lo hi body)
  | whileFold {c body} : NoReferences c → NoReferences body →
      NoReferences (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forFoldReturn v lo hi body)
  | forFoldRevReturn {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forFoldRevReturn v lo hi body)
  | whileFoldReturn {c body} : NoReferences c → NoReferences body →
      NoReferences (.whileFoldReturn c body)
  | cfBreak {e} : NoReferences e → NoReferences (.cfBreak e)
  | cfContinue {e} : NoReferences e → NoReferences (.cfContinue e)
  | cfBreakContinue {e} : NoReferences e → NoReferences (.cfBreakContinue e)

theorem NoReferences.not_borrow {e : ImpExpr} : ¬NoReferences (.borrow e) := by
  intro h; cases h
theorem NoReferences.not_deref {e : ImpExpr} : ¬NoReferences (.deref e) := by
  intro h; cases h

/-! ## NoMutation -/

/-- An expression contains no `assign` nodes. -/
inductive NoMutation : ImpExpr → Prop where
  | lit {v} : NoMutation (.lit v)
  | var {n} : NoMutation (.var n)
  | letBind {n val body} : NoMutation val → NoMutation body →
      NoMutation (.letBind n val body)
  | lam {ps body} : NoMutation body → NoMutation (.lam ps body)
  | app {f args} : (∀ a, a ∈ args → NoMutation a) →
      NoMutation (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoMutation a) →
      NoMutation (.tuple elems)
  | proj {e i} : NoMutation e → NoMutation (.proj e i)
  | ifThenElse {c t e} : NoMutation c → NoMutation t → NoMutation e →
      NoMutation (.ifThenElse c t e)
  | match_ {scrut arms} : NoMutation scrut →
      (∀ pa, pa ∈ arms → NoMutation pa.2) →
      NoMutation (.match_ scrut arms)
  | unitVal : NoMutation .unitVal
  | seq {e1 e2} : NoMutation e1 → NoMutation e2 →
      NoMutation (.seq e1 e2)
  | borrow {e} : NoMutation e → NoMutation (.borrow e)
  | deref {e} : NoMutation e → NoMutation (.deref e)
  | forLoop {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forLoop v lo hi body)
  | forLoopRev {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forLoopRev v lo hi body)
  | whileLoop {c body} : NoMutation c → NoMutation body →
      NoMutation (.whileLoop c body)
  | break_none : NoMutation (.break_ none)
  | break_some {e} : NoMutation e → NoMutation (.break_ (some e))
  | continue_ : NoMutation .continue_
  | earlyReturn {e} : NoMutation e →
      NoMutation (.earlyReturn e)
  | questionMark {e} : NoMutation e →
      NoMutation (.questionMark e)
  | forFold {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forFold v lo hi body)
  | forFoldRev {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forFoldRev v lo hi body)
  | whileFold {c body} : NoMutation c → NoMutation body →
      NoMutation (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forFoldReturn v lo hi body)
  | forFoldRevReturn {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forFoldRevReturn v lo hi body)
  | whileFoldReturn {c body} : NoMutation c → NoMutation body →
      NoMutation (.whileFoldReturn c body)
  | cfBreak {e} : NoMutation e → NoMutation (.cfBreak e)
  | cfContinue {e} : NoMutation e → NoMutation (.cfContinue e)
  | cfBreakContinue {e} : NoMutation e → NoMutation (.cfBreakContinue e)

theorem NoMutation.not_assign {n : String} {rhs : ImpExpr} :
    ¬NoMutation (.assign n rhs) := by intro h; cases h

/-! ## NoLoops -/

/-- An expression contains no `forLoop`, `whileLoop`, `break_`, or `continue_`. -/
inductive NoLoops : ImpExpr → Prop where
  | lit {v} : NoLoops (.lit v)
  | var {n} : NoLoops (.var n)
  | letBind {n val body} : NoLoops val → NoLoops body →
      NoLoops (.letBind n val body)
  | lam {ps body} : NoLoops body → NoLoops (.lam ps body)
  | app {f args} : (∀ a, a ∈ args → NoLoops a) →
      NoLoops (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoLoops a) →
      NoLoops (.tuple elems)
  | proj {e i} : NoLoops e → NoLoops (.proj e i)
  | ifThenElse {c t e} : NoLoops c → NoLoops t → NoLoops e →
      NoLoops (.ifThenElse c t e)
  | match_ {scrut arms} : NoLoops scrut →
      (∀ pa, pa ∈ arms → NoLoops pa.2) →
      NoLoops (.match_ scrut arms)
  | unitVal : NoLoops .unitVal
  | seq {e1 e2} : NoLoops e1 → NoLoops e2 →
      NoLoops (.seq e1 e2)
  | borrow {e} : NoLoops e → NoLoops (.borrow e)
  | deref {e} : NoLoops e → NoLoops (.deref e)
  | assign {n rhs} : NoLoops rhs → NoLoops (.assign n rhs)
  | earlyReturn {e} : NoLoops e → NoLoops (.earlyReturn e)
  | questionMark {e} : NoLoops e → NoLoops (.questionMark e)
  | forFold {v lo hi body} : NoLoops lo → NoLoops hi → NoLoops body →
      NoLoops (.forFold v lo hi body)
  | forFoldRev {v lo hi body} : NoLoops lo → NoLoops hi → NoLoops body →
      NoLoops (.forFoldRev v lo hi body)
  | whileFold {c body} : NoLoops c → NoLoops body →
      NoLoops (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoLoops lo → NoLoops hi → NoLoops body →
      NoLoops (.forFoldReturn v lo hi body)
  | forFoldRevReturn {v lo hi body} : NoLoops lo → NoLoops hi → NoLoops body →
      NoLoops (.forFoldRevReturn v lo hi body)
  | whileFoldReturn {c body} : NoLoops c → NoLoops body →
      NoLoops (.whileFoldReturn c body)
  | cfBreak {e} : NoLoops e → NoLoops (.cfBreak e)
  | cfContinue {e} : NoLoops e → NoLoops (.cfContinue e)
  | cfBreakContinue {e} : NoLoops e → NoLoops (.cfBreakContinue e)

theorem NoLoops.not_forLoop {v : String} {lo hi body : ImpExpr} :
    ¬NoLoops (.forLoop v lo hi body) := by intro h; cases h
theorem NoLoops.not_forLoopRev {v : String} {lo hi body : ImpExpr} :
    ¬NoLoops (.forLoopRev v lo hi body) := by intro h; cases h
theorem NoLoops.not_whileLoop {c body : ImpExpr} :
    ¬NoLoops (.whileLoop c body) := by intro h; cases h
theorem NoLoops.not_break {oe : Option ImpExpr} :
    ¬NoLoops (.break_ oe) := by intro h; cases h
theorem NoLoops.not_continue :
    ¬NoLoops (.continue_) := by intro h; cases h

/-! ## NoEarlyExit -/

/-- An expression contains no `earlyReturn` or `questionMark`. -/
inductive NoEarlyExit : ImpExpr → Prop where
  | lit {v} : NoEarlyExit (.lit v)
  | var {n} : NoEarlyExit (.var n)
  | letBind {n val body} : NoEarlyExit val → NoEarlyExit body →
      NoEarlyExit (.letBind n val body)
  | lam {ps body} : NoEarlyExit body → NoEarlyExit (.lam ps body)
  | app {f args} : (∀ a, a ∈ args → NoEarlyExit a) →
      NoEarlyExit (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoEarlyExit a) →
      NoEarlyExit (.tuple elems)
  | proj {e i} : NoEarlyExit e → NoEarlyExit (.proj e i)
  | ifThenElse {c t e} : NoEarlyExit c → NoEarlyExit t → NoEarlyExit e →
      NoEarlyExit (.ifThenElse c t e)
  | match_ {scrut arms} : NoEarlyExit scrut →
      (∀ pa, pa ∈ arms → NoEarlyExit pa.2) →
      NoEarlyExit (.match_ scrut arms)
  | unitVal : NoEarlyExit .unitVal
  | seq {e1 e2} : NoEarlyExit e1 → NoEarlyExit e2 →
      NoEarlyExit (.seq e1 e2)
  | borrow {e} : NoEarlyExit e → NoEarlyExit (.borrow e)
  | deref {e} : NoEarlyExit e → NoEarlyExit (.deref e)
  | assign {n rhs} : NoEarlyExit rhs → NoEarlyExit (.assign n rhs)
  | forLoop {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forLoop v lo hi body)
  | forLoopRev {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forLoopRev v lo hi body)
  | whileLoop {c body} : NoEarlyExit c → NoEarlyExit body →
      NoEarlyExit (.whileLoop c body)
  | break_none : NoEarlyExit (.break_ none)
  | break_some {e} : NoEarlyExit e → NoEarlyExit (.break_ (some e))
  | continue_ : NoEarlyExit .continue_
  | forFold {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forFold v lo hi body)
  | forFoldRev {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forFoldRev v lo hi body)
  | whileFold {c body} : NoEarlyExit c → NoEarlyExit body →
      NoEarlyExit (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forFoldReturn v lo hi body)
  | forFoldRevReturn {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forFoldRevReturn v lo hi body)
  | whileFoldReturn {c body} : NoEarlyExit c → NoEarlyExit body →
      NoEarlyExit (.whileFoldReturn c body)
  | cfBreak {e} : NoEarlyExit e → NoEarlyExit (.cfBreak e)
  | cfContinue {e} : NoEarlyExit e → NoEarlyExit (.cfContinue e)
  | cfBreakContinue {e} : NoEarlyExit e → NoEarlyExit (.cfBreakContinue e)

theorem NoEarlyExit.not_earlyReturn {e : ImpExpr} :
    ¬NoEarlyExit (.earlyReturn e) := by intro h; cases h
theorem NoEarlyExit.not_questionMark {e : ImpExpr} :
    ¬NoEarlyExit (.questionMark e) := by intro h; cases h

/-! ## Fully Functional -/

/-- An expression is fully functional: all imperative features eliminated. -/
def FullyFunctional (e : ImpExpr) : Prop :=
  NoReferences e ∧ NoMutation e ∧ NoLoops e ∧ NoEarlyExit e

end CatCrypt.Hax
