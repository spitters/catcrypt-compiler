/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick

/-!
# The reading commutes with substitution in the table

The reading `denoteT` at a tree table answers a call by the tree of the table. Substituting trees
for the events of the reading is the reading at the table whose trees are substituted: the
substitution is a morphism of the monads of call trees, and the reading is built from the monad
operations and the trees of the table only. So the call tree of a module, in which a call of a
function of the module runs the tree of its body, is the substitution of those trees for the call
events of a tree in which the call is an event.

## Main results

* `substT_bind`: substitution commutes with sequencing.
* `substS_denoteT`: the substituted reading is the reading at the substituted table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubstTable

open _root_.Hax
open _root_.Hax.InlineLocalClosures
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst (substT substT_vis)

variable {E E' : EventSig} (σ : ∀ e : E.Event, CallTree E' (E.Resp e))

/-- **Substitution commutes with sequencing.** -/
theorem substT_bind {α β : Type} (t : CallTree E α) (k : α → CallTree E β) :
    substT σ (t.bind k) = (substT σ t).bind fun a => substT σ (k a) := by
  induction t with
  | ret a => rfl
  | vis e c ih =>
    show (σ e).bind (fun a => substT σ ((c a).bind k)) = ((σ e).bind _).bind _
    rw [CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick.bind_assoc]
    exact congrArg _ (funext ih)

/-- Substitution in a stateful tree computation. -/
def substS {α : Type} (x : TM E α) : TM E' α := fun s => substT σ (x s)

/-- Substitution in stateful computations commutes with sequencing. -/
theorem substS_bind {α β : Type} (x : TM E α) (f : α → TM E β) :
    substS σ (x >>= f) = substS σ x >>= fun a => substS σ (f a) := by
  funext s
  exact substT_bind σ (x s) _

/-- A sequence substitutes to a sequence when its parts do. -/
theorem substS_bind_congr {α β : Type} {x : TM E α} {f : α → TM E β} {y : TM E' α}
    {g : α → TM E' β} (hx : substS σ x = y) (hf : ∀ a, substS σ (f a) = g a) :
    substS σ (x >>= f) = y >>= g := by
  rw [substS_bind, hx]
  exact congrArg (y >>= ·) (funext hf)

/-- The table whose trees are substituted. -/
def substTable (bt : TreeTable E) : TreeTable E' := fun g vals => substT σ (bt g vals)

/-- Substitution of a lifted tree. -/
theorem substS_lift {α : Type} (t : CallTree E α) :
    substS σ (StateT.lift t : TM E α) = StateT.lift (substT σ t) := by
  funext s
  exact substT_bind σ t _

/-- One step of the proof: a leaf, an induction hypothesis, a sequence, or a case split. -/
local syntax "subst_step" : tactic

macro_rules
  | `(tactic| subst_step) => `(tactic| first
      | rfl
      | (simp only [*]; done)
      | (cases ‹Outcome.val _ = Outcome.val _›; subst_step)
      | (refine substS_bind_congr _ ?_ ?_ <;> (try intro) <;> subst_step)
      | (split_ifs <;> subst_step)
      | (split <;> (try (rename_i hq; rw [hq])) <;> subst_step)
      | (rw [substS_bind, substS_lift]; simp only [substTable]; subst_step)
      | (exfalso; grind))

/-- **The substituted reading is the reading at the substituted table**, for all thirteen
    readings at once. -/
theorem substS_denoteT_and (bt : TreeTable E) :
    (∀ fuel e, substS σ (denoteT bt fuel e) = denoteT (substTable σ bt) fuel e) ∧
    (∀ fuel c b, substS σ (denoteWhileReturnT bt fuel c b) =
      denoteWhileReturnT (substTable σ bt) fuel c b) ∧
    (∀ fuel x lo hi b, substS σ (denoteForLoopRevReturnT bt fuel x lo hi b) =
      denoteForLoopRevReturnT (substTable σ bt) fuel x lo hi b) ∧
    (∀ fuel x lo hi b, substS σ (denoteForLoopReturnT bt fuel x lo hi b) =
      denoteForLoopReturnT (substTable σ bt) fuel x lo hi b) ∧
    (∀ fuel c b, substS σ (denoteWhileT bt fuel c b) = denoteWhileT (substTable σ bt) fuel c b) ∧
    (∀ fuel x lo hi b, substS σ (denoteForLoopRevT bt fuel x lo hi b) =
      denoteForLoopRevT (substTable σ bt) fuel x lo hi b) ∧
    (∀ fuel x lo hi b, substS σ (denoteForLoopT bt fuel x lo hi b) =
      denoteForLoopT (substTable σ bt) fuel x lo hi b) ∧
    (∀ fuel c b, substS σ (denoteWhileOrigT bt fuel c b) =
      denoteWhileOrigT (substTable σ bt) fuel c b) ∧
    (∀ fuel x lo hi b, substS σ (denoteForLoopRevOrigT bt fuel x lo hi b) =
      denoteForLoopRevOrigT (substTable σ bt) fuel x lo hi b) ∧
    (∀ fuel x lo hi b, substS σ (denoteForLoopOrigT bt fuel x lo hi b) =
      denoteForLoopOrigT (substTable σ bt) fuel x lo hi b) ∧
    (∀ fuel v arms, substS σ (denoteMatchArmsT bt fuel v arms) =
      denoteMatchArmsT (substTable σ bt) fuel v arms) ∧
    (∀ fuel args, substS σ (denoteArgsT bt fuel args) = denoteArgsT (substTable σ bt) fuel args) ∧
    (∀ fuel f args, substS σ (denoteAppT bt fuel f args) =
      denoteAppT (substTable σ bt) fuel f args) := by
  apply denote'.mutual_induct
  all_goals intros
  all_goals first
    | simp only [denoteT]
    | ((conv_lhs => rw [denoteWhileReturnT]); (conv_rhs => rw [denoteWhileReturnT]))
    | ((conv_lhs => rw [denoteForLoopRevReturnT]); (conv_rhs => rw [denoteForLoopRevReturnT]))
    | ((conv_lhs => rw [denoteForLoopReturnT]); (conv_rhs => rw [denoteForLoopReturnT]))
    | ((conv_lhs => rw [denoteWhileT]); (conv_rhs => rw [denoteWhileT]))
    | ((conv_lhs => rw [denoteForLoopRevT]); (conv_rhs => rw [denoteForLoopRevT]))
    | ((conv_lhs => rw [denoteForLoopT]); (conv_rhs => rw [denoteForLoopT]))
    | ((conv_lhs => rw [denoteWhileOrigT]); (conv_rhs => rw [denoteWhileOrigT]))
    | ((conv_lhs => rw [denoteForLoopRevOrigT]); (conv_rhs => rw [denoteForLoopRevOrigT]))
    | ((conv_lhs => rw [denoteForLoopOrigT]); (conv_rhs => rw [denoteForLoopOrigT]))
    | simp only [denoteMatchArmsT]
    | simp only [denoteArgsT]
    | ((conv_lhs => rw [denoteAppT]); (conv_rhs => rw [denoteAppT]))
  case case7 =>
    refine substS_bind_congr _ (by assumption) ?_
    intro r
    split
    · rfl
    · rename_i v hv
      cases v
      all_goals first
        | exact (hv _ _ rfl).elim
        | rfl | (split <;> rfl)
    · subst_step
  case case61 ih =>
    refine substS_bind_congr _ ih fun mvals => ?_
    cases mvals with
    | none => rfl
    | some vals =>
      rw [substS_bind, substS_lift]
      congr 1
      funext r
      cases r <;> rfl
  all_goals subst_step

/-- **The substituted reading is the reading at the substituted table.** -/
theorem substS_denoteT (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) :
    substS σ (denoteT bt fuel e) = denoteT (substTable σ bt) fuel e :=
  (substS_denoteT_and σ bt).1 fuel e

/-- The substituted closure table is the closure table at the substituted table. -/
theorem substTable_closureTableT (bt : TreeTable E) (fuel₀ : Nat) (f : String)
    (ps : List String) (body : ImpExpr) (ρ : Env) :
    substTable σ (closureTableT bt fuel₀ f ps body ρ) =
      closureTableT (substTable σ bt) fuel₀ f ps body ρ := by
  funext g vals
  simp only [substTable, closureTableT]
  split_ifs
  · rw [substT_bind, ← substS_denoteT]
    rfl
  · rfl
  · rfl

/-- The spine reading of a binding of a closure literal. -/
theorem denoteSpineT_lam (bt : TreeTable E) (fuel : Nat) (f : String) (ps : List String)
    (body cont : ImpExpr) :
    denoteSpineT bt fuel (.letBind f (.lam ps body) cont) =
      if closureOk f ps body (inlineSpine cont) || blockOk f ps body (inlineSpine cont) then do
        let ρ ← get
        denoteSpineT (closureTableT bt fuel f ps body ρ) fuel cont
      else denoteT bt fuel (.letBind f (.lam ps body) cont) := by
  rw [denoteSpineT]

/-- The spine reading of a binding of another expression. -/
theorem denoteSpineT_letBind (bt : TreeTable E) (fuel : Nat) (x : String) (v cont : ImpExpr)
    (hv : ∀ (ps : List String) (body : ImpExpr), v = .lam ps body → False) :
    denoteSpineT bt fuel (.letBind x v cont) = (do
      let rv ← denoteT bt fuel v
      match rv with
      | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
      | .val w => do modify (Env.extend · x w); denoteSpineT bt fuel cont
      | other => pure other) := by
  rw [denoteSpineT] <;> first | rfl | exact hv

/-- The spine reading of a sequence. -/
theorem denoteSpineT_seq (bt : TreeTable E) (fuel : Nat) (a b : ImpExpr) :
    denoteSpineT bt fuel (.seq a b) = (do
      let r ← denoteT bt fuel a
      match r with
      | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
      | .val _ => denoteSpineT bt fuel b
      | other => pure other) := by
  rw [denoteSpineT]; rfl

/-- The spine reading of an expression that is neither a binding nor a sequence. -/
theorem denoteSpineT_other (bt : TreeTable E) (fuel : Nat) (e : ImpExpr)
    (h : ∀ (x : String) (v c : ImpExpr), e = .letBind x v c → False)
    (h' : ∀ a b : ImpExpr, e = .seq a b → False) :
    denoteSpineT bt fuel e = denoteT bt fuel e := by
  cases e <;> first
    | exact (h _ _ _ rfl).elim
    | exact (h' _ _ rfl).elim
    | (rw [denoteSpineT] <;> intros <;> simp_all)

/-- **The substituted spine reading is the spine reading at the substituted table.** -/
theorem substS_denoteSpineT (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) :
    substS σ (denoteSpineT bt fuel e) = denoteSpineT (substTable σ bt) fuel e := by
  fun_induction denoteSpineT bt fuel e with
  | case1 bt f ps body cont hc ih =>
    simp only [denoteSpineT_lam, hc, ↓reduceIte]
    refine substS_bind_congr _ rfl fun ρ => ?_
    rw [ih ρ, substTable_closureTableT]
  | case2 bt f ps body cont hc =>
    simp only [denoteSpineT_lam, hc, ↓reduceIte, Bool.false_eq_true]
    exact substS_denoteT σ bt fuel _
  | case3 bt x v cont hv ih =>
    rw [denoteSpineT_letBind (substTable σ bt) fuel x v cont hv]
    refine substS_bind_congr _ (substS_denoteT σ bt fuel v) fun r => ?_
    subst_step
  | case4 bt a b ih =>
    rw [denoteSpineT_seq (substTable σ bt)]
    refine substS_bind_congr _ (substS_denoteT σ bt fuel a) fun r => ?_
    subst_step
  | case5 bt e h1 h2 h3 =>
    have hl : ∀ (x : String) (v c : ImpExpr), e = .letBind x v c → False := by grind
    have hs : ∀ a b : ImpExpr, e = .seq a b → False := by grind
    rw [denoteSpineT_other (substTable σ bt) fuel e hl hs]
    exact substS_denoteT σ bt fuel e

/-- **The substituted call tree is the call tree at the substituted table.** -/
theorem substT_nfTree (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) (env : Env) :
    substT σ (nfTree bt fuel e env) = nfTree (substTable σ bt) fuel e env :=
  congrFun (substS_denoteSpineT σ bt fuel e) env

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubstTable
