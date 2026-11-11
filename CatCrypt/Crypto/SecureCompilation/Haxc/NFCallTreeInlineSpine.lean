/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeWhileTrue
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt

/-!
# Relational refinement of call-tree readings

The refinement `RefR` of `InlineLocalClosures` at the level of call trees: `RelT h₁ Pre Post bad
tgt src` relates, from environments related by `Pre`, the call tree of `src` to the call tree of
`tgt` by `RuttS` at equal events and answers, a leaf of `src` whose result is `bad` being a failed
leaf and the other leaves being matched by leaves with the same result and final environments
related by `Post`. The combinators follow those of `RefR`, and the loop readings at tree tables
are related when their bodies are. An expression without calls (`noCalls`) reads as a leaf at
every tree table and fuel.

## Main definitions

* `RelT`: the relation of two stateful tree computations from related environments.
* `noCalls`: a literal, a variable, `unitVal`, or a tuple or projection of such expressions.
* `argsFree f e`: every call of `f` in `e` passes arguments without calls.

## Main results

* `RelT.bind`, `RelT.pure`, `RelT.of_bad`, `RelT.get`, `RelT.set`, `RelT.modify_ext`,
  `RelT.mono`: the combinators of `RelT`.
* `forLoopT_rel`, `whileT_rel` and their companions: the loop readings over related bodies.
* `argsT_rel`: the argument readings over related arguments.
* `noCalls_runT`, `noCallsArgs_vals`: an expression without calls reads as a leaf.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpine

open _root_.Hax
open _root_.Hax.InlineLocalClosures (IsErr)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run tm_pure_run)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)

variable {E : EventSig} (h₁ : ∀ e : E.Event, E.Resp e)

/-- `tgt` refines `src` from environments related by `Pre`: from `e₁` and `e₂` with
    `Pre e₁ e₂`, the call tree of `src` from `e₂` is related to the call tree of `tgt` from `e₁`
    by `RuttS` at equal events and answers, a leaf of `src` with a `bad` result being a failed
    leaf, and every other leaf matched by a leaf with the same result whose final environment is
    related by `Post` to that of `src`. -/
def RelT {α : Type} (Pre Post : Env → Env → Prop) (bad : α → Prop) (tgt src : TM E α) : Prop :=
  ∀ e₁ e₂, Pre e₁ e₂ →
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1 ∧ Post r₂.2 r₁.2) (fun r => bad r.1) (src e₂) (tgt e₁)

variable {h₁}

section Comb

variable {P Q S : Env → Env → Prop}

/-- Two equal returns. -/
theorem RelT.pure_mono {α : Type} {bad : α → Prop} (a : α) (h : ∀ e₁ e₂, P e₁ e₂ → Q e₁ e₂) :
    RelT h₁ P Q bad (Pure.pure a) (Pure.pure a) :=
  fun e₁ e₂ hp => .ret ⟨rfl, h e₁ e₂ hp⟩

/-- Two equal returns, one relation before and after. -/
theorem RelT.pure {α : Type} {bad : α → Prop} (a : α) :
    RelT h₁ P P bad (Pure.pure a) (Pure.pure a) :=
  RelT.pure_mono a fun _ _ h => h

/-- A source that ends at once in a bad result. -/
theorem RelT.of_bad {α : Type} {bad : α → Prop} {tgt src : TM E α}
    (h : ∀ env, ∃ a s, src env = .ret (a, s) ∧ bad a) : RelT h₁ P Q bad tgt src := by
  intro e₁ e₂ _
  obtain ⟨a, s, hs, hb⟩ := h e₂
  rw [hs]
  exact .fail hb

/-- Sequencing of related computations. -/
theorem RelT.bind {α β : Type} {badα : α → Prop} {badβ : β → Prop} {m₁ m₂ : TM E α}
    {k₁ k₂ : α → TM E β} (hm : RelT h₁ P Q badα m₁ m₂)
    (hk : ∀ a, ¬ badα a → RelT h₁ Q S badβ (k₁ a) (k₂ a))
    (hb : ∀ a, badα a → ∀ s, ∃ b s', k₂ a s = .ret (b, s') ∧ badβ b) :
    RelT h₁ P S badβ (m₁ >>= k₁) (m₂ >>= k₂) := by
  intro e₁ e₂ hP
  rw [tm_bind_run, tm_bind_run]
  have fl : ∀ a s, badα a → ∀ t : CallTree E (β × Env),
      RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1 ∧ S r₂.2 r₁.2) (fun r => badβ r.1) (k₂ a s) t := by
    intro a s ha t
    obtain ⟨b, s', hs, hbb⟩ := hb a ha s
    rw [hs]
    exact .fail hbb
  refine NFProgCallTree.RuttS.bind (RR' := fun r₁ r₂ => r₂.1 = r₁.1 ∧ Q r₂.2 r₁.2)
    (Fail' := fun r => badα r.1) (hm e₁ e₂ hP) (fun s₁ s₂ hs => ?_)
    (fun s₁ hf t => fl _ _ hf t)
  obtain ⟨a, x₂⟩ := s₁
  obtain ⟨a', x₁⟩ := s₂
  obtain ⟨h, hq⟩ := hs
  dsimp only at h hq
  subst h
  by_cases ha : badα a'
  · exact fl _ _ ha _
  · exact hk a' ha x₁ x₂ hq

/-- Reading the environment on both sides. -/
theorem RelT.get {α : Type} {bad : α → Prop} {k₁ k₂ : Env → TM E α}
    (h : ∀ e₁ e₂, P e₁ e₂ → RelT h₁ P Q bad (k₁ e₁) (k₂ e₂)) :
    RelT h₁ P Q bad (MonadState.get >>= k₁) (MonadState.get >>= k₂) :=
  fun e₁ e₂ hp => h e₁ e₂ hp e₁ e₂ hp

/-- Setting related environments on both sides. -/
theorem RelT.set {α : Type} {bad : α → Prop} {s₁ s₂ : Env} (hs : Q s₁ s₂)
    {k₁ k₂ : PUnit → TM E α} (h : ∀ u, RelT h₁ Q S bad (k₁ u) (k₂ u)) :
    RelT h₁ P S bad (MonadStateOf.set s₁ >>= k₁) (MonadStateOf.set s₂ >>= k₂) :=
  fun _ _ _ => h _ _ _ hs

/-- Updating the environments on both sides, keeping a relation. -/
theorem RelT.modify_mono {α : Type} {bad : α → Prop} {g₁ g₂ : Env → Env}
    (hg : ∀ e₁ e₂, P e₁ e₂ → Q (g₁ e₁) (g₂ e₂)) {k₁ k₂ : PUnit → TM E α}
    (h : ∀ u, RelT h₁ Q S bad (k₁ u) (k₂ u)) :
    RelT h₁ P S bad (_root_.modify g₁ >>= k₁) (_root_.modify g₂ >>= k₂) :=
  fun e₁ e₂ hp => h _ _ _ (hg e₁ e₂ hp)

/-- Extending both environments at the same name by the same value. -/
theorem RelT.modify_ext {α : Type} {bad : α → Prop} {n : String} {w : Value}
    (hn : ∀ e₁ e₂ w, P e₁ e₂ → P (e₁.extend n w) (e₂.extend n w))
    {k₁ k₂ : PUnit → TM E α} (h : ∀ u, RelT h₁ P P bad (k₁ u) (k₂ u)) :
    RelT h₁ P P bad (_root_.modify (fun x => x.extend n w) >>= k₁)
      (_root_.modify (fun x => x.extend n w) >>= k₂) :=
  RelT.modify_mono (fun e₁ e₂ hp => hn e₁ e₂ w hp) h

/-- Weakening of the relations. -/
theorem RelT.mono {α : Type} {P' Q' : Env → Env → Prop} {bad : α → Prop} {tgt src : TM E α}
    (h : RelT h₁ P Q bad tgt src) (hP : ∀ a b, P' a b → P a b) (hQ : ∀ a b, Q a b → Q' a b) :
    RelT h₁ P' Q' bad tgt src := fun e₁ e₂ hp =>
  NFProgCallTreeExt.RuttS.mono (fun _ _ h => ⟨h.1, hQ _ _ h.2⟩) (h e₁ e₂ (hP _ _ hp))

/-- A computation is related to itself from equal environments. -/
theorem RelT.refl {α : Type} {bad : α → Prop} (m : TM E α) :
    RelT h₁ (fun e₁ e₂ => e₁ = e₂) (fun e₁ e₂ => e₁ = e₂) bad m m := by
  intro e₁ e₂ h
  subst h
  exact NFProgCallTree.RuttS.refl (fun _ => ⟨rfl, rfl⟩) _

end Comb

/-- One step of a `RelT` proof between two readings of the same shape: identical returns, a
    hypothesis, an environment update that keeps the relation, or a sequence of two related
    readings followed by a case split on the outcome. -/
scoped syntax "relt_step" : tactic

macro_rules
  | `(tactic| relt_step) => `(tactic| first
      | exact RelT.pure _
      | (apply RelT.of_bad; intro _; exact ⟨_, _, rfl, _, rfl⟩)
      | solve_by_elim (maxDepth := 2)
      | (refine RelT.modify_ext (by assumption) (fun _ => ?_); relt_step)
      | (refine RelT.bind (badα := IsErr) (by solve_by_elim (maxDepth := 2)) (fun o ho => ?_)
            (fun a ha s => by
              obtain ⟨m, hm⟩ := ha; subst hm
              first
                | exact ⟨_, _, rfl, m, rfl⟩
                | (cases ‹Value› <;> exact ⟨_, _, rfl, _, rfl⟩)
                | (split <;> first
                    | exact ⟨_, _, rfl, _, rfl⟩ | (exfalso; simp_all) | simp_all [IsErr]))
         split <;> first | relt_step | (exfalso; simp_all [IsErr]))
      | (split <;> relt_step))

section Loops

variable {R : Env → Env → Prop} {bt₁ bt₂ : TreeTable E}

/-- The `forFold` reading over related bodies. -/
theorem forLoopT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel lo hi, RelT h₁ R R IsErr (denoteForLoopT bt₁ fuel v lo hi b₁)
      (denoteForLoopT bt₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopT; by_cases hl : lo ≥ hi <;> simp [hl] <;> relt_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relt_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relt_step

/-- The reversed counted loop over related bodies. -/
theorem forLoopRevT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel lo hi, RelT h₁ R R IsErr (denoteForLoopRevT bt₁ fuel v lo hi b₁)
      (denoteForLoopRevT bt₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevT; by_cases hl : lo ≥ hi <;> simp [hl] <;> relt_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relt_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relt_step

/-- The `forLoop` reading over related bodies. -/
theorem forLoopOrigT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel lo hi, RelT h₁ R R IsErr (denoteForLoopOrigT bt₁ fuel v lo hi b₁)
      (denoteForLoopOrigT bt₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopOrigT; by_cases hl : lo ≥ hi <;> simp [hl] <;> relt_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopOrigT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relt_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relt_step

/-- The `forLoopRev` reading over related bodies. -/
theorem forLoopRevOrigT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel lo hi, RelT h₁ R R IsErr (denoteForLoopRevOrigT bt₁ fuel v lo hi b₁)
      (denoteForLoopRevOrigT bt₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevOrigT
    by_cases hl : lo ≥ hi <;> simp [hl] <;> relt_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevOrigT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relt_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relt_step

/-- The returning counted loop over related bodies. -/
theorem forLoopReturnT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel lo hi, RelT h₁ R R IsErr (denoteForLoopReturnT bt₁ fuel v lo hi b₁)
      (denoteForLoopReturnT bt₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopReturnT
    by_cases hl : lo ≥ hi <;> simp [hl] <;> relt_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopReturnT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relt_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relt_step

/-- The returning reversed counted loop over related bodies. -/
theorem forLoopRevReturnT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel lo hi, RelT h₁ R R IsErr (denoteForLoopRevReturnT bt₁ fuel v lo hi b₁)
      (denoteForLoopRevReturnT bt₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevReturnT
    by_cases hl : lo ≥ hi <;> simp [hl] <;> relt_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevReturnT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relt_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relt_step

/-- The `whileFold` reading over related conditions and bodies. -/
theorem whileT_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel c₁) (denoteT bt₂ fuel c₂))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel, RelT h₁ R R IsErr (denoteWhileT bt₁ fuel c₁ b₁) (denoteWhileT bt₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileT; simp only [ite_true]; relt_step
  | succ n ih =>
    unfold denoteWhileT
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    relt_step

/-- The `whileLoop` reading over related conditions and bodies. -/
theorem whileOrigT_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel c₁) (denoteT bt₂ fuel c₂))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel, RelT h₁ R R IsErr (denoteWhileOrigT bt₁ fuel c₁ b₁)
      (denoteWhileOrigT bt₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileOrigT; simp only [ite_true]; relt_step
  | succ n ih =>
    unfold denoteWhileOrigT
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    relt_step

/-- The returning `while` reading over related conditions and bodies. -/
theorem whileReturnT_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel c₁) (denoteT bt₂ fuel c₂))
    (h : ∀ fuel, RelT h₁ R R IsErr (denoteT bt₁ fuel b₁) (denoteT bt₂ fuel b₂)) :
    ∀ fuel, RelT h₁ R R IsErr (denoteWhileReturnT bt₁ fuel c₁ b₁)
      (denoteWhileReturnT bt₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileReturnT; simp only [ite_true]; relt_step
  | succ n ih =>
    unfold denoteWhileReturnT
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    relt_step


/-- The argument readings over related arguments. -/
theorem argsT_rel (g : ImpExpr → ImpExpr) (args : List ImpExpr) (fuel : Nat)
    (ih : ∀ a, a ∈ args → RelT h₁ R R IsErr (denoteT bt₁ fuel (g a)) (denoteT bt₂ fuel a)) :
    RelT h₁ R R (fun o => o = none) (denoteArgsT bt₁ fuel (args.map g))
      (denoteArgsT bt₂ fuel args) := by
  induction args with
  | nil => simp only [List.map_nil, denoteArgsT]; exact RelT.pure _
  | cons a as iha =>
    simp only [List.map_cons, denoteArgsT]
    refine RelT.bind (badα := IsErr) (ih a List.mem_cons_self) (fun o ho => ?_)
      (fun o ho s => by obtain ⟨m, hm⟩ := ho; subst hm; exact ⟨_, _, rfl, rfl⟩)
    split
    · exact RelT.pure _
    · exact RelT.bind (badα := fun o => o = none)
        (iha fun b hb => ih b (List.mem_cons_of_mem a hb))
        (fun _ _ => RelT.pure _) (fun r hr s => by subst hr; exact ⟨_, _, rfl, rfl⟩)
    · exact RelT.pure _

end Loops

open _root_.Hax.InlineLocalClosures
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (
  denoteT_lit_run denoteT_var_run denoteT_var_run_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeWhileTrue (lift_bind_run)

/-! ## Expressions without calls -/

/-- An expression without calls: a literal, a variable, `unitVal`, or a tuple or projection of
    such expressions. -/
def noCalls : ImpExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .unitVal => true
  | .tuple es => allNo es
  | .proj e _ => noCalls e
  | _ => false
where
  /-- `noCalls` of every expression of a list. -/
  allNo : List ImpExpr → Bool
    | [] => true
    | e :: es => noCalls e && allNo es

/-- `noCalls.allNo` is `List.all noCalls`. -/
theorem noCalls.allNo_eq (es : List ImpExpr) : noCalls.allNo es = es.all noCalls := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [noCalls.allNo, ih]

/-- Every call of `f` in `e` passes arguments without calls. -/
def argsFree (f : String) : ImpExpr → Bool
  | .app g args => (g != f || noCalls.allNo args) && argsFreeList f args
  | .letBind _ v b => argsFree f v && argsFree f b
  | .assign _ rhs => argsFree f rhs
  | .lam _ b => argsFree f b
  | .tuple es => argsFreeList f es
  | .proj e _ => argsFree f e
  | .ifThenElse c t e => argsFree f c && argsFree f t && argsFree f e
  | .match_ scrut arms => argsFree f scrut && argsFreeArms f arms
  | .seq a b => argsFree f a && argsFree f b
  | .borrow e => argsFree f e
  | .deref e => argsFree f e
  | .forLoop _ lo hi b => argsFree f lo && argsFree f hi && argsFree f b
  | .forLoopRev _ lo hi b => argsFree f lo && argsFree f hi && argsFree f b
  | .whileLoop c b => argsFree f c && argsFree f b
  | .break_ (some e) => argsFree f e
  | .earlyReturn e => argsFree f e
  | .questionMark e => argsFree f e
  | .forFold _ lo hi b => argsFree f lo && argsFree f hi && argsFree f b
  | .forFoldRev _ lo hi b => argsFree f lo && argsFree f hi && argsFree f b
  | .whileFold c b => argsFree f c && argsFree f b
  | .forFoldReturn _ lo hi b => argsFree f lo && argsFree f hi && argsFree f b
  | .forFoldRevReturn _ lo hi b => argsFree f lo && argsFree f hi && argsFree f b
  | .whileFoldReturn c b => argsFree f c && argsFree f b
  | .cfBreak e => argsFree f e
  | .cfContinue e => argsFree f e
  | .cfBreakContinue e => argsFree f e
  | .typeAscription e _ => argsFree f e
  | _ => true
where
  /-- `argsFree` of every expression of a list. -/
  argsFreeList (f : String) : List ImpExpr → Bool
    | [] => true
    | e :: es => argsFree f e && argsFreeList f es
  /-- `argsFree` of every arm body. -/
  argsFreeArms (f : String) : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => argsFree f e && argsFreeArms f rest

/-- `argsFree.argsFreeList` is `List.all (argsFree g)`. -/
theorem argsFree.argsFreeList_eq (g : String) (es : List ImpExpr) :
    argsFree.argsFreeList g es = es.all (argsFree g) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [argsFree.argsFreeList, ih]

/-- `argsFree.argsFreeArms` checks `argsFree` of every arm body. -/
theorem argsFree.argsFreeArms_eq (g : String) (arms : List (ImpPat × ImpExpr)) :
    argsFree.argsFreeArms g arms = arms.all fun pa => argsFree g pa.2 := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [argsFree.argsFreeArms, ih]

/-- `inlineCalls` keeps an expression without calls. -/
theorem inlineCalls_noCalls (f : String) (ps : List String) (body : ImpExpr) (a : ImpExpr)
    (ha : noCalls a = true) : inlineCalls f ps body a = a := by
  induction a using ImpExpr.ind with
  | tuple es ih =>
    simp only [noCalls, noCalls.allNo_eq, List.all_eq_true] at ha
    simp only [inlineCalls, inlineCalls.mapExpr_eq, ImpExpr.tuple.injEq]
    exact (List.map_congr_left fun a h => ih a h (ha a h)).trans (by simp)
  | proj e i ih =>
    simp only [noCalls] at ha
    simp only [inlineCalls, ih ha]
  | lit => rfl
  | var => rfl
  | unitVal => rfl
  | _ => simp [noCalls] at ha

/-! ## Reading lemmas -/

/-- The reading of no arguments. -/
theorem argsT_nil_run (bt : TreeTable E) (fuel : Nat) (env : Env) :
    denoteArgsT bt fuel [] env = .ret (some [], env) := by
  rw [denoteArgsT]; rfl

/-- The reading of a list of arguments. -/
theorem argsT_cons_run (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) (es : List ImpExpr)
    (env : Env) :
    denoteArgsT bt fuel (e :: es) env = (denoteT bt fuel e env).bind fun p =>
      match p with
      | (.val (.controlFlow _ _), e1) => .ret (none, e1)
      | (.val v, e1) => (denoteArgsT bt fuel es e1).bind fun q => .ret (q.1.map (v :: ·), q.2)
      | (_, e1) => .ret (none, e1) := by
  rw [denoteArgsT, tm_bind_run]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

/-- Arguments that read as leaves, the same at every tree table and fuel, read as a leaf. -/
theorem noCallsArgs_aux (env : Env) (es : List ImpExpr)
    (h : ∀ a, a ∈ es → ∃ o, ∀ (bt : TreeTable E) fuel, denoteT bt fuel a env = .ret (o, env)) :
    ∃ ov, ∀ (bt : TreeTable E) fuel, denoteArgsT bt fuel es env = .ret (ov, env) := by
  induction es with
  | nil => exact ⟨_, fun bt fuel => argsT_nil_run bt fuel env⟩
  | cons a as ih =>
    obtain ⟨o, ho⟩ := h a List.mem_cons_self
    obtain ⟨ov, hov⟩ := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    refine ⟨match o with
      | .val (.controlFlow _ _) => none
      | .val v => ov.map (v :: ·)
      | _ => none, fun bt fuel => ?_⟩
    rw [argsT_cons_run, ho]
    rcases o with v | _ | _ | _ | _
    · cases v <;> first | rfl | (simp only [CallTree.bind]; rw [hov]; rfl)
    all_goals rfl

/-- An expression without calls reads as a leaf, the same at every tree table and fuel. -/
theorem noCalls_runT (a : ImpExpr) (ha : noCalls a = true) (env : Env) :
    ∃ o, ∀ (bt : TreeTable E) fuel, denoteT bt fuel a env = .ret (o, env) := by
  induction a using ImpExpr.ind with
  | lit l => exact ⟨_, fun bt fuel => denoteT_lit_run bt fuel l env⟩
  | var x =>
    rcases h : env x with _ | v
    · exact ⟨_, fun bt fuel => denoteT_var_run_none bt fuel x env h⟩
    · exact ⟨_, fun bt fuel => denoteT_var_run bt fuel x env v h⟩
  | unitVal => exact ⟨_, fun bt fuel => by rw [denoteT]; rfl⟩
  | tuple es ih =>
    simp only [noCalls, noCalls.allNo_eq, List.all_eq_true] at ha
    obtain ⟨ov, hov⟩ := noCallsArgs_aux env es fun a h => ih a h (ha a h)
    refine ⟨match ov with
      | some vals => .val (.tuple vals)
      | none => .err "non-value in tuple elements", fun bt fuel => ?_⟩
    rw [denoteT, tm_bind_run, hov]
    cases ov <;> rfl
  | proj e i ih =>
    simp only [noCalls] at ha
    obtain ⟨o, ho⟩ := ih ha
    refine ⟨match o with
      | .val (.controlFlow k v) => .val (.controlFlow k v)
      | .val v =>
        match v.projIdx i with
        | some vi => .val vi
        | none => .err s!"projection index {i} out of range"
      | other => other, fun bt fuel => ?_⟩
    rw [denoteT, tm_bind_run, ho]
    rcases o with v | _ | _ | _ | _
    · cases v <;> try rfl
      all_goals (simp only; split <;> (rename_i h; simp only [CallTree.bind, h]; rfl))
    all_goals rfl
  | _ => simp [noCalls] at ha

/-- The reading of a variable as a leaf at its value in the environment. -/
theorem denoteT_var_eq (bt : TreeTable E) (fuel : Nat) (x : String) (env : Env) :
    denoteT bt fuel (.var x) env =
      .ret ((env x).elim (.err s!"undefined variable: {x}") .val, env) := by
  rcases h : env x with _ | v
  · exact denoteT_var_run_none bt fuel x env h
  · exact denoteT_var_run bt fuel x env v h

/-- Arguments without calls that read as a list of values read each argument as its value. -/
theorem noCallsArgs_vals (bt : TreeTable E) (fuel : Nat) (σ : Env) :
    ∀ (args : List ImpExpr) (vals : List Value) (s : Env),
      (∀ a, a ∈ args → noCalls a = true) →
      denoteArgsT bt fuel args σ = .ret (some vals, s) →
      s = σ ∧ vals.length = args.length ∧
        ∀ av, av ∈ args.zip vals → ∀ (bt' : TreeTable E) fuel',
          denoteT bt' fuel' av.1 σ = .ret (.val av.2, σ)
  | [], vals, s, _, h => by
    rw [argsT_nil_run] at h
    cases h; exact ⟨rfl, rfl, by simp⟩
  | a :: as, vals, s, hp, h => by
    have hpa : ∀ b, b ∈ as → noCalls b = true := fun b hb => hp b (List.mem_cons_of_mem a hb)
    obtain ⟨o, ho⟩ := noCalls_runT a (hp a List.mem_cons_self) σ
    obtain ⟨ov, hov⟩ := noCallsArgs_aux σ as fun b hb => noCalls_runT b (hpa b hb) σ
    rw [argsT_cons_run, ho] at h
    rcases o with v | _ | _ | _ | _
    case val =>
      cases v
      case controlFlow => cases h
      all_goals
        simp only [CallTree.bind] at h
        rw [hov] at h
        simp only [CallTree.bind, CallTree.ret.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, rfl⟩ := h
        rcases ov with _ | vs
        · cases hv
        simp only [Option.map_some, Option.some.injEq] at hv
        subst hv
        obtain ⟨-, hlen, hz⟩ := noCallsArgs_vals bt fuel σ as vs σ hpa (hov bt fuel)
        refine ⟨rfl, by simp [hlen], ?_⟩
        intro av hav
        simp only [List.zip_cons_cons, List.mem_cons] at hav
        rcases hav with rfl | hav
        · exact ho
        · exact hz av hav
    all_goals cases h

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpine
