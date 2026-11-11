/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick

/-!
# Relational refinement of call trees and the frame of an expression

`RefT P Q bad tgt src` is the refinement of the stateful tree reading `src` by `tgt` from
environments related by `P`: from related environments the two trees are related by `Rutt` at
equal events and answers, a leaf of `src` whose result is `bad` is a failed leaf, and a leaf of
`src` is matched by a leaf of `tgt` with the same result and environments related by `Q`. It is
the counterpart over call trees of `RefR` of `InlineLocalClosures`, and it is built by the same
combinators: leaves, sequencing, and the update of a name.

## Main definitions

* `LeafP P t` — every leaf of `t` satisfies `P`.
* `RefT`, `RefET` — the relational refinement of tree readings.

## Main results

* `rutt_bind`, `rutt_refl`, `rutt_leafP` — sequencing and reflexivity of `Rutt` at equal events
  and answers, and the leaves of a source tree related to a target.
* `denoteForLoopT_rel` and its companions — the loop readings refine each other when their
  bodies do.
* `denoteT_frame` — an expression in `frameOk rd bd ok` refines itself from environments that
  agree on the names it reads and stay related at the names it binds.
* `denoteT_keeps` — the non-error leaves of an expression that binds no `x` keep `x`.
-/


@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm

open _root_.Hax
open _root_.Hax.InlineLocalClosures (IsErr frameOk)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run tm_pure_run
  denoteT_var_run denoteT_var_run_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree (Rutt)

variable {E : EventSig}

/-! ## Trees related at equal events and answers -/

section RuttLemmas

variable {RE : E.Event → E.Event → Prop}
  {RA : (e₁ : E.Event) → (e₂ : E.Event) → E.Resp e₁ → E.Resp e₂ → Prop}

/-- Related prefixes followed by continuations related at related leaves, and failed prefix
    leaves followed by continuations related to every tree, are related. -/
theorem rutt_bind {S₁ S₂ R₁ R₂ : Type} {RR' : S₁ → S₂ → Prop} {Fail' : S₁ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E S₁} {t₂ : CallTree E S₂}
    {k₁ : S₁ → CallTree E R₁} {k₂ : S₂ → CallTree E R₂}
    (h : Rutt RE RA RR' Fail' t₁ t₂)
    (hk : ∀ s₁ s₂, RR' s₁ s₂ → Rutt RE RA RR Fail (k₁ s₁) (k₂ s₂))
    (hf : ∀ s₁, Fail' s₁ → ∀ t, Rutt RE RA RR Fail (k₁ s₁) t) :
    Rutt RE RA RR Fail (t₁.bind k₁) (t₂.bind k₂) := by
  induction h with
  | ret h => exact hk _ _ h
  | fail h => exact hf _ h _
  | vis he _ ih => exact .vis he ih

/-- Relations of leaves can be weakened. -/
theorem rutt_mono {R₁ R₂ : Type} {RR RR' : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (hR : ∀ a b, RR a b → RR' a b) {t₁ : CallTree E R₁} {t₂ : CallTree E R₂}
    (h : Rutt RE RA RR Fail t₁ t₂) : Rutt RE RA RR' Fail t₁ t₂ := by
  induction h with
  | ret h => exact .ret (hR _ _ h)
  | fail h => exact .fail h
  | vis he _ ih => exact .vis he ih

end RuttLemmas

/-- A tree is related to itself at equal events and answers. -/
theorem rutt_refl {R : Type} {RR : R → R → Prop} {Fail : R → Prop} (hR : ∀ r, RR r r)
    (t : CallTree E R) :
    Rutt (fun e₁ e₂ : E.Event => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail t t := by
  induction t with
  | ret r => exact .ret (hR r)
  | vis e c ih =>
    refine .vis rfl fun a₁ a₂ ha => ?_
    cases ha
    exact ih a₁

/-- Every leaf of a tree satisfies `P`. -/
inductive LeafP {R : Type} (P : R → Prop) : CallTree E R → Prop
  | ret {r : R} (h : P r) : LeafP P (.ret r)
  | vis {e : E.Event} {k : E.Resp e → CallTree E R} (h : ∀ a, LeafP P (k a)) :
      LeafP P (.vis e k)

/-- A property of the leaves can be weakened. -/
theorem LeafP.mono {R : Type} {P P' : R → Prop} (hP : ∀ r, P r → P' r) {t : CallTree E R}
    (h : LeafP P t) : LeafP P' t := by
  induction h with
  | ret h => exact .ret (hP _ h)
  | vis _ ih => exact .vis ih

/-- Two properties of the leaves give their conjunction. -/
theorem LeafP.and {R : Type} {P P' : R → Prop} {t : CallTree E R} (h : LeafP P t)
    (h' : LeafP P' t) : LeafP (fun r => P r ∧ P' r) t := by
  induction h with
  | ret h => cases h' with | ret h' => exact .ret ⟨h, h'⟩
  | vis _ ih => cases h' with | vis h' => exact .vis fun a => ih a (h' a)

/-- The leaves of a source tree related to a target at equal events and answers satisfy every
    property implied by the relation of leaves and by failure. -/
theorem rutt_leafP {R₁ R₂ : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {P : R₁ → Prop}
    (hR : ∀ r₁ r₂, RR r₁ r₂ → P r₁) (hF : ∀ r, Fail r → P r) {t₁ : CallTree E R₁}
    {t₂ : CallTree E R₂}
    (h : Rutt (fun e₁ e₂ : E.Event => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail t₁ t₂) :
    LeafP P t₁ := by
  induction h with
  | ret h => exact .ret (hR _ _ h)
  | fail h => exact .ret (hF _ h)
  | vis he _ ih =>
    subst he
    exact .vis fun a => ih a a HEq.rfl

/-- A relation of trees carries a property of the leaves of the source tree. -/
theorem rutt_withLeaf {RE : E.Event → E.Event → Prop}
    {RA : (e₁ : E.Event) → (e₂ : E.Event) → E.Resp e₁ → E.Resp e₂ → Prop}
    {R₁ R₂ : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {P : R₁ → Prop}
    {t₁ : CallTree E R₁} {t₂ : CallTree E R₂} (h : Rutt RE RA RR Fail t₁ t₂)
    (hP : LeafP P t₁) : Rutt RE RA (fun r₁ r₂ => RR r₁ r₂ ∧ P r₁) Fail t₁ t₂ := by
  induction h with
  | ret h => cases hP with | ret hP => exact .ret ⟨h, hP⟩
  | fail h => exact .fail h
  | vis he _ ih => cases hP with | vis hP => exact .vis he fun a₁ a₂ ha => ih a₁ a₂ ha (hP a₁)

/-! ## Relational refinement of tree readings -/

/-- `tgt` refines `src` from environments related by `P`: from `P`-related environments the
    tree of `src` is related to the tree of `tgt` at equal events and answers, a leaf of `src`
    whose result is `bad` is a failed leaf, and a leaf of `src` is matched by a leaf of `tgt`
    with the same result, the final environments related by `Q`. -/
def RefT {α : Type} (P Q : Env → Env → Prop) (bad : α → Prop) (tgt src : TM E α) : Prop :=
  ∀ e₁ e₂, P e₁ e₂ → Rutt (fun a b : E.Event => a = b) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
    (fun (r₁ r₂ : α × Env) => r₂.1 = r₁.1 ∧ Q r₂.2 r₁.2) (fun r => bad r.1) (src e₂) (tgt e₁)

/-- `RefT` on outcomes with one relation before and after, an error being the failed
    result. -/
abbrev RefET (R : Env → Env → Prop) (tgt src : TM E Outcome) : Prop :=
  RefT R R IsErr tgt src

section RefT

variable {R : Env → Env → Prop}

/-- Equal leaves refine each other. -/
theorem RefT.pure {α : Type} {bad : α → Prop} (a : α) :
    RefT R R bad (pure a : TM E α) (pure a) :=
  fun _ _ h => .ret ⟨rfl, h⟩

/-- A source whose every run is a failed leaf is refined by every target. -/
theorem RefT.of_bad {α : Type} {P Q : Env → Env → Prop} {bad : α → Prop} {tgt src : TM E α}
    (h : ∀ env, ∃ r, src env = .ret r ∧ bad r.1) : RefT P Q bad tgt src := by
  intro _ e₂ _
  obtain ⟨r, hr, hb⟩ := h e₂
  rw [hr]
  exact .fail hb

/-- Sequencing of refinements. -/
theorem RefT.bind {α β : Type} {P Q S : Env → Env → Prop} {badα : α → Prop}
    {badβ : β → Prop} {m₁ m₂ : TM E α} {k₁ k₂ : α → TM E β}
    (hm : RefT P Q badα m₁ m₂) (hk : ∀ a, ¬ badα a → RefT Q S badβ (k₁ a) (k₂ a))
    (hb : ∀ a, badα a → ∀ s, ∃ r, k₂ a s = .ret r ∧ badβ r.1) :
    RefT P S badβ (m₁ >>= k₁) (m₂ >>= k₂) := by
  intro e₁ e₂ hP
  rw [tm_bind_run, tm_bind_run]
  refine rutt_bind (hm e₁ e₂ hP) (fun r₁ r₂ hr => ?_) (fun r₁ hf t => ?_)
  · obtain ⟨h1, hQ⟩ := hr
    rcases r₁ with ⟨a, s₂⟩
    rcases r₂ with ⟨a', s₁⟩
    dsimp only at h1 hQ ⊢
    subst h1
    by_cases ha : badα a'
    · obtain ⟨r, hr, hbr⟩ := hb a' ha s₂
      rw [hr]
      exact .fail hbr
    · exact hk a' ha s₁ s₂ hQ
  · obtain ⟨r, hr, hbr⟩ := hb _ hf r₁.2
    rw [hr]
    exact .fail hbr

/-- The update of a name that keeps the relation. -/
theorem RefT.modify_ext {α : Type} {bad : α → Prop} {n : String} {w : Value}
    (hn : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w))
    {k₁ k₂ : PUnit → TM E α} (h : ∀ u, RefT R R bad (k₁ u) (k₂ u)) :
    RefT R R bad (modify (fun x => x.extend n w) >>= k₁)
      (modify (fun x => x.extend n w) >>= k₂) :=
  fun e₁ e₂ hR => h _ _ _ (hn e₁ e₂ w hR)

/-- A tree lifted into the state refines itself. -/
theorem RefT.lift {α : Type} {bad : α → Prop} (t : CallTree E α) :
    RefT R R bad (StateT.lift t : TM E α) (StateT.lift t) := by
  intro e₁ e₂ hR
  change Rutt _ _ _ _ (t.bind fun a => .ret (a, e₂)) (t.bind fun a => .ret (a, e₁))
  refine rutt_bind (RR' := fun a b => a = b) (Fail' := fun _ => False) (rutt_refl (fun _ => rfl) t)
    (fun a b hab => ?_) (fun _ hf => hf.elim)
  subst hab
  exact .ret ⟨rfl, hR⟩

/-- Refinement under weaker relations. -/
theorem RefT.mono {α : Type} {P P' Q Q' : Env → Env → Prop} {bad : α → Prop}
    {tgt src : TM E α} (h : RefT P Q bad tgt src) (hP : ∀ a b, P' a b → P a b)
    (hQ : ∀ a b, Q a b → Q' a b) : RefT P' Q' bad tgt src :=
  fun e₁ e₂ hp => rutt_mono (fun _ _ h => ⟨h.1, hQ _ _ h.2⟩) (h e₁ e₂ (hP _ _ hp))

end RefT

/-- One step of a `RefT` proof between two readings of the same shape: identical leaves, a
    failed source, a hypothesis, an update that keeps the relation, or a sequence of two related
    readings followed by a case split on the outcome. -/
scoped syntax "relT_step" : tactic

macro_rules
  | `(tactic| relT_step) => `(tactic| first
      | exact RefT.pure _
      | (apply RefT.of_bad; intro _; exact ⟨_, rfl, _, rfl⟩)
      | solve_by_elim (maxDepth := 2)
      | (refine RefT.modify_ext (by assumption) (fun _ => ?_); relT_step)
      | (refine RefT.bind (badα := IsErr) (by solve_by_elim (maxDepth := 2)) (fun o ho => ?_)
            (fun a ha s => by
              obtain ⟨m, hm⟩ := ha; subst hm
              first
                | exact ⟨_, rfl, _, rfl⟩
                | (split <;>
                    first
                    | exact ⟨_, rfl, _, rfl⟩
                    | (exfalso; simp_all)
                    | simp_all [IsErr]))
         split <;> first | relT_step | (exfalso; simp_all [IsErr]))
      | (split <;> relT_step))

/-- One step of a `RefT` proof of a counted loop: the lower bound, then the upper bound, with the
    case split on the value of the lower bound at a failed upper bound. -/
scoped syntax "loop_head_step" : tactic

macro_rules
  | `(tactic| loop_head_step) => `(tactic|
      (refine RefT.bind (badα := IsErr) (by solve_by_elim (maxDepth := 2)) (fun o ho => ?_)
          (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨_, rfl, _, rfl⟩)
       split
       · relT_step
       · refine RefT.bind (badα := IsErr) (by solve_by_elim (maxDepth := 2)) (fun o ho => ?_)
           (fun a ha s => by
             obtain ⟨m, hm⟩ := ha; subst hm
             cases (‹Value›) <;> exact ⟨_, rfl, _, rfl⟩)
         split <;> first | relT_step | (exfalso; simp_all [IsErr])
       · relT_step))

/-! ## Loops -/

section Loops

variable {R : Env → Env → Prop} {bt : TreeTable E}

/-- The counted loop readings refine each other when the bodies do. -/
theorem denoteForLoopT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel lo hi, RefET R (denoteForLoopT bt fuel v lo hi b₁)
      (denoteForLoopT bt fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ↓reduceIte]; relT_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relT_step

/-- The reversed counted loop readings refine each other when the bodies do. -/
theorem denoteForLoopRevT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel lo hi, RefET R (denoteForLoopRevT bt fuel v lo hi b₁)
      (denoteForLoopRevT bt fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ↓reduceIte]; relT_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relT_step

/-- The counted loop (statement form) readings refine each other when the bodies do. -/
theorem denoteForLoopOrigT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel lo hi, RefET R (denoteForLoopOrigT bt fuel v lo hi b₁)
      (denoteForLoopOrigT bt fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopOrigT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ↓reduceIte]; relT_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopOrigT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relT_step

/-- The reversed counted loop (statement form) readings refine each other when the bodies do. -/
theorem denoteForLoopRevOrigT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel lo hi, RefET R (denoteForLoopRevOrigT bt fuel v lo hi b₁)
      (denoteForLoopRevOrigT bt fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevOrigT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ↓reduceIte]; relT_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevOrigT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relT_step

/-- The counted loop with a return readings refine each other when the bodies do. -/
theorem denoteForLoopReturnT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel lo hi, RefET R (denoteForLoopReturnT bt fuel v lo hi b₁)
      (denoteForLoopReturnT bt fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopReturnT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ↓reduceIte]; relT_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopReturnT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relT_step

/-- The reversed counted loop with a return readings refine each other when the bodies do. -/
theorem denoteForLoopRevReturnT_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel lo hi, RefET R (denoteForLoopRevReturnT bt fuel v lo hi b₁)
      (denoteForLoopRevReturnT bt fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevReturnT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ↓reduceIte]; relT_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevReturnT
    by_cases hl : lo ≥ hi
    · simp only [hl, ite_true]; relT_step
    · simp only [hl, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      relT_step

/-- The `while` readings refine each other when the conditions and the bodies do. -/
theorem denoteWhileT_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefET R (denoteT bt fuel c₁) (denoteT bt fuel c₂))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel, RefET R (denoteWhileT bt fuel c₁ b₁) (denoteWhileT bt fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileT; simp only [ite_true]; relT_step
  | succ n ih =>
    unfold denoteWhileT
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    relT_step

/-- The `while` (statement form) readings refine each other when the conditions and the bodies
    do. -/
theorem denoteWhileOrigT_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefET R (denoteT bt fuel c₁) (denoteT bt fuel c₂))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel, RefET R (denoteWhileOrigT bt fuel c₁ b₁) (denoteWhileOrigT bt fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileOrigT; simp only [ite_true]; relT_step
  | succ n ih =>
    unfold denoteWhileOrigT
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    relT_step

/-- The `while` with a return readings refine each other when the conditions and the bodies do. -/
theorem denoteWhileReturnT_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefET R (denoteT bt fuel c₁) (denoteT bt fuel c₂))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) :
    ∀ fuel, RefET R (denoteWhileReturnT bt fuel c₁ b₁) (denoteWhileReturnT bt fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileReturnT; simp only [ite_true]; relT_step
  | succ n ih =>
    unfold denoteWhileReturnT
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    relT_step

/-- The argument readings refine each other when each argument refines itself. -/
theorem denoteArgsT_rel (args : List ImpExpr) (fuel : Nat)
    (ih : ∀ a ∈ args, RefET R (denoteT bt fuel a) (denoteT bt fuel a)) :
    RefT R R (fun o => o = none) (denoteArgsT bt fuel args) (denoteArgsT bt fuel args) := by
  induction args with
  | nil => simp only [denoteArgsT]; exact RefT.pure _
  | cons a as iha =>
    simp only [denoteArgsT]
    refine RefT.bind (badα := IsErr) (ih a List.mem_cons_self) (fun o ho => ?_)
      (fun o ho s => by obtain ⟨m, hm⟩ := ho; subst hm; exact ⟨_, rfl, rfl⟩)
    split
    · exact RefT.pure _
    · exact RefT.bind (badα := fun o => o = none)
        (iha fun b hb => ih b (List.mem_cons_of_mem a hb))
        (fun _ _ => RefT.pure _) (fun r hr s => by subst hr; exact ⟨_, rfl, rfl⟩)
    · exact RefT.pure _

end Loops

/-! ## The frame of an expression -/

section Frame

variable {R : Env → Env → Prop} (bt : TreeTable E) (rd bd ok : String → Bool)

/-- **The frame of an expression.** Let `R` relate environments that agree on every variable
    `x` with `rd x`, and keep `R` under the extension of both at a name with `bd` by one value.
    An expression in `frameOk rd bd ok` refines itself from `R`-related environments. -/
theorem denoteT_frame
    (hrd : ∀ e₁ e₂ x, R e₁ e₂ → rd x = true → e₁ x = e₂ x)
    (hbd : ∀ e₁ e₂ n w, R e₁ e₂ → bd n = true → R (e₁.extend n w) (e₂.extend n w))
    (e : ImpExpr) :
    frameOk rd bd ok e = true → ∀ fuel, RefET R (denoteT bt fuel e) (denoteT bt fuel e) := by
  have ext : ∀ n, bd n = true → ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w) :=
    fun n hn e₁ e₂ w h => hbd e₁ e₂ n w h hn
  induction e using ImpExpr.ind with
  | var x =>
    intro hK fuel e₁ e₂ hR
    simp only [frameOk] at hK
    cases h : e₂ x with
    | none =>
      rw [denoteT_var_run_none bt fuel x e₂ h]
      exact .fail ⟨_, rfl⟩
    | some v =>
      rw [denoteT_var_run bt fuel x e₂ v h,
        denoteT_var_run bt fuel x e₁ v (by rw [hrd e₁ e₂ x hR hK]; exact h)]
      exact .ret ⟨rfl, hR⟩
  | app g args ih =>
    intro hK fuel
    simp only [frameOk, frameOk.okList_eq, Bool.and_eq_true, List.all_eq_true] at hK
    simp only [denoteT]
    unfold denoteAppT
    refine RefT.bind (badα := fun o => o = none)
      (denoteArgsT_rel args fuel fun a ha => ih a ha (hK.2 a ha) fuel)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl, _, rfl⟩)
    split
    · refine RefT.bind (badα := fun _ => False) (RefT.lift _) (fun r _ => ?_)
        (fun _ h => h.elim)
      split <;> exact RefT.pure _
    · exact absurd rfl hr
  | tuple es ih =>
    intro hK fuel
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true] at hK
    simp only [denoteT]
    refine RefT.bind (badα := fun o => o = none)
      (denoteArgsT_rel es fuel fun a ha => ih a ha (hK a ha) fuel)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl, _, rfl⟩)
    split
    · exact RefT.pure _
    · exact absurd rfl hr
  | match_ scrut arms _ _ => intro hK; simp [frameOk] at hK
  | lam qs b _ =>
    intro _ fuel
    exact RefT.of_bad fun _ => by simp only [denoteT]; exact ⟨_, rfl, _, rfl⟩
  | forLoop v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := denoteForLoopOrigT_rel (bt := bt) (ext v hK.1.1.1) (ihb hK.2)
    simp only [denoteT]
    loop_head_step
  | forLoopRev v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := denoteForLoopRevOrigT_rel (bt := bt) (ext v hK.1.1.1) (ihb hK.2)
    simp only [denoteT]
    loop_head_step
  | forFold v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := denoteForLoopT_rel (bt := bt) (ext v hK.1.1.1) (ihb hK.2)
    simp only [denoteT]
    loop_head_step
  | forFoldRev v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := denoteForLoopRevT_rel (bt := bt) (ext v hK.1.1.1) (ihb hK.2)
    simp only [denoteT]
    loop_head_step
  | forFoldReturn v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := denoteForLoopReturnT_rel (bt := bt) (ext v hK.1.1.1) (ihb hK.2)
    simp only [denoteT]
    loop_head_step
  | forFoldRevReturn v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := denoteForLoopRevReturnT_rel (bt := bt) (ext v hK.1.1.1) (ihb hK.2)
    simp only [denoteT]
    loop_head_step
  | whileLoop c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [denoteT]
    exact denoteWhileOrigT_rel (ihc hK.1) (ihb hK.2) fuel
  | whileFold c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [denoteT]
    exact denoteWhileT_rel (ihc hK.1) (ihb hK.2) fuel
  | whileFoldReturn c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [denoteT]
    exact denoteWhileReturnT_rel (ihc hK.1) (ihb hK.2) fuel
  | letBind n v b ihv ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hn := ext n hK.1.1
    have hv := ihv hK.1.2
    have hb := ihb hK.2
    simp only [denoteT]
    relT_step
  | assign n rhs ih =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hn := ext n hK.1
    have hr := ih hK.2
    simp only [denoteT]
    relT_step
  | seq a b iha ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have ha := iha hK.1
    have hb := ihb hK.2
    simp only [denoteT]
    relT_step
  | ifThenElse c t e ihc iht ihe =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have h1 := ihc hK.1.1
    have h2 := iht hK.1.2
    have h3 := ihe hK.2
    simp only [denoteT]
    relT_step
  | proj e _ ih | borrow e ih | deref e ih | break_some e ih | earlyReturn e ih
  | questionMark e ih | cfBreak e ih | cfContinue e ih | cfBreakContinue e ih
  | typeAscription e _ ih =>
    intro hK fuel
    simp only [frameOk] at hK
    have h := ih hK
    simp only [denoteT]
    relT_step
  | _ =>
    intro _ fuel
    simp only [denoteT]
    relT_step

/-- **A reading keeps the names it does not bind**: every leaf of the reading of an expression
    that binds no `x` whose outcome is not an error has the value of `x` it started from. -/
theorem denoteT_keeps {x : String} (e : ImpExpr)
    (h : frameOk (fun _ => true) (fun n => n != x) (fun _ => true) e = true) (fuel : Nat)
    (env : Env) :
    LeafP (fun r : Outcome × Env => ¬ IsErr r.1 → r.2 x = env x) (denoteT bt fuel e env) := by
  have := denoteT_frame (R := fun e₁ e₂ => e₁ = e₂ ∧ e₂ x = env x) bt (fun _ => true)
    (fun n => n != x) (fun _ => true) (fun e₁ e₂ y hR _ => by rw [hR.1])
    (fun e₁ e₂ n w hR hn => ⟨by rw [hR.1], by
      have hne : x ≠ n := fun h' => by simp [h'] at hn
      rw [Env.extend_other _ _ _ _ hne]; exact hR.2⟩)
    e h fuel env env ⟨rfl, rfl⟩
  exact rutt_leafP (fun r₁ r₂ hr _ => hr.2.2) (fun r hf hne => absurd hf hne) this

end Frame

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm
