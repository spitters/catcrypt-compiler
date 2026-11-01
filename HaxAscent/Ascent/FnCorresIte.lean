/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Corres

/-!
# A function correspondence of a conditional, branch by branch

A literal whose top is a conditional `.ifThenElse c t e` corresponds to the function
`fun a => if cv a then f₁ a else f₂ a` when the condition `c` returns `.bool (cv a)` from
`entry a` without changing the environment, `t` corresponds to `f₁` under the guard
strengthened by `cv a = true`, and `e` to `f₂` under the guard strengthened by
`cv a = false`. The two branches are then separate function correspondences, so the ascent
of a step whose top is a case split can be stated and proved one branch at a time.

## Main results

* `fnCorres_ifThenElse`: the correspondence of the conditional from those of its branches.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

variable {bi : Builtins} {A β : Type} [HaxEnc β] {entry : A → Env} {G : A → Prop}

/-- **Conditional, branch by branch.** If the condition `c` returns `.bool (cv a)` from
    `entry a` and leaves the environment `entry a`, and the branches correspond to `f₁`
    under `G a ∧ cv a = true` and to `f₂` under `G a ∧ cv a = false`, then the conditional
    corresponds to `fun a => if cv a then f₁ a else f₂ a` under `G`. -/
theorem fnCorres_ifThenElse {c t e : ImpExpr} {cv : A → Bool} {f₁ f₂ : A → β}
    (hc : Corres bi (fun env a => env = entry a) G c (fun a => .bool (cv a))
      (fun env a => env = entry a))
    (ht : FnCorres bi t entry (fun a => G a ∧ cv a = true) f₁)
    (he : FnCorres bi e entry (fun a => G a ∧ cv a = false) f₂) :
    FnCorres bi (.ifThenElse c t e) entry G (fun a => if cv a then f₁ a else f₂ a) := by
  intro a hG
  obtain ⟨fuel₀, env', henv, hrun⟩ := hc (entry a) a rfl hG
  subst henv
  cases hb : cv a
  · obtain ⟨fuel₁, h₂⟩ := he a ⟨hG, hb⟩
    refine ⟨max fuel₀ fuel₁, fun fuel hf => ?_⟩
    have hcr : denote' bi fuel c (entry a) = (.val (.bool false), entry a) := by
      simpa [hb] using hrun fuel (Nat.le_trans (Nat.le_max_left _ _) hf)
    rw [denote'_ifThenElse (h := hcr)]
    simpa [hb] using h₂ fuel (Nat.le_trans (Nat.le_max_right _ _) hf)
  · obtain ⟨fuel₁, h₁⟩ := ht a ⟨hG, hb⟩
    refine ⟨max fuel₀ fuel₁, fun fuel hf => ?_⟩
    have hcr : denote' bi fuel c (entry a) = (.val (.bool true), entry a) := by
      simpa [hb] using hrun fuel (Nat.le_trans (Nat.le_max_left _ _) hf)
    rw [denote'_ifThenElse (h := hcr)]
    simpa [hb] using h₁ fuel (Nat.le_trans (Nat.le_max_right _ _) hf)

end Hax.Ascent
