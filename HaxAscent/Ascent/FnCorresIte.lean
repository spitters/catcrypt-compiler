/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.AscendHax

/-!
# A function correspondence of a conditional, branch by branch

A literal whose top is a conditional `.ifThenElse c t e` corresponds to the function
`fun a => if cv a then f₁ a else f₂ a` when the condition `c` returns `.bool (cv a)` from
`entry a` without changing the environment, `t` corresponds to `f₁` under the guard
strengthened by `cv a = true`, and `e` to `f₂` under the guard strengthened by
`cv a = false`. The two branches are then separate function correspondences, so the ascent
of a step whose top is a case split can be stated and proved one branch at a time.

The reified literal is in A-normal form: the condition of a conditional is a variable bound
by a chain of `let`s before it. A `let` whose bound expression leaves the environment is
passed by extending the entry environment at its name, so the conditional below the chain
is reached with an entry that holds the temporaries.

The branch correspondences may bind their parameters in different orders; a parameter list
with distinct names binds the same environment in every order, so the entries agree.

## Main results

* `fnCorres_ifThenElse`: the correspondence of the conditional from those of its branches.
* `fnCorres_letBind`: the correspondence of `let x := val; body` from that of `body` over
  the entry extended at `x`.
* `bindParams_perm`: two orders of a parameter list with distinct names bind the same
  environment.
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

/-- **`let`, over the extended entry.** If `val` returns `V a` from `entry a`, a value that
    is not a control-flow value, and leaves the environment `entry a`, and `body`
    corresponds to `f` from the entry extended by `x ↦ V a`, then `let x := val; body`
    corresponds to `f` from `entry`. -/
theorem fnCorres_letBind {x : String} {val body : ImpExpr} {V : A → Value} {f : A → β}
    (hval : Corres bi (fun env a => env = entry a) G val V (fun env a => env = entry a))
    (hplain : ∀ a, G a → (V a).isControlFlow = false)
    (hbody : FnCorres bi body (fun a => (entry a).extend x (V a)) G f) :
    FnCorres bi (.letBind x val body) entry G f := by
  intro a hG
  obtain ⟨fuel₀, env', henv, hrun⟩ := hval (entry a) a rfl hG
  subst henv
  obtain ⟨fuel₁, hb⟩ := hbody a hG
  refine ⟨max fuel₀ fuel₁, fun fuel hf => ?_⟩
  rw [denote'_letBind (h := hrun fuel (Nat.le_trans (Nat.le_max_left _ _) hf)) (hv := hplain a hG)]
  exact hb fuel (Nat.le_trans (Nat.le_max_right _ _) hf)

/-- Two orders of a binding list with distinct names give the same lookup. -/
theorem bindLookup_perm {ps qs : List (String × Value)} (hp : ps.Perm qs)
    (hn : (ps.map Prod.fst).Nodup) : bindLookup ps = bindLookup qs := by
  induction hp with
  | nil => rfl
  | cons p _ ih =>
    obtain ⟨k, v⟩ := p
    have ht := ih (List.nodup_cons.mp hn).2
    funext x
    simp only [bindLookup_cons, ht]
  | swap p q l =>
    obtain ⟨k, v⟩ := p
    obtain ⟨k', v'⟩ := q
    have hne : k ≠ k' := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    funext x
    simp only [bindLookup_cons]
    by_cases h1 : x = k <;> by_cases h2 : x = k' <;> simp_all
  | trans h₁ _ ih₁ ih₂ =>
    rw [ih₁ hn, ih₂ ((h₁.map Prod.fst).nodup_iff.mp hn)]

/-- **Parameter order.** Two orders of a parameter list with distinct names bind the same
    environment. -/
theorem bindParams_perm {ps qs : List (String × Value)} (hp : ps.Perm qs)
    (hn : (ps.map Prod.fst).Nodup) : bindParams ps = bindParams qs := by
  funext x
  rw [bindParams_apply, bindParams_apply, bindLookup_perm hp hn]

end Hax.Ascent
