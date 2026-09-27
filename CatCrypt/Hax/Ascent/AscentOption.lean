/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.EarlyExit

/-!
# `Option` values and assignment in the `denote'` correspondence

hax-lean builds an `Option` by the calls `Some` and `None` and reads it by a `match`
with a `somePat` and a `nonePat` arm.  This module gives the `Corres` rules for these
constructs and for `assign`.

The match rule `corres_optMatch` takes the scrutinee variable holding
`.option (O σ)` under the entry relation; the `Some` arm runs from the entry
environment extended at the binder by the payload, the `None` arm from the entry
environment.  `corres_some` and `corres_none` are the leaf calls, under a builtin
table that builds `Option` values; `corres_optBindSome` and `corres_optBindNone` are
their bindings `let o = Some x` and `let o = None`.

## Main results

* `denote'_optMatch` — the one-step equation of the `Option` match
* `corres_optMatch`, `corresX_optMatch` — the `Option` match under `Corres` and
  `CorresX`
* `corres_some`, `corres_none`, `corres_optBindSome`, `corres_optBindNone` — `Some`,
  `None` and their bindings
* `corres_assign` — assignment
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

section OptSteps

variable (bi : Builtins) (fuel : Nat)

/-- The match on an `Option` variable holding `ox` runs the `Some` arm with its binder
    bound to the payload, or the `None` arm. -/
theorem denote'_optMatch {o v : String} {e2 e1 : ImpExpr} {env : Env} {ox : Option Value}
    (ho : env o = some (.option ox)) :
    denote' bi fuel (.match_ (.var o) [(.somePat (.varPat v), e2), (.nonePat, e1)]) env =
      match ox with
      | some x => denote' bi fuel e2 (env.extend v x)
      | none => denote' bi fuel e1 env := by
  cases ox <;>
    simp only [denote', denoteMatchArms', stateM_bind_apply, stateM_get_apply, ho] <;>
    rfl

end OptSteps

section OptRules

variable {S : Type} {bi : Builtins}

/-- **`Option` match.**  The scrutinee variable holds `.option (O σ)`; the `Some` arm
    runs from the entry environment extended at the binder by the payload, the `None`
    arm from the entry environment. -/
theorem corres_optMatch {P Q : Env → S → Prop} {G : S → Prop} {o v : String}
    {e2 e1 : ImpExpr} {O : S → Option Value} {V : S → Value}
    (ho : ∀ env σ, P env σ → G σ → env o = some (.option (O σ)))
    (hs : Corres bi (fun env σ => ∃ env₀ x, P env₀ σ ∧ O σ = some x ∧ env = env₀.extend v x)
      (fun σ => G σ ∧ (O σ).isSome = true) e2 V Q)
    (hn : Corres bi P (fun σ => G σ ∧ O σ = none) e1 V Q) :
    Corres bi P G (.match_ (.var o) [(.somePat (.varPat v), e2), (.nonePat, e1)]) V Q := by
  intro env σ hP hG
  have h := ho env σ hP hG
  cases hO : O σ with
  | some x =>
    rw [hO] at h
    obtain ⟨f₀, env', hQ, r⟩ := hs (env.extend v x) σ ⟨env, x, hP, hO, rfl⟩ ⟨hG, by simp [hO]⟩
    exact ⟨f₀, env', hQ, fun fuel hf => by rw [denote'_optMatch bi fuel h]; exact r fuel hf⟩
  | none =>
    rw [hO] at h
    obtain ⟨f₀, env', hQ, r⟩ := hn env σ hP ⟨hG, hO⟩
    exact ⟨f₀, env', hQ, fun fuel hf => by rw [denote'_optMatch bi fuel h]; exact r fuel hf⟩

/-- **`Option` match at the exception level.** -/
theorem corresX_optMatch {P Q : Env → S → Prop} {G : S → Prop} {o v : String}
    {e2 e1 : ImpExpr} {O : S → Option Value} {R : S → Except Value Value}
    (ho : ∀ env σ, P env σ → G σ → env o = some (.option (O σ)))
    (hs : CorresX bi (fun env σ => ∃ env₀ x, P env₀ σ ∧ O σ = some x ∧ env = env₀.extend v x)
      (fun σ => G σ ∧ (O σ).isSome = true) e2 R Q)
    (hn : CorresX bi P (fun σ => G σ ∧ O σ = none) e1 R Q) :
    CorresX bi P G (.match_ (.var o) [(.somePat (.varPat v), e2), (.nonePat, e1)]) R Q :=
  corres_optMatch ho hs hn

/-- **`Some`.**  The call `Some x` returns the `Option` of the value of `x`. -/
theorem corres_some {P Q : Env → S → Prop} {G : S → Prop} {x : ImpExpr} {V : S → Value}
    (hS : ∀ v, bi "Some" [v] = some (.option (some v))) (h : Corres bi P G x V Q)
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    Corres bi P G (.app "Some" [x]) (fun σ => .option (some (V σ))) Q :=
  corres_app (corresArgs_cons h hplain (corresArgs_nil _ _)) fun σ _ => hS (V σ)

/-- **`None`.**  The call `None` returns the empty `Option`. -/
theorem corres_none (P : Env → S → Prop) (G : S → Prop)
    (hN : bi "None" [] = some (.option none)) :
    Corres bi P G (.app "None" []) (fun _ => .option none) P :=
  corres_app (corresArgs_nil P G) fun _ _ => hN

/-- **`let o = Some x`.**  The body runs from the exit environment of `x` extended at
    `o` by the `Option` of its value. -/
theorem corres_optBindSome {P Q₁ P₂ Q : Env → S → Prop} {G : S → Prop} {o : String}
    {x body : ImpExpr} {V₁ V : S → Value} (hS : ∀ v, bi "Some" [v] = some (.option (some v)))
    (hx : Corres bi P G x V₁ Q₁) (hplain : ∀ σ, G σ → (V₁ σ).isControlFlow = false)
    (hlink : ∀ env σ, Q₁ env σ → G σ → P₂ (env.extend o (.option (some (V₁ σ)))) σ)
    (hbody : Corres bi P₂ G body V Q) :
    Corres bi P G (.letBind o (.app "Some" [x]) body) V Q :=
  corres_letBind (corres_some hS hx hplain) (fun _ _ => rfl) hlink hbody

/-- **`let o = None`.**  The body runs from the entry environment extended at `o` by
    the empty `Option`. -/
theorem corres_optBindNone {P P₂ Q : Env → S → Prop} {G : S → Prop} {o : String}
    {body : ImpExpr} {V : S → Value} (hN : bi "None" [] = some (.option none))
    (hlink : ∀ env σ, P env σ → G σ → P₂ (env.extend o (.option none)) σ)
    (hbody : Corres bi P₂ G body V Q) :
    Corres bi P G (.letBind o (.app "None" []) body) V Q :=
  corres_letBind (corres_none P G hN) (fun _ _ => rfl) hlink hbody

/-- **Assignment.**  The value of the right-hand side is bound at the name, and the
    assignment returns `.unit`. -/
theorem corres_assign {P Q₁ : Env → S → Prop} {G : S → Prop} {x : String} {rhs : ImpExpr}
    {V₁ : S → Value} (h : Corres bi P G rhs V₁ Q₁)
    (hplain : ∀ σ, G σ → (V₁ σ).isControlFlow = false) :
    Corres bi P G (.assign x rhs) (fun _ => .unit)
      (fun env σ => ∃ env₁, Q₁ env₁ σ ∧ env = env₁.extend x (V₁ σ)) := by
  intro env σ hP hG
  obtain ⟨f₀, e₁, hQ, r⟩ := h env σ hP hG
  exact ⟨f₀, _, ⟨e₁, hQ, rfl⟩, fun fuel hf => denote'_assign bi fuel (r fuel hf) (hplain σ hG)⟩

end OptRules

end Hax.Ascent
