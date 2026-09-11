/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen


@[expose] public section
set_option autoImplicit false

/-!
# Relational Hoare via the product program on the `Std.Do` WP (Route A)

`Ascent/RunBlockMvcgen.lean` places the total machine on Lean's `Std.Do`
weakest-precondition metatheory, where `mvcgen` walks a **unary** state monad
`StateM S`. This module shows that the same unary `mvcgen` machinery — with **no
new framework** — already discharges a **relational** Hoare goal about two
programs, via *self-composition* / the **product program**.

## Route A (self-composition)

For two deterministic state programs `c₁ : StateM S₁ α` and `c₂ : StateM S₂ β`,
the **product program** `prod c₁ c₂ : StateM (S₁ × S₂) (α × β)` runs `c₁` on the
first state component and `c₂` on the second. A relational Hoare judgment "if the
inputs are related by `Φ` then the outputs/final-states are related by `Ψ`" is
*exactly* a **unary** `Std.Do` triple over `prod c₁ c₂`. Hence `mvcgen` — reused
verbatim — proves relational goals on the deterministic state fragment.

* `prod` / `prod_run` — the product program and its run equation (`rfl`).
* `RelTriple` — the relational Hoare judgment on the deterministic product.
* `relTriple_iff_stddo` — **the bridge**: `RelTriple Φ c₁ c₂ Ψ` *is* the unary
  `Std.Do` triple `⦃⌜Φ⌝⦄ prod c₁ c₂ ⦃⇓ p s => ⌜Ψ p s⌝⦄`. Forward is the `StateM`
  adequacy lemma `StateM.of_wp_run_eq`; reverse strengthens the precondition of
  the product spec `Spec.wp_prod`.
* `Spec.wp_prod` — the `@[spec]` WP of the product program, so `mvcgen` walks it.
* `prod_demo` — a concrete relational goal (`c₁ = c₂ = modify (·+1)`, pre/post
  `fst = snd`) proved by rewriting through the bridge and firing `mvcgen`.

This is the deterministic instance where the *independent* product **is** the
relation. The **probabilistic coupling** case is out of scope for Route A: there
the independent product `μ₁ ⊗ μ₂` is generally *not* the coupling that witnesses a
relational lifting, so a separate route is needed — a relational lifting `T̂`
(a coupling monad / `∃`-coupling over the product) on top of the WP, rather than
the plain product monad reused here.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do

/-! ## 1. The product program

`prod c₁ c₂` runs `c₁` on the first state component and `c₂` on the second,
threading both and pairing their results. This is the deterministic
*self-composition* / product program: a single `StateM (S₁ × S₂)` computation
whose run is the two independent runs, side by side. -/

/-- **The product program.** Run `c₁` on `.1` and `c₂` on `.2`, threading both
    states and pairing the two return values. -/
def prod {S₁ S₂ α β : Type} (c₁ : StateM S₁ α) (c₂ : StateM S₂ β) :
    StateM (S₁ × S₂) (α × β) :=
  StateT.mk (fun s =>
    (((c₁.run s.1).1, (c₂.run s.2).1), ((c₁.run s.1).2, (c₂.run s.2).2)))

/-- **The run of the product program.** From `(s₁, s₂)` it returns the pair of
    the two independent return values and the pair of the two final states. -/
@[simp] theorem prod_run {S₁ S₂ α β : Type} (c₁ : StateM S₁ α) (c₂ : StateM S₂ β)
    (s₁ : S₁) (s₂ : S₂) :
    (prod c₁ c₂).run (s₁, s₂)
      = (((c₁.run s₁).1, (c₂.run s₂).1), ((c₁.run s₁).2, (c₂.run s₂).2)) := rfl

/-! ## 2. The relational triple as a unary `Std.Do` triple

`RelTriple Φ c₁ c₂ Ψ` is the standard relational Hoare judgment on the
deterministic product: for related inputs (`Φ`), the paired outputs and paired
final states are related (`Ψ`). `relTriple_iff_stddo` shows it **is** the unary
`Std.Do` triple over `prod c₁ c₂` — no relational framework, just the product. -/

/-- **The relational Hoare judgment.** For every pair of initial states related by
    `Φ`, the paired return values and paired final states of the two runs are
    related by `Ψ`. This is the deterministic relational Hoare triple, phrased on
    the product `c₁ × c₂`. -/
def RelTriple {S₁ S₂ α β : Type} (Φ : S₁ × S₂ → Prop)
    (c₁ : StateM S₁ α) (c₂ : StateM S₂ β)
    (Ψ : α × β → S₁ × S₂ → Prop) : Prop :=
  ∀ s₁ s₂, Φ (s₁, s₂) →
    Ψ ((c₁.run s₁).1, (c₂.run s₂).1) ((c₁.run s₁).2, (c₂.run s₂).2)

/-- **The product WP equation.** The weakest precondition of `prod c₁ c₂` at post
    `Q` is the post evaluated at the paired return values and paired final states.
    Both sides reduce definitionally (`rfl`), since `prod` is a `StateT.mk` atom. -/
theorem wp_prod_eq {S₁ S₂ α β : Type} (c₁ : StateM S₁ α) (c₂ : StateM S₂ β)
    (Q : PostCond (α × β) (.arg (S₁ × S₂) .pure)) :
    wp⟦prod c₁ c₂ : StateM (S₁ × S₂) (α × β)⟧ Q
      = fun s => Q.1 ((c₁.run s.1).1, (c₂.run s.2).1)
                     ((c₁.run s.1).2, (c₂.run s.2).2) := rfl

/-- **The product `@[spec]` triple.** The Hoare triple for `prod c₁ c₂`: its
    precondition is the weakest precondition (`Q` at the paired outputs/states).
    `mvcgen` fires this to walk a product goal — the unary WP of the product IS
    the relational reasoning step. Proved by reflexivity of the WP (`wp_prod_eq`). -/
@[spec]
theorem Spec.wp_prod {S₁ S₂ α β : Type} (c₁ : StateM S₁ α) (c₂ : StateM S₂ β)
    (Q : PostCond (α × β) (.arg (S₁ × S₂) .pure)) :
    Triple (prod c₁ c₂ : StateM (S₁ × S₂) (α × β))
      (fun s => Q.1 ((c₁.run s.1).1, (c₂.run s.2).1)
                    ((c₁.run s.1).2, (c₂.run s.2).2))
      Q :=
  Triple.iff.mpr (SPred.entails.refl _)

/-- **The bridge (Route A).** The relational Hoare judgment `RelTriple Φ c₁ c₂ Ψ`
    IS the unary `Std.Do` weakest-precondition triple over the product program
    `prod c₁ c₂`. Forward strengthens the product spec `Spec.wp_prod`; reverse
    evaluates the WP at a concrete initial state via the `StateM` adequacy lemma
    `StateM.of_wp_run_eq`. So `mvcgen`, which discharges the right-hand triple,
    proves relational goals on the deterministic state fragment. -/
theorem relTriple_iff_stddo {S₁ S₂ α β : Type} (Φ : S₁ × S₂ → Prop)
    (c₁ : StateM S₁ α) (c₂ : StateM S₂ β) (Ψ : α × β → S₁ × S₂ → Prop) :
    RelTriple Φ c₁ c₂ Ψ ↔
      (⦃fun s => ⌜Φ s⌝⦄ (prod c₁ c₂ : StateM (S₁ × S₂) (α × β))
        ⦃⇓ p s => ⌜Ψ p s⌝⦄) := by
  constructor
  · -- forward: strengthen the product spec's precondition using `RelTriple`.
    intro h
    refine Triple.iff.mpr ?_
    simp only [SPred.entails_1]
    intro s hΦ
    exact h s.1 s.2 hΦ
  · -- reverse: evaluate the WP at the concrete state `(s₁, s₂)` via adequacy.
    intro h s₁ s₂ hΦ
    refine StateM.of_wp_run_eq (prod_run c₁ c₂ s₁ s₂) (fun p => Ψ p.1 p.2) ?_
    exact fun _ => h (s₁, s₂) hΦ

/-! ## 3. Demonstration: `mvcgen` fires on a relational goal

Two concrete deterministic programs `c₁ = c₂ = modify (· + 1) : StateM ℕ Unit`,
with the relational pre/post "the two states are equal". The `RelTriple` is
proved by rewriting through the bridge `relTriple_iff_stddo` to the unary product
triple, then firing `mvcgen`: it walks `prod c₁ c₂` via the `@[spec]` product WP
`Spec.wp_prod`, and the residual VC (`s.1 = s.2 → s.1 + 1 = s.2 + 1`) is closed by
`omega`. This is the concrete witness that unary `mvcgen` extends to relational
reasoning on the deterministic fragment with no new framework. -/

/-- **`mvcgen` discharges a relational goal.** The relational Hoare triple
    "starting from equal states, `modify (·+1)` on each keeps the states equal" is
    proved by rewriting to the unary product triple (`relTriple_iff_stddo`) and
    firing `mvcgen`. `mvcgen` walks the product program through `Spec.wp_prod`; the
    residual arithmetic VC is `omega`. Route A: unary `mvcgen` proves a relational
    goal via the product program. -/
theorem prod_demo :
    RelTriple (fun p => p.1 = p.2)
      (modify (· + 1) : StateM Nat Unit)
      (modify (· + 1) : StateM Nat Unit)
      (fun _ p => p.1 = p.2) := by
  rw [relTriple_iff_stddo]
  mvcgen [prod]
  rename_i s h
  simp_all [StateT.run_modify]

end CatCrypt.Crypto.SecureCompilation.Ascent
