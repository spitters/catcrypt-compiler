/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.EarlyExit
public import HaxLean.Phase.Monomorphise

/-!
# Function correspondences of monomorphised literals

The literal of a Rust function generic over a trait bound calls the trait's methods by
their bare names. `Hax.Monomorphise.monomorphise tbl insts` renames each such call to the
function implementing the method at the instances `insts`. The specialised literal under a
builtin table `bi` runs as the generic literal under `withInstances bi tbl insts`, up to the
text of an error (`Hax.Monomorphise.denote'_monomorphise`). A function correspondence
concludes that a run returns a value from some fuel on, never an error, so the specialised
literal under `bi` and the generic literal under the extended table carry the same
function correspondences.

## Main results

* `fnCorres_monomorphise_iff`, `fnCorresX_monomorphise_iff` — a function correspondence of
  the specialised literal under `bi` is one of the generic literal under
  `withInstances bi tbl insts`, and conversely
* `fnCorres_of_monomorphise`, `fnCorresX_of_monomorphise` — the same, from an equation
  naming the specialised literal
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

open Hax.Monomorphise (ErrEq MonoTable withInstances monomorphise eraseErr eraseErr_eq)

/-- Two runs that agree up to the text of an error return the same outcome from the same
    environment when one of them returns an outcome that is not an error. -/
theorem outcome_eq_of_errEq {m₁ m₂ : StateM Env Outcome} (h : ErrEq m₁ m₂) (env : Env)
    (ho : ∀ a, (m₂.run env).1 ≠ .err a) : (m₁.run env).1 = (m₂.run env).1 := by
  rcases eraseErr_eq (h env).2 with h1 | ⟨a, b, _, h2⟩
  · exact h1
  · exact absurd h2 (ho b)

/-- A function correspondence transfers along runs that agree up to the text of an error
    at every fuel. -/
theorem fnCorres_of_errEq {bi₁ bi₂ : Builtins} {e₁ e₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel e₁) (denote' bi₂ fuel e₂)) {A β : Type} [HaxEnc β]
    {entry : A → Env} {G : A → Prop} {g : A → β} (hc : FnCorres bi₂ e₂ entry G g) :
    FnCorres bi₁ e₁ entry G g := by
  intro a hG
  obtain ⟨f₀, hr⟩ := hc a hG
  refine ⟨f₀, fun fuel hf => ?_⟩
  have hv := hr fuel hf
  have := outcome_eq_of_errEq (h fuel) (entry a) (fun s he => by
    change (denote' bi₂ fuel e₂ (entry a)).1 = _ at he
    rw [hv] at he; cases he)
  change (denote' bi₁ fuel e₁ (entry a)).1 = _
  exact this.trans hv

/-- An exception function correspondence transfers along runs that agree up to the text
    of an error at every fuel. -/
theorem fnCorresX_of_errEq {bi₁ bi₂ : Builtins} {e₁ e₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel e₁) (denote' bi₂ fuel e₂)) {A R β : Type}
    [HaxEnc R] [HaxEnc β] {entry : A → Env} {G : A → Prop} {g : A → Except R β}
    (hc : FnCorresX bi₂ e₂ entry G g) : FnCorresX bi₁ e₁ entry G g := by
  intro a hG
  obtain ⟨f₀, hr⟩ := hc a hG
  refine ⟨f₀, fun fuel hf => ?_⟩
  have hv := hr fuel hf
  have := outcome_eq_of_errEq (h fuel) (entry a) (fun s he => by
    change (denote' bi₂ fuel e₂ (entry a)).1 = _ at he
    rw [he] at hv; cases hv)
  change outcomeExceptCF (denote' bi₁ fuel e₁ (entry a)).1 = _
  rw [show (denote' bi₁ fuel e₁ (entry a)).1 = (denote' bi₂ fuel e₂ (entry a)).1 from this]
  exact hv

/-- **Monomorphisation.** The specialised literal under `bi` and the generic literal under
    `withInstances bi tbl insts` have the same function correspondences. -/
theorem fnCorres_monomorphise_iff {bi : Builtins} (tbl : MonoTable) (insts : List String)
    {e : ImpExpr} {A β : Type} [HaxEnc β] {entry : A → Env} {G : A → Prop} {g : A → β} :
    FnCorres bi (monomorphise tbl insts e) entry G g ↔
      FnCorres (withInstances bi tbl insts) e entry G g :=
  ⟨fnCorres_of_errEq fun fuel =>
      fun env => ⟨((Hax.Monomorphise.denote'_monomorphise bi tbl insts e fuel) env).1.symm,
        ((Hax.Monomorphise.denote'_monomorphise bi tbl insts e fuel) env).2.symm⟩,
    fnCorres_of_errEq fun fuel => Hax.Monomorphise.denote'_monomorphise bi tbl insts e fuel⟩

/-- **Monomorphisation with early return.** The specialised literal under `bi` and the
    generic literal under `withInstances bi tbl insts` have the same exception function
    correspondences. -/
theorem fnCorresX_monomorphise_iff {bi : Builtins} (tbl : MonoTable) (insts : List String)
    {e : ImpExpr} {A R β : Type} [HaxEnc R] [HaxEnc β] {entry : A → Env} {G : A → Prop}
    {g : A → Except R β} :
    FnCorresX bi (monomorphise tbl insts e) entry G g ↔
      FnCorresX (withInstances bi tbl insts) e entry G g :=
  ⟨fnCorresX_of_errEq fun fuel =>
      fun env => ⟨((Hax.Monomorphise.denote'_monomorphise bi tbl insts e fuel) env).1.symm,
        ((Hax.Monomorphise.denote'_monomorphise bi tbl insts e fuel) env).2.symm⟩,
    fnCorresX_of_errEq fun fuel => Hax.Monomorphise.denote'_monomorphise bi tbl insts e fuel⟩

/-- A function correspondence of a literal `e'` that is the specialisation of `e` is one
    of `e` under the table extended by the method table of the instances. -/
theorem fnCorres_of_monomorphise {bi : Builtins} (tbl : MonoTable) (insts : List String)
    {e e' : ImpExpr} (hmono : monomorphise tbl insts e = e') {A β : Type} [HaxEnc β]
    {entry : A → Env} {G : A → Prop} {g : A → β} (h : FnCorres bi e' entry G g) :
    FnCorres (withInstances bi tbl insts) e entry G g :=
  (fnCorres_monomorphise_iff tbl insts).mp (hmono ▸ h)

/-- An exception function correspondence of a literal `e'` that is the specialisation of
    `e` is one of `e` under the table extended by the method table of the instances. -/
theorem fnCorresX_of_monomorphise {bi : Builtins} (tbl : MonoTable) (insts : List String)
    {e e' : ImpExpr} (hmono : monomorphise tbl insts e = e') {A R β : Type} [HaxEnc R]
    [HaxEnc β] {entry : A → Env} {G : A → Prop} {g : A → Except R β}
    (h : FnCorresX bi e' entry G g) : FnCorresX (withInstances bi tbl insts) e entry G g :=
  (fnCorresX_monomorphise_iff tbl insts).mp (hmono ▸ h)

end Hax.Ascent
