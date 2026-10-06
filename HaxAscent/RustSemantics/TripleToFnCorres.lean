/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMSSpec
public import HaxAscent.RustSemantics.ToRustMSTotalCtl

/-!
# Function correspondences from triples of the state-passing `RustM` reading

`HaxAscent/RustSemantics/ToRustMSSpec.lean` derives `Std.Do` triples of the reading
`toRustMS app e ρ` from a function correspondence `Hax.Ascent.FnCorres bi e entry G f`.
This file proves the converse: a total triple of the reading, for every argument `a` with
`G a` and from an environment `ρ a` whose encoding is the entry environment `entry a`, gives
the function correspondence. The triple states that the reading returns a value encoding
`f a`, and the simulation `toRustMS_sim` carries that value to the run of the literal under
`Hax.denote'`. The statements are generic in the literal `e`.

A specification of an extracted function proved by `mvcgen` on the `RustM` reading and one
proved by the rules of the ascent are therefore interchangeable wherever the reading
returns a value: `fnCorres_iff_toRustMS_triple` states the equivalence under that
hypothesis, and `fnCorres_iff_toRustMS_triple_of_kindOf` discharges it on the kinded
fragment of `HaxAscent/RustSemantics/ToRustMSTotalCtl.lean`.

A triple with the trivial postcondition on failure and divergence does not give the
partial judgement `Hax.Ascent.FnPartial` by itself. `AppOk bi app` constrains the reading
of the calls only where it returns a value, so a reading that fails satisfies every such
triple while the run of the literal under `Hax.denote'` returns a value unrelated to `f a`.
With the hypothesis that the reading returns a value, the partial triple is the total one
(`fnCorres_of_toRustMS_triple_partial`).

## Main results

* `fnCorres_of_toRustMS_triple`: total triples of the reading give the function
  correspondence.
* `fnCorres_iff_toRustMS_triple`: the equivalence, where the reading returns a value.
* `fnCorres_iff_toRustMS_triple_of_kindOf`: the equivalence on the kinded fragment.
* `fnCorres_of_toRustMS_triple_partial`: partial triples give the function correspondence
  where the reading returns a value.
* `fnPartial_of_toRustMS_triple`: total triples give the partial judgement.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Aeneas.Std.WP Std.Do

variable {bi : Hax.Builtins} {A β : Type} [Hax.Ascent.HaxEnc β]
  {e : Hax.ImpExpr} {entry : A → Hax.Env} {G : A → Prop} {f : A → β}
  {app : String → List AVal → RustM AVal}

/-- **A function correspondence from total triples of the reading.** If, for every argument
    `a` with `G a`, the entry environment `entry a` is the encoding of `ρ a` and the reading
    from `ρ a` satisfies the total triple whose postcondition is that the returned value
    encodes `f a`, then the literal `e` corresponds to `f`. The converse of
    `fnCorres_toRustMS_triple`. -/
theorem fnCorres_of_toRustMS_triple (happ : AppOk bi app) (ρ : A → AEnv)
    (hρ : ∀ a, G a → entry a = encEnv (ρ a))
    (h : ∀ a, G a → ⦃⌜True⌝⦄ toRustMS app e (ρ a)
      ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄) :
    Hax.Ascent.FnCorres bi e entry G f := by
  intro a hG
  obtain ⟨r, hr, hP⟩ := triple_iff_exists_ok.1 (h a hG)
  obtain ⟨F, hF⟩ := toRustMS_sim happ e (ρ a) r.1 r.2 hr
  exact ⟨F, fun fuel hf => by rw [hρ a hG, hF fuel hf, hP]⟩

/-- **The two specifications are equivalent where the reading returns a value.** Under
    `AppOk`, the environment link and the hypothesis that the reading returns a value at
    every argument with `G a`, the function correspondence holds exactly when the total
    triples of the reading hold. The hypothesis `hok` is used only from the correspondence
    to the triples. -/
theorem fnCorres_iff_toRustMS_triple (happ : AppOk bi app) (ρ : A → AEnv)
    (hρ : ∀ a, G a → entry a = encEnv (ρ a))
    (hok : ∀ a, G a → ∃ r, toRustMS app e (ρ a) = .ok r) :
    Hax.Ascent.FnCorres bi e entry G f ↔
      ∀ a, G a → ⦃⌜True⌝⦄ toRustMS app e (ρ a)
        ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄ :=
  ⟨fun hF a hG => fnCorres_toRustMS_triple hF happ a hG (ρ a) (hρ a hG) (hok a hG),
   fnCorres_of_toRustMS_triple happ ρ hρ⟩

/-- **The two specifications are equivalent on the kinded fragment.** For a literal of the
    fragment, a reading of the calls typed by `sig`, and environments binding the names of
    `Γ` to values of their kinds, the function correspondence holds exactly when the total
    triples of the reading hold. The kinding hypotheses `htot`, `he` and `hΓ` are used only
    from the correspondence to the triples. -/
theorem fnCorres_iff_toRustMS_triple_of_kindOf {κ : Type} [DecidableEq κ]
    {H : κ → AVal → Prop} {sig : List (String × List (Kd κ) × Kd κ)}
    {Γ : List (String × Kd κ)} {k : Kd κ}
    (happ : AppOk bi app) (htot : AppTyped H sig app) (he : kindOf sig Γ e = some k)
    (ρ : A → AEnv) (hρ : ∀ a, G a → entry a = encEnv (ρ a))
    (hΓ : ∀ a, G a → EnvTy H Γ (ρ a)) :
    Hax.Ascent.FnCorres bi e entry G f ↔
      ∀ a, G a → ⦃⌜True⌝⦄ toRustMS app e (ρ a)
        ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄ :=
  ⟨fun hF a hG =>
     fnCorres_toRustMS_triple_of_kindOf hF happ htot he a hG (ρ a) (hρ a hG) (hΓ a hG),
   fnCorres_of_toRustMS_triple happ ρ hρ⟩

/-- A triple with the trivial postcondition on failure and divergence states the
    postcondition of a returned value. -/
theorem post_of_triple_partial_of_eq_ok {α : Type} {x : RustM α} {v : α} {P : α → Prop}
    (h : ⦃⌜True⌝⦄ x ⦃post⟨fun r => ⌜P r⌝, fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄)
    (hx : x = .ok v) : P v := by
  subst hx
  simpa [Triple, WP.wp, PredTrans.apply] using h

/-- **A function correspondence from partial triples, where the reading returns a value.**
    The partial triple of `fnCorres_toRustMS_triple_partial` at every argument with `G a`,
    with the hypothesis that the reading returns a value there, gives the function
    correspondence. Without `hok` the conclusion fails: a reading of the calls that always
    fails satisfies `AppOk` and every partial triple. -/
theorem fnCorres_of_toRustMS_triple_partial (happ : AppOk bi app) (ρ : A → AEnv)
    (hρ : ∀ a, G a → entry a = encEnv (ρ a))
    (hok : ∀ a, G a → ∃ r, toRustMS app e (ρ a) = .ok r)
    (h : ∀ a, G a → ⦃⌜True⌝⦄ toRustMS app e (ρ a)
      ⦃post⟨fun r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝, fun _ => ⌜True⌝,
        fun _ => ⌜True⌝⟩⦄) :
    Hax.Ascent.FnCorres bi e entry G f :=
  fnCorres_of_toRustMS_triple happ ρ hρ fun a hG =>
    let ⟨_, hr⟩ := hok a hG
    (triple_iff_post_of_eq_ok hr).2
      (post_of_triple_partial_of_eq_ok
        (P := fun r => r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)) (h a hG) hr)

/-- **The partial judgement from total triples of the reading.** -/
theorem fnPartial_of_toRustMS_triple (happ : AppOk bi app) (ρ : A → AEnv)
    (hρ : ∀ a, G a → entry a = encEnv (ρ a))
    (h : ∀ a, G a → ⦃⌜True⌝⦄ toRustMS app e (ρ a)
      ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄) :
    Hax.Ascent.FnPartial bi e entry G f :=
  Hax.Ascent.fnPartial_of_fnCorres (fnCorres_of_toRustMS_triple happ ρ hρ h)

end CatCrypt.Hax.RustSemantics
