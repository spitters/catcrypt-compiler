/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMS

/-!
# Specifications of the state-passing `RustM` reading from the ascent

A function correspondence `Hax.Ascent.FnCorres bi e entry G f` and a reading of the calls
`app` with `AppOk bi app` give specifications of the program `toRustMS app e ρ` over
`Aeneas.Std.RustM`, in the forms of `HaxLean/Rust/WP.lean` and as `Std.Do` triples that
`mvcgen` applies. The postcondition is fixed by the argument `a`: the returned value
encodes `f a`.

The correspondence states that the run of the literal under `Hax.denote'` returns a value;
`AppOk bi app` constrains `app` only where it returns a value. Neither states that the
reading returns: `app` may fail where the table `bi` has a value, as a checked word
operation does on overflow, where the runtime table computes on unbounded integers. The
partial forms therefore hold without further hypotheses, and the total forms take the
hypothesis `∃ r, toRustMS app e ρ = .ok r`, which `fnCorres_toRustMS_triple_iff` shows to
be necessary.

## Main results

* `fnCorres_toRustMS_partialSpec`: the `partialSpec` form, with trivial postconditions on
  failure and divergence.
* `fnCorres_toRustMS_triple_partial`: the same as a `Std.Do` triple.
* `fnCorres_toRustMS_spec`: the total `spec` form, when the reading returns a value.
* `fnCorres_toRustMS_triple`: the total `Std.Do` triple, when the reading returns a value.
* `fnCorres_toRustMS_triple_iff`: the total triple holds exactly when the reading returns
  a value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Aeneas.Std.WP Std.Do

variable {bi : Hax.Builtins} {A β : Type} [Hax.Ascent.HaxEnc β]
  {e : Hax.ImpExpr} {entry : A → Hax.Env} {G : A → Prop} {f : A → β}
  {app : String → List AVal → RustM AVal}

/-- **The partial specification of the reading.** From an environment whose encoding is
    the entry environment `entry a`, a value the reading returns encodes `f a`; failure and
    divergence carry the trivial postcondition. -/
theorem fnCorres_toRustMS_partialSpec
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) :
    partialSpec (toRustMS app e ρ) (fun r => r.1.toValue = Hax.Ascent.HaxEnc.enc (f a))
      (fun _ => True) True := by
  cases hr : toRustMS app e ρ with
  | ok r => exact fnCorres_toRustMS hF happ a hG ρ hρ r.1 r.2 hr
  | fail _ => trivial
  | div => trivial

/-- **The partial specification as a `Std.Do` triple.** The postcondition on a returned
    pair is that its value encodes `f a`; on failure and on divergence it is `True`. -/
theorem fnCorres_toRustMS_triple_partial
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) :
    ⦃⌜True⌝⦄ toRustMS app e ρ
    ⦃post⟨fun r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝, fun _ => ⌜True⌝,
      fun _ => ⌜True⌝⟩⦄ :=
  partialSpec_to_mvcgen (fnCorres_toRustMS_partialSpec hF happ a hG ρ hρ)
    (fun _ h => h) (fun _ _ => trivial) (fun _ => trivial)

/-- **The total specification of the reading**, when the reading returns a value: the
    value encodes `f a`. -/
theorem fnCorres_toRustMS_spec
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) (hok : ∃ r, toRustMS app e ρ = .ok r) :
    spec (toRustMS app e ρ) (fun r => r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)) := by
  obtain ⟨r, hr⟩ := hok
  rw [hr]
  exact (spec_ok r).2 (fnCorres_toRustMS hF happ a hG ρ hρ r.1 r.2 hr)

/-- **The total specification as a `Std.Do` triple**, when the reading returns a value.
    The postcondition is fixed by `a`, so the triple is applied by `mvcgen` at a call in
    any position. -/
theorem fnCorres_toRustMS_triple
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) (hok : ∃ r, toRustMS app e ρ = .ok r) :
    ⦃⌜True⌝⦄ toRustMS app e ρ ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄ :=
  spec_to_mvcgen (fnCorres_toRustMS_spec hF happ a hG ρ hρ hok)

/-- Under a function correspondence, the total triple of the reading holds exactly when
    the reading returns a value. -/
theorem fnCorres_toRustMS_triple_iff
    (hF : Hax.Ascent.FnCorres bi e entry G f) (happ : AppOk bi app) (a : A) (hG : G a)
    (ρ : AEnv) (hρ : entry a = encEnv ρ) :
    ⦃⌜True⌝⦄ toRustMS app e ρ ⦃⇓ r => ⌜r.1.toValue = Hax.Ascent.HaxEnc.enc (f a)⌝⦄ ↔
      ∃ r, toRustMS app e ρ = .ok r :=
  ⟨fun h => (triple_iff_exists_ok.1 h).imp fun _ h => h.1,
   fnCorres_toRustMS_triple hF happ a hG ρ hρ⟩

end CatCrypt.Hax.RustSemantics
