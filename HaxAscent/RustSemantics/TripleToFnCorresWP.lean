/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.RuntimeM
public import HaxAscent.RustSemantics.TripleToFnCorres
public import HaxAscent.RustSemantics.ToRustMSCongr
public import HaxAscent.RustSemantics.ToRustMSInv

/-!
# Total triples of the `RustM` reading in the `Std.WP` logic

`RustM` has two weakest-precondition interpretations: the `Std.Do` one of
`HaxLean/Rust/Primitives.lean` (`RustM.instWP`, read by `mvcgen`) and the `Std.WP` one of
`HaxLean/RuntimeM.lean` (`RustM.instStdWPMonad`, read by `vcgen` and `rust_vc`). A total
`Std.Do` triple `⦃⌜True⌝⦄ x ⦃⇓ r => ⌜Q r⌝⦄` and the `Std.WP` triple `⦃True⦄ x ⦃Q⦄`, whose
exception postcondition is `⊥`, both state that `x` returns a value satisfying `Q`
(`stdWP_triple_iff_stdDo`). Every lemma about total `Std.Do` triples of the reading
`toRustMS app e ρ` therefore holds for the `Std.WP` triple; this file states the ones of
`TripleToFnCorres`, `ToRustMSCongr` and `ToRustMSInv`.

## Main results

* `stdWP_triple_iff_exists_ok`: a `Std.WP` triple of a `RustM` program with exception
  postcondition `⊥` holds exactly when, under the precondition, the program returns a value
  satisfying the postcondition.
* `stdWP_triple_iff_stdDo`: the `Std.WP` triple is the total `Std.Do` triple.
* `fnCorres_of_toRustMS_tripleWP`: `Std.WP` triples of the reading give the function
  correspondence.
* `toRustMS_tripleWP_congr`, `toRustMS_tripleWP_of_inv`: the triple under a reading of the
  calls that agrees on the called names, or along invariant values.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std
-- The `Std.WP` instances `Assertion Prop` and `PartialOrder Prop` are scoped.
open _root_.Std.WP Lean.Order

/-- **A `Std.WP` triple of a `RustM` program as a returned value.** With exception
    postcondition `⊥`, the triple of `x` with precondition `P` and postcondition `Q` holds
    exactly when, under `P`, `x` returns a value satisfying `Q`. -/
theorem stdWP_triple_iff_exists_ok {α : Type} {x : RustM α} {P : Prop} {Q : α → Prop} :
    _root_.Std.WP.Triple x P Q Lean.Order.bot ↔ (P → ∃ a, x = .ok a ∧ Q a) := by
  constructor
  · rintro ⟨h⟩ hP
    have h' := h hP
    cases x with
    | ok a => exact ⟨a, rfl, h'⟩
    | fail e => exact (Lean.Order.bot_le (fun _ : Error => False) e h').elim
    | div => exact h'.elim
  · intro h
    exact ⟨fun hP => by obtain ⟨a, rfl, hQ⟩ := h hP; exact hQ⟩

/-- **The `Std.WP` triple is the total `Std.Do` triple.** For a `RustM` program `x`, the
    `Std.WP` triple `⦃True⦄ x ⦃Q⦄` (exception postcondition `⊥`) holds exactly when the
    `Std.Do` triple `⦃⌜True⌝⦄ x ⦃⇓ r => ⌜Q r⌝⦄` does. -/
theorem stdWP_triple_iff_stdDo {α : Type} {x : RustM α} {Q : α → Prop} :
    _root_.Std.WP.Triple x True Q Lean.Order.bot ↔
      Std.Do.Triple x (Std.Do.SPred.pure True)
        (Std.Do.PostCond.noThrow fun r => Std.Do.SPred.pure (Q r)) := by
  rw [stdWP_triple_iff_exists_ok, Aeneas.Std.WP.triple_iff_exists_ok]
  simp

variable {bi : _root_.Hax.Builtins} {A β : Type} [_root_.Hax.Ascent.HaxEnc β]
  {e : _root_.Hax.ImpExpr} {entry : A → _root_.Hax.Env} {G : A → Prop} {f : A → β}
  {app : String → List AVal → RustM AVal}

/-- **A function correspondence from `Std.WP` triples of the reading.** The statement of
    `fnCorres_of_toRustMS_triple` with the triples of the `Std.WP` logic. -/
theorem fnCorres_of_toRustMS_tripleWP (happ : AppOk bi app) (ρ : A → AEnv)
    (hρ : ∀ a, G a → entry a = encEnv (ρ a))
    (h : ∀ a, G a → _root_.Std.WP.Triple (toRustMS app e (ρ a)) True
      (fun r => r.1.toValue = _root_.Hax.Ascent.HaxEnc.enc (f a)) Lean.Order.bot) :
    _root_.Hax.Ascent.FnCorres bi e entry G f :=
  fnCorres_of_toRustMS_triple happ ρ hρ fun a hG => stdWP_triple_iff_stdDo.1 (h a hG)

/-- A `Std.WP` triple of the reading under `app` is the triple of the reading under a
    reading `app'` of the calls that agrees with `app` on the called names. -/
theorem toRustMS_tripleWP_congr {app app' : String → List AVal → RustM AVal}
    {ok : String → Bool} (hag : ∀ f, ok f = true → app f = app' f) {e : _root_.Hax.ImpExpr}
    (hc : _root_.Hax.Ascent.callsOK ok e = true) {ρ : AEnv} {Q : AVal × AEnv → Prop}
    (h : _root_.Std.WP.Triple (toRustMS app e ρ) True Q Lean.Order.bot) :
    _root_.Std.WP.Triple (toRustMS app' e ρ) True Q Lean.Order.bot :=
  stdWP_triple_iff_stdDo.2 (toRustMS_triple_congr hag hc (stdWP_triple_iff_stdDo.1 h))

/-- **A `Std.WP` triple of the reading along invariant values.** The statement of
    `toRustMS_triple_of_inv` with the triples of the `Std.WP` logic. -/
theorem toRustMS_tripleWP_of_inv {Inv : AVal → Prop} (hI : ValInv Inv)
    {app app' : String → List AVal → RustM AVal} {ok : String → Bool}
    (hag : AppInv Inv ok app app') {e : _root_.Hax.ImpExpr}
    (hc : _root_.Hax.Ascent.callsOK ok e = true) {ρ : AEnv} (hρ : EnvInv Inv ρ)
    {Q : AVal × AEnv → Prop}
    (h : _root_.Std.WP.Triple (toRustMS app e ρ) True Q Lean.Order.bot) :
    _root_.Std.WP.Triple (toRustMS app' e ρ) True Q Lean.Order.bot :=
  stdWP_triple_iff_stdDo.2 (toRustMS_triple_of_inv hI hag hc hρ (stdWP_triple_iff_stdDo.1 h))

end CatCrypt.Hax.RustSemantics
