/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.CorresRRel
public import HaxAscent.Ascent.Refines
public import HaxAscent.Ascent.EarlyExit

/-!
# The function judgments and the forward simulations as relational refinements

This module states the source judgments `CorresArgs`, `FnCorres`, `FnCorresX` and the
forward simulations `RefinesP`, `RefinesO`, `AbsProg.Refines` as the relational
refinement `RRelPT` of `CatCryptCore/Refinement/RRel.lean`, in the form of
`corres_iff_rrelPT` (`Ascent/CorresRRel.lean`).

* The function judgments refine the abstract program `guardProg G f` of a guarded
  function (`CatCryptCore/Refinement/Programs.lean`) by `wpA bi e` or by `wpArgsA bi es`.
* A forward simulation of a partial function `f : A → Option B` by `sem : C → Option D`
  refines the program `optProg` of the partial state transformer
  `fun a => (f a).map (·, a)`, which keeps the state, by the weakest precondition
  `wpRel` of the step relation `sem c = some d ∧ c' = c`.

## Main definitions

* `wpArgsA`: the weakest precondition of an argument list as an assertion transformer.
* `fnExc`: a pure function read as a function into `Except`, raising its result when
  the encoding is a control-flow value.

## Main results

* `corresArgs_iff_rrelPT`, `fnCorres_iff_rrelPT`, `fnCorresX_iff_rrelPT`: the
  judgments are `RRelPT` instances.
* `refinesO_iff_rrelPT`, `refinesP_iff_rrelPT`, `AbsProg.refines_iff_rrelPT`: the
  forward simulations are `RRelPT` instances.
* `corres_transport_via_rrel`: transport along one environment relation, the instance
  of `corres_of_fuelSim_via_rrel` at equal entry and exit relations.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

open Std.Do
open CatCrypt.Refinement

variable {bi : Builtins} {S : Type}

/-! ## `CorresArgs` -/

variable (bi) in
/-- The weakest precondition `wpArgs bi es` as a transformer of assertions over `Env`;
    an argument list has no control-flow postcondition. -/
def wpArgsA (es : List ImpExpr) (Φ : List Value → Assertion (.arg Env .pure)) (_ : Unit) :
    Assertion (.arg Env .pure) :=
  fun env => ⌜wpArgs bi es (fun vs s => (Φ vs s).down) env⌝

/-- **`CorresArgs` is `RRelPT`.** The correspondence of an argument list is the
    refinement of the guarded constant function `Vs` by `wpArgsA bi es`, at the assertion
    map of `entryExitRel P Q`, with the abstract exception `none` fixed to false and
    equality of value lists. -/
theorem corresArgs_iff_rrelPT {P Q : Env → S → Prop} {G : S → Prop} {es : List ImpExpr}
    {Vs : S → List Value} :
    CorresArgs bi P G es Vs Q ↔
      RRelPT (AssnRel.ofStateRel (entryExitRel P Q))
        (fun (E : ExceptConds (.except (Option Empty) (.arg (S ⊕ S) .pure))) (_ : Unit) =>
          ∀ y, ¬ (E.1 none y).down)
        (@_root_.Eq (List Value)) (fun Φ E => wp⟦guardProg (ε := Empty) G (fun σ => .ok (Vs σ))⟧ (Φ, E))
        (wpArgsA bi es) := by
  rw [corresArgs_iff_wpArgs]
  constructor
  · rintro h Φ Φ' hΦ E _ hnone env ⟨x, hx, hwp⟩
    obtain ⟨σ, rfl, hG, ⟨b, hb, hp⟩ | ⟨r, _, _⟩⟩ := (wp_guardProg_iff hnone).mp hwp
    · cases hb
      obtain ⟨vs, env', hE, rfl, hQ⟩ := h σ hG env hx
      exact ⟨Vs σ, env', hE, @hΦ (Vs σ) (Vs σ) rfl env' ⟨.inr σ, hQ, hp⟩⟩
    · exact r.elim
  · intro h σ hG env hP
    let E : ExceptConds (.except (Option Empty) (.arg (S ⊕ S) .pure)) :=
      (fun _ _ => ⌜False⌝, ())
    have hnone : ∀ y, ¬ (E.1 none y).down := fun _ h => h
    exact @h (fun vs y => ⌜vs = Vs σ ∧ y = .inr σ⌝) (fun vs s => ⌜vs = Vs σ ∧ Q s σ⌝)
      (fun _ _ hv s ⟨_, hx, h₁, h₂⟩ => by subst hv h₂; exact ⟨h₁, hx⟩) E () hnone env
      ⟨.inl σ, hP, (wp_guardProg_iff hnone).mpr ⟨σ, rfl, hG, Or.inl ⟨Vs σ, rfl, rfl, rfl⟩⟩⟩

/-! ## `FnCorres` and `FnCorresX` -/

section Functions

variable {A R β : Type}

/-- A pure function read as a function into `Except`: `f a` is raised when its
    encoding is a control-flow value and returned otherwise. -/
def fnExc [HaxEnc β] (f : A → β) (a : A) : Except β β :=
  if (enc (f a)).isControlFlow = true then .error (f a) else .ok (f a)

theorem fnExc_eq_ok [HaxEnc β] {f : A → β} {a : A} {b : β} (h : fnExc f a = .ok b) :
    b = f a := by
  unfold fnExc at h
  split at h <;> cases h
  rfl

theorem fnExc_eq_error [HaxEnc β] {f : A → β} {a : A} {b : β} (h : fnExc f a = .error b) :
    b = f a := by
  unfold fnExc at h
  split at h <;> cases h
  rfl

/-- `FnCorres` is the eventual return of `enc (f a)` under the guard. -/
theorem fnCorres_iff_eval [HaxEnc β] {e : ImpExpr} {entry : A → Env} {G : A → Prop}
    {f : A → β} :
    FnCorres bi e entry G f ↔ ∀ a, G a → ∃ env', Eval bi e (entry a) (enc (f a)) env' := by
  constructor
  · intro h a hG
    obtain ⟨f₀, hrun⟩ := h a hG
    have hv := hrun f₀ (Nat.le_refl _)
    exact ⟨(denote' bi f₀ e (entry a)).2, f₀, fun fuel hf => by
      rw [denote'_val_mono bi hv hf]
      exact Prod.ext hv rfl⟩
  · intro h a hG
    obtain ⟨env', f₀, hrun⟩ := h a hG
    exact ⟨f₀, fun fuel hf => by rw [hrun fuel hf]⟩

/-- **`FnCorres` is `RRelPT`.** The function judgment is the refinement of the guarded
    function `fnExc f` by `wpA bi e`, at the assertion map relating the entry environment
    `entry a` to `.inl a` and every exit environment to `.inr a`, with the value
    relation `v = enc b` and the control-flow postcondition at `enc b` for a raised `b`. -/
theorem fnCorres_iff_rrelPT [HaxEnc β] {e : ImpExpr} {entry : A → Env} {G : A → Prop}
    {f : A → β} :
    FnCorres bi e entry G f ↔
      RRelPT (AssnRel.ofStateRel (entryExitRel (fun env a => env = entry a) (fun _ _ => True)))
        (GuardRE (entryExitRel (fun env a => env = entry a) (fun _ _ => True)) enc)
        (fun b v => v = enc b) (fun Φ E => wp⟦guardProg G (fnExc f)⟧ (Φ, E)) (wpA bi e) := by
  rw [guardProg_rrelPT_wpA_iff, fnCorres_iff_eval]
  refine forall_congr' fun a => forall_congr' fun _ => ⟨?_, ?_⟩
  · rintro ⟨env', hE⟩ env rfl
    refine ⟨_, env', hE, ?_⟩
    cases hc : (enc (f a)).isControlFlow
    · exact Or.inl ⟨hc, trivial, f a, by simp only [fnExc, hc, Bool.false_eq_true, if_false], rfl⟩
    · exact Or.inr ⟨hc, trivial, f a, by simp only [fnExc, hc, if_true], rfl⟩
  · intro h
    obtain ⟨v, env', hE, hp⟩ := h (entry a) rfl
    refine ⟨env', ?_⟩
    rcases hp with ⟨_, _, b, hb, rfl⟩ | ⟨_, _, r, hr, rfl⟩
    · rw [← fnExc_eq_ok hb]
      exact hE
    · rw [← fnExc_eq_error hr]
      exact hE

/-- A value whose exception reading is `x` is `excVal x`. -/
theorem eq_excVal_of_cfExcept {v : Value} {x : Except Value Value} (h : cfExcept v = x) :
    v = excVal x := by
  unfold cfExcept at h
  split at h <;> subst h <;> rfl

/-- `FnCorresX` at a plain result type is the eventual return of
    `excVal (encExc (f a))` under the guard. -/
theorem fnCorresX_iff_eval [HaxEnc R] [HaxEnc β] [HaxEnc.Plain β] {e : ImpExpr}
    {entry : A → Env} {G : A → Prop} {f : A → Except R β} :
    FnCorresX bi e entry G f ↔
      ∀ a, G a → ∃ env', Eval bi e (entry a) (excVal (encExc (f a))) env' := by
  constructor
  · intro h a hG
    obtain ⟨f₀, hrun⟩ := h a hG
    have h₀ := hrun f₀ (Nat.le_refl _)
    cases hd : (denote' bi f₀ e (entry a)).1 <;> rw [hd] at h₀ <;>
      simp only [outcomeExceptCF, reduceCtorEq] at h₀
    rename_i v
    have hv : v = excVal (encExc (f a)) := eq_excVal_of_cfExcept (Option.some.inj h₀)
    subst hv
    exact ⟨(denote' bi f₀ e (entry a)).2, f₀, fun fuel hf => by
      rw [denote'_val_mono bi hd hf]
      exact Prod.ext hd rfl⟩
  · intro h a hG
    obtain ⟨env', f₀, hrun⟩ := h a hG
    exact ⟨f₀, fun fuel hf => by
      rw [hrun fuel hf]
      exact congrArg some (cfExcept_excVal (excPlain_encExc (f a)))⟩

/-- **`FnCorresX` is `RRelPT`.** At a plain result type, the function judgment with
    early return is the refinement of the guarded function `f : A → Except R β` by
    `wpA bi e`, at the assertion map relating `entry a` to `.inl a` and every exit
    environment to `.inr a`, with the value relation `v = enc b` and the control-flow
    postcondition at `.controlFlow true (enc r)` for a raised `r`. -/
theorem fnCorresX_iff_rrelPT [HaxEnc R] [HaxEnc β] [HaxEnc.Plain β] {e : ImpExpr}
    {entry : A → Env} {G : A → Prop} {f : A → Except R β} :
    FnCorresX bi e entry G f ↔
      RRelPT (AssnRel.ofStateRel (entryExitRel (fun env a => env = entry a) (fun _ _ => True)))
        (GuardRE (entryExitRel (fun env a => env = entry a) (fun _ _ => True))
          (fun r => .controlFlow true (enc r)))
        (fun b v => v = enc b) (fun Φ E => wp⟦guardProg G f⟧ (Φ, E)) (wpA bi e) := by
  rw [guardProg_rrelPT_wpA_iff, fnCorresX_iff_eval]
  refine forall_congr' fun a => forall_congr' fun _ => ⟨?_, ?_⟩
  · rintro ⟨env', hE⟩ env rfl
    refine ⟨_, env', hE, ?_⟩
    cases hf : f a with
    | ok b => exact Or.inl ⟨HaxEnc.Plain.not_cf b, trivial, b, rfl, rfl⟩
    | error r => exact Or.inr ⟨rfl, trivial, r, rfl, rfl⟩
  · intro h
    obtain ⟨v, env', hE, hp⟩ := h (entry a) rfl
    refine ⟨env', ?_⟩
    rcases hp with ⟨_, _, b, hb, rfl⟩ | ⟨_, _, r, hr, rfl⟩
    · rw [hb]
      exact hE
    · rw [hr]
      exact hE

end Functions

/-! ## The forward simulations -/

section Refines

variable {C D A B ε : Type}

/-- **`RefinesO` is `RRelPT`.** The forward simulation of the partial function `f` by
    `sem` is the refinement of `optProg` of the state-keeping transformer
    `fun a => (f a).map (·, a)` by `wpRel` of the step relation `sem c = some d ∧ c' = c`,
    at the assertion map of `SRin`, with the abstract exception postcondition fixed to
    false (an abstract `none` constrains nothing) and the value relation `SRout` on the
    outputs. -/
theorem refinesO_iff_rrelPT {sem : C → Option D} {SRin : C → A → Prop}
    {SRout : D → B → Prop} {f : A → Option B} :
    RefinesO sem SRin SRout f ↔
      RRelPT (AssnRel.ofStateRel SRin) (fun E (_ : Unit) => E = ExceptConds.false)
        (fun b d => SRout d b) (fun Φ E => wp⟦optProg fun a => (f a).map (·, a)⟧ (Φ, E))
        (wpRel fun c d c' => sem c = some d ∧ c' = c) := by
  rw [rrelPT_optProg_wpRel_iff]
  constructor
  · intro h c a p hs hf
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hf
    obtain ⟨d, hd, hR⟩ := h c a b hs hb
    exact ⟨d, c, ⟨hd, rfl⟩, hR, hs⟩
  · intro h c a b hs hf
    obtain ⟨d, _, ⟨hd, rfl⟩, hR, -⟩ := h c a (b, a) hs (by rw [hf]; rfl)
    exact ⟨d, hd, hR⟩

/-- **`RefinesP` is `RRelPT`.** Under a decidable precondition `P`, the forward
    simulation of the pure function `f` is `refinesO_iff_rrelPT` at `optGuard P f`. -/
theorem refinesP_iff_rrelPT {sem : C → Option D} {SRin : C → A → Prop}
    {SRout : D → B → Prop} {P : A → Prop} [DecidablePred P] {f : A → B} :
    RefinesP sem SRin SRout P f ↔
      RRelPT (AssnRel.ofStateRel SRin) (fun E (_ : Unit) => E = ExceptConds.false)
        (fun b d => SRout d b)
        (fun Φ E => wp⟦optProg fun a => (optGuard P f a).map (·, a)⟧ (Φ, E))
        (wpRel fun c d c' => sem c = some d ∧ c' = c) :=
  (refinesP_iff_refinesO_guard sem SRin SRout P f).trans refinesO_iff_rrelPT

/-- **`AbsProg.Refines` is `RRelPT`.** The correspondence of an abstract program at its
    level is `refinesO_iff_rrelPT` at `p.toExcept`, with the value relation `SRout` on
    `Except ε B`. -/
theorem AbsProg.refines_iff_rrelPT {sem : C → Option D} {SRin : C → A → Prop}
    {SRout : D → Except ε B → Prop} {p : AbsProg ε A B} :
    p.Refines sem SRin SRout ↔
      RRelPT (AssnRel.ofStateRel SRin) (fun E (_ : Unit) => E = ExceptConds.false)
        (fun b d => SRout d b)
        (fun Φ E => wp⟦optProg fun a => (p.toExcept a).map (·, a)⟧ (Φ, E))
        (wpRel fun c d c' => sem c = some d ∧ c' = c) :=
  (AbsProg.refines_iff_toExcept sem SRin SRout p).trans refinesO_iff_rrelPT

end Refines

/-! ## Transport along an environment relation -/

/-- **Transport along one relation**: `corres_of_fuelSim_via_rrel` at equal entry and
    exit relations. When from `R`-related environments the runs of `e` and `e'` have
    the same outcome and end in `R`-related environments at every fuel, a `Corres`
    statement for `e` gives one for `e'` from and to the environments `R`-related to
    the entry and exit environments of `e`. -/
theorem corres_transport_via_rrel {R : Env → Env → Prop} {e e' : ImpExpr}
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (hsim : ∀ fuel env envF, R env envF →
      ((denote' bi fuel e).run env).1 = ((denote' bi fuel e').run envF).1 ∧
        R ((denote' bi fuel e).run env).2 ((denote' bi fuel e').run envF).2)
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ R env envF) G e' V
      (fun envF σ => ∃ env, Q env σ ∧ R env envF) :=
  corres_of_fuelSim_via_rrel hsim h

end Hax.Ascent

end
