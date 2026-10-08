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

* The abstract program `guardProg G f : EStateM (Option ε) (S ⊕ S) α` of a guarded
  function `f : S → Except ε α` moves `.inl σ` to `.inr σ`, returning `b` when
  `f σ = .ok b` and raising `some r` when `f σ = .error r`. A failed guard, and a
  start from `.inr σ`, raise `none`, whose postcondition `GuardRE` fixes to false.
* The abstract program `optProg f : EStateM PUnit A B` of a partial function returns
  `b` when `f a = some b` and raises `()` otherwise; the concrete side of a forward
  simulation is the weakest precondition `wpOpt sem` of the partial function `sem`.

## Main definitions

* `guardProg`, `GuardRE`: the abstract program of a guarded function and the relation of
  the second postconditions.
* `wpArgsA`: the weakest precondition of an argument list as an assertion transformer.
* `fnExc`: a pure function read as a function into `Except`, raising its result when
  the encoding is a control-flow value.
* `optProg`, `wpOpt`: the abstract and the concrete program of a forward simulation.

## Main results

* `guardProg_rrelPT_wpA_iff`: `RRelPT` between `guardProg G f` and `wpA bi e` is the
  triple whose postconditions name the value of `f`.
* `corresArgs_iff_rrelPT`, `fnCorres_iff_rrelPT`, `fnCorresX_iff_rrelPT`: the
  judgments are `RRelPT` instances.
* `refinesO_iff_rrelPT`, `refinesP_iff_rrelPT`, `AbsProg.refines_iff_rrelPT`: the
  forward simulations are `RRelPT` instances.
* `corres_transport_via_rrel`: transport along one environment relation, by
  `rrelPT_wpA_of_sim` and `corres_trans_of_rrelPT`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

open Std.Do
open CatCrypt.Refinement

variable {bi : Builtins} {S : Type}

/-! ## The abstract program of a guarded function -/

/-- The abstract program of a guarded function `f`: from `.inl σ` with `G σ` it returns
    `b` in `.inr σ` when `f σ = .ok b` and raises `some r` in `.inr σ` when
    `f σ = .error r`; otherwise it raises `none`. -/
noncomputable def guardProg {ε α : Type} (G : S → Prop) (f : S → Except ε α) :
    EStateM (Option ε) (S ⊕ S) α := fun x =>
  open Classical in
  match x with
  | .inl σ =>
    if G σ then
      (match f σ with
        | .ok b => .ok b (.inr σ)
        | .error r => .error (some r) (.inr σ))
    else .error none x
  | .inr _ => .error none x

/-- The weakest precondition of `guardProg G f`, when the exception `none` has the
    false postcondition: the start is `.inl σ` with `G σ`, and the result of `f σ`
    meets the normal postcondition at `.ok b` and the postcondition of `some r` at
    `.error r`. -/
theorem wp_guardProg_iff {ε α : Type} {G : S → Prop} {f : S → Except ε α}
    {Q : PostCond α (.except (Option ε) (.arg (S ⊕ S) .pure))} {x : S ⊕ S}
    (hnone : ∀ y, ¬ (Q.2.1 none y).down) :
    (wp⟦guardProg G f⟧ Q x).down ↔ ∃ σ, x = .inl σ ∧ G σ ∧
      ((∃ b, f σ = .ok b ∧ (Q.1 b (.inr σ)).down) ∨
        (∃ r, f σ = .error r ∧ (Q.2.1 (some r) (.inr σ)).down)) := by
  rw [wp_eStateM_apply]
  rcases x with σ | σ
  · by_cases hG : G σ
    · cases hf : f σ with
      | ok b =>
        simp only [EStateM.run, guardProg, if_pos hG, hf]
        refine ⟨fun h => ⟨σ, rfl, hG, Or.inl ⟨b, hf, h⟩⟩, fun ⟨_, h, _, hp⟩ => ?_⟩
        cases h
        rw [hf] at hp
        rcases hp with ⟨_, hb, hp⟩ | ⟨_, hr, _⟩
        · cases hb
          exact hp
        · cases hr
      | error r =>
        simp only [EStateM.run, guardProg, if_pos hG, hf]
        refine ⟨fun h => ⟨σ, rfl, hG, Or.inr ⟨r, hf, h⟩⟩, fun ⟨_, h, _, hp⟩ => ?_⟩
        cases h
        rw [hf] at hp
        rcases hp with ⟨_, hb, _⟩ | ⟨_, hr, hp⟩
        · cases hb
        · cases hr
          exact hp
    · simp only [EStateM.run, guardProg, if_neg hG]
      exact ⟨fun h => (hnone _ h).elim, fun ⟨_, h, hG', _⟩ => by cases h; exact (hG hG').elim⟩
  · simp only [EStateM.run, guardProg]
    exact ⟨fun h => (hnone _ h).elim, fun ⟨_, h, _⟩ => nomatch h⟩

/-- The relation of the second postconditions for `guardProg`: the abstract exception
    `none` has the false postcondition, and the abstract postcondition of `some r`,
    mapped by `ofStateRel SR`, entails the control-flow postcondition at `encE r`. -/
def GuardRE {ε : Type} (SR : Env → S ⊕ S → Prop) (encE : ε → Value)
    (E : ExceptConds (.except (Option ε) (.arg (S ⊕ S) .pure)))
    (Ψ : Value → Assertion (.arg Env .pure)) : Prop :=
  (∀ y, ¬ (E.1 none y).down) ∧
    ∀ r, (AssnRel.ofStateRel (ε := Option ε) SR).γ (E.1 (some r)) ⊢ₛ Ψ (encE r)

/-- **`RRelPT` from a guarded function.** The refinement of `guardProg G f` by `wpA bi e`
    at the assertion map of `entryExitRel P Q`, the value relation `Rv` and `GuardRE` is
    the triple: under the guard, from an environment related by `P`, the run of `e`
    returns a plain value `Rv`-related to `b` when `f σ = .ok b` and the control-flow
    value `encE r` when `f σ = .error r`, in an environment related by `Q`. -/
theorem guardProg_rrelPT_wpA_iff {ε α : Type} {P Q : Env → S → Prop} {G : S → Prop}
    {e : ImpExpr} {f : S → Except ε α} {Rv : α → Value → Prop} {encE : ε → Value} :
    RRelPT (AssnRel.ofStateRel (entryExitRel P Q)) (GuardRE (entryExitRel P Q) encE) Rv
        (fun Φ E => wp⟦guardProg G f⟧ (Φ, E)) (wpA bi e) ↔
      ∀ σ, G σ → ∀ env, P env σ →
        wp bi e (fun v env' => Q env' σ ∧ ∃ b, f σ = .ok b ∧ Rv b v)
          (fun v env' => Q env' σ ∧ ∃ r, f σ = .error r ∧ v = encE r) env := by
  constructor
  · intro h σ hG env hP
    let E : ExceptConds (.except (Option ε) (.arg (S ⊕ S) .pure)) :=
      (fun o y => ⌜∃ r, o = some r ∧ f σ = .error r ∧ y = .inr σ⌝, ())
    have hnone : ∀ y, ¬ (E.1 none y).down := fun _ ⟨_, h, _⟩ => nomatch h
    have hw := @h (fun b y => ⌜f σ = .ok b ∧ y = .inr σ⌝)
      (fun v s => ⌜Q s σ ∧ ∃ b, f σ = .ok b ∧ Rv b v⌝)
      (fun b v hv s ⟨_, hx, h₁, h₂⟩ => by subst h₂; exact ⟨hx, b, h₁, hv⟩)
      E (fun v s => ⌜Q s σ ∧ ∃ r, f σ = .error r ∧ v = encE r⌝)
      ⟨hnone, fun r s ⟨_, hx, _, h₀, h₁, h₂⟩ => by
        cases h₀; subst h₂; exact ⟨hx, _, h₁, rfl⟩⟩ env
      ⟨.inl σ, hP, (wp_guardProg_iff hnone).mpr ⟨σ, rfl, hG, by
        cases hf : f σ with
        | ok b => exact Or.inl ⟨b, rfl, rfl, rfl⟩
        | error r => exact Or.inr ⟨r, rfl, r, rfl, hf, rfl⟩⟩⟩
    exact hw
  · rintro h Φ Φ' hΦ E E' ⟨hnone, hE⟩ env ⟨x, hx, hwp⟩
    obtain ⟨σ, rfl, hG, hp⟩ := (wp_guardProg_iff hnone).mp hwp
    refine wp_mono (h σ hG env hx) ?_ ?_
    · rintro v s - ⟨hQ, b, hb, hR⟩
      rcases hp with ⟨b', hb', hp⟩ | ⟨r, hr, _⟩
      · rw [hb] at hb'
        cases hb'
        exact @hΦ b v hR s ⟨.inr σ, hQ, hp⟩
      · rw [hb] at hr
        cases hr
    · rintro v s - ⟨hQ, r, hr, rfl⟩
      rcases hp with ⟨b, hb, _⟩ | ⟨r', hr', hp⟩
      · rw [hr] at hb
        cases hb
      · rw [hr] at hr'
        cases hr'
        exact hE r s ⟨.inr σ, hQ, hp⟩

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

/-- The abstract program of a partial function: `b` with the state kept when
    `f a = some b`, the exception `()` when `f a = none`. -/
def optProg (f : A → Option B) : EStateM PUnit A B := fun a =>
  match f a with
  | some b => .ok b a
  | none => .error () a

theorem wp_optProg_apply (f : A → Option B) (Q : PostCond B (.except PUnit (.arg A .pure)))
    (a : A) : wp⟦optProg f⟧ Q a = match f a with
      | some b => Q.1 b a
      | none => Q.2.1 () a := by
  rw [wp_eStateM_apply]
  cases h : f a <;> simp only [EStateM.run, optProg, h]

/-- The weakest precondition of a partial function `sem : C → Option D` over the
    output: `sem c = some d` with the postcondition at `d` and the input `c`. -/
def wpOpt (sem : C → Option D) (Φ : D → Assertion (.arg C .pure)) (_ : Unit) :
    Assertion (.arg C .pure) :=
  fun c => ⌜∃ d, sem c = some d ∧ (Φ d c).down⌝

/-- **`RefinesO` is `RRelPT`.** The forward simulation of the partial function `f` by
    `sem` is the refinement of `optProg f` by `wpOpt sem` at the assertion map of
    `SRin`, with the abstract exception postcondition fixed to false (an abstract
    `none` constrains nothing) and the value relation `SRout` on the outputs. -/
theorem refinesO_iff_rrelPT {sem : C → Option D} {SRin : C → A → Prop}
    {SRout : D → B → Prop} {f : A → Option B} :
    RefinesO sem SRin SRout f ↔
      RRelPT (AssnRel.ofStateRel SRin) (fun E (_ : Unit) => E = ExceptConds.false)
        (fun b d => SRout d b) (fun Φ E => wp⟦optProg f⟧ (Φ, E)) (wpOpt sem) := by
  constructor
  · rintro h Φ Φ' hΦ E _ rfl c ⟨a, hs, hwp⟩
    beta_reduce at hwp
    rw [wp_optProg_apply] at hwp
    cases hf : f a with
    | none =>
      rw [hf] at hwp
      exact hwp.elim
    | some b =>
      rw [hf] at hwp
      obtain ⟨d, hd, hR⟩ := h c a b hs hf
      exact ⟨d, hd, @hΦ b d hR c ⟨a, hs, hwp⟩⟩
  · intro h c a b hs hf
    have hw := @h (fun b' _ => ⌜b' = b⌝) (fun d _ => ⌜SRout d b⌝)
      (fun b' d hR _ ⟨_, _, he⟩ => by subst he; exact hR) ExceptConds.false () rfl c
      ⟨a, hs, by beta_reduce; rw [wp_optProg_apply, hf]; exact rfl⟩
    obtain ⟨d, hd, hR⟩ := hw
    exact ⟨d, hd, hR⟩

/-- **`RefinesP` is `RRelPT`.** Under a decidable precondition `P`, the forward
    simulation of the pure function `f` is the refinement of `optProg (optGuard P f)`
    by `wpOpt sem`. -/
theorem refinesP_iff_rrelPT {sem : C → Option D} {SRin : C → A → Prop}
    {SRout : D → B → Prop} {P : A → Prop} [DecidablePred P] {f : A → B} :
    RefinesP sem SRin SRout P f ↔
      RRelPT (AssnRel.ofStateRel SRin) (fun E (_ : Unit) => E = ExceptConds.false)
        (fun b d => SRout d b) (fun Φ E => wp⟦optProg (optGuard P f)⟧ (Φ, E)) (wpOpt sem) :=
  (refinesP_iff_refinesO_guard sem SRin SRout P f).trans refinesO_iff_rrelPT

/-- **`AbsProg.Refines` is `RRelPT`.** The correspondence of an abstract program at its
    level is the refinement of `optProg p.toExcept` by `wpOpt sem`, with the value
    relation `SRout` on `Except ε B`. -/
theorem AbsProg.refines_iff_rrelPT {sem : C → Option D} {SRin : C → A → Prop}
    {SRout : D → Except ε B → Prop} {p : AbsProg ε A B} :
    p.Refines sem SRin SRout ↔
      RRelPT (AssnRel.ofStateRel SRin) (fun E (_ : Unit) => E = ExceptConds.false)
        (fun b d => SRout d b) (fun Φ E => wp⟦optProg p.toExcept⟧ (Φ, E)) (wpOpt sem) :=
  (AbsProg.refines_iff_toExcept sem SRin SRout p).trans refinesO_iff_rrelPT

end Refines

/-! ## Transport along an environment relation -/

/-- **Transport along one relation**, by `rrelPT_wpA_of_sim` and
    `corres_trans_of_rrelPT`: when from `R`-related environments the runs of `e` and
    `e'` have the same outcome and end in `R`-related environments at every fuel, a
    `Corres` statement for `e` gives one for `e'` from and to the environments
    `R`-related to the entry and exit environments of `e`. -/
theorem corres_transport_via_rrel {R : Env → Env → Prop} {e e' : ImpExpr}
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (hsim : ∀ fuel env envF, R env envF →
      ((denote' bi fuel e).run env).1 = ((denote' bi fuel e').run envF).1 ∧
        R ((denote' bi fuel e).run env).2 ((denote' bi fuel e').run envF).2)
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ R env envF) G e' V
      (fun envF σ => ∃ env, Q env σ ∧ R env envF) :=
  corres_conseq (corres_trans_of_rrelPT h (rrelPT_wpA_of_sim hsim))
    (fun _ _ ⟨env, hP, hR⟩ _ => ⟨env, hR, hP⟩) (fun _ h => h) (fun _ _ => rfl)
    (fun _ _ _ ⟨env, hR, hQ⟩ => ⟨env, hQ, hR⟩)

end Hax.Ascent

end
