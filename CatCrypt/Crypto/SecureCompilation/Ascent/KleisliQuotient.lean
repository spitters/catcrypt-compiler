/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.SquareKleisli

/-!
# Environments up to agreement off a name, against the relations that read it

`Hax/Ascent/SquareKleisli.lean` composes horizontal arrows with `hcompK` at a name `x`
and has `hidK x` as a one-sided unit: `hidK x` exists at the relations that read `x`
(`hread`), and `corres_letBind_var_right_not_iff` refutes the right unit there.

This module states what happens to those relations under the coarsest identification of
environments that forgets `x`. `EnvAgreeOff x` relates two environments that hold the
same value at every name other than `x`; `RespectsOff x Q` says `Q` is invariant under
that relation, which is what it means for `Q` to be a relation on the quotient. An
environment and its extension at `x` are `EnvAgreeOff x`-related, so a respecting `Q`
satisfies the lowering hypothesis of `not_exit_of_read_of_lower` (`RespectsOff.lower`),
and therefore a respecting `Q` that reads `x` is empty under the guard
(`not_read_of_respectsOff`). No relation on the quotient reads `x`.

Both classes are inhabited. `readsRel x` reads `x`, is non-empty, and carries the
identity arrow `hidKReads`; `readsOther y` at `y ≠ x` respects `EnvAgreeOff x`, is
non-empty, and constrains the environment. `not_respectsOff_readsRel` is the instance of
the theorem at `readsRel x`.

`EnvAgreeOff x` forgets one name at every program point. A per-expression notion, over
the `freeVars` of `HaxLean/FreeVars.lean`, refines it by forgetting a name only where
the continuation does not read it; the statements here are about the coarse relation.

## Main definitions

* `EnvAgreeOff`, `RespectsOff` — agreement off a name, and invariance under it
* `RespectsOff.lower` — a respecting relation satisfies the lowering hypothesis
* `not_read_of_respectsOff` — a respecting relation that reads `x` is empty under the
  guard
* `readsRel`, `hidKReads`, `readsOther` — the two classes are inhabited
* `not_respectsOff_readsRel` — the relation `hidK` lives at does not respect the
  identification
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

variable {S : Type} {bi : Builtins}

/-! ## Agreement off a name -/

/-- Two environments agree off `x` when they hold the same value at every name other
    than `x`. -/
def EnvAgreeOff (x : String) (env₁ env₂ : Env) : Prop :=
  ∀ y, y ≠ x → env₁ y = env₂ y

theorem EnvAgreeOff.rfl' (x : String) (env : Env) : EnvAgreeOff x env env :=
  fun _ _ => rfl

theorem EnvAgreeOff.symm {x : String} {env₁ env₂ : Env} (h : EnvAgreeOff x env₁ env₂) :
    EnvAgreeOff x env₂ env₁ := fun y hy => (h y hy).symm

theorem EnvAgreeOff.trans {x : String} {env₁ env₂ env₃ : Env}
    (h₁ : EnvAgreeOff x env₁ env₂) (h₂ : EnvAgreeOff x env₂ env₃) :
    EnvAgreeOff x env₁ env₃ := fun y hy => (h₁ y hy).trans (h₂ y hy)

/-- Extending an environment at `x` changes it only at `x`. -/
theorem envAgreeOff_extend (x : String) (env : Env) (v : Value) :
    EnvAgreeOff x (env.extend x v) env :=
  fun y hy => Env.extend_other env x v y hy

/-- Removing `x` from an environment changes it only at `x`. -/
theorem envAgreeOff_remove (x : String) (env : Env) :
    EnvAgreeOff x (Env.remove env x) env := by
  intro y hy
  simp [Env.remove, hy]

/-! ## Relations on the quotient -/

/-- `Q` is invariant under agreement off `x`: a relation on the environments quotiented
    by `EnvAgreeOff x`. -/
def RespectsOff (x : String) (Q : Env → S → Prop) : Prop :=
  ∀ env₁ env₂ σ, EnvAgreeOff x env₁ env₂ → Q env₁ σ → Q env₂ σ

/-- A relation invariant under agreement off `x` is closed under removing the binding at
    `x`: the lowering hypothesis of `not_exit_of_read_of_lower`. -/
theorem RespectsOff.lower {x : String} {Q : Env → S → Prop} (h : RespectsOff x Q)
    {G : S → Prop} {V : S → Value} :
    ∀ env σ, G σ → Q (env.extend x (V σ)) σ → Q env σ :=
  fun env σ _ hQ => h _ _ σ (envAgreeOff_extend x env (V σ)) hQ

/-- **A relation on the quotient does not read `x`.** A relation invariant under
    agreement off `x` that places `V σ` at `x` under the guard is empty under the
    guard. -/
theorem not_read_of_respectsOff {x : String} {V : S → Value} {Q : Env → S → Prop}
    {G : S → Prop} (hresp : RespectsOff x Q)
    (hread : ∀ env σ, Q env σ → G σ → env x = some (V σ))
    {env : Env} {σ : S} (hG : G σ) : ¬ Q env σ :=
  not_exit_of_read_of_lower hread (hresp.lower (G := G) (V := V)) hG

/-! ## Both classes are inhabited -/

/-- The relation that places `Value.unit` at `x`. -/
def readsRel (x : String) : Env → Unit → Prop :=
  fun env _ => env x = some Value.unit

/-- `readsRel x` places its value at `x`. -/
theorem readsRel_read (x : String) :
    ∀ env (σ : Unit), readsRel x env σ → True → env x = some Value.unit :=
  fun _ _ h _ => h

/-- `readsRel x` holds at an environment. -/
theorem readsRel_nonempty (x : String) : readsRel x (Env.empty.extend x Value.unit) () :=
  Env.extend_same Env.empty x Value.unit

/-- The Kleisli identity at `readsRel x`: an arrow whose boundary reads `x`. -/
def hidKReads (x : String) :
    HArrowK bi (readsRel x) (fun _ => True) (readsRel x) :=
  hidK x (V := fun _ => Value.unit) (readsRel_read x) (fun _ _ => rfl)

/-- The relation that places `Value.unit` at `y`. -/
def readsOther (y : String) : Env → Unit → Prop :=
  fun env _ => env y = some Value.unit

/-- At `y ≠ x` the relation `readsOther y` is invariant under agreement off `x`. -/
theorem readsOther_respectsOff {x y : String} (h : y ≠ x) :
    RespectsOff x (readsOther y) := by
  intro env₁ env₂ _ hagree hQ
  rw [readsOther, ← hagree y h]
  exact hQ

/-- `readsOther y` holds at an environment. -/
theorem readsOther_nonempty (y : String) :
    readsOther y (Env.empty.extend y Value.unit) () :=
  Env.extend_same Env.empty y Value.unit

/-- **The relation `hidK x` lives at is not a relation on the quotient.** -/
theorem not_respectsOff_readsRel (x : String) : ¬ RespectsOff x (readsRel x) := by
  intro h
  exact not_read_of_respectsOff (V := fun _ => Value.unit) h (readsRel_read x)
    (σ := ()) trivial (readsRel_nonempty x)

end Hax.Ascent
