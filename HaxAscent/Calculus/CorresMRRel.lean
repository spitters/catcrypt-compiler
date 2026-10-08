/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.FnCorresRRel
public import HaxAscent.Calculus.RustMSquare
public import HaxAscent.Calculus.CorresGenericSpec

/-!
# The `RustM` square and `StepTriple` as relational refinements

This module states the square `CorresM` over `RustM` (`Calculus/RustMSquare.lean`) and
the total triple `StepTriple` (`Calculus/CorresGenericSpec.lean`) as the relational
refinement `RRelPT` of `CatCryptCore/Refinement/RRel.lean`. The dialect-generic
`CorresM` over an `Option`-valued step is `RefinesP` (`Calculus/CorresMCore.lean`); its
`RRelPT` form is `corresM_iff_rrelPT` (`Ascent/CorresMachineRRel.lean`).

* The `RustM` square is the refinement of the guarded constant program
  `guardProg G (fun σ => .ok (V σ))` (`CatCryptCore/Refinement/Programs.lean`) by the
  transformer `wpRustM p`, which reads the weakest precondition of `RustM` at the
  program `p c`.
* The step triple is the refinement of an `optProg` program by the weakest
  precondition `wpRel` of the step relation, as for `RefinesO`.

## Main definitions

* `RustM.wpRustM`: the weakest precondition of a state-passing `RustM` program as an
  assertion transformer over the state.

## Main results

* `RustM.corresM_iff_rrelPT`: the `RustM` square is an `RRelPT` instance.
* `stepTriple_iff_rrelPT`: the step triple is an `RRelPT` instance.
-/

@[expose] public section

set_option autoImplicit false

open Std.Do
open CatCrypt.Refinement

namespace Hax.Ascent.RustM

variable {C S A : Type}

/-- The weakest precondition of a state-passing `RustM` program `p` as a transformer of
    assertions over the state: at `c`, the `RustM` weakest precondition of `p c` at the
    postcondition `Φ` of the returned value and state and the exception conditions
    `E`. -/
def wpRustM (p : C → Aeneas.Std.RustM (A × C)) (Φ : A → Assertion (.arg C .pure))
    (E : ExceptConds (.except (ULift Aeneas.Std.Error) (.except PUnit .pure))) :
    Assertion (.arg C .pure) :=
  fun c => wp⟦p c⟧ (fun r => Φ r.1 r.2, E)

/-- **The `RustM` square is `RRelPT`.** `CorresM P G p V Q` is the refinement of the
    guarded constant program of `V` by `wpRustM p`, at the assertion map of
    `entryExitRel P Q`, with the abstract exception `none` fixed to false, arbitrary
    failure and divergence postconditions of `RustM`, and equality of values. -/
theorem corresM_iff_rrelPT {P Q : C → S → Prop} {G : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V : S → A} :
    CorresM P G p V Q ↔
      RRelPT (AssnRel.ofStateRel (entryExitRel P Q))
        (fun (E : ExceptConds (.except (Option Empty) (.arg (S ⊕ S) .pure)))
          (_ : ExceptConds (.except (ULift Aeneas.Std.Error) (.except PUnit .pure))) =>
          ∀ y, ¬ (E.1 none y).down)
        (@_root_.Eq A) (fun Φ E => wp⟦guardProg (ε := Empty) G (fun σ => .ok (V σ))⟧ (Φ, E))
        (wpRustM p) := by
  constructor
  · rintro h Φ Φ' hΦ E _ hnone c ⟨x, hx, hwp⟩
    obtain ⟨σ, rfl, hG, ⟨b, hb, hp⟩ | ⟨r, _, _⟩⟩ := (wp_guardProg_iff hnone).mp hwp
    · cases hb
      obtain ⟨c', hc, hQ⟩ := h c σ hx hG
      show (wp⟦p c⟧ _).down
      rw [hc]
      exact @hΦ (V σ) (V σ) rfl c' ⟨.inr σ, hQ, hp⟩
    · exact r.elim
  · intro h c σ hP hG
    let E : ExceptConds (.except (Option Empty) (.arg (S ⊕ S) .pure)) :=
      (fun _ _ => ⌜False⌝, ())
    have hnone : ∀ y, ¬ (E.1 none y).down := fun _ h => h
    have hw := @h (fun a y => ⌜a = V σ ∧ y = .inr σ⌝) (fun a c' => ⌜a = V σ ∧ Q c' σ⌝)
      (fun _ _ hv s ⟨_, hx, h₁, h₂⟩ => by subst hv h₂; exact ⟨h₁, hx⟩) E
      (fun _ => ⌜False⌝, fun _ => ⌜False⌝, ()) hnone c
      ⟨.inl σ, hP, (wp_guardProg_iff hnone).mpr ⟨σ, rfl, hG, Or.inl ⟨V σ, rfl, rfl, rfl⟩⟩⟩
    change (wp⟦p c⟧ _).down at hw
    cases hpc : p c with
    | ok r =>
      obtain ⟨a, c'⟩ := r
      rw [hpc] at hw
      obtain ⟨rfl, hQ⟩ := hw
      exact ⟨c', rfl, hQ⟩
    | fail e =>
      rw [hpc] at hw
      exact hw.elim
    | div =>
      rw [hpc] at hw
      exact hw.elim

end Hax.Ascent.RustM

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Hax.Ascent (RefinesO refinesO_iff_rrelPT)

variable {M C : Type} {step : C → M → Option M}

/-- **The step triple is `RRelPT`.** `StepTriple step pre c post` is the refinement of
    the one-point program `optProg (fun _ => some ((), ()))` by the weakest precondition
    `wpRel` of the step relation `step c m = some d ∧ m' = m`, at the assertion map of
    `pre` and the value relation `post` on the step result. -/
theorem stepTriple_iff_rrelPT {pre post : M → Prop} {c : C} :
    StepTriple step pre c post ↔
      RRelPT (AssnRel.ofStateRel (fun m (_ : Unit) => pre m))
        (fun E (_ : Unit) => E = ExceptConds.false) (fun _ m => post m)
        (fun Φ E => wp⟦optProg fun (_ : Unit) => some ((), ())⟧ (Φ, E))
        (wpRel fun m d m' => step c m = some d ∧ m' = m) :=
  (show StepTriple step pre c post ↔
      RefinesO (step c) (fun m (_ : Unit) => pre m) (fun m (_ : Unit) => post m)
        (fun _ => some ()) from
    ⟨fun h m _ _ hm _ => h m hm, fun h m hm => h m () () hm rfl⟩).trans refinesO_iff_rrelPT

end CatCrypt.Crypto.SecureCompilation.Ascent

end
