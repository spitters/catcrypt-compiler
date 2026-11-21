/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresMachineRRel
public import CatCryptCore.Refinement.RRelWRP

/-!
# Fuel runs of an instruction set over `Std.WP`, and `CorresIsa` as a `RefinementWP` refinement

The fuel run of a program `P` under an instruction set `isa` (`Isa.lsemFuelMemF`) is a program
`Isa.runM isa P fuel` of `StateT LstateMF Option`, whose `Std.WP` weakest precondition at the
exception postcondition `⊥` is the angelic transformer of the run. `CorresIsa isa P SR Pre fa fuel`
is then the refinement, in the sense of the refinement weakest precondition of `refinement-wp`, of
the guarded update by `Isa.runM isa P fuel`, by core's `guardedRRelPT_iff_refines`.

## Main definitions

* `VIR.LprogIsa.Isa.runM`: the fuel run as a program of `StateT LstateMF Option`.

## Main results

* `wp_runM_bot_iff`: the weakest precondition of the run at `⊥` holds exactly when the run
  halts in a state satisfying the postcondition.
* `corresIsa_iff_refines`: `CorresIsa` is `RefinementWP.Refines` of the guarded update by the run.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.WP Lean.Order
open CatCrypt.Refinement

/-- The fuel run of `P` under `isa` as a program of `StateT LstateMF Option`: it returns the
    final state of `Isa.lsemFuelMemF`, and fails when the run fails or runs out of fuel. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa.runM (isa : VIR.LprogIsa.Isa)
    (P : VIR.JasminLsemMemLoop.LprogM) (fuel : Nat) :
    StateT VIR.JasminLsemMemFlagGuard.LstateMF Option Unit :=
  fun s => (isa.lsemFuelMemF P fuel s).map ((), ·)

/-- The `Std.WP` weakest precondition of the fuel run at the exception postcondition `⊥` holds
    exactly when the run halts in a state satisfying the postcondition. -/
theorem wp_runM_bot_iff (isa : VIR.LprogIsa.Isa) (P : VIR.JasminLsemMemLoop.LprogM) (fuel : Nat)
    (Q : Unit → VIR.JasminLsemMemFlagGuard.LstateMF → Prop)
    (s : VIR.JasminLsemMemFlagGuard.LstateMF) :
    Std.WP.wp (isa.runM P fuel) Q bot s ↔
      ∃ v s', isa.lsemFuelMemF P fuel s = some s' ∧ v = () ∧ Q v s' := by
  have hr : (isa.runM P fuel).run s = (isa.lsemFuelMemF P fuel s).map ((), ·) := rfl
  simp only [StateT.wp_apply_eq, hr]
  cases h : isa.lsemFuelMemF P fuel s <;> simp
  · intro h
    change (bot : Unit → Prop) () at h
    simp only [bot_apply, bot_prop_eq] at h
  · exact ⟨fun h => ⟨(), h⟩, fun ⟨⟨⟩, h⟩ => h⟩

variable {AState : Type}

open scoped Classical in
/-- `CorresIsa isa P SR Pre fa fuel` is the `RefinementWP` refinement of the guarded update by
    the fuel run of `P` under `isa`. -/
theorem corresIsa_iff_refines (isa : VIR.LprogIsa.Isa) (P : VIR.JasminLsemMemLoop.LprogM)
    (SR : VIR.JasminLsemMemFlagGuard.LstateMF → AState → Prop) (Pre : AState → Prop)
    (fa : AState → AState) (fuel : Nat) :
    CorresIsa isa P SR Pre fa fuel ↔
      RefinementWP.Refines top (RefinementWP.Concretization.ofStateRel SR) (fun _ => bot)
        (isa.runM P fuel) (RefinementWP.optD fun a => if Pre a then some ((), fa a) else none)
        (fun _ _ _ => True) :=
  (corresIsa_iff_rrelPT isa P SR Pre fa fuel).trans
    (WRP.guardedRRelPT_iff_refines (T := fun m (_ : Unit) m' => isa.lsemFuelMemF P fuel m = some m')
      (isa.runM P fuel) fun Q s =>
        (wp_runM_bot_iff isa P fuel Q s).trans
          ⟨fun ⟨v, s', h, _, hq⟩ => ⟨v, s', h, hq⟩, fun ⟨v, s', h, hq⟩ => ⟨v, s', h, rfl, hq⟩⟩)

end CatCrypt.Crypto.SecureCompilation.Ascent

end
