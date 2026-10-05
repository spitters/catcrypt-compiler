/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Calculus.CorresGenericSpec
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

/-!
# The correspondence over an instruction set: `CorresIsa`

`CorresIsa isa P SR Pre fa fuel` is the generic forward simulation `CorresM` of
`CorresMCore` at the machine whose step is the canonical run `Isa.lsemFuelMemF` of the
instruction set `isa` on the `Lprog` program `P`. The program coordinate `C` of `CorresM` is
the fuel: the judgement states that from every flag-extended state `m` related by `SR` to an
abstract state `a` satisfying `Pre`, the run of `P` with `fuel` steps halts
(`Isa.lsemFuelMemF` returns `some`) in a state related to `fa a`. Because the definition is
`CorresM` at the step `isa.lsemFuelMemF P`, every theorem about `CorresM` applies to it
unchanged; `corresIsa_iff_post` is the instance of `corresM_iff_post`.

A run of `Isa.lsemFuelMemF` that returns `some t` ends in a halted state
(`lsemFuelMemF_halted`), and the same result is returned at every larger fuel
(`Isa.lsemFuelMemF_add`). The judgement is therefore monotone in the fuel
(`corresIsa_fuel_mono`), and the existential form `CorresIsaRun`, which quantifies the fuel
inside the simulation, follows from it (`corresIsaRun_of_corresIsa`).

## Main results

* `CorresIsa`, `corresIsa_eq_corresM`: the judgement and its definitional unfolding.
* `corresIsa_post`, `corresIsa_of_post`, `corresIsa_iff_post`: the judgement as the family of
  step triples over all postconditions.
* `lsemFuelMemF_halted`: a successful run halts.
* `corresIsa_fuel_add`, `corresIsa_fuel_mono`: monotonicity in the fuel.
* `CorresIsaRun`, `corresIsaRun_of_corresIsa`: the correspondence with the fuel chosen per
  initial state.
* `corresIsa_halted`: a program whose related states are all halted corresponds to the
  identity abstraction at every fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM findInstrMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)

/-- **The correspondence over an instruction set.** `CorresM` at the step
    `isa.lsemFuelMemF P`, whose program coordinate is the fuel: from a flag-extended state
    related by `SR` to an abstract state satisfying `Pre`, the canonical run of the `Lprog`
    program `P` under the instruction set `isa` with `fuel` steps halts in a state related
    to `fa a`. -/
def CorresIsa {AState : Type} (isa : Isa) (P : LprogM) (SR : LstateMF → AState → Prop)
    (Pre : AState → Prop) (fa : AState → AState) (fuel : Nat) : Prop :=
  CorresM (isa.lsemFuelMemF P) SR Pre fa fuel

section Generic

variable {AState : Type} {isa : Isa} {P : LprogM} {SR : LstateMF → AState → Prop}
  {Pre : AState → Prop} {fa : AState → AState} {fuel : Nat}

theorem corresIsa_eq_corresM :
    CorresIsa isa P SR Pre fa fuel = CorresM (isa.lsemFuelMemF P) SR Pre fa fuel := rfl

/-- `corresM_post` at the run of an instruction set. -/
theorem corresIsa_post (h : CorresIsa isa P SR Pre fa fuel) (Q : LstateMF → Prop) :
    StepTriple (isa.lsemFuelMemF P)
      (fun m => ∃ a, SR m a ∧ Pre a ∧ ∀ m', SR m' (fa a) → Q m') fuel Q :=
  corresM_post h Q

/-- `corresM_of_post` at the run of an instruction set. -/
theorem corresIsa_of_post
    (h : ∀ Q : LstateMF → Prop, StepTriple (isa.lsemFuelMemF P)
      (fun m => ∃ a, SR m a ∧ Pre a ∧ ∀ m', SR m' (fa a) → Q m') fuel Q) :
    CorresIsa isa P SR Pre fa fuel :=
  corresM_of_post h

/-- `CorresIsa` is equivalent to the family of step triples over all postconditions
    (`corresM_iff_post` at the run of an instruction set). -/
theorem corresIsa_iff_post :
    CorresIsa isa P SR Pre fa fuel ↔ ∀ Q : LstateMF → Prop,
      StepTriple (isa.lsemFuelMemF P)
        (fun m => ∃ a, SR m a ∧ Pre a ∧ ∀ m', SR m' (fa a) → Q m') fuel Q :=
  corresM_iff_post

end Generic

/-! ## The run halts, and more fuel returns the same state -/

/-- A successful run ends in a halted state: no instruction is fetched at its pc. -/
theorem lsemFuelMemF_halted (isa : Isa) (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), isa.lsemFuelMemF P fuel s = some t →
      findInstrMem P t.prog = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      simp only [Isa.lsemFuelMemF] at h
      split at h
      · next hf => cases h; exact hf
      · cases h
  | succ n ih =>
      intro s t h
      simp only [Isa.lsemFuelMemF] at h
      split at h
      · next hf => cases h; exact hf
      · split at h
        · exact ih _ t h
        · cases h

section Fuel

variable {AState : Type} {isa : Isa} {P : LprogM} {SR : LstateMF → AState → Prop}
  {Pre : AState → Prop} {fa : AState → AState}

/-- The correspondence at a fuel holds at every larger fuel. -/
theorem corresIsa_fuel_add {n : Nat} (h : CorresIsa isa P SR Pre fa n) (k : Nat) :
    CorresIsa isa P SR Pre fa (n + k) := by
  intro m a hSR hPre
  obtain ⟨m', hrun, hSR'⟩ := h m a hSR hPre
  exact ⟨m', isa.lsemFuelMemF_add P n k m m' hrun, hSR'⟩

/-- Monotonicity of the correspondence in the fuel. -/
theorem corresIsa_fuel_mono {n n' : Nat} (h : CorresIsa isa P SR Pre fa n) (hle : n ≤ n') :
    CorresIsa isa P SR Pre fa n' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact corresIsa_fuel_add h k

/-- **The correspondence with the fuel chosen per initial state**: from a related state the
    run of `P` halts at some fuel in a state related to `fa a`. -/
def CorresIsaRun (isa : Isa) (P : LprogM) (SR : LstateMF → AState → Prop)
    (Pre : AState → Prop) (fa : AState → AState) : Prop :=
  ∀ m a, SR m a → Pre a → ∃ fuel m', isa.lsemFuelMemF P fuel m = some m' ∧ SR m' (fa a)

/-- A correspondence at a fixed fuel gives the correspondence with the fuel chosen per
    initial state. -/
theorem corresIsaRun_of_corresIsa {n : Nat} (h : CorresIsa isa P SR Pre fa n) :
    CorresIsaRun isa P SR Pre fa := by
  intro m a hSR hPre
  obtain ⟨m', hrun, hSR'⟩ := h m a hSR hPre
  exact ⟨n, m', hrun, hSR'⟩

/-- On a program whose related states are halted, the run is the identity: the
    correspondence holds at the identity abstraction and every fuel. -/
theorem corresIsa_halted (hhalt : ∀ m a, SR m a → findInstrMem P m.prog = none)
    (fuel : Nat) : CorresIsa isa P SR Pre id fuel := by
  intro m a hSR _
  exact ⟨m, isa.lsemFuelMemF_halt P fuel m (hhalt m a hSR), hSR⟩

end Fuel

end CatCrypt.Crypto.SecureCompilation.Ascent
