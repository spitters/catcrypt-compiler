/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakM

/-!
# Constant time modulo the declassified sequence for `NFProg`

`NFProg.levelCheckD M isDeclass` (in `NFLeakM`) is the level checker in which an operation
marked by `isDeclass` is a declassification: it accepts arguments at every level and gives its
result the public level. Under `DeclassOk M isDeclass isDeclEv`, its soundness statement
`NFProg.levelCheckD_sound` gives, on valuations that agree on the public positions, equal
events of two successful runs or a first difference at a declassification event (`DeclDiff`).

The declassified sequence of a trace is its subsequence of declassification events; when both
runs have the same declassified sequence (`DeclIs`), their events are equal (`NFCTRelD`).

## Main definitions

* `DeclIs`, `NFCTRelD` — the declassified sequence of the successful runs, and constant time
  for runs with a given declassified sequence.

## Main results

* `DeclDiff.filter_ne` — traces that first differ at a declassification event have different
  declassified sequences.
* `NFProg.levelCheckD_trace` — the events of two runs are equal or first differ at a
  declassification event.
* `NFProg.nfCTRelD_of_levelCheckD` — a program the checker accepts is constant time for the
  runs with a given declassified sequence.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

/-- The declassified sequences of two traces that first differ at a declassification event
    differ. -/
theorem DeclDiff.filter_ne {D : CTLeak → Bool} {t₁ t₂ : List CTLeak} (h : DeclDiff D t₁ t₂) :
    t₁.filter D ≠ t₂.filter D := by
  obtain ⟨pre, s₁, s₂, a₁, a₂, hne, h₁, h₂, rfl, rfl⟩ := h
  intro heq
  simp only [List.filter_append, List.filter_cons, h₁, h₂, if_true, List.append_cancel_left_eq,
    List.cons.injEq] at heq
  exact hne heq.1

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

section Partial

variable [DialectDenoteM d Option]

/-- Every successful leakage run of `p` from `V` has declassified sequence `ds`: its
    subsequence of events satisfying `isDeclEv`. -/
def DeclIs (M : LeakModel d) (isDeclEv : CTLeak → Bool) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) (ds : List CTLeak) : Prop :=
  ∀ r, NFProg.leakRunM M fuel p V = some r → r.2.filter isDeclEv = ds

/-- Constant time of a program for the entry labels `L` modulo the declassified sequence
    `ds`: two valuations that agree on the positions `L` marks public, whose successful runs
    have declassified sequence `ds`, from which the program runs to results, give equal
    events. -/
def NFCTRelD (M : LeakModel d) (isDeclEv : CTLeak → Bool) {Γ : Ctxt d} {ts : List d.Ty}
    (L : Labels Γ) (fuel : Nat) (p : NFProg d Γ ts) (ds : List CTLeak) : Prop :=
  ∀ (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation ts × List CTLeak), PubEqV L V₁ V₂ →
    DeclIs M isDeclEv fuel p V₁ ds → DeclIs M isDeclEv fuel p V₂ ds →
    NFProg.leakRunM M fuel p V₁ = some r₁ → NFProg.leakRunM M fuel p V₂ = some r₂ → r₁.2 = r₂.2

/-- On valuations that agree on the positions `L` marks public, the events of two successful
    runs of a program the checker accepts are equal or first differ at a declassification
    event. -/
theorem NFProg.levelCheckD_trace (M : LeakModel d) (isDeclass : d.Op → Bool)
    (isDeclEv : CTLeak → Bool) (hD : DeclassOk M isDeclass isDeclEv) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheckD M isDeclass p L).isSome) (V₁ V₂ : Valuation Γ)
    (r₁ r₂ : Valuation ts × List CTLeak) (hp : PubEqV L V₁ V₂)
    (h₁ : NFProg.leakRunM M fuel p V₁ = some r₁) (h₂ : NFProg.leakRunM M fuel p V₂ = some r₂) :
    r₁.2 = r₂.2 ∨ DeclDiff isDeclEv r₁.2 r₂.2 := by
  rcases hR : NFProg.levelCheckD M isDeclass p L with _ | R
  · rw [hR] at h; cases h
  · rcases NFProg.levelCheckD_sound M isDeclass isDeclEv hD fuel p L R hR V₁ V₂ r₁ r₂ hp h₁ h₂
      with ⟨he, -⟩ | hd
    · exact Or.inl he
    · exact Or.inr hd

/-- A program the checker `levelCheckD` accepts for the entry labels `L` is constant time for
    `L` modulo every declassified sequence, at every fuel. -/
theorem NFProg.nfCTRelD_of_levelCheckD (M : LeakModel d) (isDeclass : d.Op → Bool)
    (isDeclEv : CTLeak → Bool) (hD : DeclassOk M isDeclass isDeclEv) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheckD M isDeclass p L).isSome) (ds : List CTLeak) :
    NFCTRelD M isDeclEv L fuel p ds := by
  intro V₁ V₂ r₁ r₂ hp hd₁ hd₂ h₁ h₂
  rcases NFProg.levelCheckD_trace M isDeclass isDeclEv hD fuel p L h V₁ V₂ r₁ r₂ hp h₁ h₂
    with he | hd
  · exact he
  · exact absurd ((hd₁ r₁ h₁).trans (hd₂ r₂ h₂).symm) hd.filter_ne

end Partial

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
