/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract
public import CatCryptCore.Prob.SDistrChain
public import CatCryptCore.Relational.Approx

/-!
# Probabilistic interpretation of a fuel family of call trees

`RuttF` relates a source call tree to a family of target trees indexed by fuel, such as the
target trees `targetTree` of a calling body. This module interprets such a family in `SPComp` and
gives the counterpart of `interpSP_ruttS` for `RuttF`.

The leaves of a target tree are optional, and the leaf `none` is read as failure (`interpSPOpt`).
The trees of a family are ordered by `FuelLe`, in which the leaf `none` is below every tree;
`targetTree` is increasing in the fuel in this order (`targetTree_fuelLe`). The interpretations
of an increasing family form a chain of `SPComp`, ordered as sub-probability measures, and the
interpretation `interpSPω` of the family is the supremum of this chain. Its failure weight is the
probability that the target does not reach a leaf `some` at any fuel.

The source handler is the point mass at a pure handler, so the source interpretation is a point
mass. A point mass is coupled with a computation only when the latter does not fail; the judgment
`interpSP_ruttF` therefore holds at the supremum, under the hypothesis that the supremum does not
fail. Every value in the support of the supremum is related to the source leaf without that
hypothesis (`ruttF_interpSPω_support`), and the statistical distance of the values read back
from the source and the target is at most the failure weight of the target plus the failure
weight of the source read-back (`sdist_readBack_ruttF`).

## Main definitions

* `FuelLe`, `FuelMono`: the fuel order on call trees with optional leaves, and increasing
  families.
* `interpSPOpt`: the interpretation of a tree with the leaf `none` read as failure.
* `interpSPω`: the interpretation of an increasing family, the supremum over the fuel.
* `readBack`: a computation followed by a partial read-back map.
* `HandlerCoupledCG`: a target handler coupled with the meanings of the linked functions on the
  separation contracts at the guarded event relation `contractREG`.
* `interpTargetω`, `srcRead`: the interpretation of the target trees of a calling body, and the
  read-back of a source leaf.

## Main results

* `targetTree_fuelLe`, `fuelMono_targetTree`: the target trees are increasing in the fuel.
* `ruttF_interpSPω_support`: every value of the interpretation of a family related by `RuttF`
  is related to the source leaf, or the source leaf fails.
* `interpSP_ruttF`: the judgment `rHoare` between the source interpretation and the
  interpretation of a related family that does not fail.
* `sdist_readBack_ruttF`: the statistical distance of the read-backs.
* `interpSP_ruttF_contract`, `sdist_readBack_contract`: the two results at the separation
  contracts, the relation of the results `resRel` and the read-back `σ.result.read`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel

open OmegaCompletePartialOrder
open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP (HandlerCoupled)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr callOps retOps)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax (HaxModule)
open _root_.Hax

/-! ## The fuel order -/

section Fuel

variable {E : EventSig} {R : Type}

/-- **The fuel order on call trees with optional leaves**: the leaf `none` is below every tree,
    a leaf is below itself, and an event is below the same event with continuations above
    pointwise. -/
inductive FuelLe : CallTree E (Option R) → CallTree E (Option R) → Prop
  | none (t : CallTree E (Option R)) : FuelLe (.ret none) t
  | ret (r : Option R) : FuelLe (.ret r) (.ret r)
  | vis (e : E.Event) {k k' : E.Resp e → CallTree E (Option R)} (h : ∀ a, FuelLe (k a) (k' a)) :
      FuelLe (.vis e k) (.vis e k')

/-- A family of call trees indexed by fuel, increasing in the fuel order. -/
def FuelMono (T : Nat → CallTree E (Option R)) : Prop :=
  ∀ n, FuelLe (T n) (T (n + 1))

/-- The continuations of two events related by the fuel order are related at every answer. -/
theorem FuelLe.vis_inv {e : E.Event} {k k' : E.Resp e → CallTree E (Option R)}
    (h : FuelLe (.vis e k) (.vis e k')) (a : E.Resp e) : FuelLe (k a) (k' a) := by
  cases h with
  | vis _ h => exact h a

/-- A tree above a leaf `some` is that leaf. -/
theorem FuelLe.eq_of_some {x : R} {t : CallTree E (Option R)} (h : FuelLe (.ret (some x)) t) :
    t = .ret (some x) := by
  cases h
  rfl

/-- In an increasing family, a leaf `some` stays at every larger fuel. -/
theorem FuelMono.ret_some {T : Nat → CallTree E (Option R)} (hT : FuelMono T) {n : Nat}
    {x : R} (hn : T n = .ret (some x)) : ∀ m, n ≤ m → T m = .ret (some x) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hn
  | succ m _ ih =>
    have h := hT m
    rw [ih] at h
    exact h.eq_of_some

end Fuel

/-! ## Interpretation of a fuel family -/

section Interp

variable {E : EventSig} {R : Type}

/-- The read of an optional leaf as a computation: `some r` returns `r`, `none` fails. -/
noncomputable def optSP {α : Type} : Option α → SPComp α
  | some r => SPComp.pure r
  | none => SPComp.fail

/-- **Interpretation of a tree with optional leaves**: `interpSP`, with the leaf `none` read as
    failure. -/
noncomputable def interpSPOpt (h : ∀ e : E.Event, SPComp (E.Resp e))
    (t : CallTree E (Option R)) : SPComp R :=
  (interpSP h t).bind optSP

/-- Unfolding lemma of `interpSPOpt` at a leaf `some`. -/
@[simp] theorem interpSPOpt_ret_some (h : ∀ e : E.Event, SPComp (E.Resp e)) (x : R) :
    interpSPOpt h (.ret (some x)) = SPComp.pure x :=
  SPComp.pure_bind _ _

/-- Unfolding lemma of `interpSPOpt` at the leaf `none`. -/
@[simp] theorem interpSPOpt_ret_none (h : ∀ e : E.Event, SPComp (E.Resp e)) :
    interpSPOpt h (.ret (none : Option R)) = SPComp.fail :=
  SPComp.pure_bind _ _

/-- Unfolding lemma of `interpSPOpt` at an event. -/
theorem interpSPOpt_vis (h : ∀ e : E.Event, SPComp (E.Resp e)) (e : E.Event)
    (k : E.Resp e → CallTree E (Option R)) :
    interpSPOpt h (.vis e k) = (h e).bind fun a => interpSPOpt h (k a) := by
  simp only [interpSPOpt, interpSP_vis, SPComp.bind_assoc]

/-- **The interpretation is monotone in the fuel order.** -/
theorem interpSPOpt_mono (h : ∀ e : E.Event, SPComp (E.Resp e)) {t t' : CallTree E (Option R)}
    (hle : FuelLe t t') : interpSPOpt h t ≤ interpSPOpt h t' := by
  induction hle with
  | none t =>
    rw [interpSPOpt_ret_none]
    refine SPComp.le_def.mpr fun s => SDistr.le_def.mpr fun a => ?_
    simp [SPComp.fail, SDistr.fail_apply_some]
  | ret r => exact le_rfl
  | vis e _ ih =>
    rw [interpSPOpt_vis, interpSPOpt_vis]
    exact SPComp.bind_mono_right _ fun a => ih a

/-- The chain of the interpretations of an increasing family. -/
noncomputable def interpChain (h : ∀ e : E.Event, SPComp (E.Resp e))
    (T : Nat → CallTree E (Option R)) (hT : FuelMono T) : Chain (SPComp R) :=
  ⟨fun n => interpSPOpt h (T n), monotone_nat_of_le_succ fun n => interpSPOpt_mono h (hT n)⟩

/-- **The interpretation of an increasing fuel family**: the supremum over the fuel of the
    interpretations of its trees. -/
noncomputable def interpSPω (h : ∀ e : E.Event, SPComp (E.Resp e))
    (T : Nat → CallTree E (Option R)) (hT : FuelMono T) : SPComp R :=
  ωSup (interpChain h T hT)

/-- The weight of a value under the interpretation of a family is the supremum over the fuel of
    its weights. -/
theorem interpSPω_apply_some (h : ∀ e : E.Event, SPComp (E.Resp e))
    (T : Nat → CallTree E (Option R)) (hT : FuelMono T) (s : Heap) (p : R × Heap) :
    interpSPω h T hT s (some p) = ⨆ n, interpSPOpt h (T n) s (some p) :=
  rfl

end Interp

/-! ## The target trees are increasing in the fuel -/

section Target

variable {σ : Type} (M : Machine σ) (prog : List RInstr) (sym : Nat → String)
  (rd : String → σ → List Value)

/-- **Fuel monotonicity of the target tree**: the target tree at a fuel is below the target tree
    at every larger fuel. -/
theorem targetTree_fuelLe :
    ∀ (n m pc : Nat) (s : σ), n ≤ m →
      FuelLe (targetTree M prog sym rd n pc s) (targetTree M prog sym rd m pc s) := by
  intro n
  induction n with
  | zero => intro m pc s _; exact .none _
  | succ n ih =>
    intro m pc s hle
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [targetTree]
    split
    · refine .vis _ fun r => ?_
      cases r with
      | some sc => exact ih _ _ _ (by omega)
      | none => exact .none _
    · split
      · exact .none _
      · exact .ret _
      · exact ih _ _ _ (by omega)

/-- The target trees from a fixed index and state form an increasing family. -/
theorem fuelMono_targetTree (pc : Nat) (s : σ) :
    FuelMono fun n => targetTree M prog sym rd n pc s :=
  fun n => targetTree_fuelLe M prog sym rd n (n + 1) pc s (Nat.le_succ n)

end Target

/-! ## Relating a source tree and a fuel family -/

/-- **A point mass coupled with a computation**: every value in the support of the computation
    satisfies the postcondition at the value of the point mass. -/
theorem rHoare_pure_left_support {α β : Type} {Φ : RPre} {a : α} {c : SPComp β}
    {Ψ : RPost α β} (h : rHoare Φ (SPComp.pure a) c Ψ) {s₁ s₂ : Heap} (hΦ : Φ s₁ s₂) {b : β}
    {s₂' : Heap} (hb : c s₂ (some (b, s₂')) ≠ 0) : Ψ a s₁ b s₂' := by
  obtain ⟨cp, hsat⟩ := h s₁ s₂ hΦ
  rw [← cp.right_marginal_sum] at hb
  obtain ⟨p₁, hp⟩ := exists_ne_zero_of_tsum_ne_zero hb
  have h1 : p₁ = (a, s₁) := by
    have := Coupling.in_left_support _ hp
    classical
    simpa [SPComp.pure, SDistr.pure, PMF.pure_apply, eq_comm] using this
  have := hsat p₁ (b, s₂') hp
  rw [h1] at this
  exact this

section Generic

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
  {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR : R₁ → Option R₂ → Prop} {Fail : R₁ → Prop} {I : RPre}
  {h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e)}

/-- **Support of the interpretation of a related family at a fuel.** Under a target handler
    coupled at related events with the point mass of the source handler, every value of the
    interpretation of a tree of an increasing family related by `RuttF` is related to the source
    leaf, at heaps related by `I`, or the source leaf fails. -/
theorem ruttF_interpSPOpt_support
    (hc : HandlerCoupled I RE RA (fun e => SPComp.pure (h₁ e)) h₂)
    (hRF : ∀ r₁, RR r₁ none → Fail r₁)
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ (Option R₂)}
    (h : RuttF h₁ RE RA RR Fail t₁ T) :
    FuelMono T → ∀ (n : Nat) {s₁ s₂ : Heap}, I s₁ s₂ → ∀ {x : R₂} {s' : Heap},
      interpSPOpt h₂ (T n) s₂ (some (x, s')) ≠ 0 →
      Fail (interp h₁ t₁) ∨ (RR (interp h₁ t₁) (some x) ∧ I s₁ s') := by
  induction h with
  | @ret r₁ r₂ T n hT hR =>
    intro hmono M s₁ s₂ hI x s' hx
    cases r₂ with
    | none => exact .inl (hRF _ hR)
    | some x₀ =>
      have hle : interpSPOpt h₂ (T M) s₂ (some (x, s')) ≤
          interpSPOpt h₂ (T (max n M)) s₂ (some (x, s')) :=
        (interpChain h₂ T hmono).monotone (le_max_right n M) s₂ (x, s')
      have hx' := pos_iff_ne_zero.mp ((pos_iff_ne_zero.mpr hx).trans_le hle)
      rw [hmono.ret_some hT _ (le_max_left n M), interpSPOpt_ret_some] at hx'
      have hp : (x, s') = (x₀, s₂) := by
        classical
        simpa [SPComp.pure, SDistr.pure, PMF.pure_apply, eq_comm] using hx'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      exact .inr ⟨hR, hI⟩
  | fail hF => intro _ _ _ _ _ _ _ _; exact .inl hF
  | @vis e₁ e₂ k₁ T K n hT he _ ih =>
    intro hmono M s₁ s₂ hI x s' hx
    have hle : interpSPOpt h₂ (T M) s₂ (some (x, s')) ≤
        interpSPOpt h₂ (T (n + M)) s₂ (some (x, s')) :=
      (interpChain h₂ T hmono).monotone (Nat.le_add_left M n) s₂ (x, s')
    have hx' := pos_iff_ne_zero.mp ((pos_iff_ne_zero.mpr hx).trans_le hle)
    rw [hT M, interpSPOpt_vis] at hx'
    obtain ⟨a, s'', ha, hk⟩ := SDistr.bind_support_witness_pair hx'
    have hK : FuelMono (K a) := fun m => by
      have h := hmono (n + m)
      rw [hT m, show n + m + 1 = n + (m + 1) by omega, hT (m + 1)] at h
      exact h.vis_inv a
    obtain ⟨hRA, hI'⟩ := rHoare_pure_left_support (hc e₁ e₂ he) hI ha
    exact ih _ a hRA hK M hI' hk
  | skip _ ih => exact ih

/-- **Support of the interpretation of a related family.** Every value of the interpretation of
    an increasing family related by `RuttF` is related to the source leaf, at heaps related by
    `I`, or the source leaf fails. -/
theorem ruttF_interpSPω_support
    (hc : HandlerCoupled I RE RA (fun e => SPComp.pure (h₁ e)) h₂)
    (hRF : ∀ r₁, RR r₁ none → Fail r₁)
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ (Option R₂)} (hT : FuelMono T)
    (h : RuttF h₁ RE RA RR Fail t₁ T) {s₁ s₂ : Heap} (hI : I s₁ s₂) {x : R₂} {s' : Heap}
    (hx : interpSPω h₂ T hT s₂ (some (x, s')) ≠ 0) :
    Fail (interp h₁ t₁) ∨ (RR (interp h₁ t₁) (some x) ∧ I s₁ s') := by
  rw [interpSPω_apply_some] at hx
  obtain ⟨n, hn⟩ : ∃ n, interpSPOpt h₂ (T n) s₂ (some (x, s')) ≠ 0 := by
    by_contra hc'
    simp only [not_exists, not_not] at hc'
    exact hx (ENNReal.iSup_eq_zero.mpr hc')
  exact ruttF_interpSPOpt_support hc hRF h hT n hI hn

/-- **Probabilistic interpretation of a tree and a related fuel family.** Under a target handler
    coupled at related events with the point mass of the source handler `h₁`, a source tree and
    an increasing family related by `RuttF` at `h₁` interpret, from heaps related by `I`, to a
    failed source leaf or to leaves related by `RR` at heaps related by `I`, when the
    interpretation of the family does not fail. -/
theorem interpSP_ruttF
    (hc : HandlerCoupled I RE RA (fun e => SPComp.pure (h₁ e)) h₂)
    (hRF : ∀ r₁, RR r₁ none → Fail r₁)
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ (Option R₂)} (hT : FuelMono T)
    (hl : ∀ s, interpSPω h₂ T hT s none = 0) (h : RuttF h₁ RE RA RR Fail t₁ T) :
    rHoare I (interpSP (fun e => SPComp.pure (h₁ e)) t₁) (interpSPω h₂ T hT)
      (fun r₁ s₁ x s₂ => Fail r₁ ∨ (RR r₁ (some x) ∧ I s₁ s₂)) := by
  rw [interpSP_pure]
  intro s₁ s₂ hI
  refine ⟨Coupling.prod _ _ (SDistr.mass_pure _) (by simp [SDistr.mass, hl s₂]), ?_⟩
  intro p₁ p₂ hp
  have h1 : p₁ = (interp h₁ t₁, s₁) := by
    have := Coupling.in_left_support _ hp
    classical
    simpa [SPComp.pure, SDistr.pure, PMF.pure_apply, eq_comm] using this
  rw [h1]
  exact ruttF_interpSPω_support hc hRF hT h hI (Coupling.in_right_support _ hp)

/-- The read-back of a computation by a partial map: the value the map reads back from the
    result, failing where the map is undefined. -/
noncomputable def readBack {α V : Type} (rb : α → Option V) (c : SPComp α) : SPComp V :=
  c.bind fun r => optSP (rb r)

/-- The read-back by a total map adds no failure weight. -/
theorem readBack_some_apply_none {α V : Type} (rb : α → V) (c : SPComp α) (s : Heap) :
    readBack (fun r => some (rb r)) c s none = c s none := by
  simp only [readBack, SPComp.bind, SDistr.bind_apply_none]
  simp [optSP, SPComp.pure, SDistr.pure_apply_none]

/-- **Statistical distance of the read-backs of a tree and a related fuel family.** Under a
    target handler coupled at related events, at equal heaps, with the point mass of the source
    handler, let a source tree and an increasing family be related by `RuttF`. Let the source
    read-back `rb₁` be undefined at failed source leaves and agree with the target read-back
    `rb₂` at related leaves. The statistical distance of the read-backs is at most a bound `ε` of
    the failure weight of the target plus a bound `δ` of the failure weight of the source
    read-back. -/
theorem sdist_readBack_ruttF {V : Type}
    (hc : HandlerCoupled eqPre RE RA (fun e => SPComp.pure (h₁ e)) h₂)
    (hRF : ∀ r₁, RR r₁ none → Fail r₁)
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ (Option R₂)} (hT : FuelMono T)
    (h : RuttF h₁ RE RA RR Fail t₁ T) (rb₁ : R₁ → Option V) (rb₂ : R₂ → V)
    (hF : ∀ r₁, Fail r₁ → rb₁ r₁ = none)
    (hrb : ∀ r₁ x v, RR r₁ (some x) → rb₁ r₁ = some v → rb₂ x = v)
    {ε δ : ℝ≥0∞} (hε : ∀ s, interpSPω h₂ T hT s none ≤ ε)
    (hδ : ∀ s, readBack rb₁ (interpSP (fun e => SPComp.pure (h₁ e)) t₁) s none ≤ δ) :
    sdist (fun _ : Unit => readBack rb₁ (interpSP (fun e => SPComp.pure (h₁ e)) t₁))
      (fun _ : Unit => readBack (fun x => some (rb₂ x)) (interpSPω h₂ T hT)) ≤ ε + δ := by
  have hsrc : readBack rb₁ (interpSP (fun e => SPComp.pure (h₁ e)) t₁) =
      optSP (rb₁ (interp h₁ t₁)) := by
    rw [readBack, interpSP_pure, SPComp.pure_bind]
  classical
  refine rHoareApprox_sdist fun s₀ s hs => ?_
  obtain rfl : s₀ = s := hs
  rw [hsrc]
  rw [hsrc] at hδ
  set d₂ := readBack (fun x => some (rb₂ x)) (interpSPω h₂ T hT) s₀ with hd₂
  have hone : d₂ none + ∑' b, d₂ (some b) = 1 := by
    rw [← SDistr.tsum_option_eq_add]; exact d₂.tsum_coe
  have hnone : d₂ none ≤ ε := by
    rw [hd₂, readBack_some_apply_none]; exact hε s₀
  cases hv : rb₁ (interp h₁ t₁) with
  | none =>
    have h1 : (1 : ℝ≥0∞) ≤ δ := by
      have := hδ s₀
      rwa [hv, optSP, SPComp.fail, SDistr.fail_apply_none] at this
    refine liftRApprox_mono_rel (fun p₁ p₂ hp => pairPost_of_eq hp) (liftRApprox_eq_of_tv ?_ ?_)
    · simp [tvMargin, optSP, SPComp.fail, SDistr.fail_apply_some]
    · calc tvMargin d₂ (optSP none s₀) = ∑' b, d₂ (some b) := by
            simp [tvMargin, optSP, SPComp.fail, SDistr.fail_apply_some]
        _ ≤ 1 := hone ▸ le_add_self
        _ ≤ ε + δ := h1.trans le_add_self
  | some v =>
    have hsupp : ∀ b, d₂ (some b) ≠ 0 → b = (v, s₀) := by
      intro b hb
      simp only [hd₂, readBack, SPComp.bind] at hb
      obtain ⟨x, s', hx, hpb⟩ := SDistr.bind_support_witness_pair hb
      have hb' : b = (rb₂ x, s') := by
        simpa [optSP, SPComp.pure, SDistr.pure, PMF.pure_apply, eq_comm] using hpb
      rcases ruttF_interpSPω_support hc hRF hT h (rfl : eqPre s₀ s₀) hx with hf | ⟨hR, hs⟩
      · rw [hF _ hf] at hv
        cases hv
      · rw [hb', hrb _ _ _ hR hv, ← hs]
    have hd : d₂ (some (v, s₀)) + d₂ none = 1 := by
      rw [← hone, add_comm, tsum_eq_single (v, s₀) fun b hb => by
        by_contra h0
        exact hb (hsupp b h0)]
    refine liftRApprox_mono_rel (fun p₁ p₂ hp => pairPost_of_eq hp) (liftRApprox_eq_of_tv ?_ ?_)
    · calc tvMargin (optSP (some v) s₀) d₂ = 1 - d₂ (some (v, s₀)) := by
            rw [tvMargin, tsum_eq_single (v, s₀) fun b hb => by
              simp [optSP, SPComp.pure, SDistr.pure_apply_some, Ne.symm hb]]
            simp [optSP, SPComp.pure, SDistr.pure_apply_some]
        _ ≤ d₂ none := tsub_le_iff_left.mpr hd.ge
        _ ≤ ε + δ := hnone.trans le_self_add
    · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun b => tsub_eq_zero_of_le ?_)
        (by simp)
      by_cases h0 : d₂ (some b) = 0
      · simp [h0]
      · rw [hsupp b h0]
        simpa [optSP, SPComp.pure, SDistr.pure_apply_some] using PMF.coe_le_one d₂ _

end Generic

/-! ## The separation contracts at the guarded event relation -/

/-- **A target handler in `SPComp` coupled with the meanings of the linked functions on the
    separation contracts at the guarded event relation `contractREG`.** -/
def HandlerCoupledCG (m : HaxModule) (I : RPre)
    (h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) : Prop :=
  HandlerCoupled I (contractREG m) (contractRAC m) (fun e => SPComp.pure (linkHandler m e)) h₂

/-- **The interpretation of the target trees** of the calling body `pc` from the entry state
    `sa`, under the target handler `h₂`: the supremum over the fuel. -/
noncomputable def interpTargetω (m : HaxModule) (pc : List RInstr) (sym : Nat → String)
    (sa : AState) (h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) :
    SPComp AState :=
  interpSPω h₂ (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa)
    (fuelMono_targetTree aMachine pc sym (linkRead m) 0 sa)

/-- The read-back of a source leaf: a value that is not a control-flow value. -/
def srcRead (r₁ : Outcome × Env) : Option Value :=
  match r₁.1 with
  | .val v => if v.isControlFlow = false then some v else none
  | _ => none

/-- A source leaf related by `resRel` to the target leaf `none` fails. -/
theorem srcFail_of_resRel_none {σ : AbiLayout} {sa : AState} {r₁ : Outcome × Env}
    (h : resRel σ sa r₁ none) : srcFail r₁ := by
  intro v hv
  by_contra hcf
  obtain ⟨s', hs', -⟩ := h v hv (by simpa using hcf)
  cases hs'

/-- A failed source leaf has no read-back. -/
theorem srcRead_of_srcFail {r₁ : Outcome × Env} (h : srcFail r₁) : srcRead r₁ = none := by
  unfold srcRead srcFail at *; split <;> simp_all

/-- The read-back of a source leaf related by `resRel` to a target leaf is the read-back of the
    result from the target leaf. -/
theorem read_of_resRel {σ : AbiLayout} {sa s' : AState} {r₁ : Outcome × Env} {v : Value}
    (h : resRel σ sa r₁ (some s')) (hv : srcRead r₁ = some v) : σ.result.read sa s' = v := by
  unfold srcRead at hv
  split at hv
  · rename_i w hw
    by_cases hcf : w.isControlFlow = false
    · simp only [hcf, ite_true, Option.some.injEq] at hv
      subst hv
      obtain ⟨s'', hs'', hres⟩ := h _ hw hcf
      cases hs''
      exact hres.symm
    · simp [hcf] at hv
  · cases hv

/-- **Probabilistic interpretation at the separation contracts.** Under a target handler coupled
    with the meanings of the linked functions of `m` on the separation contracts at the guarded
    event relation, a source tree related by `RuttF` to the target trees of the calling body
    `pc` from `sa` interprets, from heaps related by `I`, to a failed source leaf or to a leaf
    read back by `σ` from the return state, at heaps related by `I`, when the interpretation of
    the target trees does not fail. -/
theorem interpSP_ruttF_contract {m : HaxModule} {σ : AbiLayout} {sa : AState}
    {pc : List RInstr} {sym : Nat → String} {I : RPre}
    {h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hc : HandlerCoupledCG m I h₂) (hl : ∀ s, interpTargetω m pc sym sa h₂ s none = 0)
    {t₁ : CallTree linkSig (Outcome × Env)}
    (h : RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail t₁
      (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa)) :
    rHoare I (interpSP (fun e => SPComp.pure (linkHandler m e)) t₁)
      (interpTargetω m pc sym sa h₂)
      (fun r₁ s₁ s' s₂ => srcFail r₁ ∨ (resRel σ sa r₁ (some s') ∧ I s₁ s₂)) :=
  interpSP_ruttF hc (fun _ => srcFail_of_resRel_none) _ hl h

/-- **Statistical distance at the separation contracts.** Under a target handler coupled at
    equal heaps with the meanings of the linked functions of `m` on the separation contracts at
    the guarded event relation, let a source tree be related by `RuttF` to the target trees of
    the calling body `pc` from `sa`. The statistical distance of the source value read back by
    `srcRead` and the target value read back by `σ` from the return state is at most a bound `ε`
    of the failure weight of the target plus a bound `δ` of the failure weight of the source
    read-back. -/
theorem sdist_readBack_contract {m : HaxModule} {σ : AbiLayout} {sa : AState}
    {pc : List RInstr} {sym : Nat → String}
    {h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hc : HandlerCoupledCG m eqPre h₂) {t₁ : CallTree linkSig (Outcome × Env)}
    (h : RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail t₁
      (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa))
    {ε δ : ℝ≥0∞} (hε : ∀ s, interpTargetω m pc sym sa h₂ s none ≤ ε)
    (hδ : ∀ s, readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e)) t₁) s none
      ≤ δ) :
    sdist (fun _ : Unit => readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e)) t₁))
      (fun _ : Unit => readBack (fun s' => some (σ.result.read sa s'))
        (interpTargetω m pc sym sa h₂)) ≤ ε + δ :=
  sdist_readBack_ruttF hc (fun _ => srcFail_of_resRel_none) _ h srcRead _
    (fun _ => srcRead_of_srcFail) (fun _ _ _ => read_of_resRel) hε hδ

end CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
