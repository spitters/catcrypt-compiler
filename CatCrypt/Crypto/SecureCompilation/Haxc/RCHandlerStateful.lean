/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
public import CatCryptCore.Relational.CouplingMass

/-!
# Robust compilation over stateful probabilistic source oracles

`RCHandlerKeyed` states robust compilation for source oracles that draw a key before the run and
answer each call by a point mass at that key. This module states it for source oracles whose
state changes across calls: a stateful handler answers a call at a handler state by a
computation of the answer and the next handler state (`interpSt`). The handler state is kept
apart from the heap, so that the heaps of the source and the target stay equal and the
distinguisher, which reads the final heap, sees no oracle state.

The source and target handlers are coupled up to failure (`RelF`): each computation is turned
into one that does not fail by moving its failure weight to an outcome `none` (`totC`), and the
two are coupled with a postcondition that holds at every pair with a failure on either side
(`FailOr`). A coupling up to failure at equality bounds the one-sided statistical distance by
the failure weight of the other side (`tvMargin_le_none_of_relF`). The target trees at a fuel
fail where the fuel runs out; the coupling holds at every fuel, and the bound passes to the
supremum over the fuel (`tvMargin_le_of_iSup`).

## Main definitions

* `totC`, `FailOr`, `RelF`: failure as a value, and couplings up to failure.
* `interpSt`, `interpStOpt`, `interpStω`: interpretation under a stateful handler.
* `StHandlerCoupled`, `StSkips`: stateful handlers coupled up to failure, and a stateful source
  handler answering skipped calls within the skip predicate.
* `StOracle`, `stSrc`, `stTgt`, `HandlerCoupledSt`, `HandlerRCSt`: stateful source oracles of
  the linked functions and robust compilation over them.
* `constSt`, `keyedSt`: a handler family indexed by the state, and a keyed oracle as a stateful
  oracle.

## Main results

* `relF_interpSt_ruttFA`: trees related by `RuttFA` interpret to outcomes coupled up to failure.
* `sdist_readBack_ruttFA`: the statistical distance of the read-backs under stateful handlers.
* `sdist_st_contract`: the statistical distance at a stateful oracle and the separation
  contracts.
* `handlerRCKeyed_of_handlerRCSt`: `HandlerRCKeyed` is the instance at `keyedSt`.
* `haxc_rcHSt`: for a result of `compileA`, `HandlerRCSt` at every stateful oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful

open OmegaCompletePartialOrder
open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA)

/-! ## Failure as a value -/

section FailVal

variable {α β γ δ : Type}

/-- An outcome of a computation with failure as a value: a value `a` with its heap is `some a`
    with that heap, and failure is `none` at the empty heap. -/
def failVal : Option (α × Heap) → Option (Option α × Heap)
  | some p => some (some p.1, p.2)
  | none => some (none, Heap.empty)

/-- **A computation with failure as a value**: the failure weight of `c` is moved to the outcome
    `none` at the empty heap, so that the computation does not fail. -/
noncomputable def totC (c : SPComp α) : SPComp (Option α) :=
  fun s => PMF.map failVal (c s)

/-- A computation with failure as a value does not fail. -/
theorem totC_apply_none (c : SPComp α) (s : Heap) : totC c s none = 0 := by
  simp only [totC, PMF.map_apply]
  refine ENNReal.tsum_eq_zero.mpr fun o => ?_
  cases o <;> simp [failVal]

/-- The weight of a value with failure as a value is its weight. -/
theorem totC_apply_some_some (c : SPComp α) (s s' : Heap) (a : α) :
    totC c s (some (some a, s')) = c s (some (a, s')) := by
  simp only [totC, PMF.map_apply]
  rw [tsum_eq_single (some (a, s'))]
  · simp [failVal]
  · intro o ho
    cases o with
    | none => simp [failVal]
    | some p =>
      simp only [failVal]
      grind

/-- The failure of a computation is the outcome `none` at the empty heap. -/
theorem totC_apply_some_none (c : SPComp α) (s s' : Heap) :
    totC c s (some (none, s')) = if s' = Heap.empty then c s none else 0 := by
  simp only [totC, PMF.map_apply]
  rw [tsum_eq_single none]
  · by_cases h : s' = Heap.empty <;> simp [failVal, h]
  · intro o ho
    cases o with
    | none => exact absurd rfl ho
    | some p => simp [failVal]

/-- A point mass with failure as a value. -/
theorem totC_pure (a : α) : totC (SPComp.pure a) = SPComp.pure (some a) := by
  funext s
  simp [totC, SPComp.pure, SDistr.pure, PMF.pure_map, failVal]

/-- A failed computation with failure as a value. -/
theorem totC_fail : totC (SPComp.fail : SPComp α) = fun _ => SDistr.pure (none, Heap.empty) := by
  funext s
  simp [totC, SPComp.fail, SDistr.fail, SDistr.pure, PMF.pure_map, failVal]

/-- **A sequence with failure as a value**: the first computation with failure as a value,
    followed by the continuation with failure as a value at a value, and by the outcome `none`
    at failure. -/
theorem totC_bind (c : SPComp α) (f : α → SPComp β) :
    totC (c.bind f) = (totC c).bind fun o => match o with
      | none => SPComp.pure none
      | some a => totC (f a) := by
  funext s
  simp only [totC, SPComp.bind, SDistr.bind, PMF.map_bind, PMF.bind_map]
  congr 1
  funext o
  cases o with
  | none => simp [SDistr.fail, PMF.pure_map, failVal, Function.comp, SPComp.pure, SDistr.pure]
  | some p => rfl

/-- The outcome of a point mass of nonzero weight is the value at the initial heap. -/
theorem pure_support {a : α} {s : Heap} {p : α × Heap} (h : SPComp.pure a s (some p) ≠ 0) :
    p = (a, s) := by
  classical
  simpa [SPComp.pure, SDistr.pure, PMF.pure_apply, eq_comm] using h

/-- **With failure as a value, a computation that does not fail is the computation followed by
    `some`.** -/
theorem totC_eq_of_noFail {c : SPComp α} (hc : ∀ s, c s none = 0) :
    totC c = c.bind fun a => SPComp.pure (some a) := by
  funext s
  simp only [totC, SPComp.bind, SDistr.bind, PMF.map]
  refine PMF.ext fun x => ?_
  simp only [PMF.bind_apply]
  refine tsum_congr fun o => ?_
  cases o with
  | none => simp [hc s]
  | some p => simp [failVal, SPComp.pure, SDistr.pure]

end FailVal

/-! ## Couplings up to failure -/

section RelF

variable {α β γ δ : Type}

/-- **The postcondition up to failure**: at two values the postcondition `Ψ`, and every pair with
    a failure on either side. -/
def FailOr (Ψ : RPost α β) : RPost (Option α) (Option β) := fun o₁ s₁ o₂ s₂ =>
  match o₁, o₂ with
  | some a, some b => Ψ a s₁ b s₂
  | _, _ => True

/-- **A coupling up to failure**: the two computations with failure as a value are coupled with
    the postcondition up to failure. The failure weights of the two computations may differ. -/
def RelF (Φ : RPre) (c₁ : SPComp α) (c₂ : SPComp β) (Ψ : RPost α β) : Prop :=
  rHoare Φ (totC c₁) (totC c₂) (FailOr Ψ)

/-- **The product coupling of two computations that do not fail**, at a postcondition that holds
    at every pair of outcomes of nonzero weight. -/
theorem rHoare_prod_of_noFail {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β} {Ψ : RPost α β}
    (h₁ : ∀ s, c₁ s none = 0) (h₂ : ∀ s, c₂ s none = 0)
    (hΨ : ∀ s₁ s₂, Φ s₁ s₂ → ∀ p q, c₁ s₁ (some p) ≠ 0 → c₂ s₂ (some q) ≠ 0 →
      Ψ p.1 p.2 q.1 q.2) :
    rHoare Φ c₁ c₂ Ψ := by
  intro s₁ s₂ hΦ
  refine ⟨Coupling.prod _ _ (by simp [SDistr.mass, h₁ s₁]) (by simp [SDistr.mass, h₂ s₂]), ?_⟩
  intro p q hpq
  exact hΨ s₁ s₂ hΦ p q (Coupling.in_left_support _ hpq) (Coupling.in_right_support _ hpq)

/-- **A coupling up to failure from the outcomes**: when the postcondition holds at every pair of
    values of nonzero weight. -/
theorem RelF.of_forall {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β} {Ψ : RPost α β}
    (h : ∀ s₁ s₂, Φ s₁ s₂ → ∀ a s₁' b s₂', c₁ s₁ (some (a, s₁')) ≠ 0 →
      c₂ s₂ (some (b, s₂')) ≠ 0 → Ψ a s₁' b s₂') :
    RelF Φ c₁ c₂ Ψ := by
  refine rHoare_prod_of_noFail (totC_apply_none c₁) (totC_apply_none c₂) ?_
  rintro s₁ s₂ hΦ ⟨o₁, s₁'⟩ ⟨o₂, s₂'⟩ h₁ h₂
  cases o₁ with
  | none => trivial
  | some a =>
    cases o₂ with
    | none => trivial
    | some b =>
      rw [totC_apply_some_some] at h₁ h₂
      exact h s₁ s₂ hΦ a s₁' b s₂' h₁ h₂

/-- A failed computation is coupled up to failure with every computation. -/
theorem RelF.fail_left {Φ : RPre} {c₂ : SPComp β} {Ψ : RPost α β} :
    RelF Φ SPComp.fail c₂ Ψ :=
  RelF.of_forall fun _ _ _ _ _ _ _ h => by simp [SPComp.fail, SDistr.fail_apply_some] at h

/-- A computation is coupled up to failure with a failed computation. -/
theorem RelF.fail_right {Φ : RPre} {c₁ : SPComp α} {Ψ : RPost α β} :
    RelF Φ c₁ SPComp.fail Ψ :=
  RelF.of_forall fun _ _ _ _ _ _ _ _ h => by simp [SPComp.fail, SDistr.fail_apply_some] at h

/-- **The return rule up to failure.** -/
theorem RelF.ret {Φ : RPre} {a : α} {b : β} {Ψ : RPost α β}
    (h : ∀ s₁ s₂, Φ s₁ s₂ → Ψ a s₁ b s₂) :
    RelF Φ (SPComp.pure a) (SPComp.pure b) Ψ := by
  unfold RelF
  rw [totC_pure, totC_pure]
  exact rHoare_ret h

/-- **The rule of consequence up to failure.** -/
theorem RelF.conseq {Φ Φ' : RPre} {Ψ Ψ' : RPost α β} {c₁ : SPComp α} {c₂ : SPComp β}
    (hPre : ∀ s₁ s₂, Φ' s₁ s₂ → Φ s₁ s₂)
    (hPost : ∀ a s₁ b s₂, Ψ a s₁ b s₂ → Ψ' a s₁ b s₂) (h : RelF Φ c₁ c₂ Ψ) :
    RelF Φ' c₁ c₂ Ψ' := by
  refine rHoare_conseq hPre ?_ h
  rintro (_ | a) s₁ (_ | b) s₂ hp
  · trivial
  · trivial
  · trivial
  · exact hPost a s₁ b s₂ hp

/-- The continuation of a sequence with failure as a value does not fail. -/
theorem totC_cont_noFail (f : α → SPComp β) (o : Option α) (s : Heap) :
    (match o with
      | none => SPComp.pure none
      | some a => totC (f a)) s none = 0 := by
  cases o with
  | none => exact SDistr.pure_apply_none _
  | some a => exact totC_apply_none _ _

/-- **The sequence rule up to failure.** -/
theorem RelF.bind {Φ : RPre} {Ψ : RPost α β} {Θ : RPost γ δ} {c₁ : SPComp α} {c₂ : SPComp β}
    {f₁ : α → SPComp γ} {f₂ : β → SPComp δ} (hc : RelF Φ c₁ c₂ Ψ)
    (hf : ∀ a b, RelF (fun s₁ s₂ => Ψ a s₁ b s₂) (f₁ a) (f₂ b) Θ) :
    RelF Φ (c₁.bind f₁) (c₂.bind f₂) Θ := by
  unfold RelF
  rw [totC_bind, totC_bind]
  refine rHoare_bind hc fun o₁ o₂ => ?_
  cases o₁ with
  | none =>
    refine rHoare_prod_of_noFail (totC_cont_noFail f₁ none) (totC_cont_noFail f₂ o₂) ?_
    intro s₁ s₂ _ p q hp _
    rw [pure_support hp]
    trivial
  | some a =>
    cases o₂ with
    | none =>
      refine rHoare_prod_of_noFail (totC_cont_noFail f₁ (some a)) (totC_cont_noFail f₂ none) ?_
      intro s₁ s₂ _ p q _ hq
      rw [pure_support hq]
      rcases p with ⟨_ | _, _⟩ <;> trivial
    | some b => exact hf a b

/-- A point mass is coupled up to failure with every computation, at a postcondition that holds
    at the value of the point mass. -/
theorem RelF.pure_left {Φ : RPre} {a : α} {c₂ : SPComp β} {Ψ : RPost α β}
    (h : ∀ s₁ s₂, Φ s₁ s₂ → ∀ b s₂', Ψ a s₁ b s₂') : RelF Φ (SPComp.pure a) c₂ Ψ :=
  RelF.of_forall fun s₁ s₂ hΦ a' s₁' b s₂' h₁ _ => by
    obtain ⟨ha, hs⟩ := Prod.mk.inj (pure_support h₁)
    rw [ha, hs]
    exact h s₁ s₂ hΦ b s₂'

/-- A fact implied by the precondition, together with the equality of heaps, may be assumed. -/
theorem RelF.of_pre_fact {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β} {Ψ : RPost α β} {P : Prop}
    (hP : ∀ s₁ s₂, Φ s₁ s₂ → P ∧ eqPre s₁ s₂) (h : P → RelF eqPre c₁ c₂ Ψ) :
    RelF Φ c₁ c₂ Ψ :=
  fun s₁ s₂ hΦ => h (hP s₁ s₂ hΦ).1 s₁ s₂ (hP s₁ s₂ hΦ).2

end RelF

/-! ## Stateful handlers -/

section Stateful

variable {E : EventSig} {S R : Type}

/-- **The interpretation of a call tree under a stateful handler**: the handler answers an event
    at a handler state by a computation of the answer and the next handler state, and the
    interpretation threads the handler state through the events of the tree. -/
noncomputable def interpSt (h : ∀ e : E.Event, S → SPComp (E.Resp e × S)) :
    CallTree E R → S → SPComp (R × S)
  | .ret r, σ => SPComp.pure (r, σ)
  | .vis e k, σ => (h e σ).bind fun p => interpSt h (k p.1) p.2

/-- Unfolding lemma of `interpSt` at a leaf. -/
@[simp] theorem interpSt_ret (h : ∀ e : E.Event, S → SPComp (E.Resp e × S)) (r : R) (σ : S) :
    interpSt h (.ret r) σ = SPComp.pure (r, σ) := rfl

/-- Unfolding lemma of `interpSt` at an event. -/
@[simp] theorem interpSt_vis (h : ∀ e : E.Event, S → SPComp (E.Resp e × S)) (e : E.Event)
    (k : E.Resp e → CallTree E R) (σ : S) :
    interpSt h (.vis e k) σ = (h e σ).bind fun p => interpSt h (k p.1) p.2 := rfl

/-- **The interpretation of a tree with optional leaves under a stateful handler**: the leaf
    `none` is read as failure, and the final handler state is discarded. -/
noncomputable def interpStOpt (h : ∀ e : E.Event, S → SPComp (E.Resp e × S))
    (t : CallTree E (Option R)) (σ : S) : SPComp R :=
  (interpSt h t σ).bind fun p => optSP p.1

/-- Unfolding lemma of `interpStOpt` at a leaf `some`. -/
@[simp] theorem interpStOpt_ret_some (h : ∀ e : E.Event, S → SPComp (E.Resp e × S)) (x : R)
    (σ : S) : interpStOpt h (.ret (some x)) σ = SPComp.pure x :=
  SPComp.pure_bind _ _

/-- Unfolding lemma of `interpStOpt` at the leaf `none`. -/
@[simp] theorem interpStOpt_ret_none (h : ∀ e : E.Event, S → SPComp (E.Resp e × S)) (σ : S) :
    interpStOpt h (.ret (none : Option R)) σ = SPComp.fail :=
  SPComp.pure_bind _ _

/-- Unfolding lemma of `interpStOpt` at an event. -/
theorem interpStOpt_vis (h : ∀ e : E.Event, S → SPComp (E.Resp e × S)) (e : E.Event)
    (k : E.Resp e → CallTree E (Option R)) (σ : S) :
    interpStOpt h (.vis e k) σ = (h e σ).bind fun p => interpStOpt h (k p.1) p.2 := by
  simp only [interpStOpt, interpSt_vis, SPComp.bind_assoc]

/-- **The stateful interpretation is monotone in the fuel order.** -/
theorem interpStOpt_mono (h : ∀ e : E.Event, S → SPComp (E.Resp e × S))
    {t t' : CallTree E (Option R)} (hle : FuelLe t t') (σ : S) :
    interpStOpt h t σ ≤ interpStOpt h t' σ := by
  induction hle generalizing σ with
  | none t =>
    rw [interpStOpt_ret_none]
    refine SPComp.le_def.mpr fun s => SDistr.le_def.mpr fun a => ?_
    simp [SPComp.fail, SDistr.fail_apply_some]
  | ret r => exact le_rfl
  | vis e _ ih =>
    rw [interpStOpt_vis, interpStOpt_vis]
    exact SPComp.bind_mono_right _ fun p => ih p.1 p.2

/-- The chain of the stateful interpretations of an increasing family. -/
noncomputable def interpStChain (h : ∀ e : E.Event, S → SPComp (E.Resp e × S))
    (T : Nat → CallTree E (Option R)) (hT : FuelMono T) (σ : S) : Chain (SPComp R) :=
  ⟨fun n => interpStOpt h (T n) σ, monotone_nat_of_le_succ fun n => interpStOpt_mono h (hT n) σ⟩

/-- **The stateful interpretation of an increasing fuel family**: the supremum over the fuel of
    the stateful interpretations of its trees. -/
noncomputable def interpStω (h : ∀ e : E.Event, S → SPComp (E.Resp e × S))
    (T : Nat → CallTree E (Option R)) (hT : FuelMono T) (σ : S) : SPComp R :=
  ωSup (interpStChain h T hT σ)

end Stateful

/-! ## Coupled stateful handlers and related trees -/

section Coupled

variable {E₁ E₂ : EventSig} {R₁ R₂ S₁ S₂ : Type}

/-- **Two stateful handlers coupled up to failure**: at events related by `RE` and handler states
    related by `Rσ`, from equal heaps, the computations of the two handlers are coupled up to
    failure with answers related by `RA`, next handler states related by `Rσ` and equal heaps. -/
def StHandlerCoupled (Rσ : S₁ → S₂ → Prop) (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop)
    (h₁ : ∀ e : E₁.Event, S₁ → SPComp (E₁.Resp e × S₁))
    (h₂ : ∀ e : E₂.Event, S₂ → SPComp (E₂.Resp e × S₂)) : Prop :=
  ∀ e₁ e₂, RE e₁ e₂ → ∀ σ₁ σ₂, Rσ σ₁ σ₂ → RelF eqPre (h₁ e₁ σ₁) (h₂ e₂ σ₂)
    (fun p₁ s₁ p₂ s₂ => RA e₁ e₂ p₁.1 p₂.1 ∧ Rσ p₁.2 p₂.2 ∧ s₁ = s₂)

/-- **A stateful source handler that answers skipped events within the skip predicate**: at a
    handler state related by `Rσ` to a target handler state `σ₂`, from equal heaps, the
    computation of the source handler is coupled up to failure with the target doing nothing,
    with answers admitted by `Sk`, a next source handler state related by `Rσ` to `σ₂`, and the
    heap kept. -/
def StSkips (Rσ : S₁ → S₂ → Prop) (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
    (h₁ : ∀ e : E₁.Event, S₁ → SPComp (E₁.Resp e × S₁)) : Prop :=
  ∀ e₁ σ₁ σ₂, Rσ σ₁ σ₂ → RelF eqPre (h₁ e₁ σ₁) (SPComp.pure ())
    (fun p₁ s₁ _ s₂ => Sk e₁ p₁.1 ∧ Rσ p₁.2 σ₂ ∧ s₁ = s₂)

variable {h₁ : ∀ e : E₁.Event, S₁ → SPComp (E₁.Resp e × S₁)}
  {h₂ : ∀ e : E₂.Event, S₂ → SPComp (E₂.Resp e × S₂)}
  {Sk : (e : E₁.Event) → E₁.Resp e → Prop} {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR : R₁ → Option R₂ → Prop} {Fail : R₁ → Prop} {Rσ : S₁ → S₂ → Prop}

/-- **Coupling of a source tree with the trees of a related fuel family.** Let the stateful
    handlers be coupled up to failure and the source handler answer skipped events within the
    skip predicate. A source tree and an increasing family related by `RuttFA` interpret, from
    related handler states and equal heaps, at every tree below a tree of the family, to
    outcomes coupled up to failure at which the source leaf fails or is related to the target
    leaf at equal heaps. -/
theorem relF_interpSt_ruttFA (hc : StHandlerCoupled Rσ RE RA h₁ h₂) (hs : StSkips Rσ Sk h₁)
    (hRF : ∀ r₁, RR r₁ none → Fail r₁) {t₁ : CallTree E₁ R₁}
    {T : Nat → CallTree E₂ (Option R₂)} (h : RuttFA Sk RE RA RR Fail t₁ T) :
    FuelMono T → ∀ (N : Nat) (t₂ : CallTree E₂ (Option R₂)), FuelLe t₂ (T N) →
      ∀ σ₁ σ₂, Rσ σ₁ σ₂ → RelF eqPre (interpSt h₁ t₁ σ₁) (interpStOpt h₂ t₂ σ₂)
        (fun p₁ s₁ x s₂ => Fail p₁.1 ∨ (RR p₁.1 (some x) ∧ s₁ = s₂)) := by
  induction h with
  | @ret r₁ r₂ T n hT hR =>
    intro hmono N t₂ ht σ₁ σ₂ _
    have ht' : FuelLe t₂ (T (max N n)) :=
      fuelLe_trans ht (fuelMono_le hmono (le_max_left N n))
    cases r₂ with
    | none => exact RelF.pure_left fun _ _ _ _ _ => .inl (hRF _ hR)
    | some x =>
      rw [hmono.ret_some hT _ (le_max_right N n)] at ht'
      cases ht' with
      | none => rw [interpStOpt_ret_none]; exact RelF.fail_right
      | ret => rw [interpStOpt_ret_some]; exact RelF.ret fun _ _ hs => .inr ⟨hR, hs⟩
  | fail hF => intro _ _ _ _ _ _ _; exact RelF.pure_left fun _ _ _ _ _ => .inl hF
  | @vis e₁ e₂ k₁ T K n hT he hk ih =>
    intro hmono N t₂ ht σ₁ σ₂ hσ
    have ht' : FuelLe t₂ (T (n + N)) :=
      fuelLe_trans ht (fuelMono_le hmono (Nat.le_add_left N n))
    rw [hT N] at ht'
    have hK : ∀ a, FuelMono (K a) := fun a m => by
      have h := hmono (n + m)
      rw [hT m, show n + m + 1 = n + (m + 1) by omega, hT (m + 1)] at h
      exact h.vis_inv a
    cases ht' with
    | none => rw [interpStOpt_ret_none]; exact RelF.fail_right
    | @vis _ k₂ _ hk₂ =>
      rw [interpSt_vis, interpStOpt_vis]
      refine RelF.bind (hc e₁ e₂ he σ₁ σ₂ hσ) fun p₁ p₂ => ?_
      refine RelF.of_pre_fact (P := RA e₁ e₂ p₁.1 p₂.1 ∧ Rσ p₁.2 p₂.2)
        (fun _ _ hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩) fun hp => ?_
      exact ih p₁.1 p₂.1 hp.1 (hK p₂.1) N (k₂ p₂.1) (hk₂ p₂.1) p₁.2 p₂.2 hp.2
  | @skip e₁ k₁ T _ ih =>
    intro hmono N t₂ ht σ₁ σ₂ hσ
    have hpb : interpStOpt h₂ t₂ σ₂ = (SPComp.pure ()).bind fun _ => interpStOpt h₂ t₂ σ₂ := by
      rw [SPComp.pure_bind]
    rw [interpSt_vis, hpb]
    refine RelF.bind (hs _ σ₁ σ₂ hσ) fun p₁ _ => ?_
    refine RelF.of_pre_fact (P := Sk e₁ p₁.1 ∧ Rσ p₁.2 σ₂)
      (fun _ _ hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩) fun hp => ?_
    exact ih p₁.1 hp.1 hmono N t₂ ht p₁.2 σ₂ hp.2

end Coupled

/-! ## Statistical distance from a coupling up to failure -/

section Distance

variable {V : Type}

/-- **One-sided statistical distance from a coupling up to failure at equality**: the mass by
    which the left computation exceeds the right one is at most the failure weight of the right
    computation. -/
theorem tvMargin_le_none_of_relF {c₁ c₂ : SPComp V} (h : RelF eqPre c₁ c₂ eqPost) (s : Heap) :
    tvMargin (c₁ s) (c₂ s) ≤ c₂ s none := by
  classical
  obtain ⟨J, hJ⟩ := h s s rfl
  have hpt : ∀ x : V × Heap, c₁ s (some x) - c₂ s (some x) ≤
      J.joint (some ((some x.1, x.2), (none, Heap.empty))) := by
    rintro ⟨v, hv⟩
    have hle : ∀ q, J.joint (some ((some v, hv), q)) ≤
        (if q = (some v, hv) then J.joint (some ((some v, hv), (some v, hv))) else 0) +
        (if q = (none, Heap.empty) then J.joint (some ((some v, hv), (none, Heap.empty)))
          else 0) := by
      rintro ⟨o, h'⟩
      by_cases h0 : J.joint (some ((some v, hv), (o, h'))) = 0
      · rw [h0]; exact zero_le
      cases o with
      | some w =>
        obtain ⟨rfl, rfl⟩ := hJ _ _ h0
        simp
      | none =>
        have hr := Coupling.in_right_support _ h0
        rw [totC_apply_some_none] at hr
        have he : h' = Heap.empty := by
          by_contra hne
          simp [hne] at hr
        subst he
        simp
    have h1 : c₁ s (some (v, hv)) ≤ J.joint (some ((some v, hv), (some v, hv))) +
        J.joint (some ((some v, hv), (none, Heap.empty))) := by
      rw [← totC_apply_some_some, ← Coupling.left_marginal_sum J]
      refine (ENNReal.tsum_le_tsum hle).trans ?_
      rw [ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq]
    have h2 : J.joint (some ((some v, hv), (some v, hv))) ≤ c₂ s (some (v, hv)) := by
      rw [← totC_apply_some_some, ← Coupling.right_marginal_sum J,
        ENNReal.tsum_eq_add_tsum_ite (some v, hv)]
      exact le_self_add
    refine tsub_le_iff_left.mpr (h1.trans ?_)
    gcongr
  calc tvMargin (c₁ s) (c₂ s)
      ≤ ∑' x : V × Heap, J.joint (some ((some x.1, x.2), (none, Heap.empty))) :=
        ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' p : Option V × Heap, J.joint (some (p, (none, Heap.empty))) :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun x : V × Heap => (some x.1, x.2))
          (fun x y hxy => by
            simp only [Prod.mk.injEq, Option.some.injEq] at hxy
            exact Prod.ext hxy.1 hxy.2) (fun p => J.joint (some (p, (none, Heap.empty))))
    _ = c₂ s none := by
        rw [Coupling.right_marginal_sum J, totC_apply_some_none]
        simp

/-- A coupling up to failure at equality is symmetric. -/
theorem RelF.symm_eq {c₁ c₂ : SPComp V} (h : RelF eqPre c₁ c₂ eqPost) :
    RelF eqPre c₂ c₁ eqPost := by
  refine rHoare_symm (rHoare_conseq (fun _ _ hs => hs.symm) ?_ h)
  rintro (_ | a) s₁ (_ | b) s₂ hp
  · trivial
  · trivial
  · trivial
  · exact ⟨hp.1.symm, hp.2.symm⟩

/-- The failure weight of a sub-distribution is one minus the weight of its values. -/
theorem sdistr_none_eq (d : SDistr V) : d none = 1 - ∑' x, d (some x) := by
  refine ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top ?_
  rw [← SDistr.tsum_option_eq_add]
  exact d.tsum_coe

/-- **Statistical distance to a supremum.** Let the weights of the values of `d` be the suprema of
    those of an increasing sequence `d' N`, let `d₁` exceed each `d' N` by at most the failure
    weight of `d' N`, and let each `d' N` exceed `d₁` by at most the failure weight of `d₁`. Then
    `d₁` exceeds `d` by at most the failure weight of `d`, and `d` exceeds `d₁` by at most the
    failure weight of `d₁`. -/
theorem tvMargin_le_of_iSup {d₁ d : SDistr V} {d' : ℕ → SDistr V}
    (hmono : ∀ x, Monotone fun N => d' N (some x))
    (hd : ∀ x, d (some x) = ⨆ N, d' N (some x))
    (h₁ : ∀ N, tvMargin d₁ (d' N) ≤ d' N none) (h₂ : ∀ N, tvMargin (d' N) d₁ ≤ d₁ none) :
    tvMargin d₁ d ≤ d none ∧ tvMargin d d₁ ≤ d₁ none := by
  constructor
  · have hle : ∀ N, tvMargin d₁ d ≤ d' N none := fun N => by
      refine le_trans ?_ (h₁ N)
      unfold tvMargin
      gcongr with x
      rw [hd]
      exact le_iSup (fun N => d' N (some x)) N
    rw [sdistr_none_eq d]
    simp_rw [hd]
    rw [NonUniform.tsum_iSup_of_monotone hmono, ENNReal.sub_iSup ENNReal.one_ne_top]
    exact le_iInf fun N => (hle N).trans (sdistr_none_eq (d' N)).le
  · unfold tvMargin
    simp_rw [hd, ENNReal.iSup_sub]
    rw [NonUniform.tsum_iSup_of_monotone (g := fun x N => d' N (some x) - d₁ (some x))
      fun x _ _ hNM => tsub_le_tsub_right (hmono x hNM) _]
    exact iSup_le h₂

/-- The weight of a value under the read-back of the supremum of a chain is the supremum of its
    weights under the read-backs of the chain. -/
theorem readBack_ωSup_apply_some {α : Type} (rb : α → Option V) (c : Chain (SPComp α))
    (s : Heap) (y : V × Heap) :
    readBack rb (ωSup c) s (some y) = ⨆ N, readBack rb (c N) s (some y) := by
  change SDistr.bind (ωSup (c.map ⟨fun x => x s, fun _ _ hle => hle s⟩)) _ (some y) = _
  rw [SDistr.ωSup_bind, SDistr.ωSup_apply_some]
  rfl

/-- The weights under the read-backs of a chain increase along the chain. -/
theorem readBack_chain_mono {α : Type} (rb : α → Option V) (c : Chain (SPComp α)) (s : Heap)
    (y : V × Heap) : Monotone fun N => readBack rb (c N) s (some y) :=
  fun _ _ hNM => SPComp.bind_mono_left (c.monotone hNM) _ s y

end Distance

/-! ## The statistical distance of the read-backs -/

section Main

variable {E₁ E₂ : EventSig} {R₁ R₂ S₁ S₂ V : Type}
  {h₁ : ∀ e : E₁.Event, S₁ → SPComp (E₁.Resp e × S₁)}
  {h₂ : ∀ e : E₂.Event, S₂ → SPComp (E₂.Resp e × S₂)}
  {Sk : (e : E₁.Event) → E₁.Resp e → Prop} {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR : R₁ → Option R₂ → Prop} {Fail : R₁ → Prop} {Rσ : S₁ → S₂ → Prop}

/-- **Statistical distance of the read-backs under stateful probabilistic handlers.** Let the
    stateful handlers be coupled up to failure at related events and related handler states, the
    source handler answer skipped events within the skip predicate, and a source tree and an
    increasing family be related by `RuttFA`. Let the source read-back `rb₁` be undefined at
    failed source leaves and agree with the target read-back `rb₂` at related leaves. From
    related initial handler states, the statistical distance of the read-backs is at most a bound
    `ε` of the failure weight of the target plus a bound `δ` of the failure weight of the source
    read-back. -/
theorem sdist_readBack_ruttFA (hc : StHandlerCoupled Rσ RE RA h₁ h₂) (hs : StSkips Rσ Sk h₁)
    (hRF : ∀ r₁, RR r₁ none → Fail r₁) {t₁ : CallTree E₁ R₁}
    {T : Nat → CallTree E₂ (Option R₂)} (hT : FuelMono T) (h : RuttFA Sk RE RA RR Fail t₁ T)
    (rb₁ : R₁ → Option V) (rb₂ : R₂ → V) (hF : ∀ r₁, Fail r₁ → rb₁ r₁ = none)
    (hrb : ∀ r₁ x v, RR r₁ (some x) → rb₁ r₁ = some v → rb₂ x = v) {σ₁ : S₁} {σ₂ : S₂}
    (hσ : Rσ σ₁ σ₂) {ε δ : ℝ≥0∞} (hε : ∀ s, interpStω h₂ T hT σ₂ s none ≤ ε)
    (hδ : ∀ s, readBack (fun p => rb₁ p.1) (interpSt h₁ t₁ σ₁) s none ≤ δ) :
    sdist (fun _ : Unit => readBack (fun p => rb₁ p.1) (interpSt h₁ t₁ σ₁))
      (fun _ : Unit => readBack (fun x => some (rb₂ x)) (interpStω h₂ T hT σ₂)) ≤ ε + δ := by
  have hN : ∀ N, RelF eqPre (readBack (fun p => rb₁ p.1) (interpSt h₁ t₁ σ₁))
      (readBack (fun x => some (rb₂ x)) (interpStOpt h₂ (T N) σ₂)) eqPost := fun N => by
    refine RelF.bind (relF_interpSt_ruttFA hc hs hRF h hT N (T N) (fuelLe_refl _) σ₁ σ₂ hσ)
      fun p₁ x => ?_
    change RelF _ (optSP (rb₁ p₁.1)) (optSP (some (rb₂ x))) _
    cases hv : rb₁ p₁.1 with
    | none => exact RelF.fail_left
    | some v =>
      refine RelF.ret fun s₁ s₂ hp => ?_
      rcases hp with hf | ⟨hR, hs'⟩
      · rw [hF _ hf] at hv
        cases hv
      · exact ⟨(hrb _ _ _ hR hv).symm, hs'⟩
  refine rHoareApprox_sdist fun s₀ s hs₀ => ?_
  obtain rfl : s₀ = s := hs₀
  have hmono : ∀ y, Monotone fun N =>
      readBack (fun x => some (rb₂ x)) (interpStOpt h₂ (T N) σ₂) s₀ (some y) :=
    fun y => readBack_chain_mono _ (interpStChain h₂ T hT σ₂) s₀ y
  have hsup : ∀ y, readBack (fun x => some (rb₂ x)) (interpStω h₂ T hT σ₂) s₀ (some y) =
      ⨆ N, readBack (fun x => some (rb₂ x)) (interpStOpt h₂ (T N) σ₂) s₀ (some y) :=
    fun y => readBack_ωSup_apply_some _ (interpStChain h₂ T hT σ₂) s₀ y
  obtain ⟨hl, hr⟩ := tvMargin_le_of_iSup hmono hsup
    (fun N => tvMargin_le_none_of_relF (hN N) s₀)
    (fun N => tvMargin_le_none_of_relF (hN N).symm_eq s₀)
  refine liftRApprox_mono_rel (fun p₁ p₂ hp => pairPost_of_eq hp) (liftRApprox_eq_of_tv ?_ ?_)
  · rw [readBack_some_apply_none] at hl
    exact (hl.trans (hε s₀)).trans le_self_add
  · exact (hr.trans (hδ s₀)).trans le_add_self

end Main

/-! ## Handler families indexed by the state -/

section Const

variable {E : EventSig} {S R : Type}

/-- **A handler family indexed by a state, as a stateful handler** that keeps its state. -/
noncomputable def constSt (h : S → ∀ e : E.Event, SPComp (E.Resp e)) :
    ∀ e : E.Event, S → SPComp (E.Resp e × S) :=
  fun e σ => (h σ e).bind fun a => SPComp.pure (a, σ)

/-- The stateful interpretation under a handler family indexed by the state is the
    interpretation under the handler at the initial state, with that state. -/
theorem interpSt_constSt (h : S → ∀ e : E.Event, SPComp (E.Resp e)) (t : CallTree E R)
    (σ : S) : interpSt (constSt h) t σ = (interpSP (h σ) t).bind fun r => SPComp.pure (r, σ) := by
  induction t with
  | ret r => simp [SPComp.pure_bind]
  | vis e k ih =>
    simp only [interpSt_vis, interpSP_vis, constSt, SPComp.bind_assoc, SPComp.pure_bind, ih]

/-- The stateful interpretation with optional leaves under a handler family indexed by the state
    is `interpSPOpt` at the handler of the initial state. -/
theorem interpStOpt_constSt (h : S → ∀ e : E.Event, SPComp (E.Resp e))
    (t : CallTree E (Option R)) (σ : S) : interpStOpt (constSt h) t σ = interpSPOpt (h σ) t := by
  simp only [interpStOpt, interpSt_constSt, SPComp.bind_assoc, SPComp.pure_bind, interpSPOpt]

/-- The stateful interpretation of a family under a handler family indexed by the state is
    `interpSPω` at the handler of the initial state. -/
theorem interpStω_constSt (h : S → ∀ e : E.Event, SPComp (E.Resp e))
    (T : Nat → CallTree E (Option R)) (hT : FuelMono T) (σ : S) :
    interpStω (constSt h) T hT σ = interpSPω (h σ) T hT := by
  unfold interpStω interpSPω
  refine le_antisymm (ωSup_le _ _ fun n => le_ωSup_of_le n ?_)
    (ωSup_le _ _ fun n => le_ωSup_of_le n ?_)
  · exact (interpStOpt_constSt h (T n) σ).le
  · exact (interpStOpt_constSt h (T n) σ).ge

/-- The read-back of the stateful interpretation under a handler family indexed by the state. -/
theorem readBack_interpSt_constSt {V : Type} (rb : R → Option V)
    (h : S → ∀ e : E.Event, SPComp (E.Resp e)) (t : CallTree E R) (σ : S) :
    readBack (fun p => rb p.1) (interpSt (constSt h) t σ) = readBack rb (interpSP (h σ) t) := by
  simp only [readBack, interpSt_constSt, SPComp.bind_assoc, SPComp.pure_bind]

end Const

/-- **The exact coupling of two computations that do not fail is a coupling up to failure.** -/
theorem RelF.of_rHoare {α β : Type} {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β}
    {Ψ : RPost α β} (h₁ : ∀ s, c₁ s none = 0) (h₂ : ∀ s, c₂ s none = 0)
    (h : rHoare Φ c₁ c₂ Ψ) : RelF Φ c₁ c₂ Ψ := by
  unfold RelF
  rw [totC_eq_of_noFail h₁, totC_eq_of_noFail h₂]
  exact rHoare_bind h fun _ _ => rHoare_ret fun _ _ hp => hp

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful

open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn hax64WExit)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
open _root_.Hax

/-! ## Stateful source oracles of the linked functions -/

/-- **A stateful probabilistic source oracle** for the linked functions of `m`: a handler state
    of type `St` drawn by `init`, and at a handler state the computation `step e` of the answer
    to a call `e` and the next handler state. At a skipped call the answers are admitted by the
    skip predicate `SkipAns TypedAns m`, and the handler state and the heap are kept. -/
structure StOracle (m : HaxModule) where
  /-- The type of the handler states. -/
  St : Type
  /-- The distribution of the initial handler state. -/
  init : SPComp St
  /-- The answer to a call and the next handler state. -/
  step : ∀ e : linkSig.Event, St → SPComp (linkSig.Resp e × St)
  /-- Skipped calls are answered within the skip predicate, keeping the state and the heap. -/
  skips : StSkips (fun σ₁ σ₂ : St => σ₁ = σ₂) (SkipAns TypedAns m) step

variable {m : HaxModule}

/-- **The source computation of a stateful oracle**: draw the initial handler state, interpret
    the source tree under the oracle, and read back the value of the source leaf. -/
noncomputable def stSrc (O : StOracle m) (t : CallTree linkSig (Outcome × Env)) :
    SPComp Value :=
  O.init.bind fun x => readBack (fun p => srcRead p.1) (interpSt O.step t x)

/-- **The interpretation of the target trees** of the calling body `pc` from the entry state
    `sa` under a stateful target handler from the handler state `x`. -/
noncomputable def interpTargetStω {S : Type} (m : HaxModule) (pc : List RInstr)
    (sym : Nat → String) (sa : AState)
    (h₂ : ∀ e : (kSig AState).Event, S → SPComp ((kSig AState).Resp e × S)) (x : S) :
    SPComp AState :=
  interpStω h₂ (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa)
    (fuelMono_targetTree aMachine pc sym (linkRead m) 0 sa) x

/-- **The target computation of a stateful oracle**: draw the initial handler state, interpret
    the target trees of the calling body under the stateful target handler from that state, and
    read back the result by `σ`. -/
noncomputable def stTgt (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String) (sa : AState)
    (O : StOracle m)
    (h₂ : ∀ e : (kSig AState).Event, O.St → SPComp ((kSig AState).Resp e × O.St)) :
    SPComp Value :=
  O.init.bind fun x =>
    readBack (fun s' => some (σ.result.read sa s')) (interpTargetStω m pc sym sa h₂ x)

/-- **A stateful target handler coupled with a stateful oracle** up to failure, at equal handler
    states, on the separation contracts at the typed answer relation. -/
def HandlerCoupledSt (O : StOracle m)
    (h₂ : ∀ e : (kSig AState).Event, O.St → SPComp ((kSig AState).Resp e × O.St)) : Prop :=
  StHandlerCoupled (fun σ₁ σ₂ : O.St => σ₁ = σ₂) (contractREG m) (contractRACA TypedAns m)
    O.step h₂

/-- **Statistical distance at a stateful oracle.** Let a source tree be related by `RuttFA` at
    the skip predicate `SkipAns TypedAns m` and the separation contracts at `TypedAns` to the
    target trees of the calling body `pc` from `sa`, and let the stateful target handler be
    coupled with the stateful oracle `O`. The statistical distance of the source and target
    computations is at most a bound `ε` of the failure weight of the target at every initial
    handler state plus a bound `δ` of the failure weight of the source read-back at every initial
    handler state. -/
theorem sdist_st_contract {σ : AbiLayout} {sa : AState} {pc : List RInstr}
    {sym : Nat → String} (O : StOracle m)
    {h₂ : ∀ e : (kSig AState).Event, O.St → SPComp ((kSig AState).Resp e × O.St)}
    (hc : HandlerCoupledSt O h₂) {t₁ : CallTree linkSig (Outcome × Env)}
    (h : RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
      srcFail t₁ (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa))
    {ε δ : ℝ≥0∞} (hε : ∀ x s, interpTargetStω m pc sym sa h₂ x s none ≤ ε)
    (hδ : ∀ x s, readBack (fun p => srcRead p.1) (interpSt O.step t₁ x) s none ≤ δ) :
    sdist (fun _ : Unit => stSrc O t₁) (fun _ : Unit => stTgt σ pc sym sa O h₂) ≤ ε + δ := by
  have hk : ∀ x, sdist
      (fun _ : Unit => readBack (fun p => srcRead p.1) (interpSt O.step t₁ x))
      (fun _ : Unit => readBack (fun s' => some (σ.result.read sa s'))
        (interpTargetStω m pc sym sa h₂ x)) ≤ ε + δ := fun x =>
    sdist_readBack_ruttFA hc O.skips (fun _ => srcFail_of_resRel_none) _ h srcRead _
      (fun _ => srcRead_of_srcFail) (fun _ _ _ => read_of_resRel) rfl (hε x) (hδ x)
  have hfun : sdist
      (fun x => readBack (fun p => srcRead p.1) (interpSt O.step t₁ x))
      (fun x => readBack (fun s' => some (σ.result.read sa s'))
        (interpTargetStω m pc sym sa h₂ x)) ≤ ε + δ :=
    iSup_le fun D => iSup_le fun x => iSup_le fun h₀ => sdist_le_of_forall (hk x) D () h₀
  exact sdist_bind_right_dep (fun _ : Unit => O.init) _ _ fun _ => hfun

/-! ## Robust compilation over stateful oracles -/

/-- **Robust compilation over the stateful target handlers coupled with a stateful oracle.** At
    every entry state `sa` of the domain of `σ`, every source environment `env` of the narrowed
    entry, and every fuel, let `δ` bound the failure weight of the source read-back under the
    stateful oracle `O` at every initial handler state. Then replacing the source computation
    `stSrc` by the target computation `stTgt` is robust compilation at `ε + δ` over the stateful
    target handlers coupled with `O` whose failure weight at every initial handler state is at
    most `ε`. -/
def HandlerRCSt (m : HaxModule) (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String)
    (O : StOracle m) : Prop :=
  ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
    ∀ (fuelC fuel : Nat) (ε δ : ℝ≥0∞),
      (∀ x s, readBack (fun p => srcRead p.1) (interpSt O.step
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env) x) s none ≤ δ) →
      RobustCompilationH
        (fun h₂ => HandlerCoupledSt O h₂ ∧
          ∀ x s, interpTargetStω m pc sym sa h₂ x s none ≤ ε) (ε + δ)
        (fun h₂ (_ : Unit) => stTgt σ pc sym sa O h₂)
        (fun _ (_ : Unit) =>
          stSrc O (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env))

/-! ## The keyed oracle as a stateful oracle -/

/-- **A keyed oracle as a stateful oracle**: the handler state is the key, drawn by `keyDist`
    and kept by every call. -/
noncomputable def keyedSt (O : KeyedOracle m) : StOracle m where
  St := O.Key
  init := O.keyDist
  step := constSt fun k e => SPComp.pure (O.ans k e)
  skips := by
    rintro e k _ rfl
    change RelF _ ((SPComp.pure _).bind _) _ _
    rw [SPComp.pure_bind]
    exact RelF.ret fun _ _ hs => ⟨O.typed k e, rfl, hs⟩

/-- The source computation of a keyed oracle as a stateful oracle is `keyedSrc`. -/
theorem stSrc_keyedSt (O : KeyedOracle m) (t : CallTree linkSig (Outcome × Env)) :
    stSrc (keyedSt O) t = keyedSrc O t := by
  simp only [stSrc, keyedSrc, keyedSt, readBack_interpSt_constSt]

/-- The target computation of a keyed oracle as a stateful oracle, at a target handler family
    indexed by the key, is `keyedTgt`. -/
theorem stTgt_keyedSt (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String) (sa : AState)
    (O : KeyedOracle m)
    (h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) :
    stTgt σ pc sym sa (keyedSt O) (constSt h₂) = keyedTgt σ pc sym sa O h₂ := by
  simp only [stTgt, keyedTgt, keyedSt, interpTargetStω, interpStω_constSt, interpTargetω]

/-- **A target handler family coupled with a keyed oracle is coupled with it as a stateful
    oracle.** -/
theorem handlerCoupledSt_keyedSt {O : KeyedOracle m}
    {h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hc : HandlerCoupledKeyed O h₂) : HandlerCoupledSt (keyedSt O) (constSt h₂) := by
  rintro e₁ e₂ he k _ rfl
  have hk := hc k e₁ e₂ he
  have hnf : ∀ s, h₂ k e₂ s none = 0 :=
    rHoare_noFail_right (Φ := eqPre) hk (fun s => ⟨s, rfl⟩) fun _ => SDistr.pure_apply_none _
  change RelF eqPre ((SPComp.pure (O.ans k e₁)).bind fun a => SPComp.pure (a, k))
    ((h₂ k e₂).bind fun a => SPComp.pure (a, k)) _
  refine RelF.bind (RelF.of_rHoare (fun _ => SDistr.pure_apply_none _) hnf hk) fun a b => ?_
  exact RelF.ret fun _ _ hp => ⟨hp.1, rfl, hp.2⟩

/-- **`HandlerRCKeyed` is the instance of `HandlerRCSt` at a keyed oracle**, whose handler state
    is the key. -/
theorem handlerRCKeyed_of_handlerRCSt {σ : AbiLayout} {pc : List RInstr} {sym : Nat → String}
    {O : KeyedOracle m} (h : HandlerRCSt m σ pc sym (keyedSt O)) :
    HandlerRCKeyed m σ pc sym O := by
  intro sa hsa env henv fC fuel ε δ hδ
  refine (robustCompilationH_iff_sdist _ _ _ _).mpr fun h₂ hh => ?_
  have hk := (robustCompilationH_iff_sdist _ _ _ _).mp
    (h sa hsa env henv fC fuel ε δ fun (k : O.Key) s => by
      have he := readBack_interpSt_constSt (S := O.Key) srcRead
        (fun k e => SPComp.pure (O.ans k e))
        (nfTree (moduleTreeTable m hax64WExit fC) fuel m.entry.erase env) k
      exact (congrArg (fun c : SPComp Value => c s none) he).trans_le (hδ k s)) (constSt h₂)
    ⟨handlerCoupledSt_keyedSt hh.1, fun (k : O.Key) s => by
      have hk := hh.2 k s
      rw [interpTargetω, ← interpStω_constSt] at hk
      exact hk⟩
  rwa [stTgt_keyedSt, stSrc_keyedSt] at hk

/-- **Robust compilation over stateful oracles, for the hax compiler.** Let `compileA` compile
    the module `m` to `(P, bytes)` under the hypotheses of
    `NFCallTreeR3Linked.r3FA_of_shape_linked`. The bytes decode to a calling body `pc` followed by the shifted linked code `Q`, and `HandlerRCSt` holds at
    `pc` for every stateful oracle of `m`. -/
theorem haxc_rcHSt {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m hax64WExit) _ q.1).run q.2 = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false)
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hint : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o →
          NFCallTreeFrontModule.OpOk NFCallTreeGoodCall.IntArgFree o)
    (hfp : ∀ f ∈ m.fns, ∀ p ∈ f.params, p.2 ≠ .int)
    (hbody : ∀ f ∈ m.fns, (crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params)
      f.res m.linkSig).isSome = true)
    (hintB : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → NFCallTreeFrontModule.OpOk NFCallTreeGoodCall.IntArgFree o) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ O : StOracle m, HandlerRCSt m σ pc sym O := by
  obtain ⟨pc, Q, sym, hd, hrel⟩ :=
    NFCallTreeR3Linked.r3FA_of_shape_linked hc hnd hk hn hpt hcf tE htE hpar hword hin
      hspine hfs hint hfp hbody hintB
  refine ⟨pc, Q, sym, hd, fun O sa hsa env henv fC fuel ε δ hδ => ?_⟩
  refine (robustCompilationH_iff_sdist _ _ _ _).mpr fun h hh => ?_
  rw [sdist_sym]
  exact sdist_st_contract O hh.1 (hrel sa hsa env henv fC fuel) hh.2 hδ

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful
