/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.UCMonad.ITreeNCompose
public import CatCrypt.Crypto.UCMonad.ITreeNMetric
public import CatCrypt.Crypto.UCMonad.StateTInstance

/-!
# StateT S (ITreeN n E) Bridge

This file provides infrastructure for using `StateT S (ITreeN n E)` as the
monad for Canetti-style UC proofs with state and visible events.

## Key definitions

* `StatefulITreeN` — abbreviation for `StateT S (ITreeN n E)`
* `embedSPComp` — embed `SPComp α` into `ITreeN n E α`
* `liftSPComp` — embed `SPComp α` into `StatefulITreeN S n E α`
* `UCEmulatesConcurrent_of_sdistITreeN` — lift sdist bounds to concurrent UC

## Design

The embedding `embedSPComp` wraps `SPComp α` into `ITreeN n E α`:
- At level 0: identity (since `ITreeN 0 E α = SPComp α`)
- At level n+1: `c.bind (fun a => pure (.inl a))` (embed as immediate return)

The key property: `flattenAll ∘ embedSPComp = id`, so sdist is preserved.
-/

@[expose] public section

namespace UCMonad.StateTITreeN

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad UCMonad.ITreeNUC UCMonad.RoundMUC
open scoped ENNReal

/-! ## Section 1: Abbreviation -/

/-- Stateful ITreeN: the monad for Canetti-style UC with state and events. -/
abbrev StatefulITreeN (S : Type) (n : Nat) (E : EventSig) :=
  StateT S (ITreeN n E)

/-! ## Section 2: Embedding SPComp into ITreeN -/

/-- Embed `SPComp α` into `ITreeN n E α`.

    At level 0, this is the identity.
    At level n+1, wraps the computation as an immediate return (.inl). -/
noncomputable def embedSPComp {α : Type} {E : EventSig} :
    (n : Nat) → SPComp α → ITreeN n E α
  | 0, c => c
  | _ + 1, c => SPComp.bind c (fun a =>
      (SPComp.pure (Sum.inl a) : SPComp (ITreeNStep _ E α)))

/-- Flatten of embedSPComp reduces the depth by 1. -/
theorem flatten_embedSPComp {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (c : SPComp α) :
    ITreeN.flatten handler n (embedSPComp (E := E) (n + 1) c) = embedSPComp n c := by
  cases n with
  | zero =>
    simp only [embedSPComp, ITreeN.flatten_zero, SPComp.bind_assoc, SPComp.pure_bind]
    exact SPComp.bind_pure c
  | succ m =>
    simp only [embedSPComp, ITreeN.flatten_succ, SPComp.bind_assoc, SPComp.pure_bind]

/-- `flattenAll` of `embedSPComp n c` equals `c`. -/
theorem flattenAll_embedSPComp {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (c : SPComp α) :
    ITreeN.flattenAll handler n (embedSPComp (E := E) n c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ITreeN.flattenAll_succ]
    rw [flatten_embedSPComp handler n c]
    exact ih

/-! ## Section 2b: flattenAll of vis nodes -/

/-- Helper: flatten of vis equals bind' with embedded handler. -/
theorem flatten_vis_eq_bind' {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (m : Nat) (e : E.Event) (k : E.Resp e → ITreeN m E α) :
    ITreeN.flatten handler m (ITreeN.vis m e k) =
    ITreeN.bind' handler m (embedSPComp m (handler e)) k := by
  cases m with
  | zero =>
    simp only [ITreeN.vis, ITreeN.flatten_zero, SPComp.pure_bind,
      embedSPComp, ITreeN.bind'_zero]
  | succ n =>
    simp only [ITreeN.vis, ITreeN.flatten_succ, SPComp.pure_bind,
      embedSPComp, ITreeN.bind'_succ, SPComp.bind_assoc]

/-- flattenAll of vis: event resolved by handler. -/
theorem flattenAll_vis {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (m : Nat) (e : E.Event) (k : E.Resp e → ITreeN m E α) :
    ITreeN.flattenAll handler (m + 1) (ITreeN.vis m e k) =
    SPComp.bind (handler e) (fun r => ITreeN.flattenAll handler m (k r)) := by
  rw [ITreeN.flattenAll_succ, flatten_vis_eq_bind' handler m e k]
  rw [flattenAll_bind handler m (embedSPComp m (handler e)) k]
  rw [flattenAll_embedSPComp handler m (handler e)]

/-- flattenAll of a cast vis node. -/
theorem flattenAll_vis_cast {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n m : Nat) (h : m + 1 = n) (e : E.Event)
    (k : E.Resp e → ITreeN m E α) :
    ITreeN.flattenAll handler n (h ▸ ITreeN.vis m e k) =
    SPComp.bind (handler e) (fun r => ITreeN.flattenAll handler m (k r)) := by
  subst h; exact flattenAll_vis handler m e k

/-! ## Section 3: Lifting to StatefulITreeN -/

/-- Embed a pure `SPComp α` computation into `StatefulITreeN`.

    The computation runs the SPComp and pairs the result with the state. -/
noncomputable def liftSPComp {S : Type} {n : Nat} {E : EventSig} {α : Type}
    (c : SPComp α) : StatefulITreeN S n E α :=
  fun s => embedSPComp n (c.bind (fun a => SPComp.pure (a, s)))

/-- Lift a Kleisli arrow `α → SPComp β` into `α → StatefulITreeN`. -/
noncomputable def liftSPCompK {S : Type} {n : Nat} {E : EventSig} {α β : Type}
    (f : α → SPComp β) : α → StatefulITreeN S n E β :=
  fun a => liftSPComp (f a)

/-! ## Section 4: FlattenAll of liftSPComp -/

theorem flattenAll_liftSPComp {S : Type} {n : Nat} {E : EventSig} {α : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (c : SPComp α) (s : S) :
    ITreeN.flattenAll handler n (liftSPComp (S := S) (n := n) (E := E) c s) =
    c.bind (fun a => SPComp.pure (a, s)) := by
  unfold liftSPComp
  exact flattenAll_embedSPComp handler n _

/-! ## Section 5: sdist Preservation -/

/-- The sdist of lifted SPComp computations in `StatefulITreeN` is bounded by
    the original sdist.

    Proof: For any distinguisher D' and input (a, s), the composition
    `D' ∘ (·, s)` is a distinguisher for the original f vs g. -/
theorem sdistITreeN_liftSPComp_le {S : Type} {n : Nat} {E : EventSig} {α β : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → SPComp β) :
    sdistITreeN n E handler
      (fun (p : α × S) => liftSPComp (f p.1) p.2)
      (fun (p : α × S) => liftSPComp (g p.1) p.2) ≤
    sdist f g := by
  show sdist
    (fun (p : α × S) => ITreeN.flattenAll handler n (liftSPComp (f p.1) p.2))
    (fun (p : α × S) => ITreeN.flattenAll handler n (liftSPComp (g p.1) p.2)) ≤ _
  simp only [flattenAll_liftSPComp]
  -- Goal: sdist (fun p => (f p.1).bind (fun a => pure (a, p.2)))
  --             (fun p => (g p.1).bind (fun a => pure (a, p.2))) ≤ sdist f g
  -- Direct proof via sdist definition
  apply iSup_le; intro D'  -- distinguisher D' : (β × S) → SPComp Bool
  apply iSup_le; intro ⟨a, s⟩  -- input (a, s) : α × S
  apply iSup_le; intro h₀  -- heap h₀
  -- bind (f a).bind(fun b => pure (b,s)) D' = bind (f a) (fun b => D' (b, s))
  have eq1 : SPComp.bind ((f a).bind (fun b => SPComp.pure (b, s))) D' =
      SPComp.bind (f a) (fun b => D' (b, s)) := by
    simp [SPComp.bind_assoc, SPComp.pure_bind]
  have eq2 : SPComp.bind ((g a).bind (fun b => SPComp.pure (b, s))) D' =
      SPComp.bind (g a) (fun b => D' (b, s)) := by
    simp [SPComp.bind_assoc, SPComp.pure_bind]
  rw [eq1, eq2]
  -- Now: |prTrue(bind (f a) D_s, h₀) - prTrue(bind (g a) D_s, h₀)| ≤ sdist f g
  -- where D_s = fun b => D' (b, s) is a distinguisher for f vs g
  exact le_iSup₂_of_le (fun b => D' (b, s)) a (le_iSup_of_le h₀ le_rfl)

/-! ## Section 6: Kantorovich for embedSPComp and liftSPComp -/

/-- Kantorovich distance of embedded SPComps is bounded by their kantLift distance.
    At level 0 this is equality; at level n+1, `embedSPComp` wraps via `.inl`
    which is a 1-Lipschitz embedding into the step metric. -/
theorem kdistITreeN_pt_embedSPComp_le :
    ∀ (n : Nat) (E : EventSig) {β : Type}
    (c₁ c₂ : SPComp β),
    (kdistITreeN_pt n E β).dist (embedSPComp (E := E) n c₁)
      (embedSPComp (E := E) n c₂) ≤
    kantLift (discreteMetric β) c₁ c₂ := by
  intro n; induction n with
  | zero => intro _ _ _ _; exact le_rfl
  | succ m _ih =>
    intro E β c₁ c₂
    -- embedSPComp (m+1) c = c.bind (fun a => pure (.inl a))
    simp only [embedSPComp, kdistITreeN_pt]
    -- fun a => pure (.inl a) is Lipschitz from discreteMetric β to stepMetric
    exact kantLift_comp_right (discreteMetric β) _ _ _ _
      (fun _D' _hD' => isLipDist_discrete _)

/-- The Kantorovich distance of lifted SPComp computations in `StatefulITreeN` is bounded
    by the original sdist.

    This is the Kantorovich analogue of `sdistITreeN_liftSPComp_le`. -/
theorem kdistITreeN_liftSPComp_le {S : Type} {n : Nat} {E : EventSig} {α β : Type}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (f g : α → SPComp β) :
    kdistITreeN n E handler
      (fun (p : α × S) => liftSPComp (f p.1) p.2)
      (fun (p : α × S) => liftSPComp (g p.1) p.2) ≤
    sdist f g := by
  apply iSup_le; intro ⟨a, s⟩
  show (kdistITreeN_pt n E (β × S)).dist (liftSPComp (f a) s)
    (liftSPComp (g a) s) ≤ sdist f g
  simp only [liftSPComp]
  -- Step 1: embedSPComp preserves kantLift distance
  apply le_trans (kdistITreeN_pt_embedSPComp_le n E _ _)
  -- Step 2: factor out the (fun b => pure (b, s)) continuation
  apply le_trans (kantLift_comp_right (discreteMetric β) _ _ _ _
    (fun _D' _hD' => isLipDist_discrete _))
  -- Step 3: kantLift (discreteMetric β) (f a) (g a) ≤ sdist f g
  apply iSup_le; intro D; apply iSup_le; intro _; apply iSup_le; intro h₀
  exact le_iSup₂_of_le D a (le_iSup_of_le h₀ le_rfl)

/-! ## Section 7: UCEmulatesConcurrent from sdist -/

/-- Lift a `sdist` bound to `UCEmulatesConcurrent`.

    When `leak = view` (same interface), the simulator is the identity (S = A).
    The bound follows from sdist + right PPL. -/
theorem UCEmulatesConcurrent_of_sdistITreeN {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) {hon out leak : Type} {ε : ℝ≥0∞}
    {π F : hon → ITreeN n E (out ⊕ leak)}
    (h : sdistITreeN n E handler π F ≤ ε) :
    UCEmulatesConcurrent handler n ε π F := by
  intro A
  exact ⟨A, le_trans (sdistITreeN_comp_right n E handler π F A) h⟩

/-! ## Section 7: Instances -/

/-- UCMonadMetric for `StatefulITreeN` via generic StateT lifting. -/
@[reducible] noncomputable def instUCMonadMetricStatefulITreeN
    (S : Type) (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    UCMonadMetric (StatefulITreeN S n E) := by
  letI : UCMonadMetric (ITreeN n E) := instUCMonadMetricITreeN n E handler
  exact stateT_UCMonadMetric

/-- Monad instance for `StatefulITreeN`. -/
@[reducible] noncomputable def instMonadStatefulITreeN
    (S : Type) (n : Nat) (E : EventSig)
    (handler : ∀ e : E.Event, SPComp (E.Resp e)) :
    Monad (StatefulITreeN S n E) := by
  letI : Monad (ITreeN n E) := instMonadITreeN n E handler
  exact StateT.instMonad

end UCMonad.StateTITreeN
