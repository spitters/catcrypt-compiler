/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Framework

/-!
# Post-Resolution Compiler Correctness

Defines `CompilerCorrectResolved` — equality after `flattenAll` handler resolution —
and `CompilerCorrectCrossEvSig` — the cross-event-signature version where source
and target may have *different* event signatures but produce identical observations.

This models Jasmin-style compilation (arXiv 2511.11292) where source ≠ target as
ITreeN values but their observable behavior (after event resolution) coincides.

## Key insight

The existing `CompilerCorrect` demands `source x = target x` (before resolution),
making it trivial. The new `CompilerCorrectResolved` demands equality only after
`flattenAll`, allowing genuinely different tree structures.

## Main theorems

* `resolved_sdist_zero` — CompilerCorrectResolved ⟹ sdistITreeN = 0
* `cross_evsig_sdist_zero` — cross-event-sig ⟹ sdist = 0
* `resolved_preserves_uc` — UC security transfers post-resolution
* `resolved_trans` — compose two resolved-correct passes
* `CompilerCorrect_implies_Resolved` — old notion is a special case

## Infrastructure lemmas

* `flatten_yield` — flatten absorbs yields
* `flattenAll_yield` — flattenAll absorbs yields
* `flattenAll_vis` — flattenAll resolves vis nodes via handler
* `flattenAll_done` — flattenAll of done is pure

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open scoped ENNReal

/-! ## Infrastructure Lemmas for flattenAll -/

/-- Flatten absorbs a yield: `flatten handler n (yield n k) = k`. -/
theorem flatten_yield {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (k : ITreeN n E α) :
    ITreeN.flatten handler n (ITreeN.yield n k) = k := by
  cases n with
  | zero =>
    simp only [ITreeN.yield, ITreeN.flatten_zero, SPComp.pure_bind]
  | succ m =>
    simp only [ITreeN.yield, ITreeN.flatten_succ, SPComp.pure_bind]

/-- FlattenAll absorbs a yield: computing `flattenAll` of a yield
    equals `flattenAll` of the continuation. -/
theorem flattenAll_yield {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (k : ITreeN n E α) :
    ITreeN.flattenAll handler (n + 1) (ITreeN.yield n k) =
    ITreeN.flattenAll handler n k := by
  simp only [ITreeN.flattenAll_succ, flatten_yield]

/-- Flatten of a vis equals bind' with embedSPComp of the handler. -/
theorem flatten_vis_eq_bind' {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (e : E.Event) (k : E.Resp e → ITreeN n E α) :
    ITreeN.flatten handler n (ITreeN.vis n e k) =
    ITreeN.bind' handler n (embedSPComp n (handler e)) k := by
  cases n with
  | zero =>
    simp only [ITreeN.vis, ITreeN.flatten_zero, SPComp.pure_bind,
      ITreeN.bind'_zero, embedSPComp]
  | succ m =>
    simp only [ITreeN.vis, ITreeN.flatten_succ, SPComp.pure_bind,
      ITreeN.bind'_succ, embedSPComp, SPComp.bind_assoc]

/-- FlattenAll of a vis node resolves the event and continues. -/
theorem flattenAll_vis {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (e : E.Event) (k : E.Resp e → ITreeN n E α) :
    ITreeN.flattenAll handler (n + 1) (ITreeN.vis n e k) =
    SPComp.bind (handler e)
      (fun r => ITreeN.flattenAll handler n (k r)) := by
  simp only [ITreeN.flattenAll_succ]
  rw [flatten_vis_eq_bind' handler n e k, flattenAll_bind, flattenAll_embedSPComp]

/-- FlattenAll of a done value is `SPComp.pure a`. -/
theorem flattenAll_done {α : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (a : α) :
    ITreeN.flattenAll handler n (ITreeN.done (E := E) n a) = SPComp.pure a := by
  induction n with
  | zero => rfl
  | succ m ih =>
    -- flattenAll (m+1) (done (m+1) a) = flattenAll m (flatten m (done (m+1) a))
    -- done (m+1) a = SPComp.pure (.inl a)
    -- flatten m (SPComp.pure (.inl a)) = SPComp.pure (.inl a) |> match => done m a
    -- We use flattenAll_embedSPComp: flattenAll n (embedSPComp n c) = c
    -- done (m+1) a = SPComp.pure (.inl a) = embedSPComp (m+1) (SPComp.pure a)?
    -- Actually, embedSPComp (m+1) c = SPComp.bind c (fun a => SPComp.pure (.inl a))
    -- So embedSPComp (m+1) (SPComp.pure a) = SPComp.bind (SPComp.pure a) ... = SPComp.pure (.inl a)
    -- = done (m+1) a ✓
    have : ITreeN.done (E := E) (m + 1) a = embedSPComp (m + 1) (SPComp.pure a) := by
      show SPComp.pure (Sum.inl a) = SPComp.bind (SPComp.pure a) (fun a => SPComp.pure (Sum.inl a))
      rw [SPComp.pure_bind]
    rw [this, flattenAll_embedSPComp]

/-! ## Post-Resolution Compiler Correctness -/

/-- Post-resolution compiler correctness: source and target produce equal
    SPComp computations after flattening with the handler.

    Unlike `CompilerCorrect` (which demands tree equality), this allows
    source and target to have different ITreeN structures as long as they
    agree after event resolution. -/
def CompilerCorrectResolved {hon β : Type} {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (source target : hon → ITreeN n E β) : Prop :=
  ∀ x, ITreeN.flattenAll handler n (source x) = ITreeN.flattenAll handler n (target x)

/-- Cross-event-signature compiler correctness: source and target may have
    *different* event signatures, resolved by different handlers, but produce
    identical observable behavior.

    This is the Jasmin-style scenario: the source program has function-call
    events that are resolved by inlining, while the target has no such events. -/
def CompilerCorrectCrossEvSig {hon β : Type} {E_S E_T : EventSig} {n : Nat}
    (handler_S : ∀ e : E_S.Event, SPComp (E_S.Resp e))
    (handler_T : ∀ e : E_T.Event, SPComp (E_T.Resp e))
    (source : hon → ITreeN n E_S β)
    (target : hon → ITreeN n E_T β) : Prop :=
  ∀ x, ITreeN.flattenAll handler_S n (source x) = ITreeN.flattenAll handler_T n (target x)

/-! ## sdist = 0 from Resolved Correctness -/

/-- Post-resolution correctness implies zero statistical distance. -/
theorem resolved_sdist_zero {hon β : Type} {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    (h : CompilerCorrectResolved handler source target) :
    sdistITreeN n E handler source target = 0 := by
  have : (fun a => ITreeN.flattenAll handler n (source a)) =
         (fun a => ITreeN.flattenAll handler n (target a)) := funext h
  simp only [sdistITreeN, this, sdist_self]

/-- Cross-event-sig correctness gives zero sdist on the source side. -/
theorem cross_evsig_sdist_zero_source {hon β : Type} {E_S E_T : EventSig} {n : Nat}
    (handler_S : ∀ e : E_S.Event, SPComp (E_S.Resp e))
    (handler_T : ∀ e : E_T.Event, SPComp (E_T.Resp e))
    {source : hon → ITreeN n E_S β}
    {target : hon → ITreeN n E_T β}
    (h : CompilerCorrectCrossEvSig handler_S handler_T source target) :
    sdist (fun a => ITreeN.flattenAll handler_S n (source a))
          (fun a => ITreeN.flattenAll handler_T n (target a)) = 0 := by
  have : (fun a => ITreeN.flattenAll handler_S n (source a)) =
         (fun a => ITreeN.flattenAll handler_T n (target a)) := funext h
  rw [this]; exact sdist_self _

/-! ## UC Security Transfer -/

/-- Resolved correctness preserves UC security.

    If source UC-emulates F at distance ε, and source and target agree
    after handler resolution, then target also UC-emulates F at distance ε. -/
theorem resolved_preserves_uc {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {hon S out leak view : Type}
    {source target : hon → StatefulITreeN S n E (out ⊕ leak)}
    {F : hon → StatefulITreeN S n E (out ⊕ view)}
    {ε : ℝ≥0∞}
    (hcc : ∀ x s, ITreeN.flattenAll handler n (source x s) =
                   ITreeN.flattenAll handler n (target x s))
    (hsec : UCEmulatesConcurrentStateful handler n ε source F) :
    UCEmulatesConcurrentStateful handler n ε target F := by
  intro A
  obtain ⟨Sim, hSim⟩ := hsec A
  refine ⟨Sim, ?_⟩
  -- sdistITreeN compares flattenAll ∘ bind, and flattenAll_bind decomposes
  show sdistITreeN n E handler
    (fun (ps : hon × S) => ITreeN.bind' handler n (target ps.1 ps.2) A)
    (fun (ps : hon × S) => ITreeN.bind' handler n (F ps.1 ps.2) Sim) ≤ ε
  have key : ∀ (ps : hon × S),
      ITreeN.flattenAll handler n (ITreeN.bind' handler n (target ps.1 ps.2) A) =
      ITreeN.flattenAll handler n (ITreeN.bind' handler n (source ps.1 ps.2) A) := by
    intro ⟨x, s⟩
    simp only [flattenAll_bind]
    rw [hcc x s]
  have heq : (fun ps : hon × S =>
      ITreeN.flattenAll handler n (ITreeN.bind' handler n (target ps.1 ps.2) A)) =
    (fun ps : hon × S =>
      ITreeN.flattenAll handler n (ITreeN.bind' handler n (source ps.1 ps.2) A)) :=
    funext key
  show sdistITreeN n E handler _ _ ≤ ε
  unfold sdistITreeN
  rw [heq]
  exact hSim

/-! ## Composition -/

/-- Transitivity: compose two resolved-correct passes. -/
theorem resolved_trans {hon β : Type} {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {p₁ p₂ p₃ : hon → ITreeN n E β}
    (h₁₂ : CompilerCorrectResolved handler p₁ p₂)
    (h₂₃ : CompilerCorrectResolved handler p₂ p₃) :
    CompilerCorrectResolved handler p₁ p₃ :=
  fun x => (h₁₂ x).trans (h₂₃ x)

/-- The old `CompilerCorrect` notion implies `CompilerCorrectResolved` for any handler. -/
theorem CompilerCorrect_implies_Resolved {hon β : Type} {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    (h : CompilerCorrect source target) :
    CompilerCorrectResolved handler source target :=
  fun x => by rw [h x]

/-- Reflexivity. -/
theorem resolved_refl {hon β : Type} {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (p : hon → ITreeN n E β) :
    CompilerCorrectResolved handler p p :=
  fun _ => rfl

/-- Symmetry. -/
theorem resolved_symm {hon β : Type} {E : EventSig} {n : Nat}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    {p₁ p₂ : hon → ITreeN n E β}
    (h : CompilerCorrectResolved handler p₁ p₂) :
    CompilerCorrectResolved handler p₂ p₁ :=
  fun x => (h x).symm

end CatCrypt.Crypto.SecureCompilation
