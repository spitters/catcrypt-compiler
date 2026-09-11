/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Resolved

/-!
# Compiler Passes with Non-Trivial Correctness Proofs

Three compiler passes demonstrating genuinely non-trivial post-resolution
compiler correctness:

## Pass 1: Yield-to-EmbedSPComp Elimination
- **Source**: `vis e (fun r => yield n (k r))` — event + silent yield + k
- **Target**: `embedSPComp` of the flattened continuation — structurally different
- **Proof**: `flattenAll_yield` + `flattenAll_embedSPComp`

## Pass 2: Sample Reordering
- **Source**: `embedSPComp (bind (sample W) (fun a => bind (sample W) (fun b => g a b)))`
- **Target**: Same with a, b swapped
- **Proof**: `flattenAll_embedSPComp` + `isPure_bind_comm_left` (Fubini)

## Pass 3: Function Call Inlining (Same-Event-Sig)
- **Source**: `vis (.inr fid) k` — function call event
- **Target**: `bind' (embedSPComp (body fid)) k` — inlined function body
- **Proof**: `flattenAll_vis` resolves event via handler = `flattenAll_bind` inlines body

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Passes

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN
open SecureCompilation
open scoped ENNReal

/-! ## Pass 1: Yield Elimination

Source adds a yield (silent step) after an event; target skips it.
These are different ITreeN values but produce the same flattenAll.
-/

/-- Source: event e, then yield (silent step), then done with value. -/
noncomputable def yieldElim_source {β : Type} {E : EventSig}
    (n : Nat) (e : E.Event) (v : E.Resp e → β) :
    Unit → ITreeN (n + 2) E β :=
  fun () => ITreeN.vis (n + 1) e (fun r => ITreeN.yield n (ITreeN.done n (v r)))

/-- Target: event e, then directly done with value (no yield). -/
noncomputable def yieldElim_target {β : Type} {E : EventSig}
    (n : Nat) (e : E.Event) (v : E.Resp e → β) :
    Unit → ITreeN (n + 2) E β :=
  fun () => ITreeN.vis (n + 1) e (fun r => ITreeN.done (n + 1) (v r))

/-- Yield elimination is `CompilerCorrectResolved`: source and target agree
    after `flattenAll` because yields are absorbed and `done` is pure. -/
theorem yieldElim_resolved {β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (e : E.Event) (v : E.Resp e → β) :
    CompilerCorrectResolved handler
      (yieldElim_source n e v)
      (yieldElim_target n e v) := by
  intro ()
  simp only [yieldElim_source, yieldElim_target]
  rw [flattenAll_vis handler (n + 1) e (fun r => ITreeN.yield n (ITreeN.done n (v r)))]
  rw [flattenAll_vis handler (n + 1) e (fun r => ITreeN.done (n + 1) (v r))]
  congr 1; funext r
  -- LHS: flattenAll (n+1) (yield n (done n (v r))) = flattenAll n (done n (v r)) = pure (v r)
  rw [flattenAll_yield, flattenAll_done]
  -- RHS: flattenAll (n+1) (done (n+1) (v r)) = pure (v r)
  rw [flattenAll_done]

/-- The sdist between source and target is 0. -/
theorem yieldElim_sdist_zero {β : Type} {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (e : E.Event) (v : E.Resp e → β) :
    sdistITreeN (n + 2) E handler
      (yieldElim_source n e v)
      (yieldElim_target n e v) = 0 :=
  resolved_sdist_zero handler (yieldElim_resolved handler n e v)

/-! ## Pass 2: Sample Reordering

Two independent samples can be reordered because `sample` is `IsPure`
(heap-independent), so bind commutes by Fubini's theorem.
-/

/-- Source: sample a, then sample b, apply g. -/
noncomputable def sampleReorder_source {β : Type} {E : EventSig}
    {W : Type} [Fintype W] [Nonempty W]
    (n : Nat) (g : W → W → SPComp β) :
    Unit → ITreeN n E β :=
  fun () => embedSPComp n
    (SPComp.bind (SPComp.sample W) fun a =>
     SPComp.bind (SPComp.sample W) fun b =>
     g a b)

/-- Target: sample b, then sample a, apply g (reordered). -/
noncomputable def sampleReorder_target {β : Type} {E : EventSig}
    {W : Type} [Fintype W] [Nonempty W]
    (n : Nat) (g : W → W → SPComp β) :
    Unit → ITreeN n E β :=
  fun () => embedSPComp n
    (SPComp.bind (SPComp.sample W) fun b =>
     SPComp.bind (SPComp.sample W) fun a =>
     g a b)

/-- Sample reordering is resolved-correct: `sample` is `IsPure`, so
    bind commutes by Fubini's theorem (`isPure_bind_comm_left`). -/
theorem sampleReorder_resolved {β : Type} {E : EventSig}
    {W : Type} [Fintype W] [Nonempty W]
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (g : W → W → SPComp β) :
    CompilerCorrectResolved handler
      (sampleReorder_source (E := E) n g)
      (sampleReorder_target (E := E) n g) := by
  intro ()
  simp only [sampleReorder_source, sampleReorder_target]
  rw [flattenAll_embedSPComp, flattenAll_embedSPComp]
  exact SPComp.isPure_bind_comm_left _ _ g (SPComp.sample_isPure W)

/-- The sdist between source and target is 0. -/
theorem sampleReorder_sdist_zero {β : Type} {E : EventSig}
    {W : Type} [Fintype W] [Nonempty W]
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (g : W → W → SPComp β) :
    sdistITreeN n E handler
      (sampleReorder_source (E := E) n g)
      (sampleReorder_target (E := E) n g) = 0 :=
  resolved_sdist_zero handler (sampleReorder_resolved handler n g)

/-! ## Pass 3: Function Call Inlining

Source emits a visible event for a function call; target inlines the body.
Both live in the same event signature. The handler resolves the source event
to the same SPComp as the inlined body.
-/

/-- Function call event signature: one event per function ID, response is return value. -/
def FuncCallSig (FuncId Ret : Type) : EventSig where
  Event := FuncId
  Resp := fun _ => Ret

/-- Source: emits a visible event for `fid`, then continues with `k`.
    The event type is exactly `E.Event`, so `fid : E.Event`. -/
noncomputable def funcInline_source {α : Type}
    {E : EventSig}
    (n : Nat) (fid : E.Event)
    (k : E.Resp fid → ITreeN n E α) :
    Unit → ITreeN (n + 1) E α :=
  fun () => ITreeN.vis n fid k

/-- Target: inlines the body (from the handler), then continues with `k`.
    Uses `bind'` to sequence `embedSPComp (body fid)` with the continuation. -/
noncomputable def funcInline_target {α : Type}
    {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (fid : E.Event)
    (k : E.Resp fid → ITreeN n E α) :
    Unit → ITreeN (n + 1) E α :=
  fun () => ITreeN.bind' handler (n + 1)
    (embedSPComp (n + 1) (handler fid))
    (fun r => embedSPComp (n + 1)
      (ITreeN.flattenAll handler n (k r)))

/-- Function call inlining is resolved-correct:
    source emits vis, resolved by handler; target inlines handler directly.
    Both produce `SPComp.bind (handler fid) (flattenAll n ∘ k)` after flattenAll. -/
theorem funcInline_resolved {α : Type}
    {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (fid : E.Event)
    (k : E.Resp fid → ITreeN n E α) :
    CompilerCorrectResolved handler
      (funcInline_source n fid k)
      (funcInline_target handler n fid k) := by
  intro ()
  simp only [funcInline_source, funcInline_target]
  -- LHS: flattenAll (n+1) (vis n fid k)
  -- = SPComp.bind (handler fid) (fun r => flattenAll n (k r))
  rw [flattenAll_vis handler n fid k]
  -- RHS: flattenAll (n+1) (bind' (n+1) (embedSPComp (n+1) (handler fid)) ...)
  -- = SPComp.bind (flattenAll (n+1) (embedSPComp (n+1) (handler fid)))
  --              (fun r => flattenAll (n+1) (embedSPComp (n+1) (flattenAll n (k r))))
  -- = SPComp.bind (handler fid) (fun r => flattenAll n (k r))
  rw [flattenAll_bind, flattenAll_embedSPComp]
  congr 1; funext r
  exact (flattenAll_embedSPComp handler (n + 1) (ITreeN.flattenAll handler n (k r))).symm

/-- sdist = 0 for the inlining pass. -/
theorem funcInline_sdist_zero {α : Type}
    {E : EventSig}
    (handler : ∀ e : E.Event, SPComp (E.Resp e))
    (n : Nat) (fid : E.Event)
    (k : E.Resp fid → ITreeN n E α) :
    sdistITreeN (n + 1) E handler
      (funcInline_source n fid k)
      (funcInline_target handler n fid k) = 0 :=
  resolved_sdist_zero handler (funcInline_resolved handler n fid k)

end CatCrypt.Crypto.SecureCompilation.Passes
