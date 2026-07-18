/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.UCMonad.ITreeN

/-!
# Event Signature Operations

Sum, injection, and mapping operations for `EventSig`. Used to model
compiler passes that change event signatures (e.g., resolving function
calls via inlining).

## Inspired by

Jasmin compiler (arXiv 2511.11292): event types `recCall +' ErrEvent +' void1`
composed via the ITree library's `+'` operator.

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.SecureCompilation

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC

/-! ## EventSig Sum -/

/-- Sum of two event signatures. Models compound adversary interfaces. -/
def EventSig.sum (E₁ E₂ : EventSig) : EventSig where
  Event := E₁.Event ⊕ E₂.Event
  Resp := fun
    | .inl e => E₁.Resp e
    | .inr e => E₂.Resp e

infixl:65 " +ₑ " => EventSig.sum

/-- Error event: triggers with error data, no valid continuation (Empty response). -/
def ErrEventSig (ErrData : Type) : EventSig where
  Event := ErrData
  Resp := fun _ => Empty

/-- Random sampling event: requests `n` random bytes. -/
def RndEventSig (SizeT ByteArr : Type) : EventSig where
  Event := SizeT
  Resp := fun _ => ByteArr

/-! ## Event Mapping -/

/-- An event mapping between two event signatures. -/
structure EventMap (E₁ E₂ : EventSig) where
  fwd : E₁.Event → E₂.Event
  bwd : ∀ e : E₁.Event, E₂.Resp (fwd e) → E₁.Resp e

/-- Identity event mapping. -/
def EventMap.id (E : EventSig) : EventMap E E where
  fwd := _root_.id
  bwd := fun _ => _root_.id

/-- Composition of event mappings. -/
def EventMap.comp {E₁ E₂ E₃ : EventSig}
    (g : EventMap E₂ E₃) (f : EventMap E₁ E₂) : EventMap E₁ E₃ where
  fwd := g.fwd ∘ f.fwd
  bwd := fun e r => f.bwd e (g.bwd (f.fwd e) r)

/-- Left injection into a sum event signature. -/
def EventMap.inl (E₁ E₂ : EventSig) : EventMap E₁ (E₁ +ₑ E₂) where
  fwd := Sum.inl
  bwd := fun _ r => r

/-- Right injection into a sum event signature. -/
def EventMap.inr (E₁ E₂ : EventSig) : EventMap E₂ (E₁ +ₑ E₂) where
  fwd := Sum.inr
  bwd := fun _ r => r

/-! ## ITreeN Event Remapping -/

/-- Remap events in an ITreeN via an EventMap. At level 0 (pure SPComp),
    events don't exist, so this is the identity. -/
noncomputable def ITreeN.mapEvents {α : Type} {E₁ E₂ : EventSig}
    (m : EventMap E₁ E₂) :
    (n : Nat) → ITreeN n E₁ α → ITreeN n E₂ α
  | 0, c => c
  | n + 1, c => SPComp.bind c (fun
    | .inl a => SPComp.pure (.inl a)
    | .inr (.inl k) => SPComp.pure (.inr (.inl (ITreeN.mapEvents m n k)))
    | .inr (.inr ⟨e, k⟩) =>
      SPComp.pure (.inr (.inr ⟨m.fwd e, fun r => ITreeN.mapEvents m n (k (m.bwd e r))⟩)))

/-- mapEvents at level 0 is the identity. -/
@[simp] theorem ITreeN.mapEvents_zero {α : Type} {E₁ E₂ : EventSig}
    (m : EventMap E₁ E₂) (c : SPComp α) :
    ITreeN.mapEvents (E₁ := E₁) (E₂ := E₂) m 0 c = c := rfl

/-- mapEvents preserves done. -/
theorem ITreeN.mapEvents_done {α : Type} {E₁ E₂ : EventSig}
    (m : EventMap E₁ E₂) : (n : Nat) → (a : α) →
    ITreeN.mapEvents m n (ITreeN.done n a) = ITreeN.done n a
  | 0, _ => rfl
  | _ + 1, a => by
    show SPComp.bind (SPComp.pure (Sum.inl a)) _ = SPComp.pure (Sum.inl a)
    exact SPComp.pure_bind (Sum.inl a) _

/-- mapEvents with identity mapping is the identity. -/
theorem ITreeN.mapEvents_id {α : Type} {E : EventSig} :
    (n : Nat) → (t : ITreeN n E α) →
    ITreeN.mapEvents (EventMap.id E) n t = t
  | 0, c => rfl
  | n + 1, c => by
    show SPComp.bind c _ = c
    conv_rhs => rw [← SPComp.bind_pure c]
    congr 1; funext x; cases x with
    | inl a => rfl
    | inr s => cases s with
      | inl k =>
        show SPComp.pure (Sum.inr (Sum.inl (ITreeN.mapEvents _ n k))) =
             SPComp.pure (Sum.inr (Sum.inl k))
        rw [ITreeN.mapEvents_id n k]
      | inr vc =>
        obtain ⟨e, k⟩ := vc
        -- Goal: pure (.inr (.inr ⟨(EventMap.id E).fwd e,
        --   fun r => mapEvents (EventMap.id E) n (k ((EventMap.id E).bwd e r))⟩))
        --       = pure (.inr (.inr ⟨e, k⟩))
        have hk : (fun r => ITreeN.mapEvents (E₁ := E) (E₂ := E)
            { fwd := _root_.id, bwd := fun _ => _root_.id } n (k r)) = k := by
          funext r; exact ITreeN.mapEvents_id n (k r)
        show SPComp.pure (α := ITreeNStep n E α)
            (Sum.inr (Sum.inr ⟨e, fun r =>
              ITreeN.mapEvents (E₁ := E) (E₂ := E)
                { fwd := _root_.id, bwd := fun _ => _root_.id } n (k r)⟩))
          = SPComp.pure (α := ITreeNStep n E α)
              (Sum.inr (Sum.inr ⟨e, k⟩))
        rw [hk]

/-! ## Handler Composition -/

/-- Pull back a handler along an EventMap. -/
noncomputable def EventMap.pullbackHandler {E₁ E₂ : EventSig} (m : EventMap E₁ E₂)
    (handler₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e)) :
    ∀ e : E₁.Event, SPComp (E₁.Resp e) :=
  fun e => SPComp.bind (handler₂ (m.fwd e)) (fun r => SPComp.pure (m.bwd e r))

/-- Handler for a sum event signature from handlers for each component. -/
noncomputable def sumHandler {E₁ E₂ : EventSig}
    (h₁ : ∀ e : E₁.Event, SPComp (E₁.Resp e))
    (h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e)) :
    ∀ e : (E₁ +ₑ E₂).Event, SPComp ((E₁ +ₑ E₂).Resp e)
  | .inl e => h₁ e
  | .inr e => h₂ e

/-! ## FlattenAll Commutation (Level 0) -/

/-- At level 0, mapEvents is identity so flattenAll commutes trivially. -/
@[simp] theorem ITreeN.mapEvents_flattenAll_zero {α : Type} {E₁ E₂ : EventSig}
    (m : EventMap E₁ E₂)
    (handler₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e))
    (t : SPComp α) :
    ITreeN.flattenAll handler₂ 0 (ITreeN.mapEvents (E₁ := E₁) m 0 t) =
    ITreeN.flattenAll (m.pullbackHandler handler₂) 0 t := rfl

/-! ## Flatten-mapEvents Commutation -/

/-- Flatten commutes with mapEvents via the pullback handler. -/
theorem flatten_mapEvents {α : Type} {E₁ E₂ : EventSig}
    (m : EventMap E₁ E₂)
    (handler₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e))
    (n : Nat) (c : ITreeN (n + 1) E₁ α) :
    ITreeN.flatten handler₂ n (ITreeN.mapEvents m (n + 1) c) =
    ITreeN.mapEvents m n (ITreeN.flatten (m.pullbackHandler handler₂) n c) := by
  cases n with
  | zero =>
    -- Both sides are SPComp; unfold and use bind_assoc
    simp only [ITreeN.mapEvents, ITreeN.flatten_zero, SPComp.bind_assoc]
    congr 1; funext x; cases x with
    | inl a => simp [SPComp.pure_bind]
    | inr s => cases s with
      | inl k => simp [SPComp.pure_bind]
      | inr vc =>
        obtain ⟨e, k⟩ := vc
        simp only [SPComp.pure_bind, EventMap.pullbackHandler, SPComp.bind_assoc]
  | succ m' =>
    simp only [ITreeN.mapEvents, ITreeN.flatten_succ, SPComp.bind_assoc]
    congr 1; funext x; cases x with
    | inl a => simp [SPComp.pure_bind]
    | inr s => cases s with
      | inl k => simp [SPComp.pure_bind]
      | inr vc =>
        obtain ⟨e, k⟩ := vc
        simp only [SPComp.pure_bind, EventMap.pullbackHandler, SPComp.bind_assoc]

/-- **Main commutation theorem**: `flattenAll` after `mapEvents` equals `flattenAll`
    with the pullback handler. This is the key lemma for cross-event-signature
    compilation: it shows that resolving mapped events is the same as resolving
    the original events with the pulled-back handler.

    Proof by induction on `n`:
    - Base: both sides are `t` (mapEvents 0 = id, flattenAll 0 = id)
    - Step: unfold flattenAll, apply `flatten_mapEvents`, then IH -/
theorem mapEvents_flattenAll {α : Type} {E₁ E₂ : EventSig}
    (m : EventMap E₁ E₂)
    (handler₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e))
    : (n : Nat) → (t : ITreeN n E₁ α) →
    ITreeN.flattenAll handler₂ n (ITreeN.mapEvents m n t) =
    ITreeN.flattenAll (m.pullbackHandler handler₂) n t
  | 0, t => rfl
  | n + 1, t => by
    simp only [ITreeN.flattenAll_succ]
    rw [flatten_mapEvents m handler₂ n t]
    exact mapEvents_flattenAll m handler₂ n _

/-! ## sumHandler and pullbackHandler Interaction -/

/-- Pulling back a sumHandler along inl gives the left handler. -/
theorem pullbackHandler_inl_sumHandler {E₁ E₂ : EventSig}
    (h₁ : ∀ e : E₁.Event, SPComp (E₁.Resp e))
    (h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e))
    (e : E₁.Event) :
    (EventMap.inl E₁ E₂).pullbackHandler (sumHandler h₁ h₂) e =
    SPComp.bind (h₁ e) (fun r => SPComp.pure r) := rfl

/-- Pulling back a sumHandler along inr gives the right handler. -/
theorem pullbackHandler_inr_sumHandler {E₁ E₂ : EventSig}
    (h₁ : ∀ e : E₁.Event, SPComp (E₁.Resp e))
    (h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e))
    (e : E₂.Event) :
    (EventMap.inr E₁ E₂).pullbackHandler (sumHandler h₁ h₂) e =
    SPComp.bind (h₂ e) (fun r => SPComp.pure r) := rfl

/-- The pullback handler along inl of a sumHandler equals h₁ up to bind-pure. -/
theorem pullbackHandler_inl_eq {E₁ E₂ : EventSig}
    (h₁ : ∀ e : E₁.Event, SPComp (E₁.Resp e))
    (h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e)) :
    (EventMap.inl E₁ E₂).pullbackHandler (sumHandler h₁ h₂) =
    fun e => SPComp.bind (h₁ e) SPComp.pure := rfl

end CatCrypt.Crypto.SecureCompilation
