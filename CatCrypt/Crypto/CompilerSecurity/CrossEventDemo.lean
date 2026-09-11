/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.CompilerSecurity.EventSum
public import CatCrypt.Crypto.CompilerSecurity.Resolved

/-!
# Cross-Event-Signature Compilation Case Study

Demonstrates `CompilerCorrectCrossEvSig` where source and target have
*different* event signatures:

- **Source**: `KEX_EventSig +ₑ KDFCallSig` (KDF is a function-call event)
- **Target**: `KEX_EventSig` only (KDF body inlined)

After resolving events, both produce the same `SPComp` computation,
proved via `flattenAll_vis` on both sides and the fact that `sumHandler`
dispatches correctly.

## Main theorems

* `kex_cross_compiler_correct` -- `CompilerCorrectCrossEvSig` for the case study
* `kex_cross_sdist_zero` -- sdist = 0 between source and target
* `kex_cross_security_transfer` -- UC security transfers

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.CrossEventDemo

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation
open scoped ENNReal

/-! ## Event Signatures -/

/-- Key exchange events (crypto-relevant). -/
inductive CrossKexEvent where
  | keyExchange
  | deliver

/-- Key exchange event signature. -/
def CrossKEX_EventSig : EventSig where
  Event := CrossKexEvent
  Resp := fun _ => Unit

/-- KDF function-call event: a single call that returns Unit. -/
inductive KDFCallEvent where
  | callKDF

/-- KDF function-call event signature. -/
def KDFCallSig : EventSig where
  Event := KDFCallEvent
  Resp := fun _ => Unit

/-! ## Abstract Dependencies -/

/-- Abstract dependencies for the cross-event key exchange. -/
structure CrossKexDeps (W : Type) where
  /-- Core computation after key exchange and KDF -/
  core : SPComp W
  /-- KDF body (the computation that callKDF represents) -/
  kdf_body : SPComp Unit

variable {W : Type}

/-! ## Source Protocol (with KDF call events) -/

/-- Source protocol: uses `KEX_EventSig +ₑ KDFCallSig`.
    Events: keyExchange (left) -> callKDF (right) -> deliver (left) -> core. -/
noncomputable def kex_cross_source (deps : CrossKexDeps W) :
    Unit -> ITreeN 4 (CrossKEX_EventSig +ₑ KDFCallSig) W :=
  fun () =>
    ITreeN.vis 3 (Sum.inl CrossKexEvent.keyExchange) fun () =>
    ITreeN.vis 2 (Sum.inr KDFCallEvent.callKDF) fun () =>
    ITreeN.vis 1 (Sum.inl CrossKexEvent.deliver) fun () =>
    embedSPComp 1 deps.core

/-! ## Target Protocol (KDF inlined) -/

/-- Target protocol: uses only `CrossKEX_EventSig`.
    Events: keyExchange -> [inline kdf_body] -> deliver -> core.
    The KDF event is replaced by directly binding the KDF body via the handler. -/
noncomputable def kex_cross_target (deps : CrossKexDeps W)
    (kex_handler : forall e : CrossKEX_EventSig.Event, SPComp (CrossKEX_EventSig.Resp e))
    (kdf_body : SPComp Unit) :
    Unit -> ITreeN 4 CrossKEX_EventSig W :=
  fun () =>
    ITreeN.vis 3 CrossKexEvent.keyExchange fun () =>
    ITreeN.bind' kex_handler 3
      (embedSPComp 3 kdf_body) fun () =>
    ITreeN.vis 2 CrossKexEvent.deliver fun () =>
    embedSPComp 2 deps.core

/-! ## Compiler Correctness -/

/-- Cross-event-sig compiler correctness: source (with KDF events) and
    target (KDF inlined) produce the same SPComp after resolution.

    Source resolves via `sumHandler kex_handler kdf_handler` which dispatches
    `callKDF` to `kdf_handler`. Target directly embeds `kdf_body`. Both
    produce `bind (kex_handler keyExchange) (... bind kdf_body ...)`. -/
theorem kex_cross_compiler_correct (deps : CrossKexDeps W)
    (kex_handler : forall e : CrossKEX_EventSig.Event, SPComp (CrossKEX_EventSig.Resp e))
    (kdf_handler : forall e : KDFCallSig.Event, SPComp (KDFCallSig.Resp e)) :
    CompilerCorrectCrossEvSig
      (sumHandler kex_handler kdf_handler)
      kex_handler
      (kex_cross_source deps)
      (kex_cross_target deps kex_handler (kdf_handler KDFCallEvent.callKDF)) := by
  intro ()
  simp only [kex_cross_source, kex_cross_target]
  -- LHS: flattenAll (sumHandler ...) 4 (vis 3 (.inl keyExchange) ...)
  rw [flattenAll_vis (sumHandler kex_handler kdf_handler) 3
    (Sum.inl CrossKexEvent.keyExchange)]
  -- RHS: flattenAll kex_handler 4 (vis 3 keyExchange ...)
  rw [flattenAll_vis kex_handler 3 CrossKexEvent.keyExchange]
  -- sumHandler (.inl e) = kex_handler e
  simp only [sumHandler]
  congr 1; funext ()
  -- LHS: flattenAll 3 (vis 2 (.inr callKDF) ...)
  rw [flattenAll_vis (sumHandler kex_handler kdf_handler) 2
    (Sum.inr KDFCallEvent.callKDF)]
  -- RHS: flattenAll 3 (bind' 3 (embedSPComp 3 kdf_body) ...)
  rw [flattenAll_bind, flattenAll_embedSPComp]
  -- sumHandler (.inr e) = kdf_handler e
  simp only [sumHandler]
  congr 1; funext ()
  -- LHS: flattenAll 2 (vis 1 (.inl deliver) ...)
  rw [flattenAll_vis (sumHandler kex_handler kdf_handler) 1
    (Sum.inl CrossKexEvent.deliver)]
  -- RHS: flattenAll 3 (vis 2 deliver ...)
  rw [flattenAll_vis kex_handler 2 CrossKexEvent.deliver]
  simp only [sumHandler]
  congr 1; funext ()
  rw [flattenAll_embedSPComp, flattenAll_embedSPComp]

/-! ## sdist = 0 -/

/-- Zero sdist follows from cross-event-sig correctness. -/
theorem kex_cross_sdist_zero (deps : CrossKexDeps W)
    (kex_handler : forall e : CrossKEX_EventSig.Event, SPComp (CrossKEX_EventSig.Resp e))
    (kdf_handler : forall e : KDFCallSig.Event, SPComp (KDFCallSig.Resp e)) :
    sdist
      (fun a => ITreeN.flattenAll (sumHandler kex_handler kdf_handler) 4
        (kex_cross_source deps a))
      (fun a => ITreeN.flattenAll kex_handler 4
        (kex_cross_target deps kex_handler (kdf_handler KDFCallEvent.callKDF) a)) = 0 :=
  cross_evsig_sdist_zero_source _ _
    (kex_cross_compiler_correct deps kex_handler kdf_handler)

/-! ## Security Transfer -/

/-- If the source is ε-close to an ideal functionality (in the sum-event-sig world),
    the target (with KDF inlined) inherits the same bound. -/
theorem kex_cross_security_transfer (deps : CrossKexDeps W)
    (kex_handler : forall e : CrossKEX_EventSig.Event, SPComp (CrossKEX_EventSig.Resp e))
    (kdf_handler : forall e : KDFCallSig.Event, SPComp (KDFCallSig.Resp e))
    (ideal : Unit -> ITreeN 4 CrossKEX_EventSig W)
    (ε : ℝ≥0∞)
    (hsec : sdist
      (fun a => ITreeN.flattenAll (sumHandler kex_handler kdf_handler) 4
        (kex_cross_source deps a))
      (fun a => ITreeN.flattenAll kex_handler 4 (ideal a)) ≤ ε) :
    sdist
      (fun a => ITreeN.flattenAll kex_handler 4
        (kex_cross_target deps kex_handler (kdf_handler KDFCallEvent.callKDF) a))
      (fun a => ITreeN.flattenAll kex_handler 4 (ideal a)) ≤ ε := by
  have heq := kex_cross_compiler_correct deps kex_handler kdf_handler
  have : (fun a => ITreeN.flattenAll kex_handler 4
      (kex_cross_target deps kex_handler (kdf_handler KDFCallEvent.callKDF) a)) =
    (fun a => ITreeN.flattenAll (sumHandler kex_handler kdf_handler) 4
      (kex_cross_source deps a)) := funext (fun x => (heq x).symm)
  rw [this]; exact hsec

/-! ## Using mapEvents_flattenAll -/

/-- Alternative proof via `mapEvents_flattenAll`: the source's left-injected events
    resolve via the pullback handler, which equals `kex_handler` up to `bind-pure`. -/
theorem kex_cross_via_mapEvents (_deps : CrossKexDeps W)
    (kex_handler : forall e : CrossKEX_EventSig.Event, SPComp (CrossKEX_EventSig.Resp e))
    (kdf_handler : forall e : KDFCallSig.Event, SPComp (KDFCallSig.Resp e))
    (t : ITreeN 4 CrossKEX_EventSig W) :
    ITreeN.flattenAll (sumHandler kex_handler kdf_handler) 4
      (ITreeN.mapEvents (EventMap.inl CrossKEX_EventSig KDFCallSig) 4 t) =
    ITreeN.flattenAll
      ((EventMap.inl CrossKEX_EventSig KDFCallSig).pullbackHandler
        (sumHandler kex_handler kdf_handler)) 4 t :=
  mapEvents_flattenAll _ _ 4 t

end CatCrypt.Crypto.SecureCompilation.CrossEventDemo
