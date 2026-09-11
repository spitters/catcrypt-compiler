/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Passes

/-!
# Case Study: Key Exchange with KDF Function Call Inlining

Full case study demonstrating genuinely non-trivial secure compilation:

1. **Source**: Key exchange protocol where KDF is a *visible event* (function call)
2. **Target**: Key exchange with KDF *inlined* — structurally different ITreeN
3. **Compiler correctness**: Non-trivial `CompilerCorrectResolved` proof
4. **Security transfer**: UC security at ε transfers from source to target

The source and target are **different** ITreeN values: the source uses
`vis deriveKey` while the target uses `bind' (embedSPComp (handler deriveKey))`.
After `flattenAll`, both resolve to the same `SPComp` computation.

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.InliningDemo

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation Passes
open scoped ENNReal

/-! ## Protocol Definitions -/

/-- Key exchange visible events. -/
inductive KexEvent where
  | keyExchange  -- Initiate key exchange
  | deriveKey    -- Call KDF (function-call event)
  | deliver      -- Deliver result

/-- Key exchange event signature: all events return Unit. -/
def KEX_EventSig : EventSig where
  Event := KexEvent
  Resp := fun _ => Unit

/-- Abstract dependencies for the key exchange. -/
structure KexDeps (W : Type) where
  /-- Key exchange computation -/
  kex : SPComp W
  /-- Key derivation function -/
  kdf : W → SPComp W
  /-- Format output -/
  format : W → SPComp W

variable {W : Type}

/-- The common tail: deliver event + core computation. -/
noncomputable def kex_tail (deps : KexDeps W) : ITreeN 2 KEX_EventSig W :=
  ITreeN.vis (E := KEX_EventSig) 1 KexEvent.deliver fun () =>
  embedSPComp (E := KEX_EventSig) 1
    (SPComp.bind deps.kex fun rawKey =>
     SPComp.bind (deps.kdf rawKey) fun derivedKey =>
     deps.format derivedKey)

/-! ## Source Protocol -/

/-- Source protocol: KDF is a visible event.
    Events: keyExchange → deriveKey → deliver → compute. -/
noncomputable def kex_source (deps : KexDeps W) :
    Unit → ITreeN 4 KEX_EventSig W :=
  fun () =>
    ITreeN.vis (E := KEX_EventSig) 3 KexEvent.keyExchange fun () =>
    ITreeN.vis (E := KEX_EventSig) 2 KexEvent.deriveKey fun () =>
    kex_tail deps

/-! ## Target Protocol -/

/-- Target protocol: KDF is inlined via `bind' handler (embedSPComp (handler deriveKey))`.
    Events: keyExchange → [inline KDF body] → deliver → compute. -/
noncomputable def kex_target (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e)) :
    Unit → ITreeN 4 KEX_EventSig W :=
  fun () =>
    ITreeN.vis (E := KEX_EventSig) 3 KexEvent.keyExchange fun () =>
    ITreeN.bind' handler 3
      (embedSPComp (E := KEX_EventSig) 3 (handler KexEvent.deriveKey))
      fun () => embedSPComp (E := KEX_EventSig) 3
        (ITreeN.flattenAll handler 2 (kex_tail deps))

/-! ## Compiler Correctness -/

/-- Compiler correctness for the KDF inlining pass.
    After flattenAll, both produce the same SPComp computation because
    the handler resolves `vis deriveKey` to the same value that the target inlines.

    This is genuinely NON-TRIVIAL: source and target are different ITreeN values.
    The proof requires `flattenAll_vis`, `flattenAll_bind`, `flattenAll_embedSPComp`. -/
theorem kex_compiler_correct (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e)) :
    CompilerCorrectResolved handler
      (kex_source deps)
      (kex_target deps handler) := by
  intro ()
  simp only [kex_source, kex_target]
  -- LHS: flattenAll 4 (vis 3 keyExchange (fun () => vis 2 deriveKey (fun () => tail)))
  rw [flattenAll_vis handler 3 KexEvent.keyExchange]
  -- LHS = bind (handler keyExchange) (fun () =>
  --          flattenAll 3 (vis 2 deriveKey (fun () => tail)))
  -- RHS: flattenAll 4 (vis 3 keyExchange (fun () =>
  --         bind' handler 3 (embedSPComp 3 (handler deriveKey)) (fun () => embedSPComp 3 ...)))
  rw [flattenAll_vis handler 3 KexEvent.keyExchange]
  -- RHS = bind (handler keyExchange) (fun () =>
  --          flattenAll 3 (bind' handler 3 (embedSPComp 3 ...) ...))
  congr 1; funext ()
  -- LHS: flattenAll 3 (vis 2 deriveKey (fun () => tail))
  rw [flattenAll_vis handler 2 KexEvent.deriveKey]
  -- LHS = bind (handler deriveKey) (fun () => flattenAll 2 tail)
  -- RHS: flattenAll 3 (bind' handler 3 (embedSPComp 3 (handler deriveKey)) ...)
  rw [flattenAll_bind, flattenAll_embedSPComp]
  -- RHS = bind (handler deriveKey) (fun () => flattenAll 3 (embedSPComp 3 (flattenAll 2 tail)))
  congr 1; funext ()
  -- Goal: flattenAll 2 (kex_tail deps) =
  --       flattenAll 3 (embedSPComp 3 (flattenAll 2 (kex_tail deps)))
  exact (flattenAll_embedSPComp handler 3 _).symm

/-- sdist = 0 between source and target. -/
theorem kex_sdist_zero (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e)) :
    sdistITreeN 4 KEX_EventSig handler
      (kex_source deps)
      (kex_target deps handler) = 0 :=
  resolved_sdist_zero handler (kex_compiler_correct deps handler)

/-! ## Ideal Functionality -/

/-- Ideal functionality: replaces derived key with random. -/
noncomputable def kex_ideal (deps : KexDeps W) (sampleRandom : SPComp W) :
    Unit → ITreeN 4 KEX_EventSig W :=
  fun () =>
    ITreeN.vis (E := KEX_EventSig) 3 KexEvent.keyExchange fun () =>
    ITreeN.vis (E := KEX_EventSig) 2 KexEvent.deriveKey fun () =>
    ITreeN.vis (E := KEX_EventSig) 1 KexEvent.deliver fun () =>
    embedSPComp (E := KEX_EventSig) 1
      (SPComp.bind deps.kex fun _rawKey =>
       SPComp.bind sampleRandom fun randomKey =>
       deps.format randomKey)

/-! ## Security Transfer -/

/-- **Main theorem**: If source has sdist ≤ ε to ideal, target also has sdist ≤ ε.
    Proof: triangle inequality + sdist(target, source) = 0.

    This is the secure compilation guarantee: the compiler produces code
    that inherits the source's security bound exactly. -/
theorem kex_security_transfer (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e))
    (ideal : Unit → ITreeN 4 KEX_EventSig W)
    (ε : ℝ≥0∞)
    (hsec : sdistITreeN 4 KEX_EventSig handler
      (kex_source deps) ideal ≤ ε) :
    sdistITreeN 4 KEX_EventSig handler
      (kex_target deps handler) ideal ≤ ε :=
  calc sdistITreeN 4 KEX_EventSig handler (kex_target deps handler) ideal
      ≤ sdistITreeN 4 KEX_EventSig handler (kex_target deps handler) (kex_source deps)
        + sdistITreeN 4 KEX_EventSig handler (kex_source deps) ideal :=
        sdistITreeN_triangle ..
    _ = 0 + sdistITreeN 4 KEX_EventSig handler (kex_source deps) ideal := by
        rw [sdistITreeN_sym, kex_sdist_zero]
    _ ≤ ε := by simp; exact hsec

/-- Security transfer specialized to the KDF ideal: compiled code is
    ε-close to the KDF-ideal functionality. -/
theorem kex_inlined_security (deps : KexDeps W)
    (sampleRandom : SPComp W) (ε : ℝ≥0∞)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e))
    (hsec : sdistITreeN 4 KEX_EventSig handler
      (kex_source deps)
      (kex_ideal deps sampleRandom) ≤ ε) :
    sdistITreeN 4 KEX_EventSig handler
      (kex_target deps handler)
      (kex_ideal deps sampleRandom) ≤ ε :=
  kex_security_transfer deps handler _ ε hsec

end CatCrypt.Crypto.SecureCompilation.InliningDemo
