/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.InliningDemo

/-!
# Multi-Pass Compiler Composition

Demonstrates composition of two compiler passes via `resolved_trans`:

```
kex_with_yields (yields + KDF events)
    ↓ Pass 1: yield elimination (CompilerCorrectResolved)
kex_source (KDF events remain)
    ↓ Pass 2: KDF inlining (CompilerCorrectResolved)
kex_target (no extra yields or events)
```

Each pass has a non-trivial proof (not `rfl`), and the composition
inherits zero sdist transitively.

## Main theorems

* `pass1_correct` — yield elimination is resolved-correct
* `pass2_correct` — KDF inlining is resolved-correct
* `multipass_correct` — composition via `resolved_trans`
* `multipass_security_transfer` — UC security transfers through both passes

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.SecureCompilation.MultiPass

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation Passes InliningDemo
open scoped ENNReal

variable {W : Type}

/-! ## Stage 0: Source with Yields

The original "unoptimized" source has extra yield (silent steps)
after the keyExchange event, representing redundant no-op rounds. -/

/-- Source with extra yields: keyExchange → yield → deriveKey → yield → tail. -/
noncomputable def kex_with_yields (deps : KexDeps W) :
    Unit → ITreeN 6 KEX_EventSig W :=
  fun () =>
    ITreeN.vis (E := KEX_EventSig) 5 KexEvent.keyExchange fun () =>
    ITreeN.yield (E := KEX_EventSig) 4
      (ITreeN.vis (E := KEX_EventSig) 3 KexEvent.deriveKey fun () =>
       ITreeN.yield (E := KEX_EventSig) 2
         (ITreeN.vis (E := KEX_EventSig) 1 KexEvent.deliver fun () =>
          embedSPComp (E := KEX_EventSig) 1
            (SPComp.bind deps.kex fun rawKey =>
             SPComp.bind (deps.kdf rawKey) fun derivedKey =>
             deps.format derivedKey)))

/-! ## Stage 1: Yield-Eliminated Source

After yield elimination: keyExchange → deriveKey → deliver → compute. -/

/-- Yield-eliminated: same as kex_source but at depth 6, with done padding. -/
noncomputable def kex_no_yields (deps : KexDeps W) :
    Unit → ITreeN 6 KEX_EventSig W :=
  fun () =>
    ITreeN.vis (E := KEX_EventSig) 5 KexEvent.keyExchange fun () =>
    ITreeN.done (E := KEX_EventSig) 5 () |>
    fun _ =>  -- depth 5 → use vis at 4
    ITreeN.vis (E := KEX_EventSig) 4 KexEvent.deriveKey fun () =>
    ITreeN.done (E := KEX_EventSig) 4 () |>
    fun _ =>
    ITreeN.vis (E := KEX_EventSig) 3 KexEvent.deliver fun () =>
    embedSPComp (E := KEX_EventSig) 3
      (SPComp.bind deps.kex fun rawKey =>
       SPComp.bind (deps.kdf rawKey) fun derivedKey =>
       deps.format derivedKey)

/-! ## Stage 2: KDF-Inlined Target

After KDF inlining: keyExchange → [inline KDF] → deliver → compute. -/

/-- KDF-inlined target at depth 6. -/
noncomputable def kex_inlined (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e)) :
    Unit → ITreeN 6 KEX_EventSig W :=
  fun () =>
    ITreeN.vis (E := KEX_EventSig) 5 KexEvent.keyExchange fun () =>
    ITreeN.bind' handler 5
      (embedSPComp (E := KEX_EventSig) 5 (handler KexEvent.deriveKey))
      fun () =>
    ITreeN.vis (E := KEX_EventSig) 4 KexEvent.deliver fun () =>
    embedSPComp (E := KEX_EventSig) 4
      (SPComp.bind deps.kex fun rawKey =>
       SPComp.bind (deps.kdf rawKey) fun derivedKey =>
       deps.format derivedKey)

/-! ## Pass 1: Yield Elimination -/

/-- Pass 1 correctness: yields are absorbed by flattenAll.
    Source has extra `yield` nodes; target replaces them with structural padding. -/
theorem pass1_correct (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e)) :
    CompilerCorrectResolved handler
      (kex_with_yields deps)
      (kex_no_yields deps) := by
  intro ()
  simp only [kex_with_yields, kex_no_yields]
  rw [flattenAll_vis handler 5 KexEvent.keyExchange]
  rw [flattenAll_vis handler 5 KexEvent.keyExchange]
  congr 1; funext ()
  -- LHS: flattenAll 5 (yield 4 (vis 3 deriveKey ...))
  rw [flattenAll_yield]
  -- LHS: flattenAll 4 (vis 3 deriveKey (fun () => yield 2 (vis 1 deliver ...)))
  rw [flattenAll_vis handler 3 KexEvent.deriveKey]
  -- RHS: flattenAll 5 (done 5 () |> ...)
  -- done 5 () |> fun _ => vis 4 deriveKey ... — this is just vis 4 deriveKey ...
  -- Actually, `ITreeN.done 5 () |> fun _ => vis 4 deriveKey ...` is
  -- `(fun _ => vis 4 deriveKey ...) (ITreeN.done 5 ())` = `vis 4 deriveKey ...`
  rw [flattenAll_vis handler 4 KexEvent.deriveKey]
  congr 1; funext ()
  -- LHS: flattenAll 3 (yield 2 (vis 1 deliver (fun () => embedSPComp 1 ...)))
  rw [flattenAll_yield]
  -- LHS: flattenAll 2 (vis 1 deliver ...)
  -- RHS: flattenAll 4 (done 4 () |> fun _ => vis 3 deliver (fun () => embedSPComp 3 ...))
  -- = flattenAll 4 (vis 3 deliver ...)
  rw [flattenAll_vis handler 1 KexEvent.deliver]
  rw [flattenAll_vis handler 3 KexEvent.deliver]
  congr 1; funext ()
  -- LHS: flattenAll 1 (embedSPComp 1 ...)
  -- RHS: flattenAll 3 (embedSPComp 3 ...)
  rw [flattenAll_embedSPComp, flattenAll_embedSPComp]

/-! ## Pass 2: KDF Inlining -/

/-- Pass 2 correctness: KDF event replaced by inlined body. -/
theorem pass2_correct (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e)) :
    CompilerCorrectResolved handler
      (kex_no_yields deps)
      (kex_inlined deps handler) := by
  intro ()
  simp only [kex_no_yields, kex_inlined]
  rw [flattenAll_vis handler 5 KexEvent.keyExchange]
  rw [flattenAll_vis handler 5 KexEvent.keyExchange]
  congr 1; funext ()
  -- LHS: flattenAll 5 (vis 4 deriveKey (fun () => ...))
  rw [flattenAll_vis handler 4 KexEvent.deriveKey]
  -- RHS: flattenAll 5 (bind' handler 5 (embedSPComp 5 (handler deriveKey)) ...)
  rw [flattenAll_bind, flattenAll_embedSPComp]
  congr 1; funext ()
  -- LHS: flattenAll 4 (vis 3 deliver (fun () => embedSPComp 3 ...))
  -- RHS: flattenAll 5 (vis 4 deliver (fun () => embedSPComp 4 ...))
  rw [flattenAll_vis handler 3 KexEvent.deliver]
  rw [flattenAll_vis handler 4 KexEvent.deliver]
  congr 1; funext ()
  rw [flattenAll_embedSPComp, flattenAll_embedSPComp]

/-! ## Multi-Pass Composition -/

/-- **Multi-pass correctness**: composing yield elimination and KDF inlining
    via `resolved_trans`. Each pass has a non-trivial proof. -/
theorem multipass_correct (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e)) :
    CompilerCorrectResolved handler
      (kex_with_yields deps)
      (kex_inlined deps handler) :=
  resolved_trans handler
    (pass1_correct deps handler)
    (pass2_correct deps handler)

/-- sdist = 0 for the multi-pass compilation. -/
theorem multipass_sdist_zero (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e)) :
    sdistITreeN 6 KEX_EventSig handler
      (kex_with_yields deps)
      (kex_inlined deps handler) = 0 :=
  resolved_sdist_zero handler (multipass_correct deps handler)

/-! ## Security Transfer -/

/-- **Main theorem**: If the original (unoptimized, with yields) protocol is
    ε-close to ideal, then the fully optimized (yields eliminated + KDF inlined)
    protocol is also ε-close.

    This composes two non-trivial compiler passes and transfers security exactly. -/
theorem multipass_security_transfer (deps : KexDeps W)
    (handler : ∀ e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e))
    (ideal : Unit → ITreeN 6 KEX_EventSig W)
    (ε : ℝ≥0∞)
    (hsec : sdistITreeN 6 KEX_EventSig handler
      (kex_with_yields deps) ideal ≤ ε) :
    sdistITreeN 6 KEX_EventSig handler
      (kex_inlined deps handler) ideal ≤ ε :=
  calc sdistITreeN 6 KEX_EventSig handler (kex_inlined deps handler) ideal
      ≤ sdistITreeN 6 KEX_EventSig handler (kex_inlined deps handler)
          (kex_with_yields deps)
        + sdistITreeN 6 KEX_EventSig handler (kex_with_yields deps) ideal :=
        sdistITreeN_triangle ..
    _ = 0 + sdistITreeN 6 KEX_EventSig handler (kex_with_yields deps) ideal := by
        rw [sdistITreeN_sym, multipass_sdist_zero]
    _ ≤ ε := by simp; exact hsec

end CatCrypt.Crypto.SecureCompilation.MultiPass
