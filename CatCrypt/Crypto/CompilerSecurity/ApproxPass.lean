/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Passes
public import CatCrypt.Crypto.CompilerSecurity.MultiPass

/-!
# Approximate Compiler Pass (Non-Zero ε)

A compiler pass where source and target differ by a bounded amount ε,
not zero. This models passes like PRG approximation where the compiled
code uses a cheaper computation that is ε-close to the original.

## Key idea

Previous passes have `sdist = 0` (exact correctness). Here we allow
`sdist ≤ ε_prg`, then compose with exact passes via the triangle inequality.

## Main theorems

* `approxPass_sdist_le` -- sdist between approximate source/target bounded by core sdist
* `multipass_nonzero_composition` -- compose exact (ε=0) and approximate (ε>0) passes
* `multipass_nonzero_security_transfer` -- full pipeline: source security + compilation

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.ApproxPass

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation Passes InliningDemo
open scoped ENNReal

/-! ## Approximate Compiler Pass -/

/-- Source: event + exact core computation. -/
noncomputable def approxPass_source {β : Type} {E : EventSig}
    (exact_core : SPComp β) (n : Nat) (e : E.Event) :
    Unit -> ITreeN (n + 1) E β :=
  fun () => ITreeN.vis n e (fun _ => embedSPComp n exact_core)

/-- Target: event + approximate core (ε-close to exact). -/
noncomputable def approxPass_target {β : Type} {E : EventSig}
    (approx_core : SPComp β) (n : Nat) (e : E.Event) :
    Unit -> ITreeN (n + 1) E β :=
  fun () => ITreeN.vis n e (fun _ => embedSPComp n approx_core)

/-- The sdist between approximate source and target is bounded by sdist between cores.
    Proof: `flattenAll_vis` reduces both to `bind (handler e) (fun _ => core)`,
    then `flattenAll_embedSPComp` gives the raw cores. -/
theorem approxPass_sdist_le {β : Type} {E : EventSig}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (exact_core approx_core : SPComp β)
    (n : Nat) (e : E.Event) :
    sdistITreeN (n + 1) E handler
      (approxPass_source exact_core n e)
      (approxPass_target approx_core n e) ≤
    sdist (fun (_ : Unit) => exact_core)
          (fun (_ : Unit) => approx_core) := by
  unfold sdistITreeN sdist approxPass_source approxPass_target
  apply iSup_le; intro D
  apply iSup_le; intro ()
  apply iSup_le; intro h₀
  simp only [flattenAll_vis, flattenAll_embedSPComp, SPComp.bind_assoc]
  apply absDiff_prTrue_bind_le (handler e) _ _ h₀
  · intro _ h'
    apply le_add_of_absDiff_le
    exact le_iSup₂_of_le D () (le_iSup_of_le h' le_rfl)
  · intro _ h'
    apply le_add_of_absDiff_le
    rw [absDiff_comm]
    exact le_iSup₂_of_le D () (le_iSup_of_le h' le_rfl)

/-- Simplified: if `sdist` between cores is at most ε, so is `sdistITreeN`. -/
theorem approxPass_sdist_le' {β : Type} {E : EventSig}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (exact_core approx_core : SPComp β)
    (n : Nat) (e : E.Event) (ε : ℝ≥0∞)
    (hε : sdist (fun (_ : Unit) => exact_core)
               (fun (_ : Unit) => approx_core) ≤ ε) :
    sdistITreeN (n + 1) E handler
      (approxPass_source exact_core n e)
      (approxPass_target approx_core n e) ≤ ε :=
  le_trans (approxPass_sdist_le handler exact_core approx_core n e) hε

/-! ## Multi-Pass Composition with Non-Zero ε -/

variable {W : Type}

/-- A "PRG-approximated" version of the KDF target: same structure as kex_inlined
    but with an approximate core. -/
noncomputable def kex_approx (deps : KexDeps W)
    (handler : forall e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e))
    (approx_format : W -> SPComp W) :
    Unit -> ITreeN 6 KEX_EventSig W :=
  fun () =>
    ITreeN.vis 5 KexEvent.keyExchange fun () =>
    ITreeN.bind' handler 5
      (embedSPComp 5 (handler KexEvent.deriveKey))
      fun () =>
    ITreeN.vis 4 KexEvent.deliver fun () =>
    embedSPComp 4
      (SPComp.bind deps.kex fun rawKey =>
       SPComp.bind (deps.kdf rawKey) fun derivedKey =>
       approx_format derivedKey)

/-- Multi-pass composition: exact pass (yield elimination, sdist = 0) followed by
    approximate pass (format approximation, sdist ≤ ε). Total: 0 + ε = ε. -/
theorem multipass_nonzero_composition
    (deps : KexDeps W)
    (handler : forall e : KEX_EventSig.Event, SPComp (KEX_EventSig.Resp e))
    (approx_format : W -> SPComp W)
    (ε : ℝ≥0∞)
    (h_approx : sdistITreeN 6 KEX_EventSig handler
      (MultiPass.kex_inlined deps handler)
      (kex_approx deps handler approx_format) ≤ ε) :
    sdistITreeN 6 KEX_EventSig handler
      (MultiPass.kex_with_yields deps)
      (kex_approx deps handler approx_format) ≤ 0 + ε :=
  calc sdistITreeN 6 KEX_EventSig handler
        (MultiPass.kex_with_yields deps)
        (kex_approx deps handler approx_format)
      ≤ sdistITreeN 6 KEX_EventSig handler
          (MultiPass.kex_with_yields deps)
          (MultiPass.kex_inlined deps handler) +
        sdistITreeN 6 KEX_EventSig handler
          (MultiPass.kex_inlined deps handler)
          (kex_approx deps handler approx_format) := sdistITreeN_triangle ..
    _ = 0 + sdistITreeN 6 KEX_EventSig handler
          (MultiPass.kex_inlined deps handler)
          (kex_approx deps handler approx_format) := by
        rw [MultiPass.multipass_sdist_zero]
    _ ≤ 0 + ε := by simp; exact h_approx

/-! ## Full Security Pipeline -/

/-- Full pipeline: if source has sdist ≤ ε₁ to ideal, and the approximate pass
    adds at most ε₂, then the final compiled code has sdist ≤ ε₁ + ε₂.

    Pipeline:
    ```
    source --[exact passes, sdist=0]--> intermediate --[approx, sdist≤ε₂]--> target
       |                                                                        |
       | sdist ≤ ε₁ to ideal                              sdist ≤ ε₁ + ε₂ to ideal
    ```
-/
theorem multipass_nonzero_security_transfer
    {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source intermediate target ideal : hon -> ITreeN n E β}
    {ε₁ ε₂ : ℝ≥0∞}
    (h_exact : CompilerCorrectResolved handler source intermediate)
    (h_approx : sdistITreeN n E handler intermediate target ≤ ε₂)
    (h_sec : sdistITreeN n E handler source ideal ≤ ε₁) :
    sdistITreeN n E handler target ideal ≤ ε₁ + ε₂ := by
  have h1 : sdistITreeN n E handler target intermediate ≤ ε₂ := by
    rw [sdistITreeN_sym]; exact h_approx
  have h2 : sdistITreeN n E handler intermediate ideal ≤ ε₁ := by
    calc sdistITreeN n E handler intermediate ideal
        ≤ sdistITreeN n E handler intermediate source
          + sdistITreeN n E handler source ideal := sdistITreeN_triangle ..
      _ = 0 + sdistITreeN n E handler source ideal := by
          rw [sdistITreeN_sym, resolved_sdist_zero handler h_exact]
      _ = sdistITreeN n E handler source ideal := zero_add _
      _ ≤ ε₁ := h_sec
  calc sdistITreeN n E handler target ideal
      ≤ sdistITreeN n E handler target intermediate
        + sdistITreeN n E handler intermediate ideal := sdistITreeN_triangle ..
    _ ≤ ε₂ + ε₁ := add_le_add h1 h2
    _ = ε₁ + ε₂ := add_comm _ _

end CatCrypt.Crypto.SecureCompilation.ApproxPass
