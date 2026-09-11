/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Resolved

/-!
# Stateful Compiler Passes

Extends the secure compilation framework to stateful protocols (like the KEM
example in KEMDemo.lean). The key insight: a stateful protocol
`hon → S → ITreeN n E (β × S)` can be treated as a non-stateful protocol
`(hon × S) → ITreeN n E (β × S)` via uncurrying, reusing all existing
infrastructure.

## Main theorems

* `StatefulResolved` -- post-resolution equality for stateful protocols
* `stateful_resolved_sdist_zero` -- sdist = 0 from stateful resolved correctness
* `stateful_resolved_preserves_uc` -- UC security transfer for stateful protocols
* `stateful_resolved_of_pointwise` -- construct from pointwise equality
* `stateful_approx_security_transfer` -- ε-approximate stateful compilation pipeline

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.StatefulPass

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation
open scoped ENNReal

/-! ## Stateful Compiler Correctness (Post-Resolution) -/

/-- Stateful post-resolution compiler correctness: after resolving events,
    source and target produce the same SPComp for every input and state. -/
def StatefulResolved {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (source target : hon → S → ITreeN n E β) : Prop :=
  ∀ x s, ITreeN.flattenAll handler n (source x s) =
         ITreeN.flattenAll handler n (target x s)

/-- StatefulResolved is a special case of CompilerCorrectResolved via uncurrying. -/
theorem statefulResolved_iff_resolved {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (source target : hon → S → ITreeN n E β) :
    StatefulResolved handler source target ↔
    CompilerCorrectResolved handler
      (fun (p : hon × S) => source p.1 p.2)
      (fun (p : hon × S) => target p.1 p.2) :=
  ⟨fun h ⟨x, s⟩ => h x s, fun h x s => h ⟨x, s⟩⟩

/-! ## Zero sdist -/

/-- Stateful resolved correctness implies zero sdist. -/
theorem stateful_resolved_sdist_zero {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → S → ITreeN n E β}
    (h : StatefulResolved handler source target) :
    sdistITreeN n E handler
      (fun (p : hon × S) => source p.1 p.2)
      (fun (p : hon × S) => target p.1 p.2) = 0 :=
  resolved_sdist_zero handler ((statefulResolved_iff_resolved handler source target).mp h)

/-! ## Construction -/

/-- Construct stateful resolved correctness from pointwise flattenAll equality. -/
theorem stateful_resolved_of_pointwise {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (source target : hon → S → ITreeN n E β)
    (h : ∀ x s, ITreeN.flattenAll handler n (source x s) =
                 ITreeN.flattenAll handler n (target x s)) :
    StatefulResolved handler source target :=
  h

/-- Construct from CompilerCorrectStateful (pre-resolution). -/
theorem stateful_resolved_of_exact {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → S → ITreeN n E β}
    (h : ∀ x s, source x s = target x s) :
    StatefulResolved handler source target :=
  fun x s => by rw [h]

/-! ## Composition -/

/-- Transitivity of stateful resolved correctness. -/
theorem stateful_resolved_trans {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {f g h : hon → S → ITreeN n E β}
    (hfg : StatefulResolved handler f g)
    (hgh : StatefulResolved handler g h) :
    StatefulResolved handler f h :=
  fun x s => by rw [hfg x s, hgh x s]

/-- Symmetry. -/
theorem stateful_resolved_symm {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {f g : hon → S → ITreeN n E β}
    (h : StatefulResolved handler f g) :
    StatefulResolved handler g f :=
  fun x s => (h x s).symm

/-! ## Security Transfer -/

/-- Stateful resolved correctness preserves sdist bounds. -/
theorem stateful_resolved_preserves_sdist {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → S → ITreeN n E β}
    {ideal : hon → S → ITreeN n E β}
    {ε : ℝ≥0∞}
    (hcc : StatefulResolved handler source target)
    (hsec : sdistITreeN n E handler
      (fun (p : hon × S) => source p.1 p.2)
      (fun (p : hon × S) => ideal p.1 p.2) ≤ ε) :
    sdistITreeN n E handler
      (fun (p : hon × S) => target p.1 p.2)
      (fun (p : hon × S) => ideal p.1 p.2) ≤ ε := by
  calc sdistITreeN n E handler
        (fun (p : hon × S) => target p.1 p.2)
        (fun (p : hon × S) => ideal p.1 p.2)
      ≤ sdistITreeN n E handler
          (fun (p : hon × S) => target p.1 p.2)
          (fun (p : hon × S) => source p.1 p.2)
        + sdistITreeN n E handler
          (fun (p : hon × S) => source p.1 p.2)
          (fun (p : hon × S) => ideal p.1 p.2) := sdistITreeN_triangle ..
    _ = 0 + sdistITreeN n E handler
          (fun (p : hon × S) => source p.1 p.2)
          (fun (p : hon × S) => ideal p.1 p.2) := by
        rw [sdistITreeN_sym,
            stateful_resolved_sdist_zero handler hcc]
    _ ≤ ε := by simp; exact hsec

/-! ## Approximate Stateful Compilation -/

/-- Full pipeline for stateful compilation: exact pass + approximate pass. -/
theorem stateful_approx_security_transfer {hon S β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source intermediate target : hon → S → ITreeN n E β}
    {ideal : hon → S → ITreeN n E β}
    {ε₁ ε₂ : ℝ≥0∞}
    (h_exact : StatefulResolved handler source intermediate)
    (h_approx : sdistITreeN n E handler
      (fun (p : hon × S) => intermediate p.1 p.2)
      (fun (p : hon × S) => target p.1 p.2) ≤ ε₂)
    (h_sec : sdistITreeN n E handler
      (fun (p : hon × S) => source p.1 p.2)
      (fun (p : hon × S) => ideal p.1 p.2) ≤ ε₁) :
    sdistITreeN n E handler
      (fun (p : hon × S) => target p.1 p.2)
      (fun (p : hon × S) => ideal p.1 p.2) ≤ ε₁ + ε₂ := by
  have h1 : sdistITreeN n E handler
      (fun (p : hon × S) => target p.1 p.2)
      (fun (p : hon × S) => intermediate p.1 p.2) ≤ ε₂ := by
    rw [sdistITreeN_sym]; exact h_approx
  have h2 : sdistITreeN n E handler
      (fun (p : hon × S) => intermediate p.1 p.2)
      (fun (p : hon × S) => ideal p.1 p.2) ≤ ε₁ :=
    stateful_resolved_preserves_sdist handler h_exact h_sec
  calc sdistITreeN n E handler
        (fun (p : hon × S) => target p.1 p.2)
        (fun (p : hon × S) => ideal p.1 p.2)
      ≤ sdistITreeN n E handler
          (fun (p : hon × S) => target p.1 p.2)
          (fun (p : hon × S) => intermediate p.1 p.2)
        + sdistITreeN n E handler
          (fun (p : hon × S) => intermediate p.1 p.2)
          (fun (p : hon × S) => ideal p.1 p.2) := sdistITreeN_triangle ..
    _ ≤ ε₂ + ε₁ := add_le_add h1 h2
    _ = ε₁ + ε₂ := add_comm _ _

end CatCrypt.Crypto.SecureCompilation.StatefulPass
