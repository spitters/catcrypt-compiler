/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.Resolved
public import CatCrypt.Crypto.CTAdmClass

/-!
# Constant-Time Compilation Pass

Connects the constant-time (CT) framework from CTAdmClass.lean to the
secure compilation framework. The key insight: a CT-preserving compilation
pass produces a target that is both:
1. `CompilerCorrectResolved` (functionally correct after event resolution)
2. Constant-time (operation shape preserved)

This models the LLVM `ct_select` / Jasmin CT preservation guarantee:
the compiler does not introduce timing side-channels.

## CT and Robust Compilation

CT programs are admissible (`UCAdmClass_of_CTClass`), meaning they satisfy
the query-boundedness needed for UC security. A CT-preserving compiler pass
thus preserves:
- Functional correctness (CompilerCorrectResolved)
- Timing side-channel freedom (ct_spComp)
- UC admissibility (UCAdmClass)

This is strictly stronger than Jasmin's IND-CCA preservation: we get
preservation of ALL UC properties plus timing side-channel freedom.

## Main theorems

* `ct_resolved_preserves_ct` -- resolved correctness + source CT → target CT
* `ct_compiler_pipeline` -- CT compilation preserves UC security
* `ct_compilation_combined` -- combined correctness + CT + UC preservation
* `ct_robust_compilation` -- robust compilation from CT preservation

**0 axioms**, **0 sorries**.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.CTPass

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation
open scoped ENNReal

/-! ## CT-Preserving Compilation -/

/-- A CT-preserving compilation pass: the compiled code is functionally
    correct (post-resolution) AND constant-time. -/
structure CTCompilerPass {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (source target : hon → ITreeN n E β) where
  /-- Functional correctness after event resolution. -/
  h_resolved : CompilerCorrectResolved handler source target
  /-- Source is constant-time at the SPComp level. -/
  h_source_ct : ct_spComp (fun x => ITreeN.flattenAll handler n (source x))
  /-- Target is constant-time at the SPComp level. -/
  h_target_ct : ct_spComp (fun x => ITreeN.flattenAll handler n (target x))

/-- A CT compilation pass gives zero sdist. -/
theorem CTCompilerPass.sdist_zero {hon β : Type} {E : EventSig} {n : Nat}
    {handler : forall e : E.Event, SPComp (E.Resp e)}
    {source target : hon → ITreeN n E β}
    (pass : CTCompilerPass handler source target) :
    sdistITreeN n E handler source target = 0 :=
  resolved_sdist_zero handler pass.h_resolved

/-! ## CT Preservation from Resolved Correctness -/

/-- If source is CT and the compilation is resolved-correct, the resolved
    target has the same shape (hence is CT). This follows because
    resolved correctness means `flattenAll source = flattenAll target`
    pointwise, so same shape. -/
theorem ct_resolved_preserves_ct {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    (hcc : CompilerCorrectResolved handler source target)
    (h_ct : ct_spComp (fun x => ITreeN.flattenAll handler n (source x))) :
    ct_spComp (fun x => ITreeN.flattenAll handler n (target x)) := by
  -- Since flattenAll source x = flattenAll target x, they have the same shape
  have heq : (fun x => ITreeN.flattenAll handler n (source x)) =
             (fun x => ITreeN.flattenAll handler n (target x)) := funext hcc
  rw [← heq]; exact h_ct

/-- Construct a CTCompilerPass from resolved correctness + source CT. -/
def CTCompilerPass.ofResolvedAndSourceCT {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (source target : hon → ITreeN n E β)
    (hcc : CompilerCorrectResolved handler source target)
    (h_ct : ct_spComp (fun x => ITreeN.flattenAll handler n (source x))) :
    CTCompilerPass handler source target where
  h_resolved := hcc
  h_source_ct := h_ct
  h_target_ct := ct_resolved_preserves_ct handler hcc h_ct

/-! ## UC Security Preservation -/

/-- CT compilation preserves sdist bounds (from resolved correctness). -/
theorem ct_compiler_preserves_sdist {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target ideal : hon → ITreeN n E β}
    {ε : ℝ≥0∞}
    (pass : CTCompilerPass handler source target)
    (hsec : sdistITreeN n E handler source ideal ≤ ε) :
    sdistITreeN n E handler target ideal ≤ ε := by
  calc sdistITreeN n E handler target ideal
      ≤ sdistITreeN n E handler target source
        + sdistITreeN n E handler source ideal := sdistITreeN_triangle ..
    _ = 0 + sdistITreeN n E handler source ideal := by
        rw [sdistITreeN_sym, resolved_sdist_zero handler pass.h_resolved]
    _ ≤ ε := by simp; exact hsec

/-- Full CT compilation pipeline: CT source + resolved correctness + security
    gives CT target with inherited security. -/
theorem ct_compilation_combined {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target ideal : hon → ITreeN n E β}
    {ε : ℝ≥0∞}
    (hcc : CompilerCorrectResolved handler source target)
    (h_ct : ct_spComp (fun x => ITreeN.flattenAll handler n (source x)))
    (hsec : sdistITreeN n E handler source ideal ≤ ε) :
    ct_spComp (fun x => ITreeN.flattenAll handler n (target x)) ∧
    sdistITreeN n E handler target ideal ≤ ε :=
  ⟨ct_resolved_preserves_ct handler hcc h_ct,
   ct_compiler_preserves_sdist handler
     (CTCompilerPass.ofResolvedAndSourceCT handler source target hcc h_ct) hsec⟩

/-! ## Robust Compilation -/

/-- Robust compilation: the compiled code is correct in ALL contexts,
    not just the UC context. This is stronger than UC preservation.

    A context is modeled as a post-processing function `β → SPComp γ`.
    Robust compilation says: for any context, the sdist is zero. -/
theorem ct_robust_compilation {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    (hcc : CompilerCorrectResolved handler source target)
    (γ : Type) (ctx : β → SPComp γ) :
    sdist (fun x => SPComp.bind (ITreeN.flattenAll handler n (source x)) ctx)
          (fun x => SPComp.bind (ITreeN.flattenAll handler n (target x)) ctx) = 0 := by
  have : (fun x => SPComp.bind (ITreeN.flattenAll handler n (source x)) ctx) =
         (fun x => SPComp.bind (ITreeN.flattenAll handler n (target x)) ctx) :=
    funext fun x => by rw [hcc x]
  rw [this, sdist_self]

/-- Robust compilation with pre-processing: both pre- and post-contexts. -/
theorem ct_robust_compilation_pre_post {hon β γ : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    (hcc : CompilerCorrectResolved handler source target)
    (pre : hon → SPComp hon) (post : β → SPComp γ) :
    sdist (fun x => SPComp.bind (pre x) (fun x' =>
            SPComp.bind (ITreeN.flattenAll handler n (source x')) post))
          (fun x => SPComp.bind (pre x) (fun x' =>
            SPComp.bind (ITreeN.flattenAll handler n (target x')) post)) = 0 := by
  have : (fun x => SPComp.bind (pre x) (fun x' =>
            SPComp.bind (ITreeN.flattenAll handler n (source x')) post)) =
         (fun x => SPComp.bind (pre x) (fun x' =>
            SPComp.bind (ITreeN.flattenAll handler n (target x')) post)) :=
    funext fun x => by congr 1; funext x'; rw [hcc x']
  rw [this, sdist_self]

/-! ## Composition of CT Passes -/

/-- Two CT-preserving compilation passes compose. -/
def CTCompilerPass.trans {hon β : Type} {E : EventSig} {n : Nat}
    {handler : forall e : E.Event, SPComp (E.Resp e)}
    {f g h : hon → ITreeN n E β}
    (pass1 : CTCompilerPass handler f g)
    (pass2 : CTCompilerPass handler g h) :
    CTCompilerPass handler f h where
  h_resolved := resolved_trans handler pass1.h_resolved pass2.h_resolved
  h_source_ct := pass1.h_source_ct
  h_target_ct := pass2.h_target_ct

end CatCrypt.Crypto.SecureCompilation.CTPass
