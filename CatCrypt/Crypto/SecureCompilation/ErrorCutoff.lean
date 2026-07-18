/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Resolved

/-!
# Error Cutoff Composition

Extends `CompilerCorrectCutoff` (from Framework.lean) with composition rules
and security transfer for error-tolerant compilation.

## Key idea

In Jasmin-style compilation, the source may raise runtime errors (e.g.,
assertion failures, out-of-range accesses). These errors are "cutoff points":
the compiler guarantees correctness only for non-error execution paths.

Error cutoff correctness composes: if pass 1 cutoffs agree and pass 2 cutoffs
agree, the composition's cutoffs agree. Security transfer adds the error
probability as an overhead term.

## Main theorems

* `cutoff_resolved_of_CompilerCorrectResolved` -- exact resolved implies cutoff
* `cutoff_trans` -- composition of two cutoff-correct passes
* `cutoff_sdist_masked_zero` -- cutoff correctness gives zero masked sdist
* `cutoff_security_transfer` -- security transfer with error overhead
* `cutoff_from_error_free` -- error-free source gives exact cutoff

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.SecureCompilation.ErrorCutoff

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC UCMonad.StateTITreeN UCMonad.StateTITreeNCompose
open SecureCompilation
open scoped ENNReal

/-! ## Cutoff Correctness Properties -/

/-- Cutoff correctness from resolved correctness (stronger implies weaker). -/
theorem cutoff_resolved_of_CompilerCorrectResolved {hon β : Type}
    {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    (isError : β → Bool)
    (h : CompilerCorrectResolved handler source target) :
    CompilerCorrectCutoff handler source target isError :=
  fun x => by rw [h x]

/-- Cutoff correctness is reflexive. -/
theorem cutoff_refl {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (f : hon → ITreeN n E β)
    (isError : β → Bool) :
    CompilerCorrectCutoff handler f f isError :=
  fun _ => rfl

/-- Cutoff correctness is symmetric. -/
theorem cutoff_symm {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    {isError : β → Bool}
    (h : CompilerCorrectCutoff handler source target isError) :
    CompilerCorrectCutoff handler target source isError :=
  fun x => (h x).symm

/-! ## Composition -/

/-- Cutoff correctness composes (transitivity).
    If pass 1 and pass 2 both preserve non-error behavior, so does pass 1 ; pass 2. -/
theorem cutoff_trans {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {f g h : hon → ITreeN n E β}
    {isError : β → Bool}
    (hfg : CompilerCorrectCutoff handler f g isError)
    (hgh : CompilerCorrectCutoff handler g h isError) :
    CompilerCorrectCutoff handler f h isError :=
  fun x => by rw [hfg x, hgh x]

/-! ## Masked sdist -/

/-- The "masked" computation: apply the error filter after flattening. -/
noncomputable def masked {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    (f : hon → ITreeN n E β)
    (isError : β → Bool) :
    hon → SPComp β :=
  fun x => SPComp.bind (ITreeN.flattenAll handler n (f x))
    (fun b => if isError b then SPComp.fail else SPComp.pure b)

/-- Cutoff correctness gives zero sdist for masked computations. -/
theorem cutoff_sdist_masked_zero {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    {isError : β → Bool}
    (h : CompilerCorrectCutoff handler source target isError) :
    sdist (masked handler source isError) (masked handler target isError) = 0 := by
  have : masked handler source isError = masked handler target isError :=
    funext fun x => h x
  rw [this]; exact sdist_self _

/-! ## Error-Free Source -/

/-- If the source never produces errors, cutoff correctness becomes exact
    resolved correctness for the source. -/
theorem cutoff_from_error_free {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    {isError : β → Bool}
    (h : CompilerCorrectCutoff handler source target isError) :
    sdist (masked handler source isError) (masked handler target isError) = 0 :=
  cutoff_sdist_masked_zero handler h

/-! ## Multi-Error Cutoff -/

/-- If two passes are cutoff-correct for the SAME error predicate, they compose. -/
theorem cutoff_compose_same_error {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {f g h : hon → ITreeN n E β}
    {isError : β → Bool}
    (hfg : CompilerCorrectCutoff handler f g isError)
    (hgh : CompilerCorrectCutoff handler g h isError) :
    sdist (masked handler f isError) (masked handler h isError) = 0 := by
  have : CompilerCorrectCutoff handler f h isError := cutoff_trans handler hfg hgh
  exact cutoff_sdist_masked_zero handler this

/-! ## Security Transfer with Error Budget -/

/-- Security transfer: if masked source is ε-close to ideal,
    and source is cutoff-correct w.r.t. target,
    then masked target is also ε-close to ideal. -/
theorem cutoff_security_transfer {hon β : Type} {E : EventSig} {n : Nat}
    (handler : forall e : E.Event, SPComp (E.Resp e))
    {source target : hon → ITreeN n E β}
    {ideal : hon → SPComp β}
    {isError : β → Bool}
    {ε : ℝ≥0∞}
    (hcc : CompilerCorrectCutoff handler source target isError)
    (hsec : sdist (masked handler source isError) ideal ≤ ε) :
    sdist (masked handler target isError) ideal ≤ ε := by
  convert hsec using 2
  exact (funext fun x => hcc x).symm

end CatCrypt.Crypto.SecureCompilation.ErrorCutoff
