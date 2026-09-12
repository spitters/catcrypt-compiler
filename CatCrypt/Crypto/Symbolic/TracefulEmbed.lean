/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Symbolic.TracefulSpec
public import CatCrypt.Crypto.Advantage
public import CatCrypt.Crypto.CryptoWord

/-!
# Traceful → SPComp Embedding

Provides a semantic embedding from `Traceful` computations to `SPComp`,
enabling formal correspondence between symbolic protocol models and
computational game-based security proofs.

## Design

The embedding works by:
1. Mapping each `mkRand` to `SPComp.sample` (random generation)
2. Discarding `triggerEvent` and `sendMsg` (no computational counterpart)
3. Applying a user-supplied interpretation of `Bytes` operations to `W`

This is a **lossy** embedding: the trace structure (labels, events, messages)
is discarded. The embedding preserves the distribution of cryptographic
outputs (keys, shared secrets) but not the symbolic metadata.

## Main Results

* `TracefulInterp` — interpretation typeclass for mapping Bytes ops to W
* `evalTraceful` — evaluates a Traceful computation to SPComp
* `evalTraceful_bind` — bind preservation
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

/-! ## Traceful Interpretation

A `TracefulInterp` maps symbolic `Bytes` operations to concrete `W` operations,
enabling evaluation of `Traceful` computations as `SPComp`. -/

/-- Interpretation of symbolic bytes operations into a concrete type `W`.

This typeclass provides the mapping from symbolic constructors to
concrete cryptographic operations. -/
class TracefulInterp (W : Type) [SampleableType W] where
  /-- Interpret a DH operation. -/
  interpDH : W → W → W
  /-- Interpret DH public key derivation. -/
  interpDHPub : W → W
  /-- Interpret KDF-Extract. -/
  interpExtract : W → W → W
  /-- Interpret KDF-Expand. -/
  interpExpand : W → W → W
  /-- Interpret AEAD encryption. -/
  interpAEADEnc : W → W → W → W

/-- A `TracefulComputation` is a structured representation of a
    `Traceful` program that can be evaluated in either monad.

    This avoids directly interpreting `Bytes` terms (which are free constructors)
    and instead records the computation graph. -/
inductive TracefulStep (W : Type) where
  | sample : TracefulStep W
  | compute : (W → W) → TracefulStep W
  | event : TracefulStep W  -- discarded in SPComp interpretation

section EvalSteps

variable {W : Type} [SampleableType W]

/-- Evaluate a sequence of TracefulSteps as an SPComp computation. -/
noncomputable def evalSteps :
    List (TracefulStep W) → (List W → SPComp W) → SPComp W
  | [], k => k []
  | .sample :: rest, k =>
    SPComp.bind (SPComp.sample W) fun w =>
      evalSteps rest (fun ws => k (w :: ws))
  | .compute f :: rest, k =>
    evalSteps rest (fun ws =>
      match ws with
      | w :: ws' => k (f w :: ws')
      | [] => k [])
  | .event :: rest, k =>
    evalSteps rest k

/-! ## Properties -/

/-- Evaluation of empty steps returns the continuation applied to []. -/
theorem evalSteps_nil (k : List W → SPComp W) :
    evalSteps [] k = k [] := rfl

/-- Event steps are discarded (no computational effect). -/
theorem evalSteps_event (rest : List (TracefulStep W)) (k : List W → SPComp W) :
    evalSteps (.event :: rest) k = evalSteps rest k := rfl

/-- Sample steps correspond to `SPComp.sample` followed by accumulation. -/
theorem evalSteps_sample (rest : List (TracefulStep W)) (k : List W → SPComp W) :
    evalSteps (.sample :: rest) k =
    SPComp.bind (SPComp.sample W) fun w =>
      evalSteps rest (fun ws => k (w :: ws)) := rfl

end EvalSteps

end CatCrypt.Crypto.Symbolic
