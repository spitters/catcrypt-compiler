/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.FeSubSourceTower
public import HaxLean.Pipeline
public import HaxLean.PipelineCF

/-!
# Welding hax-lean's `pipeline_correct` on top of the `feSub` source tower

`FeSubSourceTower.feSub_source_to_bytes_tower` carries the `feSub` source kernel
`r0 := a0 - b0` — as a `RustSubset` straight-line program — all the way down to
the emitted jasmin program `feJcom`'s bytes and their clean `ZMod 2^64`
subtraction spec, with no free `Corres`/`RustExec` hypothesis.  That tower starts
from the *already-lowered* source word `feSubSourceWord`.

One level *up* sits hax-lean's own imperative front: the RAW, pre-optimization
extracted `ImpExpr e` produced by `cargo hax into lean`, before any of the
functionalizing phases run.  hax-lean's `pipeline` (`../hax-lean`,
`HaxLean/Pipeline.lean`) is the 4-phase lowering
(`dropReferences → localMutation → functionalizeLoops → cfIntoMonads`), and
`pipeline_correct` proves it *denote-preserving*: `denote bi fuel (pipeline e) =
denote bi fuel e` for every `ImpExpr` whose post-phase-1-2 form is loop-free and
early-exit-free — which the control-flow-free `feSub` kernel is.  Its
control-flow-aware strengthening `pipeline_correct'` (`HaxLean/PipelineCF.lean`)
drops the loop-freeness side condition in favour of the builtin-table contract
`Builtins.DeepNoControlFlow bi`, discharged for the standard table by
`Builtins.defaultBuiltins_deepNoControlFlow`.

## What this module welds

This module chains
`pipeline_correct` (raw `e` ≈ `pipeline e`) → the source→bytes tower, so that the
RAW pre-optimization `ImpExpr` reaches the emitted bytes as a single statement.

The join between the two frameworks is a word identification: hax-lean's
reference semantics returns an `Outcome` (a `Value`), whereas the source tower
consumes a `BitVec 64`.  `haxOutcomeWord` reads a 64-bit word out of a hax
`Outcome`, and the identification "the raw `e`'s evaluated output word *is*
`feSubSourceWord`" is taken here as one explicit, named interface hypothesis
`hBridge`.  Everything else — the denote-preservation of the whole optimization
pipeline, and the source-word→bytes tower — is discharged with no free
hypothesis.  So the remaining interface is precisely `hBridge`, the concrete
`ImpExpr`↔`RustSubset` value coincidence for the feSub kernel.

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (sgraf812/ascent).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (Ctx)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## Reading a 64-bit word out of a hax reference-semantics outcome -/

/-- Extract a 64-bit word from a hax reference-semantics `Outcome`: a normally
    terminating unsigned-integer value carries its natural number, reinterpreted
    as a `BitVec 64`.  Any other outcome (early return, break, continue, error,
    or a non-integer value) yields no word. -/
def haxOutcomeWord : Hax.Outcome → Option (BitVec 64)
  | .val (.uint _ n) => some (BitVec.ofNat 64 n)
  | _ => none

/-- `haxOutcomeWord` is invariant under the phase-3 control-flow encoding
    `encodeCF3`: the only outcome it reads a word from is a `val`, which
    `encodeCF3` leaves untouched.  Lets the `pipeline_correct'` route reuse the
    same word identification `hBridge`. -/
theorem haxOutcomeWord_encodeCF3 (o : Hax.Outcome) (w : BitVec 64)
    (h : haxOutcomeWord o = some w) :
    haxOutcomeWord (Hax.Outcome.encodeCF3 o) = some w := by
  cases o with
  | val v => exact h
  | earlyRet v => simp [haxOutcomeWord] at h
  | broke v => simp [haxOutcomeWord] at h
  | continued => simp [haxOutcomeWord] at h
  | err msg => simp [haxOutcomeWord] at h

/-- Extract a 64-bit word from a hax outcome under the pipeline's control-flow
    encoding: a normally terminating unsigned-integer value, or an unsigned-integer
    value wrapped in a `controlFlow` tag (the phase-3/4 encoding of a `break` or an
    early `return` carrying that word).  Any other outcome yields no word. -/
def haxOutcomeWordCF : Hax.Outcome → Option (BitVec 64)
  | .val (.uint _ n) => some (BitVec.ofNat 64 n)
  | .val (.controlFlow _ (.uint _ n)) => some (BitVec.ofNat 64 n)
  | _ => none

/-- `haxOutcomeWordCF` extends `haxOutcomeWord`: every word the untagged reader
    finds, the tagged reader finds. -/
theorem haxOutcomeWordCF_of_haxOutcomeWord (o : Hax.Outcome) (w : BitVec 64)
    (h : haxOutcomeWord o = some w) : haxOutcomeWordCF o = some w := by
  cases o with
  | val v => cases v <;> first | exact h | simp [haxOutcomeWord] at h
  | _ => simp [haxOutcomeWord] at h

/-- `haxOutcomeWordCF` is invariant under the phase-3 encoding `encodeCF3`: the
    only outcomes it reads are `val`s, which `encodeCF3` leaves untouched. -/
theorem haxOutcomeWordCF_encodeCF3 (o : Hax.Outcome) (w : BitVec 64)
    (h : haxOutcomeWordCF o = some w) :
    haxOutcomeWordCF (Hax.Outcome.encodeCF3 o) = some w := by
  cases o with
  | val v => exact h
  | _ => simp [haxOutcomeWordCF] at h

/-- `haxOutcomeWordCF` is invariant under the phase-4 encoding `encodeCF4`. -/
theorem haxOutcomeWordCF_encodeCF4 (o : Hax.Outcome) (w : BitVec 64)
    (h : haxOutcomeWordCF o = some w) :
    haxOutcomeWordCF (Hax.Outcome.encodeCF4 o) = some w := by
  cases o with
  | val v => exact h
  | _ => simp [haxOutcomeWordCF] at h

/-- `haxOutcomeWordCF` is invariant under the combined encoding `encodeCF`. -/
theorem haxOutcomeWordCF_encodeCF (o : Hax.Outcome) (w : BitVec 64)
    (h : haxOutcomeWordCF o = some w) :
    haxOutcomeWordCF (Hax.Outcome.encodeCF o) = some w := by
  rw [← Hax.Outcome.encodeCF4_encodeCF3]
  exact haxOutcomeWordCF_encodeCF4 _ _ (haxOutcomeWordCF_encodeCF3 _ _ h)

/-- The word of an early return survives the phase-4 encoding: the tagged reader on
    `encodeCF4 (earlyRet v)` is the untagged reader on `val v`. -/
theorem haxOutcomeWordCF_encodeCF4_earlyRet (v : Hax.Value) :
    haxOutcomeWordCF (Hax.Outcome.encodeCF4 (.earlyRet v)) = haxOutcomeWord (.val v) := by
  cases v <;> rfl

/-- The word of an early return survives the combined encoding `encodeCF`. -/
theorem haxOutcomeWordCF_encodeCF_earlyRet (v : Hax.Value) :
    haxOutcomeWordCF (Hax.Outcome.encodeCF (.earlyRet v)) = haxOutcomeWord (.val v) := by
  cases v <;> rfl

/-! ## The raw-source-to-bytes weld -/

/-- **`feSub_raw_source_to_bytes`.**  The RAW, pre-optimization hax `ImpExpr e`
    reaches the emitted bytes.

    Given a raw `ImpExpr e` whose post-phase-1-2 form is loop-free (`hNoLoops`)
    and early-exit-free (`hNoEE`) — both true of the control-flow-free `feSub`
    kernel — and the source-word identification `hBridge` saying the raw `e`'s
    evaluated output word is `feSubSourceWord`, we conclude, as one statement:

    * the *optimized* program `pipeline e` evaluates to the same output word
      `feSubSourceWord` (hax-lean's `pipeline_correct`, the denote-preservation
      of the whole 4-phase optimization, chained through `hBridge`); and
    * that word reaches the emitted jasmin program `feJcom`'s bytes
      (`feJcom.denote … = ctTransTy feSubSourceWord`), whose clean `ZMod 2^64`
      spec is exactly `(av : ZMod 2^64) - (bv : ZMod 2^64)`
      (the source→bytes tower `feSub_source_to_bytes_tower`).

    The only free interface is `hBridge` — the concrete `ImpExpr`↔`RustSubset`
    value coincidence for the feSub kernel.  `pipeline_correct` (denote
    preservation) and the source-word→bytes tower carry no free hypothesis. -/
theorem feSub_raw_source_to_bytes
    (N : Nat) (leafSpec : LeafSpec)
    (bi : Hax.Builtins) (fuel : Nat) (env : Hax.Env) (e : Hax.ImpExpr)
    (hNoLoops : Hax.NoLoops
      (Hax.localMutation (Hax.mutatedVars e) (Hax.dropReferences e)))
    (hNoEE : Hax.NoEarlyExit
      (Hax.localMutation (Hax.mutatedVars e) (Hax.dropReferences e)))
    (hBridge : haxOutcomeWord (Hax.denote bi fuel e env).1 = some feSubSourceWord) :
    haxOutcomeWord (Hax.denote bi fuel (Hax.pipeline e) env).1 = some feSubSourceWord
      ∧ feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
          = ctTransTy feSubSourceWord
      ∧ wEnc feSubSourceWord
          = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) := by
  refine ⟨?_, (feSub_source_to_bytes_tower N leafSpec).1,
    (feSub_source_to_bytes_tower N leafSpec).2⟩
  rw [congrFun (Hax.pipeline_correct bi fuel e hNoLoops hNoEE) env]
  exact hBridge

/-- **`feSub_raw_source_to_bytes'`.**  The `pipeline_correct'` route, at the
    standard builtin table.

    Same weld as `feSub_raw_source_to_bytes`, but reading the optimized program
    with the control-flow-aware evaluator `denote'` via `pipeline_correct'`.  The
    loop-freeness side condition `hNoLoops` is replaced by the builtin-table
    contract `Builtins.DeepNoControlFlow`, discharged here for the concrete
    `defaultBuiltins` by `Builtins.defaultBuiltins_deepNoControlFlow` — the
    honest form of "feSub is control-flow-free".  The residual side conditions
    are `NoCFConstructors e`, `NoEarlyExit`, and `Env.NoControlFlow env` (all
    true of a real feSub extraction), plus the same word bridge `hBridge`. -/
theorem feSub_raw_source_to_bytes'
    (N : Nat) (leafSpec : LeafSpec)
    (fuel : Nat) (env : Hax.Env) (e : Hax.ImpExpr)
    (hncf : Hax.NoCFConstructors e)
    (hNoEE : Hax.NoEarlyExit
      (Hax.localMutation (Hax.mutatedVars e) (Hax.dropReferences e)))
    (henv : Hax.Env.NoControlFlow env)
    (hBridge : haxOutcomeWord (Hax.denote Hax.defaultBuiltins fuel e env).1
      = some feSubSourceWord) :
    haxOutcomeWord (Hax.denote' Hax.defaultBuiltins fuel (Hax.pipeline e) env).1
        = some feSubSourceWord
      ∧ feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
          = ctTransTy feSubSourceWord
      ∧ wEnc feSubSourceWord
          = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) := by
  refine ⟨?_, (feSub_source_to_bytes_tower N leafSpec).1,
    (feSub_source_to_bytes_tower N leafSpec).2⟩
  rw [Hax.pipeline_correct' Hax.defaultBuiltins
    Hax.Builtins.defaultBuiltins_deepNoControlFlow e hncf hNoEE fuel env henv]
  exact haxOutcomeWord_encodeCF3 _ _ hBridge

end CatCrypt.Crypto.SecureCompilation.Ascent
