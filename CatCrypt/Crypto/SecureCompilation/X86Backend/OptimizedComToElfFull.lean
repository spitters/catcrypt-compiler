/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf

/-!
# `optimizedCompileComToElf` — the optimized full-ELF emit for GoldenPath kernels

This is the optimized analogue of
`CompileComToElfJInstrFull6.compileComToElfJInstrFull6`. Both lower a `Com` to its
physical-ABI body, gather it into a `JInstr` block with the immediate-form-correct
`GatherImmForms.gatherJBlock6`, and frame + stitch the result through the same
`wrapFundefBytes` + `ElfObject.buildElfObjectMulti` + `bytesToByteArray` path. The
only difference is one step: between gather and encode, this entry runs the block
through the validated optimization pipeline `X86OptPipelineComposed.composeValidated
OptimizedComToElf.optPipeline`.

## The byte path

```
Com  →  physBodyOf              (Com.toLprogPhysAbi, the single function's body)
     →  gatherJBlock6           (imm-form-correct JInstr gather, `some` on covered bodies)
     →  composeValidated optPipeline   (validated store-to-load forwarding + no-op passes)
     →  encodeJBlock6 physAlloc  (the imm-form-correct encoder)
     →  wrapFundefBytes          (the leaf-ABI framing)
     →  buildElfObjectMulti / bytesToByteArray   (the ELF stitch)
```

When the body is outside the `gatherJBlock6` fragment the entry falls back to the
reference `CompileComToElf.compileComToElf`, so a pointed kernel never emits
truncated bytes.

## Correctness anchoring

The optimization step is the only place these bytes can differ from
`compileComToElfJInstrFull6`'s. Its semantic effect is pinned by
`optimizedCompileComToElf_sound`: the optimized block is `runBlock`-equal, on every
machine state, to the unoptimized gathered block. This is an instance of the
unconditional `X86OptPipelineComposed.composeValidated_sound` (the same soundness
`OptimizedComToElf.optimizedJBlock_sound` packages for the `lowerLinstrExtL` gather).
`optimizedCompileComToElf_allDirect` carries the direct-addressing constant-time
class through the same pipeline.

A kernel pointed to this entry is therefore anchored on `runBlock`-equivalence
plus an executed spec-KAT against authoritative vectors, rather than on byte
identity with the reference encoder.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JState runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6 encodeJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (physAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
  (composeValidated composeValidated_sound composeValidated_allDirect composeValidated_sound_fp
    composedDead agreeExcept)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf (optPipeline)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf (bytesToByteArray)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
  (wrapFundefBytes physBodyOf)

/-! ## 1. The optimized full-ELF entry -/

/-- The optimized full-body JInstr bytes of a physical body: gather with the
    immediate-form-correct `gatherJBlock6`, run the validated optimization pipeline
    (`composeValidated optPipeline`), then encode under `physAlloc` via
    `encodeJBlock6`. The `getD []` guard is total; on a `gatherJBlock6`-coverable
    body it is `some`. -/
def optJBodyBytes6 (body : List Linstr) : List (BitVec 8) :=
  ((gatherJBlock6 body).map
    (fun g => encodeJBlock6 physAlloc (composeValidated optPipeline g))).getD []

/-- The optimized full-body ELF entry over a physical body: the same framing wrap
    (`wrapFundefBytes`) and ELF stitch (`buildElfObjectMulti` + `bytesToByteArray`)
    as `CompileComToElfJInstrFull6.jElf6`, with `optJBodyBytes6` in the body slot. -/
def optJElf6 (body : List Linstr) (fname : String) : ByteArray :=
  bytesToByteArray
    (ElfObject.buildElfObjectMulti
      [{ name := fname, text := wrapFundefBytes body (optJBodyBytes6 body) }])

/-- **The optimized `Com → ELF` owned-emit entry.** Lower the `Com` to its
    physical-ABI body the same way `compileComToElfJInstrFull6` does, gather with
    `gatherJBlock6`, run the validated optimization pipeline, encode, and frame.
    Falls back to the reference `CompileComToElf.compileComToElf` when the body is
    outside the `gatherJBlock6` fragment, so a pointed kernel never emits
    truncated bytes. -/
def optimizedCompileComToElf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : ByteArray :=
  let body := physBodyOf com fname
  if (gatherJBlock6 body).isSome then optJElf6 body fname
  else CompileComToElf.compileComToElf com fname

/-! ## 2. Soundness: the optimization preserves the gathered block's semantics

The gather + framing + ELF stitch are shared with `compileComToElfJInstrFull6`; the
only step that can move the bytes is `composeValidated optPipeline`. Its `runBlock`
effect is nil: on every block and every state the optimized block lands in the same
final state as its input. This is the `gatherJBlock6` analogue of
`OptimizedComToElf.optimizedJBlock_sound`, both instances of the unconditional
`composeValidated_sound`. -/

/-- **Soundness.** The optimized block `composeValidated optPipeline g` — the block
    whose bytes `optimizedCompileComToElf` emits when the physical body gathers to
    `g` (`gatherJBlock6 body = some g`) — is `runBlock`-equal to the unoptimized
    gathered block `g`, on every machine state. An instance of
    `composeValidated_sound`. -/
theorem optimizedCompileComToElf_sound (g : List (JInstr 64)) :
    ∀ s : JState 64, runBlock s (composeValidated optPipeline g) = runBlock s g :=
  fun s => composeValidated_sound optPipeline g rfl s

/-- **Footprint-relative soundness.** The general form of
    `optimizedCompileComToElf_sound`: the optimized block agrees with the gathered
    block `g` modulo the pipeline's accumulated dead set `composedDead optPipeline g`
    on every state. For this pipeline that dead set is `[]`, so this specializes to
    the full-state `optimizedCompileComToElf_sound`. An instance of
    `composeValidated_sound_fp`. -/
theorem optimizedCompileComToElf_sound_fp (g : List (JInstr 64)) :
    ∀ s : JState 64,
      agreeExcept (composedDead optPipeline g) (runBlock s (composeValidated optPipeline g))
        (runBlock s g) :=
  fun s => composeValidated_sound_fp optPipeline g s

/-- **Constant-time preservation.** When the gathered block is in the
    direct-addressing constant-time class (`allDirect g = true`), the optimized block
    is too. An instance of `composeValidated_allDirect`. -/
theorem optimizedCompileComToElf_allDirect (g : List (JInstr 64))
    (hd : allDirect g = true) : allDirect (composeValidated optPipeline g) = true :=
  composeValidated_allDirect optPipeline g hd

end CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull
