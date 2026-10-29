/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# Spill insertion after the scalar-arith lowering `lowerSeq` is constant-time

The scalar-arith lowering `lowerSeq` always produces an `allDirect` block
(`lowerSeq_allDirect`; the fragment is memory-free). Composed with
`RegAllocSpillCT.spillRewrite_allDirect`, lowering followed by the rename+spill rewrite
produces a `CompilableCT` block. This is the spill-path CT-preservation that
`SecureCompileChain.LoweringCTPreserving` assumes: a (no-secret-control) source lowers,
through register allocation including spilling, to a `CompilableCT` machine block. The
connection to `secure_compile_constant_time` needs the `ImpExpr ↔ LowCT`/`ArithSrc`
source-IR bridge (the lowering there is typed `ImpExpr → Option (List (JInstr 64))`),
which is not part of this module.

The theorems are declared in the namespace
`CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT`.

## Main results

* `ourLowering_spill_CompilableCT` — `spillRewrite ρ frameBase slots (lowerSeq ρmap ps)`
  is `CompilableCT`.
* `ourLowering_spill_constant_time` — the same block has a state-independent machine
  leakage trace.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-- **Our lowering + spill is `CompilableCT`.** For any register map `ρmap`, any
    resident-half renaming `ρ`, any frame base and slot map, the rename+spill
    rewrite of the lowered scalar-arith block `lowerSeq ρmap ps` is in the
    machine constant-time subset. Composes `lowerSeq_allDirect` (lowering is
    direct) with `spillRewrite_allDirect` (spill insertion preserves direct). -/
theorem ourLowering_spill_CompilableCT (ρmap : RegMap) (ρ : String → String)
    (frameBase : String) (slots : String → Option Int) (ps : List ArithSrc) :
    CompilableCT (spillRewrite ρ frameBase slots (lowerSeq ρmap ps)) :=
  spillRewrite_CompilableCT ρ frameBase slots (lowerSeq ρmap ps) (lowerSeq_allDirect ρmap ps)

/-- **Our lowering + spill is constant-time.** The end-to-end CT statement for
    the spill-extended lowering: lower a scalar-arith source block, run the
    rename+spill register allocation rewrite, and the resulting machine block has
    a state-independent leakage trace. The lowering + resident-rename + spill
    chain preserves constant-time. -/
theorem ourLowering_spill_constant_time (ρmap : RegMap) (ρ : String → String)
    (frameBase : String) (slots : String → Option Int) (ps : List ArithSrc)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (spillRewrite ρ frameBase slots (lowerSeq ρmap ps))
      = blockLeak s₂ (spillRewrite ρ frameBase slots (lowerSeq ρmap ps)) :=
  CompilableCT.constant_time (ourLowering_spill_CompilableCT ρmap ρ frameBase slots ps) s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT
