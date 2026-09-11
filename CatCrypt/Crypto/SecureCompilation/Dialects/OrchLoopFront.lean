/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront
public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchLoopsEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchLoopsEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ZkSumCheckWholeProverEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ZkSumCheckWholeProverEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ProveDriverEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ProveDriverEmit

/-!
# Loop-over-call orchestration front: validation against the deployed drivers

The loop-over-call combinator core (`OrchStep`/`stepToLinstr`/`bandLcmd`/
`OrchLoopSpec`/`buildOrchLoop`/`buildOrchCallSeq`, and the two whole-prover specs
`strideCallSpec`/`sumcheckSpec`) lives upstream in
`Dialects.OrchFront` — imported only from the owned backend
(`JasminLprogExport` + `LprogControlFlow`), so it sits above the whole-prover
emit modules with no cycle.

Those emit modules now set their DEPLOYED `Lfundef` `:= buildOrchLoop <spec>`
(resp. `buildOrchCallSeq …`), so the deployed kernel IS the front's output. This
module — which imports both `OrchFront` and the emit modules — records the
**validation** lemmas: each deployed driver equals `buildOrchLoop`/`buildOrchCallSeq`
of its spec. Because the deployed def is *definitionally* the front output, each
equality is `rfl` and the emitted bytes are byte-identical (no `.s` change).

The whole-prover modules whose driver IS one `loopLcmd`-`Lfundef` are so
re-sourced:

* `Plonky3OrchLoopsEmit.orchLoopFundef`  — single-leaf-call strided loop,
* `ZkSumCheckWholeProverEmit.sumcheckLoopFundef` — two-leaf-call round loop
  with callee-saved base reload,
* `Plonky3ProveDriverEmit.proveDriverFundef` — straight-line phase call
  sequence (the degenerate no-loop case, `buildOrchCallSeq`).

The FiatShamir word-move duplex is the residual: its loops are memref word
copies, not leaf calls, and its driver is a multi-loop function — out of the
loop-over-call band.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.OrchLoopFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront

/-! ## 1. Component band facts

Each driver's prologue band and per-iteration loop-body band render to the same
`Lcmd` the emit modules describe by hand (`orchLoopBody` / `sumcheckRoundBody` /
the counter-init `MOV`s). These are the ≤9-instruction `rfl`s the whole-`Lfundef`
equalities factor through. -/

/-- Component (module 1): the loop-body schedule renders to the hand-authored
    `orchLoopBody` — a bounded 4-instruction `rfl`. -/
theorem strideCall_body_eq (leaf : String) (so si : Nat) :
    bandLcmd 64 [OrchStep.call leaf, OrchStep.addImm "RDI" so,
        OrchStep.addImm "RSI" si, OrchStep.subImm "R8" 1]
      = Plonky3OrchLoopsEmit.orchLoopBody leaf so si := rfl

/-- Component (module 1): the prologue schedule renders to the counter-init `MOV`
    band — a 1-instruction `rfl`. -/
theorem strideCall_prologue_eq (n : Nat) :
    bandLcmd 64 [OrchStep.movImm "R8" n]
      = [(⟨0, .Lopn [.reg "R8"] "MOV:64" [.imm n]⟩ : Linstr)] := rfl

/-- **Validate (module 1).** The loop-over-call front reproduces the deployed
    `orchLoopFundef` exactly. Definitional: the deployed driver IS
    `buildOrchLoop (strideCallSpec …)`, so the emitted bytes are unchanged. -/
theorem buildOrchLoop_eq_orchLoopFundef (leaf : String) (n so si : Nat) :
    buildOrchLoop (strideCallSpec leaf n so si)
      = Plonky3OrchLoopsEmit.orchLoopFundef leaf n so si := rfl

/-- Component (module 2): the two-call round-body schedule renders to the
    hand-authored `sumcheckRoundBody` — a bounded 9-instruction `rfl`. -/
theorem sumcheck_body_eq (so si : Nat) :
    bandLcmd 64 [OrchStep.movRR "RDI" "R12", OrchStep.movRR "RSI" "R13",
        OrchStep.call "zk_sumcheck_round_step_rc",
        OrchStep.movRR "RDI" "R12", OrchStep.movRR "RSI" "R13",
        OrchStep.call "zk_poseidon2_squeeze_rc",
        OrchStep.addImm "R12" so, OrchStep.addImm "R13" si, OrchStep.subImm "R8" 1]
      = ZkSumCheckWholeProverEmit.sumcheckRoundBody so si := rfl

/-- Component (module 2): the base-seed + counter-init prologue schedule renders
    to the three seed `MOV`s — a bounded 3-instruction `rfl`. -/
theorem sumcheck_prologue_eq (n : Nat) :
    bandLcmd 64 [OrchStep.movRR "R12" "RDI", OrchStep.movRR "R13" "RSI",
        OrchStep.movImm "R8" n]
      = [(⟨0, .Lopn [.reg "R12"] "MOV:64" [.reg "RDI"]⟩ : Linstr),
         ⟨0, .Lopn [.reg "R13"] "MOV:64" [.reg "RSI"]⟩,
         ⟨0, .Lopn [.reg "R8"] "MOV:64" [.imm n]⟩] := rfl

/-- **Validate (module 2).** The loop-over-call front reproduces the deployed
    `sumcheckLoopFundef` exactly — a two-call round body with base reload is the
    same front, a longer body schedule. Definitional (the deployed driver IS
    `buildOrchLoop (sumcheckSpec …)`). -/
theorem buildOrchLoop_eq_sumcheckLoopFundef (n so si : Nat) :
    buildOrchLoop (sumcheckSpec n so si)
      = ZkSumCheckWholeProverEmit.sumcheckLoopFundef n so si := rfl

/-- **Validate (module 4, no-loop).** The straight-line phase-call sequence
    `proveDriverFundef` is the degenerate case: `buildOrchCallSeq` over the phase
    symbols reproduces it. It carries no `loopLcmd` (it is a call *sequence*, not
    a loop), so it lives in the sibling combinator, not `buildOrchLoop`.
    Definitional (the deployed driver IS
    `buildOrchCallSeq 64 (provePhaseSymbols.map OrchStep.call)`). -/
theorem buildOrchCallSeq_eq_proveDriverFundef :
    buildOrchCallSeq 64
        (Plonky3ProveDriverEmit.provePhaseSymbols.map OrchStep.call)
      = Plonky3ProveDriverEmit.proveDriverFundef := rfl

/-! ## 2. The generated driver carries the owned back-edge + the leaf call

The deployed module-1 driver *is* the front output (by the `rfl` validation
above), so the plonky3 module's already-proven rendering KAT
`merkleLeafLoop_renders_control_flow` — that the rendered `.s` carries the loop
label `.L0:`, the public counter test `cmpq $0, %r8`, the `jne .L0` back-edge,
and the `call plonky3_merkle_hash_leaf_rc` body — witnesses the front-sourced
driver's owned control-flow shape with no re-rendering. -/

/-- The front output for the Merkle leaf level equals the deployed
    `merkleLeafLoop` — so its rendering KAT (`merkleLeafLoop_renders_control_flow`)
    applies to the front-sourced driver verbatim. Derived from the general
    `buildOrchLoop_eq_orchLoopFundef` at the concrete Merkle args
    (`merkleLeafLoop` *is* `orchLoopFundef "…" 32 32 64`). -/
theorem buildOrchLoop_eq_merkleLeafLoop :
    buildOrchLoop (strideCallSpec "plonky3_merkle_hash_leaf_rc" 32 32 64)
      = Plonky3OrchLoopsEmit.merkleLeafLoop :=
  buildOrchLoop_eq_orchLoopFundef "plonky3_merkle_hash_leaf_rc" 32 32 64

/-- The front-sourced Merkle-leaf driver renders the owned loop back-edge and the
    leaf `call` — the plonky3 module's KAT applies to the generated driver by
    definitional equality (the generated `Lfundef` *is* `merkleLeafLoop`), so this
    is the plonky3 proof term at the front-sourced goal, no `native_decide`. -/
theorem buildOrchLoop_merkleLeaf_renders_control_flow :
    let s := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLfundef
      "p3_merkle_leaf_loop"
      (buildOrchLoop (strideCallSpec "plonky3_merkle_hash_leaf_rc" 32 32 64)).lfd_body
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow.occursIn ".L0:" s = true
      ∧ CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow.occursIn "cmpq $0, %r8" s = true
      ∧ CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow.occursIn "jne .L0" s = true
      ∧ CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow.occursIn
          "call plonky3_merkle_hash_leaf_rc" s = true := by
  rw [buildOrchLoop_eq_merkleLeafLoop]
  exact Plonky3OrchLoopsEmit.merkleLeafLoop_renders_control_flow

end CatCrypt.Crypto.SecureCompilation.Dialects.OrchLoopFront
