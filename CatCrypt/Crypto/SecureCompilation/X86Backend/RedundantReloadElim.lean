/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed

/-!
# Redundant spill-reload elimination on an owned-emit block

The pass itself — the recognizer `isRedundantReload`, the rewrite `dropReloads`,
the `runBlock`-equality `dropReloads_runBlock` and the constant-time-class
preservation `dropReloads_allDirect` — is `Optimizer.RedundantReloadElim`. It is
a stage of both shipped pipelines: `X86ComPipeline.defaultX86Pipeline` (as
`dropReloadsPass`) and `X86OptPipelineComposed.defaultValidatedPipeline` (as
`dropReloadsValidated defaultSpillBases`).

This module exercises the pass on `poly1305ExcerptBlock`, a straight-line block
transcribed from the owned emit
`bench/poly1305_compare/gen_com/poly1305_mac_hacl.s`, and records what each
pipeline does to it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RedundantReloadElim

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
/-! The pass is re-exported here so callers that reach it through this module keep
naming it `RedundantReloadElim.dropReloads`. -/

export CatCrypt.Crypto.Optimizer.RedundantReloadElim
  (storeKey loadKey isRedundantReload eq_of_isRedundantReload consDrop dropReloads
   defaultSpillBases setReg_get_self evalInstr_loadMem_storeMem consDrop_runBlock
   dropReloads_runBlock consDrop_sublist dropReloads_sublist dropReloads_allDirect)

open CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline (optimizeX86Block)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
  (ValidatedPass composeValidated defaultValidatedPipeline defaultValidatedPipeline_sound)

/-! ## 1. The owned-emit block

`poly1305ExcerptBlock` transcribes lines 85–115 of the owned emit
`bench/poly1305_compare/gen_com/poly1305_mac_hacl.s` — the inner accumulator
sequence of `poly1305_mac_hacl`, thirty-one instructions containing three
store/reload pairs against `%rsp`. -/

/-- Thirty-one straight-line instructions from the owned `poly1305_mac_hacl` emit. -/
def poly1305ExcerptBlock : List (JInstr 64) :=
  [ .loadMem "%r15" "%rsp" 24,
    .loadMemIdx "%r15" "%r14" "%r15" 8,
    .storeMem "%rsp" 32 (.reg "%r15"),
    .storeMem "%rsp" 24 (.imm 2),
    .loadMem "%r15" "%rsp" 40,
    .storeMem "%rsp" 16 (.reg "%r15"),
    .loadMem "%r15" "%rsp" 16,
    .loadMem "%r14" "%rsp" 24,
    .add "%r15" (.reg "%r14"),
    .storeMem "%rsp" 16 (.reg "%r15"),
    .loadMem "%r14" "%rsp" 112,
    .loadMem "%r15" "%rsp" 16,
    .loadMemIdx "%r15" "%r14" "%r15" 8,
    .storeMem "%rsp" 24 (.reg "%r15"),
    .storeMem "%rsp" 16 (.imm 3),
    .loadMem "%r15" "%rsp" 40,
    .storeMem "%rsp" 8 (.reg "%r15"),
    .loadMem "%r15" "%rsp" 8,
    .loadMem "%r14" "%rsp" 16,
    .add "%r15" (.reg "%r14"),
    .storeMem "%rsp" 8 (.reg "%r15"),
    .loadMem "%r14" "%rsp" 112,
    .loadMem "%r15" "%rsp" 8,
    .loadMemIdx "%r15" "%r14" "%r15" 8,
    .storeMem "%rsp" 16 (.reg "%r15"),
    .storeMem "%rsp" 8 (.imm 4),
    .loadMem "%r15" "%rsp" 40,
    .storeMem "%rsp" 0 (.reg "%r15"),
    .loadMem "%r15" "%rsp" 0,
    .loadMem "%r14" "%rsp" 8,
    .add "%r15" (.reg "%r14") ]

/-! ## 2. The pass alone -/

/-- The pass alone deletes three of the excerpt's thirty-one instructions. -/
theorem dropReloads_poly1305Excerpt_length :
    poly1305ExcerptBlock.length = 31 ∧
      (dropReloads defaultSpillBases poly1305ExcerptBlock).length = 28 := by
  constructor <;> rfl

/-- The pass fires on the excerpt: the swept block differs from the input. -/
theorem dropReloads_poly1305Excerpt_fires :
    dropReloads defaultSpillBases poly1305ExcerptBlock ≠ poly1305ExcerptBlock := by
  intro h
  have := congrArg List.length h
  rw [dropReloads_poly1305Excerpt_length.1, dropReloads_poly1305Excerpt_length.2] at this
  exact absurd this (by decide)

/-- The swept excerpt runs to the same machine state as the original on every start
    state — an instance of `dropReloads_runBlock`. -/
theorem dropReloads_poly1305Excerpt_runBlock (s : JState 64) :
    runBlock s (dropReloads defaultSpillBases poly1305ExcerptBlock)
      = runBlock s poly1305ExcerptBlock :=
  dropReloads_runBlock defaultSpillBases poly1305ExcerptBlock s

/-! ## 3. The pass inside the driver pipeline

On this block store-to-load forwarding already rewrites all three store/reload
pairs to self-moves and the self-move drop deletes them, so the driver reaches
twenty-six instructions and the elimination stage finds nothing further. The
stage's own reach is the reloads forwarding leaves behind — see
`X86ComPipeline.twoCellReloadBlock`. -/

/-- The default owned-x86 driver takes the excerpt from thirty-one instructions to
    twenty-six. -/
theorem optimizeX86Block_poly1305Excerpt_length :
    (optimizeX86Block poly1305ExcerptBlock).length = 26 := by rfl

/-- On this block the elimination stage is inert after the driver's forwarding and
    self-move drop: the three pairs it recognizes were already removed. -/
theorem dropReloads_poly1305Excerpt_after_driver :
    dropReloads defaultSpillBases (optimizeX86Block poly1305ExcerptBlock)
      = optimizeX86Block poly1305ExcerptBlock := by rfl

/-- The validated pipeline preserves the excerpt's `runBlock` state — an instance of
    `defaultValidatedPipeline_sound` at the demonstration placement. -/
theorem defaultValidatedPipeline_poly1305Excerpt_sound (s : JState 64) :
    runBlock s
        (composeValidated (defaultValidatedPipeline [] [] 0 "%rbp") poly1305ExcerptBlock)
      = runBlock s poly1305ExcerptBlock :=
  defaultValidatedPipeline_sound [] [] 0 "%rbp" poly1305ExcerptBlock s

end CatCrypt.Crypto.SecureCompilation.X86Backend.RedundantReloadElim
