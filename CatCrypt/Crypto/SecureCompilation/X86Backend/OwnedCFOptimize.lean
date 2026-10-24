/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed

/-!
# The composed validated pipeline at the leaves of a structured block

`X86OptPipelineComposed.composeValidated` rewrites a straight-line
`List (JInstr 64)` behind a per-pass decidable certificate.
`MachineConstantTime.OwnedCF` is the structured control-flow block — sequential
composition, a counted loop, a public-guard conditional — whose leaves are
straight-line `List (JInstr 64)`.

`optimizeCF ps` applies `composeValidated ps` at every straight-line leaf and
keeps the control-flow structure. Its two guarantees are the leaf guarantees
carried across that structure:

* `optimizeCF_cfExec_snd` — the optimized block reaches the same `cfExec`
  post-state as the input, from every machine state. Induction on the block,
  chaining `composeValidated_sound` at the leaves.
* `optimizeCF_allDirect` — every leaf stays in the direct-addressing
  constant-time class, by `composeValidated_allDirect`.

The leak trace is not preserved: a pass that deletes an instruction deletes its
`MLeak` event, so `(cfExec s (optimizeCF ps cf)).1` and `(cfExec s cf).1` differ
whenever a certificate fires on a memory-touching instruction. The
constant-time statement carried here is the decidable addressing class
`ConstantTimeCoverage.allDirect` at each leaf, which is the `Bool` form of
`SpeculativeCTControlFlow.CFAllDirect`'s leaf condition.

## The hypothesis `composeValidated_sound` carries

`composeValidated_sound` is stated with `hdead : composedDead ps b = []` — the
hypothesis-free form is the footprint-relative `composeValidated_sound_fp`,
whose conclusion is `agreeExcept (composedDead ps b)` rather than state
equality. The induction here therefore takes `∀ b, composedDead ps b = []`.
Every pass in the registry has `dead := fun _ => []`
(`X86OptPipelineComposed.passRegistry_dead_nil`), so the hypothesis is `rfl` at
`defaultValidatedPipeline` and `composedDead_pipelineByName` at a named
pipeline; `optimizeCF_cfExec_snd_default` and `optimizeCF_cfExec_snd_byName`
are those two instances.

## Main results

* `optimizeCF` — the composed validated pipeline applied at every straight-line
  leaf of an `OwnedCF`.
* `cfLeaves` / `cfSize` — the straight-line leaves of a block, in order, and the
  total instruction count over them.
* `cfLeaves_optimizeCF` — the leaves of the optimized block are the optimized
  leaves.
* `optimizeCF_cfExec_snd` — post-state preservation, for every state.
* `optimizeCF_cfExec_snd_default` / `optimizeCF_cfExec_snd_byName` — the two
  hypothesis-free instances.
* `optimizeCF_allDirect` — the leaves stay in the direct-addressing class.
* `#guard`s recording which of the seven registered certificates fire on the
  pipeline's pilot block and what the composed pipeline does to it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCFOptimize

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JState runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
  (OwnedCF cfExec cfLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
  (ValidatedPass composeValidated composedDead composeValidated_sound
   composeValidated_allDirect defaultValidatedPipeline pipelineByName
   composedDead_pipelineByName passRegistry demoPipeline)

/-! ## 1. The leaves of a structured block -/

/-- The straight-line leaves of a structured control-flow block, in the order the
    block visits them. -/
def cfLeaves {w : Nat} : OwnedCF w → List (List (JInstr w))
  | .straight body => [body]
  | .seq a b => cfLeaves a ++ cfLeaves b
  | .loop _ body => cfLeaves body
  | .ifPub _ thenB elseB => cfLeaves thenB ++ cfLeaves elseB

/-- The total instruction count over the straight-line leaves of a block. Each
    leaf is counted once, whatever its iteration count. -/
def cfSize {w : Nat} (cf : OwnedCF w) : Nat := ((cfLeaves cf).map List.length).sum

/-! ## 2. The pipeline at every leaf -/

/-- **The composed validated pipeline over a structured block.** Apply
    `composeValidated ps` at each straight-line leaf; keep the control-flow
    structure, the loop trip counts and the conditional guards. -/
def optimizeCF (ps : List ValidatedPass) : OwnedCF 64 → OwnedCF 64
  | .straight body => .straight (composeValidated ps body)
  | .seq a b => .seq (optimizeCF ps a) (optimizeCF ps b)
  | .loop n body => .loop n (optimizeCF ps body)
  | .ifPub guard thenB elseB => .ifPub guard (optimizeCF ps thenB) (optimizeCF ps elseB)

/-- The leaves of the optimized block are the pipeline applied to the leaves of
    the input, in the same order. -/
theorem cfLeaves_optimizeCF (ps : List ValidatedPass) (cf : OwnedCF 64) :
    cfLeaves (optimizeCF ps cf) = (cfLeaves cf).map (composeValidated ps) := by
  induction cf with
  | straight body => rfl
  | seq a b iha ihb =>
    simp only [optimizeCF, cfLeaves, iha, ihb, List.map_append]
  | loop n body ih => simp only [optimizeCF, cfLeaves, ih]
  | ifPub g t e iht ihe =>
    simp only [optimizeCF, cfLeaves, iht, ihe, List.map_append]

/-! ## 3. Post-state preservation across the control-flow structure -/

/-- The counted-loop half of post-state preservation: when one iteration of the
    optimized body reaches the same state as one iteration of the body, so does
    the `n`-fold loop, for every `n`. Induction on the trip count. -/
theorem optimizeCF_cfLoop_snd (ps : List ValidatedPass) (body : OwnedCF 64)
    (ih : ∀ s : JState 64, (cfExec s (optimizeCF ps body)).2 = (cfExec s body).2) :
    ∀ (n : Nat) (s : JState 64),
      (cfLoop n (optimizeCF ps body) s).2 = (cfLoop n body s).2 := by
  intro n
  induction n with
  | zero => intro s; simp only [cfLoop]
  | succ m ihm =>
    intro s
    simp only [cfLoop, ih s, ihm (cfExec s body).2]

/-- **The optimized block reaches the same post-state.** For a pipeline whose
    accumulated dead set is empty on every block, the block with
    `composeValidated ps` at each leaf lands in the same `cfExec` post-state as
    the input, from every machine state. Induction on the block: a leaf closes by
    `composeValidated_sound`, a loop by `optimizeCF_cfLoop_snd`, and a conditional
    reads its guard in the unchanged pre-state so both blocks take the same
    arm. -/
theorem optimizeCF_cfExec_snd (ps : List ValidatedPass)
    (hdead : ∀ b, composedDead ps b = []) :
    ∀ (cf : OwnedCF 64) (s : JState 64),
      (cfExec s (optimizeCF ps cf)).2 = (cfExec s cf).2 := by
  intro cf
  induction cf with
  | straight body =>
    intro s
    simp only [optimizeCF, cfExec]
    exact composeValidated_sound ps body (hdead body) s
  | seq a b iha ihb =>
    intro s
    simp only [optimizeCF, cfExec, iha s, ihb (cfExec s a).2]
  | loop n body ih =>
    intro s
    simp only [optimizeCF, cfExec]
    exact optimizeCF_cfLoop_snd ps body ih n s
  | ifPub g t e iht ihe =>
    intro s
    by_cases hz : s.get g = 0
    · simp only [optimizeCF, cfExec, ite_eq_left hz, ihe s]
    · simp only [optimizeCF, cfExec, ite_eq_right hz, iht s]

/-- Post-state preservation at the default validated pipeline: every stage has an
    empty dead set, so the hypothesis of `optimizeCF_cfExec_snd` is `rfl`. -/
theorem optimizeCF_cfExec_snd_default
    (prot : List (String × Int))
    (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String)
    (cf : OwnedCF 64) (s : JState 64) :
    (cfExec s (optimizeCF (defaultValidatedPipeline prot pinned frameBase spillBase) cf)).2
      = (cfExec s cf).2 :=
  optimizeCF_cfExec_snd _ (fun _ => rfl) cf s

/-- Post-state preservation at a pipeline assembled by pass name, through
    `composedDead_pipelineByName`. -/
theorem optimizeCF_cfExec_snd_byName (names : List String)
    (cf : OwnedCF 64) (s : JState 64) :
    (cfExec s (optimizeCF (pipelineByName names) cf)).2 = (cfExec s cf).2 :=
  optimizeCF_cfExec_snd _ (composedDead_pipelineByName names) cf s

/-! ## 4. The addressing class at the leaves -/

/-- **The optimized leaves stay in the direct-addressing class.** Each leaf of the
    optimized block is `composeValidated ps` of a leaf of the input
    (`cfLeaves_optimizeCF`), and `composeValidated_allDirect` preserves `allDirect`
    unconditionally. -/
theorem optimizeCF_allDirect (ps : List ValidatedPass) (cf : OwnedCF 64)
    (h : ∀ b ∈ cfLeaves cf, allDirect b = true) :
    ∀ b ∈ cfLeaves (optimizeCF ps cf), allDirect b = true := by
  intro b hb
  rw [cfLeaves_optimizeCF, List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  exact composeValidated_allDirect ps c (h c hc)

/-! ## 5. What the registered certificates decide on the pilot block

`X86OptPipelineComposed.demoPipeline` is `defaultValidatedPipeline` at the
registry's placement parameters, and `Fe25519MulKernel.feMulBlock` is the pilot
block its §5 demonstration is stated over. The `#guard`s below record what each
of the seven certificates decides on that block and what the fold does to it. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (feMulBlock)

/-- The names of the registered passes whose certificate fires on `b`. -/
def firingOn (b : List (JInstr 64)) : List String :=
  (passRegistry.filter (fun rp => rp.chk b)).map (fun rp => rp.name)

/-- The names of the registered passes that rewrite `b` to something other than
    `b`, whether or not their certificate fires. -/
def rewritingOn (b : List (JInstr 64)) : List String :=
  (passRegistry.filter (fun rp => !decide (rp.f b = b))).map (fun rp => rp.name)

-- Four of the seven certificates fire on the pilot block: the two `fun _ => true`
-- gates, store-to-load forwarding's `allDirect`-preservation implication, and the
-- flag-liveness-guarded fusion. The mem2reg certificate declines because its
-- dead-store-elimination stage is not inert here, and the two no-op-gated
-- allocator passes decline because they rewrite.
#guard firingOn feMulBlock
  = ["store-to-load-forward", "drop-id-movs", "drop-reloads", "fuse-mulx"]

-- The three passes that decline are exactly the three that would rewrite the
-- block, and no pass both fires and rewrites: the fold is the identity here.
#guard rewritingOn feMulBlock = ["mem2reg", "graph-color-ra", "spill-slot-reuse"]
#guard composeValidated demoPipeline feMulBlock = feMulBlock

/-- The pilot block wrapped as a counted loop, for the leaf-count reading of
    `optimizeCF` on a block carrying control-flow structure. -/
def demoCF : OwnedCF 64 := .loop 4 (.straight feMulBlock)

-- `optimizeCF` maps the leaf and keeps the loop, so the leaf count of the
-- optimized block is the length of the composed pipeline's output on the pilot
-- block, which the guard above pins to be the pilot block itself.
#guard cfSize (optimizeCF demoPipeline demoCF) = cfSize demoCF

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCFOptimize
