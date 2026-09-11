/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge

@[expose] public section

set_option autoImplicit false

/-!
# The INLINE-nested-loop closed machine fold (capability B5)

`nestSegDN` (`JasminLsemMemLoopNestDepth`) closes arbitrary-depth **nested
CALLS**: its segment bodies are `Lopn ∪ Lcall`, so an inner loop realised as a
region call is one instruction and the depth induction recurses through the
callee environment.  An **INLINE** nest (`loopLinstrRM` inside `loopLinstrRM` —
the inner back-edge's `Llabel`/`Lcond` INSIDE the outer body, no call) is the
shape the lowering `forLoopLcmdNRtNested` emits (inner runtime loop at label
`d+1` inside outer label `d`); it was validated depth-3 by `native_decide`
(`ggm_depth3_validate`) but had no closed theorem: an `Lopn ∪ call` segment
lemma cannot treat the inner `Llabel`/`Lcond` as opaque ops.  This module closes
it.

## The control-flow-aware segment lemma (`segInlineBlocks`)

A segment is structured as a list of `IBlock`s: either a **straight**
`Lopn ∪ linked-leaf-call` segment, or a complete **inline loop region**
`Llabel top :: flat body ++ [Lcond nReg top]` — a well-bracketed single-entry
single-exit region at its own label, whose body is again a block list
(regions nest to ARBITRARY depth; the block tree is the depth index).  The
spec fold `runIBsL` runs a straight block via A2's call-resolving
`lsemStraightMemC` and a region as a **data-dependent do-while** (`runRegion`:
body-fold, then loop while the counter register is non-zero, pc reset to the
label+1 on each taken back-edge — exactly the machine's `evalJumpMemC`), with a
fuel budget bounding taken back-edges (any `some` result is a
termination, as A3's `runWhileMem`).

`segInlineBlocks` proves: if the flattened segment occupies its positions in
the program body, every region label resolves (via `findLabelMem` on the whole
body) to the region's own position — labels distinct per nesting depth, as the
lowering guarantees with labels `d` vs `d+1` — and the spec fold terminates,
then the machine `lsemFuelMemLC` consumes some fuel `n` and lands exactly on
the fold's out-state.  Each region is handled as ONE composite step whose
effect is the inner fold: the outer walk enters the region at its label, the
inner loop runs to ITS exit (the single-loop pass logic at the inner label),
and the outer walk resumes at the instruction after the region.  The proof is
a strong induction on the back-edge budget (each taken back-edge strictly
decreases it) with an inner induction on the block list — NOT a flat
instruction induction; straight blocks are discharged by A3's `segCallG`
(never re-proved).

## The closed inline-nest theorems

* `inlineNest_closed` — the whole-program closed theorem: for the singleton
  program whose body IS the flattened block list (the emitted nest), the
  machine run from pc `0` halts on exactly the spec fold's out-state.  Depth-N
  is structural: a region inside a region inside a region is just a deeper
  block tree (the GGM validate below instantiates it at depth 3).
* `runRegion_reconstructs` — a terminating region do-while reconstructs the
  fixed-`m` bounded fold `runBoundedIBs` + its counter schedule (trip count
  read off the run, as A3's `runWhileMem_halts_schedule`).
* `runBoundedIBs_decodes_nestedDenote` — the B4-composable fold induction: if
  each outer pass of the (region-containing) body computes one inner fold
  `(List.range (innerTripAtC jd)).foldl (stepCNested jd)` under the `decodeM`
  correspondence, the `m`-fold decodes to `JLoopBodyN.nestedDenote` — the
  source semantics of `ComL.forLoopNRtNested`
  (`comL_forLoopNRtNested_ret_denote` closes it onto `ComL.denote`).
* `inlineNest_export_decodes_nestedDenote` — the composed export theorem for
  the emitted two-level shape (outer region whose body recomputes the inner
  count and runs the inner region): machine run `decodeM`s the accumulator to
  `JLoopBodyN.nestedDenote` — stated exactly like B4's
  `runBoundedLoopMem_decodes_denote` conclusion, so it composes with
  `JasminLsemMemSourceTie` §6.

## Validate: GGM depth-3 re-derived THROUGH the closed theorem

`ggmBlks` is `ggmProg`'s body as a depth-3 block tree (region 0 ⊃ region 1 ⊃
region 2, with the per-outer `mid := num >> (jd+1)` recompute as a straight
block); `ggmBlks_flat` checks the flattening is `ggmProg`'s body.
`ggm_depth3_rederived` / `ggm_recompute_rederived` re-derive the
`ggm_depth3_validate` / `ggm_recompute_reads_num` results through
`inlineNest_closed`: the machine side comes from the closed theorem (no
`native_decide` on the interpreter run); `native_decide` only evaluates the
SPEC fold `runIBsL`, which must equal `ggmNestedFold` (`= 14` at `num = 8`,
`= 28` at `num = 16` — `ggm_depth3_num_sensitive`).

**0 sorries; axioms = {propext, Classical.choice, Quot.sound}** for the
segment lemma and the closed theorems (+ `Lean.ofReduceBool` for the
`native_decide` SPEC-fold evaluations in the validate).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestInline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge

/-! ## 0. State-plumbing prerequisites -/

/-- `nextPc` is `setLpc (lpc + 1)` — the fall-through step is a pc write. -/
theorem LstateM.nextPc_eq_setLpc (s : LstateM) : s.nextPc = s.setLpc (s.lpc + 1) := rfl

/-- Consecutive pc writes collapse to the last. -/
@[simp] theorem LstateM.setLpc_setLpc (s : LstateM) (a b : Nat) :
    (s.setLpc a).setLpc b = s.setLpc b := rfl

/-- **Every successful inline call-resolving step advances the pc by one** —
    unconditionally (no `BodyStepOK` needed): a call's `calleeEffect` maps to
    `setLpc (lpc + 1)`; every other arm is `lsemStepMem`. -/
theorem lsemStepMemC_lpc_succ (env : LeafEnvM) (i : LinstrRM) (s s' : LstateM)
    (h : lsemStepMemC env i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold lsemStepMemC at h
  split at h
  · unfold calleeEffect at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨c, _, hc⟩ := h; rw [← hc]; rfl
    · simp at h
  · exact lsemStepMem_lpc_succ i s s' h

/-- The call-resolving body-fold advances the pc by the body length, for **any**
    body (each `lsemStepMemC` advances by one). -/
theorem lsemStraightMemC_lpc_any (env : LeafEnvM) :
    ∀ (body : List LinstrRM) (s b : LstateM),
      lsemStraightMemC env body s = some b → b.lpc = s.lpc + body.length := by
  intro body
  induction body with
  | nil => intro s b h; simp only [lsemStraightMemC_nil, Option.some.injEq] at h; subst h; simp
  | cons i is ih =>
      intro s b h
      rw [lsemStraightMemC_cons] at h
      cases hstep : lsemStepMemC env i s with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some s' =>
          rw [hstep] at h
          have h1 := lsemStepMemC_lpc_succ env i s s' hstep
          have h2 := ih s' b h
          rw [h2, h1, List.length_cons]; omega

/-- The loop shape's length: label + body + back-edge. -/
theorem loopLinstrRM_length (top : LLabel) (nReg : String) (body : List LinstrRM) :
    (loopLinstrRM top nReg body).length = body.length + 2 := by
  simp [loopLinstrRM]

/-- The loop shape's head is its label. -/
theorem loop_label_pos (top : LLabel) (nReg : String) (body : List LinstrRM) :
    (loopLinstrRM top nReg body)[0]? =
      some (LinstrR.Llabel .internal top, MemTag.reg none) := rfl

/-! ## 1. The block structure: straight segments and inline loop regions

`IBlock` is the control-flow-aware segment grammar: a straight
`Lopn ∪ linked-leaf-call` run, or a complete inline loop region at its own
label whose body is again a block list.  The nesting depth is the tree depth —
no separate depth index. -/

/-- A control-flow-aware segment block: a straight (`Lopn` ∪ region-call)
    segment, or a complete inline loop region
    `Llabel top :: flat body ++ [Lcond (.reg nReg) top]`. -/
inductive IBlock : Type where
  /-- A straight-line-with-calls segment (A2's `BodyStepOK` instructions). -/
  | straight (seg : List LinstrRM) : IBlock
  /-- A complete inline loop region at label `top` with counter `nReg`. -/
  | region (top : LLabel) (nReg : String) (body : List IBlock) : IBlock

mutual
/-- The flattened instruction stream of a block. -/
def IBlock.flat : IBlock → List LinstrRM
  | .straight seg => seg
  | .region top nReg body => loopLinstrRM top nReg (flatL body)
/-- The flattened instruction stream of a block list. -/
def flatL : List IBlock → List LinstrRM
  | [] => []
  | b :: rest => b.flat ++ flatL rest
end

@[simp] theorem flat_straight (seg : List LinstrRM) :
    (IBlock.straight seg).flat = seg := by rw [IBlock.flat]

@[simp] theorem flat_region (top : LLabel) (nReg : String) (body : List IBlock) :
    (IBlock.region top nReg body).flat = loopLinstrRM top nReg (flatL body) := by
  rw [IBlock.flat]

@[simp] theorem flatL_nil : flatL [] = [] := by rw [flatL]

@[simp] theorem flatL_cons (b : IBlock) (rest : List IBlock) :
    flatL (b :: rest) = b.flat ++ flatL rest := by rw [flatL]

mutual
/-- Block well-formedness: a straight block's instructions are A2's
    `BodyStepOK` (`Lopn` ∪ call-to-a-linked-leaf); a region's body is
    recursively well-formed. -/
def IBlockOK (env : LeafEnvM) (P : LprogM) : IBlock → Prop
  | .straight seg => ∀ i ∈ seg, BodyStepOK env P i
  | .region _ _ body => IBlocksOK env P body
/-- Block-list well-formedness. -/
def IBlocksOK (env : LeafEnvM) (P : LprogM) : List IBlock → Prop
  | [] => True
  | b :: rest => IBlockOK env P b ∧ IBlocksOK env P rest
end

@[simp] theorem IBlockOK_straight (env : LeafEnvM) (P : LprogM) (seg : List LinstrRM) :
    IBlockOK env P (.straight seg) = ∀ i ∈ seg, BodyStepOK env P i := by rw [IBlockOK]

@[simp] theorem IBlockOK_region (env : LeafEnvM) (P : LprogM) (top : LLabel)
    (nReg : String) (body : List IBlock) :
    IBlockOK env P (.region top nReg body) = IBlocksOK env P body := by rw [IBlockOK]

@[simp] theorem IBlocksOK_nil (env : LeafEnvM) (P : LprogM) :
    IBlocksOK env P [] = True := by rw [IBlocksOK]

@[simp] theorem IBlocksOK_cons (env : LeafEnvM) (P : LprogM) (b : IBlock)
    (rest : List IBlock) :
    IBlocksOK env P (b :: rest) = (IBlockOK env P b ∧ IBlocksOK env P rest) := by
  rw [IBlocksOK]

mutual
/-- Label resolution at absolute position `p`: each region's label is the
    FIRST occurrence of that label in the whole program body (labels are
    distinct per nesting depth in the emitted shape, so the interpreter's
    global `findLabelMem` hits the region's own label). -/
def IBlockResolves (P : LprogM) : IBlock → Nat → Prop
  | .straight _, _ => True
  | .region top _ body, p =>
      findLabelMem top P.body = some p ∧ IBlocksResolve P body (p + 1)
/-- Label resolution for a block list starting at absolute position `p`. -/
def IBlocksResolve (P : LprogM) : List IBlock → Nat → Prop
  | [], _ => True
  | b :: rest, p => IBlockResolves P b p ∧ IBlocksResolve P rest (p + b.flat.length)
end

@[simp] theorem IBlockResolves_straight (P : LprogM) (seg : List LinstrRM) (p : Nat) :
    IBlockResolves P (.straight seg) p = True := by rw [IBlockResolves]

@[simp] theorem IBlockResolves_region (P : LprogM) (top : LLabel) (nReg : String)
    (body : List IBlock) (p : Nat) :
    IBlockResolves P (.region top nReg body) p
      = (findLabelMem top P.body = some p ∧ IBlocksResolve P body (p + 1)) := by
  rw [IBlockResolves]

@[simp] theorem IBlocksResolve_nil (P : LprogM) (p : Nat) :
    IBlocksResolve P [] p = True := by rw [IBlocksResolve]

@[simp] theorem IBlocksResolve_cons (P : LprogM) (b : IBlock) (rest : List IBlock)
    (p : Nat) :
    IBlocksResolve P (b :: rest) p
      = (IBlockResolves P b p ∧ IBlocksResolve P rest (p + b.flat.length)) := by
  rw [IBlocksResolve]

/-! ## 2. The spec fold: straight blocks via `lsemStraightMemC`, regions as
data-dependent do-whiles

`runRegion` is pc-faithful: the body-fold starts at the label+1, the taken
back-edge resets to label+1 (the machine's `evalJumpMemC` target), the exit
falls through to label + |body| + 2 (the instruction after the region).  The
fuel bounds taken back-edges — as A3's `runWhileMem`, any `some` result is a
termination within the budget. -/

mutual
/-- Run one block: a straight block is the call-resolving fold; a region is
    the do-while from its own label position (`s.lpc`). -/
def runIB (env : LeafEnvM) : Nat → IBlock → LstateM → Option LstateM
  | _, .straight seg, s => lsemStraightMemC env seg s
  | wf, .region _ nReg body, s =>
      runRegion env nReg body s.lpc wf (s.setLpc (s.lpc + 1))
  termination_by wf blk _ => (wf, sizeOf blk, 1)
/-- Run a block list in sequence. -/
def runIBsL (env : LeafEnvM) : Nat → List IBlock → LstateM → Option LstateM
  | _, [], s => some s
  | wf, b :: rest, s => (runIB env wf b s).bind (runIBsL env wf rest)
  termination_by wf blks _ => (wf, sizeOf blks, 2)
/-- The region do-while from the top of the body (pc `p + 1`): run the body
    blocks; loop (pc back to `p + 1`) while the counter `nReg` is non-zero;
    exit past the back-edge (pc `p + |flat body| + 2`). -/
def runRegion (env : LeafEnvM) (nReg : String) (body : List IBlock) (p : Nat) :
    Nat → LstateM → Option LstateM
  | 0, _ => none
  | wf + 1, s =>
      (runIBsL env wf body s).bind (fun b =>
        if condNZ b (.reg nReg) then runRegion env nReg body p wf (b.setLpc (p + 1))
        else some (b.setLpc (p + (flatL body).length + 2)))
  termination_by wf _ => (wf, sizeOf body, 0)
end

theorem runIB_straight (env : LeafEnvM) (wf : Nat) (seg : List LinstrRM) (s : LstateM) :
    runIB env wf (.straight seg) s = lsemStraightMemC env seg s := by rw [runIB]

theorem runIB_region (env : LeafEnvM) (wf : Nat) (top : LLabel) (nReg : String)
    (body : List IBlock) (s : LstateM) :
    runIB env wf (.region top nReg body) s
      = runRegion env nReg body s.lpc wf (s.setLpc (s.lpc + 1)) := by rw [runIB]

@[simp] theorem runIBsL_nil (env : LeafEnvM) (wf : Nat) (s : LstateM) :
    runIBsL env wf [] s = some s := by rw [runIBsL]

theorem runIBsL_cons (env : LeafEnvM) (wf : Nat) (b : IBlock) (rest : List IBlock)
    (s : LstateM) :
    runIBsL env wf (b :: rest) s = (runIB env wf b s).bind (runIBsL env wf rest) := by
  rw [runIBsL]

@[simp] theorem runRegion_zero (env : LeafEnvM) (nReg : String) (body : List IBlock)
    (p : Nat) (s : LstateM) : runRegion env nReg body p 0 s = none := by rw [runRegion]

theorem runRegion_succ (env : LeafEnvM) (nReg : String) (body : List IBlock)
    (p : Nat) (wf : Nat) (s : LstateM) :
    runRegion env nReg body p (wf + 1) s
      = (runIBsL env wf body s).bind (fun b =>
          if condNZ b (.reg nReg) then runRegion env nReg body p wf (b.setLpc (p + 1))
          else some (b.setLpc (p + (flatL body).length + 2))) := by rw [runRegion]

/-! ### pc-faithfulness of the spec fold -/

/-- A region do-while exits at the instruction after the region — regardless
    of entry state (all exits go through the explicit pc write). -/
theorem runRegion_lpc (env : LeafEnvM) (nReg : String) (body : List IBlock) (p : Nat) :
    ∀ (wf : Nat) (s b : LstateM), runRegion env nReg body p wf s = some b →
      b.lpc = p + (flatL body).length + 2 := by
  intro wf
  induction wf with
  | zero => intro s b h; rw [runRegion_zero] at h; exact absurd h (by simp)
  | succ w ih =>
      intro s b h
      rw [runRegion_succ] at h
      cases hb1 : runIBsL env w body s with
      | none => rw [hb1] at h; simp at h
      | some b1 =>
          rw [hb1, Option.bind_some] at h
          by_cases hg : condNZ b1 (.reg nReg)
          · rw [if_pos hg] at h; exact ih _ b h
          · rw [if_neg hg] at h
            obtain rfl := Option.some.inj h
            simp

/-- A successful block run advances the pc by the block's flat length. -/
theorem runIB_lpc (env : LeafEnvM) (wf : Nat) (blk : IBlock) (s b : LstateM)
    (h : runIB env wf blk s = some b) : b.lpc = s.lpc + blk.flat.length := by
  cases blk with
  | straight seg =>
      rw [runIB_straight] at h
      rw [flat_straight]
      exact lsemStraightMemC_lpc_any env seg s b h
  | region top nReg body =>
      rw [runIB_region] at h
      have := runRegion_lpc env nReg body s.lpc wf _ b h
      rw [flat_region, loopLinstrRM_length]
      omega

/-- A successful block-list run advances the pc by the flattened length. -/
theorem runIBsL_lpc (env : LeafEnvM) :
    ∀ (blks : List IBlock) (wf : Nat) (s b : LstateM),
      runIBsL env wf blks s = some b → b.lpc = s.lpc + (flatL blks).length := by
  intro blks
  induction blks with
  | nil =>
      intro wf s b h
      rw [runIBsL_nil] at h
      obtain rfl := Option.some.inj h
      simp
  | cons blk rest ih =>
      intro wf s b h
      rw [runIBsL_cons] at h
      cases hb1 : runIB env wf blk s with
      | none => rw [hb1] at h; simp at h
      | some b1 =>
          rw [hb1, Option.bind_some] at h
          have h1 := runIB_lpc env wf blk s b1 hb1
          have h2 := ih wf b1 b h
          rw [h2, h1, flatL_cons, List.length_append]
          omega

/-! ## 3. The control-flow-aware segment lemma (`segCore`)

The joint statement at back-edge budget `wf`, proved by strong induction on
`wf`: the region half first (its body pass and its tail recursion both live at
budget `wf - 1`), then blocks by an inner list induction — a region is ONE
composite step whose effect is the region do-while; a straight block is
`segCallG` (A3), never re-proved. -/

/-- The block-list segment lemma at budget `wf` (the induction carrier). -/
def SegBlocksAt (env : LeafEnvM) (P : LprogM) (wf : Nat) : Prop :=
  ∀ (blks : List IBlock) (s : LstatePMC) (b : LstateM),
    s.lfn = P.lfn →
    IBlocksOK env P blks →
    (∀ k, k < (flatL blks).length → P.body[s.base.lpc + k]? = (flatL blks)[k]?) →
    IBlocksResolve P blks s.base.lpc →
    runIBsL env wf blks s.base = some b →
    ∃ n, ∀ f, lsemFuelMemLC env P (n + f) s = lsemFuelMemLC env P f { s with base := b }

/-- The region-run lemma at budget `wf` (the induction carrier): from the top
    of a region's body (pc = label + 1), a terminating region do-while is
    realised by the machine. -/
def SegRegionAt (env : LeafEnvM) (P : LprogM) (wf : Nat) : Prop :=
  ∀ (top : LLabel) (nReg : String) (body : List IBlock) (p : Nat)
    (s : LstatePMC) (b : LstateM),
    s.lfn = P.lfn →
    IBlocksOK env P body →
    (∀ k, k < (loopLinstrRM top nReg (flatL body)).length →
      P.body[p + k]? = (loopLinstrRM top nReg (flatL body))[k]?) →
    findLabelMem top P.body = some p →
    IBlocksResolve P body (p + 1) →
    s.base.lpc = p + 1 →
    runRegion env nReg body p wf s.base = some b →
    ∃ n, ∀ f, lsemFuelMemLC env P (n + f) s = lsemFuelMemLC env P f { s with base := b }

/-- **The control-flow-aware segment lemma** (joint form).  Strong induction on
    the back-edge budget; regions recurse through the budget, blocks through
    the list — never a flat instruction induction. -/
theorem segCore (env : LeafEnvM) (P : LprogM) :
    ∀ wf : Nat, SegRegionAt env P wf ∧ SegBlocksAt env P wf := by
  intro wf
  induction wf using Nat.strongRecOn with
  | ind wf ih =>
    -- ── the region half at `wf` ──
    have hreg : SegRegionAt env P wf := by
      cases wf with
      | zero =>
          intro _ _ _ _ _ _ _ _ _ _ _ _ hrun
          rw [runRegion_zero] at hrun
          exact absurd hrun (by simp)
      | succ w =>
          intro top nReg body p s b hfn hok hpos hlbl hres hpc hrun
          rw [runRegion_succ] at hrun
          cases hb1 : runIBsL env w body s.base with
          | none => rw [hb1] at hrun; simp at hrun
          | some b1 =>
              rw [hb1, Option.bind_some] at hrun
              -- the body pass, via the block lemma at budget `w`
              have hposB : ∀ k, k < (flatL body).length →
                  P.body[s.base.lpc + k]? = (flatL body)[k]? := by
                intro k hk
                have h1 := hpos (1 + k) (by rw [loopLinstrRM_length]; omega)
                rw [hpc, show p + 1 + k = p + (1 + k) from by omega, h1]
                exact loop_body_pos top nReg (flatL body) k hk
              obtain ⟨n1, hn1⟩ := (ih w (Nat.lt_succ_self w)).2 body s b1 hfn hok hposB
                (by rw [hpc]; exact hres) hb1
              -- the state after the body sits at the back-edge
              have hb1_lpc : b1.lpc = p + 1 + (flatL body).length := by
                have := runIBsL_lpc env body w s.base b1 hb1
                rw [hpc] at this; exact this
              have hfetch : findInstrMemC env P { s with base := b1 }
                  = some (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) := by
                unfold findInstrMemC
                rw [curBodyC_self env P _ hfn]
                show P.body[b1.lpc]? = _
                have hcond := hpos (1 + (flatL body).length)
                  (by rw [loopLinstrRM_length]; omega)
                rw [hb1_lpc,
                  show p + 1 + (flatL body).length = p + (1 + (flatL body).length) from by
                    omega, hcond]
                exact loop_cond_pos top nReg (flatL body)
              by_cases hg : condNZ b1 (.reg nReg)
              · -- back-edge TAKEN: jump to the region's own label + 1, recurse
                rw [if_pos hg] at hrun
                obtain ⟨n2, hn2⟩ := (ih w (Nat.lt_succ_self w)).1 top nReg body p
                  { s with base := b1.setLpc (p + 1) } b hfn hok hpos hlbl hres rfl hrun
                refine ⟨n1 + 1 + n2, fun f => ?_⟩
                rw [show n1 + 1 + n2 + f = n1 + (1 + (n2 + f)) from by omega,
                  hn1 (1 + (n2 + f)),
                  show 1 + (n2 + f) = (n2 + f) + 1 from by omega,
                  lsemFuelMemLC, hfetch]
                simp only []
                have heval : evalInstrPMemLC env P
                    (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) { s with base := b1 }
                      = some { s with base := b1.setLpc (p + 1) } := by
                  unfold evalInstrPMemLC
                  simp only [hg, if_true]
                  unfold evalJumpMemC
                  have hcur : curBodyC env P
                      ({ s with base := b1 } : LstatePMC).lfn = P.body :=
                    curBodyC_self env P _ hfn
                  rw [hcur, hlbl]
                rw [heval]
                simp only []
                exact hn2 f
              · -- back-edge NOT taken: fall through past the region
                rw [if_neg hg] at hrun
                obtain rfl := Option.some.inj hrun
                have hg' : condNZ b1 (.reg nReg) = false := by simpa using hg
                refine ⟨n1 + 1, fun f => ?_⟩
                rw [show n1 + 1 + f = n1 + (1 + f) from by omega, hn1 (1 + f),
                  show 1 + f = f + 1 from by omega, lsemFuelMemLC, hfetch]
                simp only []
                have heval : evalInstrPMemLC env P
                    (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) { s with base := b1 }
                      = some { s with base := b1.nextPc } := by
                  unfold evalInstrPMemLC
                  simp only [hg', Bool.false_eq_true, if_false]
                rw [heval]
                simp only []
                have hnp : b1.nextPc = b1.setLpc (p + (flatL body).length + 2) := by
                  rw [LstateM.nextPc_eq_setLpc, hb1_lpc,
                    show p + 1 + (flatL body).length + 1
                      = p + (flatL body).length + 2 from by omega]
                rw [hnp]
    -- ── the single-block lemma at `wf` (from the region half) ──
    have hblk : ∀ (blk : IBlock) (s : LstatePMC) (b : LstateM),
        s.lfn = P.lfn →
        IBlockOK env P blk →
        (∀ k, k < blk.flat.length → P.body[s.base.lpc + k]? = blk.flat[k]?) →
        IBlockResolves P blk s.base.lpc →
        runIB env wf blk s.base = some b →
        ∃ n, ∀ f, lsemFuelMemLC env P (n + f) s
          = lsemFuelMemLC env P f { s with base := b } := by
      intro blk s b hfn hok hpos hres hrun
      cases blk with
      | straight seg =>
          -- straight block: A3's `segCallG` (`Lopn ∪ call`), never re-proved
          rw [runIB_straight] at hrun
          simp only [flat_straight] at hpos
          rw [IBlockOK_straight] at hok
          refine ⟨fuelCostC env seg, fun f => ?_⟩
          have hseg := segCallG env P P.lfn seg s f hfn hok
            (by intro k hk
                rw [curBodyC_self env P P.lfn rfl]
                exact hpos k hk)
          rw [hseg, hrun, Option.bind_some]
      | region top nReg body =>
          -- region block: label step, then the region do-while
          rw [runIB_region] at hrun
          simp only [flat_region] at hpos
          rw [IBlockOK_region] at hok
          rw [IBlockResolves_region] at hres
          obtain ⟨hlbl, hresB⟩ := hres
          have hfetch : findInstrMemC env P s
              = some (LinstrR.Llabel .internal top, MemTag.reg none) := by
            unfold findInstrMemC
            rw [curBodyC_self env P _ hfn]
            have h0 := hpos 0 (by rw [loopLinstrRM_length]; omega)
            rw [Nat.add_zero] at h0
            rw [h0]
            exact loop_label_pos top nReg (flatL body)
          obtain ⟨n2, hn2⟩ := hreg top nReg body s.base.lpc
            { s with base := s.base.setLpc (s.base.lpc + 1) } b hfn hok hpos hlbl hresB
            rfl hrun
          refine ⟨1 + n2, fun f => ?_⟩
          rw [show 1 + n2 + f = (n2 + f) + 1 from by omega, lsemFuelMemLC, hfetch]
          simp only []
          have heval : evalInstrPMemLC env P
              (LinstrR.Llabel .internal top, MemTag.reg none) s
                = some { s with base := s.base.nextPc } := by
            unfold evalInstrPMemLC
            simp only []
          rw [heval]
          simp only []
          rw [LstateM.nextPc_eq_setLpc]
          exact hn2 f
    -- ── the block-list lemma at `wf` (inner list induction) ──
    refine ⟨hreg, ?_⟩
    intro blks
    induction blks with
    | nil =>
        intro s b _ _ _ _ hrun
        rw [runIBsL_nil] at hrun
        obtain rfl := Option.some.inj hrun
        exact ⟨0, fun f => by rw [Nat.zero_add]⟩
    | cons blk rest ihrest =>
        intro s b hfn hok hpos hres hrun
        rw [runIBsL_cons] at hrun
        rw [IBlocksOK_cons] at hok
        rw [IBlocksResolve_cons] at hres
        obtain ⟨hokB, hokR⟩ := hok
        obtain ⟨hresB, hresR⟩ := hres
        cases hb1 : runIB env wf blk s.base with
        | none => rw [hb1] at hrun; simp at hrun
        | some b1 =>
            rw [hb1, Option.bind_some] at hrun
            have hposHead : ∀ k, k < blk.flat.length →
                P.body[s.base.lpc + k]? = blk.flat[k]? := by
              intro k hk
              have h1 := hpos k (by rw [flatL_cons, List.length_append]; omega)
              rw [h1, flatL_cons, List.getElem?_append_left hk]
            obtain ⟨n1, hn1⟩ := hblk blk s b1 hfn hokB hposHead hresB hb1
            have hb1_lpc := runIB_lpc env wf blk s.base b1 hb1
            have hposRest : ∀ k, k < (flatL rest).length →
                P.body[({ s with base := b1 } : LstatePMC).base.lpc + k]?
                  = (flatL rest)[k]? := by
              intro k hk
              show P.body[b1.lpc + k]? = (flatL rest)[k]?
              have h1 := hpos (blk.flat.length + k)
                (by rw [flatL_cons, List.length_append]; omega)
              rw [hb1_lpc, show s.base.lpc + blk.flat.length + k
                  = s.base.lpc + (blk.flat.length + k) from by omega, h1, flatL_cons,
                List.getElem?_append_right (by omega)]
              congr 1
              omega
            have hresRest : IBlocksResolve P rest
                ({ s with base := b1 } : LstatePMC).base.lpc := by
              show IBlocksResolve P rest b1.lpc
              rw [hb1_lpc]
              exact hresR
            obtain ⟨n2, hn2⟩ := ihrest { s with base := b1 } b hfn hokR hposRest
              hresRest hrun
            refine ⟨n1 + n2, fun f => ?_⟩
            rw [show n1 + n2 + f = n1 + (n2 + f) from by omega, hn1 (n2 + f)]
            exact hn2 f

/-- **The control-flow-aware segment lemma** (`segInlineBlocks`).  If the
    flattened block segment occupies positions `lpc .. lpc + |flat| - 1` of the
    program body, every region label resolves to its own position, and the
    spec fold (straight blocks via `lsemStraightMemC`, regions as
    data-dependent do-whiles) terminates within back-edge budget `wf`, then
    the machine `lsemFuelMemLC` consumes some fuel `n` and continues from the
    fold's out-state — each complete inner loop region acts as one composite
    step whose effect is the region do-while. -/
theorem segInlineBlocks (env : LeafEnvM) (P : LprogM) (wf : Nat)
    (blks : List IBlock) (s : LstatePMC) (b : LstateM)
    (hfn : s.lfn = P.lfn)
    (hok : IBlocksOK env P blks)
    (hpos : ∀ k, k < (flatL blks).length → P.body[s.base.lpc + k]? = (flatL blks)[k]?)
    (hres : IBlocksResolve P blks s.base.lpc)
    (hrun : runIBsL env wf blks s.base = some b) :
    ∃ n, ∀ f, lsemFuelMemLC env P (n + f) s
      = lsemFuelMemLC env P f { s with base := b } :=
  (segCore env P wf).2 blks s b hfn hok hpos hres hrun

/-- The region form of the segment lemma: from the top of a region's body, a
    terminating region do-while is realised by the machine (the inner loop
    runs to ITS halt at its own label, then the walk resumes after the
    region). -/
theorem segInlineRegion (env : LeafEnvM) (P : LprogM) (wf : Nat)
    (top : LLabel) (nReg : String) (body : List IBlock) (p : Nat)
    (s : LstatePMC) (b : LstateM)
    (hfn : s.lfn = P.lfn)
    (hok : IBlocksOK env P body)
    (hpos : ∀ k, k < (loopLinstrRM top nReg (flatL body)).length →
      P.body[p + k]? = (loopLinstrRM top nReg (flatL body))[k]?)
    (hlbl : findLabelMem top P.body = some p)
    (hres : IBlocksResolve P body (p + 1))
    (hpc : s.base.lpc = p + 1)
    (hrun : runRegion env nReg body p wf s.base = some b) :
    ∃ n, ∀ f, lsemFuelMemLC env P (n + f) s
      = lsemFuelMemLC env P f { s with base := b } :=
  (segCore env P wf).1 top nReg body p s b hfn hok hpos hlbl hres hpc hrun

/-! ## 4. The closed inline-nest theorem (whole program, any depth) -/

/-- **The closed inline-nest theorem.**  For the singleton program whose body
    IS the flattened block list (the emitted inline nest — e.g. an outer
    region containing an inner region containing …, to any depth, with
    data-dependent per-level trip counts), the machine run from pc `0` halts
    on exactly the spec fold's out-state.  Fuel is existential; the fold's
    termination within the back-edge budget `wf` is the only run hypothesis. -/
theorem inlineNest_closed (env : LeafEnvM) (fn : String) (blks : List IBlock)
    (wf : Nat) (s : LstatePMC) (b : LstateM)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 0)
    (hok : IBlocksOK env (singletonProgM fn (flatL blks)) blks)
    (hres : IBlocksResolve (singletonProgM fn (flatL blks)) blks 0)
    (hrun : runIBsL env wf blks s.base = some b) :
    ∃ n, lsemFuelMemLC env (singletonProgM fn (flatL blks)) n s
      = some { s with base := b } := by
  set P := singletonProgM fn (flatL blks) with hP
  have hfn' : s.lfn = P.lfn := hfn
  have hpos : ∀ k, k < (flatL blks).length →
      P.body[s.base.lpc + k]? = (flatL blks)[k]? := by
    intro k hk
    rw [hpc, Nat.zero_add]
    rfl
  obtain ⟨n, hn⟩ := segInlineBlocks env P wf blks s b hfn' hok hpos
    (by rw [hpc]; exact hres) hrun
  refine ⟨n, ?_⟩
  have h0 := hn 0
  rw [Nat.add_zero] at h0
  rw [h0]
  apply lsemFuelMemLC_halt
  unfold findInstrMemC
  rw [curBodyC_self env P _ hfn']
  show P.body[b.lpc]? = none
  have hb := runIBsL_lpc env blks wf s.base b hrun
  rw [hpc, Nat.zero_add] at hb
  rw [hb]
  exact List.getElem?_eq_none (le_refl _)

/-! ## 5. The bounded fold, fuel monotonicity, and schedule reconstruction

For the decode/source-tie layer, a terminating region do-while is
reconstructed as the fixed-`m` bounded fold `runBoundedIBs` (per-pass at a
uniform back-edge budget) plus its counter schedule — the trip count read off
the run, as A3's `runWhileMem_halts_schedule`.  Fuel monotonicity bridges the
do-while's decreasing per-pass budgets to the uniform one. -/

/-- The fixed-trip bounded fold of a region body: `m` passes of the block-list
    fold, pc reset to the loop top (`p + 1`) after each pass. -/
def runBoundedIBs (env : LeafEnvM) (wf : Nat) (body : List IBlock) (p : Nat) :
    Nat → LstateM → Option LstateM
  | 0, s => some s
  | k + 1, s =>
      (runIBsL env wf body s).bind
        (fun b => runBoundedIBs env wf body p k (b.setLpc (p + 1)))

@[simp] theorem runBoundedIBs_zero (env : LeafEnvM) (wf : Nat) (body : List IBlock)
    (p : Nat) (s : LstateM) : runBoundedIBs env wf body p 0 s = some s := rfl

@[simp] theorem runBoundedIBs_succ (env : LeafEnvM) (wf : Nat) (body : List IBlock)
    (p : Nat) (k : Nat) (s : LstateM) :
    runBoundedIBs env wf body p (k + 1) s
      = (runIBsL env wf body s).bind
          (fun b => runBoundedIBs env wf body p k (b.setLpc (p + 1))) := rfl

/-- Peel the last pass. -/
theorem runBoundedIBs_succ_right (env : LeafEnvM) (wf : Nat) (body : List IBlock)
    (p : Nat) :
    ∀ (j : Nat) (s : LstateM),
      runBoundedIBs env wf body p (j + 1) s
        = (runBoundedIBs env wf body p j s).bind
            (fun bj => (runIBsL env wf body bj).map (fun b => b.setLpc (p + 1))) := by
  intro j
  induction j with
  | zero =>
      intro s
      simp only [runBoundedIBs_succ, runBoundedIBs_zero, Option.bind_some]
      cases runIBsL env wf body s <;> simp
  | succ n ih =>
      intro s
      rw [runBoundedIBs_succ]
      conv_rhs => rw [runBoundedIBs_succ]
      cases hb : runIBsL env wf body s with
      | none => simp
      | some b => rw [Option.bind_some, Option.bind_some]; exact ih (b.setLpc (p + 1))

/-- A successful `m`-fold has successful prefixes. -/
theorem runBoundedIBs_prefix (env : LeafEnvM) (wf : Nat) (body : List IBlock) (p : Nat) :
    ∀ (m j : Nat) (s b : LstateM), j ≤ m →
      runBoundedIBs env wf body p m s = some b →
      ∃ bj, runBoundedIBs env wf body p j s = some bj := by
  intro m
  induction m with
  | zero =>
      intro j s b hj h
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      exact ⟨b, h⟩
  | succ k ih =>
      intro j s b hj h
      cases j with
      | zero => exact ⟨s, rfl⟩
      | succ j' =>
          rw [runBoundedIBs_succ] at h
          cases h1 : runIBsL env wf body s with
          | none => rw [h1] at h; simp at h
          | some b1 =>
              rw [h1, Option.bind_some] at h
              obtain ⟨bj, hbj⟩ := ih j' (b1.setLpc (p + 1)) b (by omega) h
              exact ⟨bj, by rw [runBoundedIBs_succ, h1, Option.bind_some]; exact hbj⟩

/-- The fuel-monotonicity carrier at budget `wf`. -/
def MonoAt (env : LeafEnvM) (wf : Nat) : Prop :=
  (∀ (blks : List IBlock) (s b : LstateM),
      runIBsL env wf blks s = some b → runIBsL env (wf + 1) blks s = some b) ∧
  (∀ (nReg : String) (body : List IBlock) (p : Nat) (s b : LstateM),
      runRegion env nReg body p wf s = some b →
        runRegion env nReg body p (wf + 1) s = some b)

/-- **Fuel monotonicity**: a fold that terminates within budget `wf` gives the
    same result at budget `wf + 1` (extra back-edge budget is a no-op). -/
theorem monoCore (env : LeafEnvM) : ∀ wf, MonoAt env wf := by
  intro wf
  induction wf using Nat.strongRecOn with
  | ind wf ih =>
    have hreg : ∀ (nReg : String) (body : List IBlock) (p : Nat) (s b : LstateM),
        runRegion env nReg body p wf s = some b →
          runRegion env nReg body p (wf + 1) s = some b := by
      cases wf with
      | zero =>
          intro _ _ _ _ _ h
          rw [runRegion_zero] at h
          exact absurd h (by simp)
      | succ w =>
          intro nReg body p s b h
          rw [runRegion_succ] at h
          rw [runRegion_succ]
          cases h1 : runIBsL env w body s with
          | none => rw [h1] at h; simp at h
          | some b1 =>
              rw [h1, Option.bind_some] at h
              rw [(ih w (Nat.lt_succ_self w)).1 body s b1 h1, Option.bind_some]
              by_cases hg : condNZ b1 (.reg nReg)
              · rw [if_pos hg] at h ⊢
                exact (ih w (Nat.lt_succ_self w)).2 nReg body p _ b h
              · rw [if_neg hg] at h ⊢
                exact h
    have hblk : ∀ (blk : IBlock) (s b : LstateM),
        runIB env wf blk s = some b → runIB env (wf + 1) blk s = some b := by
      intro blk s b h
      cases blk with
      | straight seg => rw [runIB_straight] at h ⊢; exact h
      | region top nReg body =>
          rw [runIB_region] at h ⊢
          exact hreg nReg body s.lpc _ b h
    refine ⟨?_, hreg⟩
    intro blks
    induction blks with
    | nil => intro s b h; rwa [runIBsL_nil] at h ⊢
    | cons blk rest ihr =>
        intro s b h
        rw [runIBsL_cons] at h ⊢
        cases h1 : runIB env wf blk s with
        | none => rw [h1] at h; simp at h
        | some b1 =>
            rw [h1, Option.bind_some] at h
            rw [hblk blk s b1 h1, Option.bind_some]
            exact ihr b1 b h

/-- Bounded-fold fuel monotonicity (per-pass lift of `monoCore`). -/
theorem runBoundedIBs_mono_fuel (env : LeafEnvM) (wf : Nat) (body : List IBlock)
    (p : Nat) :
    ∀ (m : Nat) (s b : LstateM), runBoundedIBs env wf body p m s = some b →
      runBoundedIBs env (wf + 1) body p m s = some b := by
  intro m
  induction m with
  | zero => intro s b h; simpa using h
  | succ k ih =>
      intro s b h
      rw [runBoundedIBs_succ] at h
      rw [runBoundedIBs_succ]
      cases h1 : runIBsL env wf body s with
      | none => rw [h1] at h; simp at h
      | some b1 =>
          rw [h1, Option.bind_some] at h
          rw [(monoCore env wf).1 body s b1 h1, Option.bind_some]
          exact ih _ b h

/-- **Schedule reconstruction.**  A terminating region do-while yields its trip
    count `m` and *proves* the counter schedule — the bounded `m`-fold at the
    do-while's own budget, "guard false at the end", and "guard true after
    each of the first `m - 1` passes" — derived from the run, not supplied
    (the data-dependent trips of the inline nest, as A3's
    `runWhileMem_halts_schedule` for the single while). -/
theorem runRegion_reconstructs (env : LeafEnvM) (nReg : String) (body : List IBlock)
    (p : Nat) :
    ∀ (wf : Nat) (s bfin : LstateM),
      runRegion env nReg body p wf s = some bfin →
      ∃ m, 0 < m
        ∧ runBoundedIBs env wf body p m s = some (bfin.setLpc (p + 1))
        ∧ condNZ bfin (.reg nReg) = false
        ∧ (∀ i, 0 < i → i < m → ∀ bi, runBoundedIBs env wf body p i s = some bi →
            condNZ bi (.reg nReg) = true) := by
  intro wf
  induction wf with
  | zero =>
      intro s bfin h
      rw [runRegion_zero] at h
      exact absurd h (by simp)
  | succ w ih =>
      intro s bfin h
      rw [runRegion_succ] at h
      cases h1 : runIBsL env w body s with
      | none => rw [h1] at h; simp at h
      | some b1 =>
          rw [h1, Option.bind_some] at h
          have h1' : runIBsL env (w + 1) body s = some b1 :=
            (monoCore env w).1 body s b1 h1
          by_cases hg : condNZ b1 (.reg nReg)
          · rw [if_pos hg] at h
            obtain ⟨m', hm', hbound', hgf', hsched'⟩ := ih (b1.setLpc (p + 1)) bfin h
            have hbound'' : runBoundedIBs env (w + 1) body p m' (b1.setLpc (p + 1))
                = some (bfin.setLpc (p + 1)) :=
              runBoundedIBs_mono_fuel env w body p m' _ _ hbound'
            refine ⟨m' + 1, by omega, ?_, hgf', ?_⟩
            · rw [runBoundedIBs_succ, h1', Option.bind_some]
              exact hbound''
            · intro i hi him bi hbi
              obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
              rw [runBoundedIBs_succ, h1', Option.bind_some] at hbi
              cases i' with
              | zero =>
                  rw [runBoundedIBs_zero] at hbi
                  obtain rfl := Option.some.inj hbi
                  rw [condNZ_setLpc]
                  exact hg
              | succ i'' =>
                  obtain ⟨bj, hbj⟩ := runBoundedIBs_prefix env w body p m' (i'' + 1)
                    (b1.setLpc (p + 1)) _ (by omega) hbound'
                  have hbj' := runBoundedIBs_mono_fuel env w body p (i'' + 1) _ _ hbj
                  rw [hbi] at hbj'
                  obtain rfl := Option.some.inj hbj'
                  exact hsched' (i'' + 1) (by omega) (by omega) bi hbj
          · rw [if_neg hg] at h
            obtain rfl := Option.some.inj h
            have hg' : condNZ b1 (.reg nReg) = false := by simpa using hg
            refine ⟨1, Nat.one_pos, ?_, ?_, ?_⟩
            · rw [runBoundedIBs_succ, h1', Option.bind_some, runBoundedIBs_zero,
                LstateM.setLpc_setLpc]
            · rw [condNZ_setLpc]
              exact hg'
            · intro i hi him
              omega

/-! ## 6. The decode layer: the bounded fold decodes to
`JLoopBodyN.nestedDenote` (the B4-composable form)

Mirrors `JasminLsemMemSourceTie.runBoundedLoopMem_decodes_denote`: a per-pass
simulation under the `decodeM` correspondence lifts through the bounded fold.
Instantiated at the per-outer-pass effect "one inner fold at the recomputed
trip" it concludes `JLoopBodyN.nestedDenote` — the source semantics of
`ComL.forLoopNRtNested` (`comL_forLoopNRtNested_ret_denote` reaches
`ComL.denote`). -/

/-- **The bounded-fold decode induction, over an arbitrary decoder.**  If the start
    state decodes the seed under `dec` and every pass `t < m` of the region body
    computes one `step t` under `dec`, the `m`-fold decodes to the `m`-fold of
    `step`. The decoder enters only through the seed and the `setLpc`-invariance
    `hset`; the register form `runBoundedIBs_decodes_fold` and the array-carrier
    form both instantiate it. -/
theorem runBoundedIBs_decodes_fold_gen {α : Type} (env : LeafEnvM) (wf : Nat)
    (body : List IBlock) (p : Nat) (dec : LstateM → Option α)
    (hset : ∀ (b : LstateM) (k : Nat), dec (b.setLpc k) = dec b)
    (step : Nat → α → α) (s0 : LstateM) (acc0 : α)
    (hinit : dec s0 = some acc0) :
    ∀ m : Nat,
      (∀ t, t < m → ∀ (bt : LstateM) (acct : α),
        runBoundedIBs env wf body p t s0 = some bt →
        dec bt = some acct →
        ∀ bt', runIBsL env wf body bt = some bt' →
        dec bt' = some (step t acct)) →
      ∀ bfin : LstateM, runBoundedIBs env wf body p m s0 = some bfin →
        dec bfin = some ((List.range m).foldl (fun a t => step t a) acc0) := by
  intro m
  induction m with
  | zero =>
      intro _ bfin hrun
      rw [runBoundedIBs_zero] at hrun
      obtain rfl := Option.some.inj hrun
      simpa using hinit
  | succ k ih =>
      intro hsim bfin hrun
      rw [runBoundedIBs_succ_right] at hrun
      cases hbk : runBoundedIBs env wf body p k s0 with
      | none => rw [hbk] at hrun; simp at hrun
      | some bk =>
          rw [hbk, Option.bind_some] at hrun
          cases hbt' : runIBsL env wf body bk with
          | none => rw [hbt'] at hrun; simp at hrun
          | some bt' =>
              rw [hbt', Option.map_some] at hrun
              obtain rfl := Option.some.inj hrun
              have hdk := ih (fun t ht => hsim t (Nat.lt_succ_of_lt ht)) bk hbk
              have hstep := hsim k (Nat.lt_succ_self k) bk _ hbk hdk bt' hbt'
              rw [hset, List.range_succ, List.foldl_append, List.foldl_cons,
                List.foldl_nil]
              exact hstep

/-- **The bounded-fold decode induction (register accumulator).**  If the start
    state decodes the seed and every pass `t < m` of the region body computes one
    `step t` under the `decodeM` correspondence, the `m`-fold decodes to the
    `m`-fold of `step` — stated exactly like B4's `runBoundedLoopMem_decodes_denote`,
    over the region-body fold `runIBsL` (which may itself contain inner regions).
    The `decodeM` instance of `runBoundedIBs_decodes_fold_gen`. -/
theorem runBoundedIBs_decodes_fold {w : Nat} (env : LeafEnvM) (wf : Nat)
    (body : List IBlock) (p : Nat) (accReg : String)
    (step : Nat → BitVec w → BitVec w) (s0 : LstateM) (acc0 : BitVec w)
    (hinit : decodeM s0 accReg w = some acc0) :
    ∀ m : Nat,
      (∀ t, t < m → ∀ (bt : LstateM) (acct : BitVec w),
        runBoundedIBs env wf body p t s0 = some bt →
        decodeM bt accReg w = some acct →
        ∀ bt', runIBsL env wf body bt = some bt' →
        decodeM bt' accReg w = some (step t acct)) →
      ∀ bfin : LstateM, runBoundedIBs env wf body p m s0 = some bfin →
        decodeM bfin accReg w
          = some ((List.range m).foldl (fun a t => step t a) acc0) :=
  runBoundedIBs_decodes_fold_gen env wf body p (fun s => decodeM s accReg w)
    (fun b k => decodeM_setLpc b k accReg w) step s0 acc0 hinit

/-- **The bounded fold decodes to `JLoopBodyN.nestedDenote`.**  Instantiating
    the per-pass effect at outer index `jd` with "the inner fold of
    `stepCNested` over the recomputed trip `innerTripAtC jd`", the `m`-fold
    decodes to the nested runtime fold — the source semantics of
    `ComL.forLoopNRtNested` (compose with `comL_forLoopNRtNested_ret_denote`
    for `ComL.denote`, and with `JasminLsemMemSourceTie` §6's runner bridges
    to discharge the per-pass hypothesis from the straight-line
    faithfulness). -/
theorem runBoundedIBs_decodes_nestedDenote {w : Nat} {invTys : Ctxt jasminDialect}
    (env : LeafEnvM) (wf : Nat) (body : List IBlock) (p : Nat) (accReg : String)
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect
      (JasminTy.reg w :: .reg 64 :: .reg 64 :: invTys) (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys) (s0 : LstateM) (acc0 : BitVec w)
    (hinit : decodeM s0 accReg w = some acc0) (m : Nat)
    (hsim : ∀ t, t < m → ∀ (bt : LstateM) (acct : BitVec w),
      runBoundedIBs env wf body p t s0 = some bt →
      decodeM bt accReg w = some acct →
      ∀ bt', runIBsL env wf body bt = some bt' →
      decodeM bt' accReg w
        = some ((List.range (JLoopBodyN.innerTripAtC innerCount invs t)).foldl
            (fun a u => JLoopBodyN.stepCNested innerUpdate invs t u a) acct))
    (bfin : LstateM) (hrun : runBoundedIBs env wf body p m s0 = some bfin) :
    decodeM bfin accReg w
      = some (JLoopBodyN.nestedDenote innerCount innerUpdate m invs acc0) :=
  runBoundedIBs_decodes_fold env wf body p accReg
    (fun t a => (List.range (JLoopBodyN.innerTripAtC innerCount invs t)).foldl
      (fun a2 u => JLoopBodyN.stepCNested innerUpdate invs t u a2) a)
    s0 acc0 hinit m hsim bfin hrun

/-- **The composed inline-nest export theorem (decodeM form).**  For the
    emitted two-level inline nest — the whole program is one outer region
    whose body blocks recompute the inner count and run the inner region (the
    `forLoopLcmdNRtNested` control skeleton) — under the per-outer-pass
    simulation, the machine run from the encoded seed halts at a state whose
    accumulator register decodes to **`JLoopBodyN.nestedDenote`** at the trip
    count `m` read off the run (with the bounded-fold witness and its schedule
    exposed for the consumer to pin `m`).  Composes with B4's source tie
    exactly as `runBoundedLoopMem_decodes_denote` does. -/
theorem inlineNest_export_decodes_nestedDenote {w : Nat} {invTys : Ctxt jasminDialect}
    (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String) (body : List IBlock)
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect
      (JasminTy.reg w :: .reg 64 :: .reg 64 :: invTys) (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys)
    (wf : Nat) (s : LstatePMC) (bfin : LstateM) (accReg : String) (acc0 : BitVec w)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 0)
    (hok : IBlocksOK env (singletonProgM fn (flatL [IBlock.region top nReg body]))
      [IBlock.region top nReg body])
    (hres : IBlocksResolve (singletonProgM fn (flatL [IBlock.region top nReg body]))
      [IBlock.region top nReg body] 0)
    (hrun : runIBsL env wf [IBlock.region top nReg body] s.base = some bfin)
    (hinit : decodeM s.base accReg w = some acc0)
    (hsim : ∀ t (bt : LstateM) (acct : BitVec w),
      runBoundedIBs env wf body 0 t (s.base.setLpc 1) = some bt →
      decodeM bt accReg w = some acct →
      ∀ bt', runIBsL env wf body bt = some bt' →
      decodeM bt' accReg w
        = some ((List.range (JLoopBodyN.innerTripAtC innerCount invs t)).foldl
            (fun a u => JLoopBodyN.stepCNested innerUpdate invs t u a) acct)) :
    ∃ (n m : Nat) (t : LstatePMC), 0 < m
      ∧ lsemFuelMemLC env (singletonProgM fn (flatL [IBlock.region top nReg body])) n s
          = some t
      ∧ t.base = bfin
      ∧ runBoundedIBs env wf body 0 m (s.base.setLpc 1) = some (bfin.setLpc 1)
      ∧ decodeM t.base accReg w
          = some (JLoopBodyN.nestedDenote innerCount innerUpdate m invs acc0) := by
  -- the machine run, from the whole-program closed theorem
  obtain ⟨n, hn⟩ := inlineNest_closed env fn [IBlock.region top nReg body] wf s bfin
    hfn hpc hok hres hrun
  -- extract the region do-while from the singleton block list
  have hrunR : runRegion env nReg body 0 wf (s.base.setLpc 1) = some bfin := by
    rw [runIBsL_cons] at hrun
    cases hx : runIB env wf (IBlock.region top nReg body) s.base with
    | none => rw [hx] at hrun; simp at hrun
    | some x =>
        rw [hx, Option.bind_some, runIBsL_nil] at hrun
        obtain rfl := Option.some.inj hrun
        rw [runIB_region] at hx
        have hlpc : s.base.lpc = 0 := hpc
        rw [hlpc, Nat.zero_add] at hx
        exact hx
  -- reconstruct the bounded fold + schedule (trip count read off the run)
  obtain ⟨m, hm, hbound, _, _⟩ := runRegion_reconstructs env nReg body 0 wf _ bfin hrunR
  have hbound' : runBoundedIBs env wf body 0 m (s.base.setLpc 1)
      = some (bfin.setLpc 1) := by
    simpa using hbound
  -- decode through the fold induction
  have hinit' : decodeM (s.base.setLpc 1) accReg w = some acc0 := by
    rw [decodeM_setLpc]; exact hinit
  have hdec := runBoundedIBs_decodes_nestedDenote env wf body 0 accReg innerCount
    innerUpdate invs (s.base.setLpc 1) acc0 hinit' m
    (fun t _ => hsim t) (bfin.setLpc 1) hbound'
  rw [decodeM_setLpc] at hdec
  exact ⟨n, m, { s with base := bfin }, hm, hn, rfl, hbound', hdec⟩

/-! ## 7. Validate: the GGM depth-3 inline nest re-derived THROUGH the closed
theorem

`ggmBlks` is `ggmProg`'s body as the depth-3 block tree; the machine value
comes from `inlineNest_closed` (the segment lemma applied at all three
labels), and `native_decide` only evaluates the SPEC fold `runIBsL`.  The
result must equal the existing interpreter-level `native_decide` value:
`ggmNestedFold 3 8 2 = 14`, and the recompute sensitivity
`ggmNestedFold 3 16 2 = 28` (`ggm_depth3_num_sensitive`). -/

/-- The innermost GGM region (label `2`, counter `mc`): `acc += 1; mc -= 1`. -/
def ggmInnerBlk : IBlock := .region 2 "mc" [.straight ggmInnerBody]

/-- The middle GGM region (label `1`, counter `mid`): reseed `mc := outlen`,
    run the inner region, `mid -= 1`. -/
def ggmMidBlk : IBlock :=
  .region 1 "mid"
    [ .straight [(LinstrR.Lopn [.reg "mc"] "MOV:64" [.imm 2], MemTag.reg none)]
    , ggmInnerBlk
    , .straight [(LinstrR.Lopn [.reg "mid"] "SUB:64" [.reg "mid", .imm 1],
        MemTag.reg none)] ]

/-- The outer GGM region (label `0`, counter `oc`): recompute the middle trip
    `mid := num >> (jd + 1)` (a real `SHR` on the outer index), run the middle
    region, advance `jd`, decrement `oc`. -/
def ggmOuterBlk : IBlock :=
  .region 0 "oc"
    [ .straight [ (LinstrR.Lopn [.reg "sa"] "ADD:64" [.reg "jd", .imm 1],
          MemTag.reg none)
        , (LinstrR.Lopn [.reg "mid"] "SHR:64" [.reg "num", .reg "sa"],
          MemTag.reg none) ]
    , ggmMidBlk
    , .straight [ (LinstrR.Lopn [.reg "jd"] "ADD:64" [.reg "jd", .imm 1],
          MemTag.reg none)
        , (LinstrR.Lopn [.reg "oc"] "SUB:64" [.reg "oc", .imm 1],
          MemTag.reg none) ] ]

/-- `ggmProg`'s body as a depth-3 block tree (region 0 ⊃ region 1 ⊃ region 2). -/
def ggmBlks : List IBlock := [ggmOuterBlk]

/-- The block tree flattens to exactly `ggmProg`'s body. -/
theorem ggmBlks_flat : flatL ggmBlks = loopLinstrRM 0 "oc" ggmOuterBody := by
  simp [ggmBlks, ggmOuterBlk, ggmMidBlk, ggmInnerBlk, ggmOuterBody, ggmMiddleBody,
    ggmInnerBody, loopLinstrRM]

/-- The singleton program over the flattened tree IS `ggmProg`. -/
theorem ggmBlks_prog : singletonProgM "g" (flatL ggmBlks) = ggmProg := by
  rw [ggmBlks_flat]; rfl

/-- Well-formedness: every straight block of the GGM tree is all-`Lopn`. -/
theorem ggmBlks_ok :
    IBlocksOK (fun _ => none) (singletonProgM "g" (flatL ggmBlks)) ggmBlks := by
  simp only [ggmBlks, ggmOuterBlk, ggmMidBlk, ggmInnerBlk, ggmInnerBody, IBlocksOK_cons,
    IBlocksOK_nil, IBlockOK_region, IBlockOK_straight, and_true]
  and_intros <;>
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      all_goals exact Or.inl ⟨_, _, _, rfl⟩

/-- Label resolution: labels `0`/`1`/`2` occur first at their own region
    positions (`0`/`3`/`5`) in `ggmProg`'s body. -/
theorem ggmBlks_resolve :
    IBlocksResolve (singletonProgM "g" (flatL ggmBlks)) ggmBlks 0 := by
  rw [ggmBlks_flat]
  simp only [ggmBlks, ggmOuterBlk, ggmMidBlk, ggmInnerBlk, ggmInnerBody,
    IBlocksResolve_cons, IBlocksResolve_nil, IBlockResolves_region,
    IBlockResolves_straight, flat_straight, flat_region, flatL_cons, flatL_nil,
    and_true, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The spec fold of the GGM tree at `num = 8` decodes `acc` to
    `ggmNestedFold 3 8 2` (`= 14`): the fold side of the re-derivation,
    evaluated by `native_decide`. -/
theorem ggm_fold_value_8 :
    (runIBsL (fun _ => none) 64 ggmBlks (ggmStart 8).base).map
        (fun b => decodeM b "acc" 64)
      = some (some (BitVec.ofNat 64 (ggmNestedFold 3 8 2))) := by native_decide

/-- The spec fold at `num = 16` decodes to `ggmNestedFold 3 16 2` (`= 28`):
    the middle trip is recomputed from the `num` register. -/
theorem ggm_fold_value_16 :
    (runIBsL (fun _ => none) 64 ggmBlks (ggmStart 16).base).map
        (fun b => decodeM b "acc" 64)
      = some (some (BitVec.ofNat 64 (ggmNestedFold 3 16 2))) := by native_decide

/-- **GGM depth-3, re-derived THROUGH the closed theorem.**  The machine run of
    `ggmProg` (the depth-3 inline nest) halts at a state decoding
    `acc = ggmNestedFold 3 8 2 = 14` — the machine side comes from
    `inlineNest_closed` (the control-flow-aware segment lemma applied at all
    three labels), matching `ggm_depth3_validate`'s interpreter value. -/
theorem ggm_depth3_rederived :
    ∃ (n : Nat) (t : LstatePMC),
      lsemFuelMemLC (fun _ => none) ggmProg n (ggmStart 8) = some t
        ∧ decodeM t.base "acc" 64 = some (BitVec.ofNat 64 (ggmNestedFold 3 8 2)) := by
  cases hb : runIBsL (fun _ => none) 64 ggmBlks (ggmStart 8).base with
  | none =>
      have := ggm_fold_value_8
      rw [hb] at this
      simp at this
  | some b =>
      have hdec : decodeM b "acc" 64 = some (BitVec.ofNat 64 (ggmNestedFold 3 8 2)) := by
        have := ggm_fold_value_8
        rw [hb] at this
        simpa using this
      obtain ⟨n, hn⟩ := inlineNest_closed (fun _ => none) "g" ggmBlks 64 (ggmStart 8) b
        rfl rfl ggmBlks_ok ggmBlks_resolve hb
      rw [ggmBlks_prog] at hn
      exact ⟨n, _, hn, hdec⟩

/-- **Recompute sensitivity, re-derived.**  With `num = 16` the same closed
    theorem gives `acc = ggmNestedFold 3 16 2 = 28`, not `14`: the middle trip
    is read from the recomputed `num >> (jd+1)`, not baked in
    (`ggm_depth3_num_sensitive` ties the two numbers). -/
theorem ggm_recompute_rederived :
    ∃ (n : Nat) (t : LstatePMC),
      lsemFuelMemLC (fun _ => none) ggmProg n (ggmStart 16) = some t
        ∧ decodeM t.base "acc" 64 = some (BitVec.ofNat 64 (ggmNestedFold 3 16 2)) := by
  cases hb : runIBsL (fun _ => none) 64 ggmBlks (ggmStart 16).base with
  | none =>
      have := ggm_fold_value_16
      rw [hb] at this
      simp at this
  | some b =>
      have hdec : decodeM b "acc" 64
          = some (BitVec.ofNat 64 (ggmNestedFold 3 16 2)) := by
        have := ggm_fold_value_16
        rw [hb] at this
        simpa using this
      obtain ⟨n, hn⟩ := inlineNest_closed (fun _ => none) "g" ggmBlks 64 (ggmStart 16) b
        rfl rfl ggmBlks_ok ggmBlks_resolve hb
      rw [ggmBlks_prog] at hn
      exact ⟨n, _, hn, hdec⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestInline
