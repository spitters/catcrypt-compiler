/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFlagLiveness
public import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc
public import CatCrypt.Crypto.Optimizer.Mem2Reg
public import CatCrypt.Crypto.Optimizer.RedundantReloadElim
public import CatCrypt.Crypto.Optimizer.SpillSlotReuse

/-!
# A translation-validated composed owned-x86 optimizer pipeline

`X86ComPipeline.lean` gives the *unconditional-core* driver: a pipeline of
`X86Pass`es, each of which carries a **global, all-blocks, all-states**
`runBlock`-equality theorem together with a global `allDirect`-preservation
theorem.  Four owned-x86 transforms have those side-condition-free shapes
(store-to-load forwarding, the identity-mov drop, redundant spill-reload
elimination, the guarded MUL→MULX fusion);
the stronger passes (graph-coloring register allocation, mem2reg / dead-store
elimination, move coalescing, the latency scheduler) remain **per-kernel
opt-ins**: each carries a *side-conditioned* certificate (`AgreeOn`, a
`SpillValid` sandwich, a `StateRel` simulation, a per-block legality proof) that
does not chain transitively without threading a hypothesis.

This module is a **CompCert-style
verified-validator** pipeline that lets those stronger passes become the default
*safely*.  The design is the classic translation-validation gate:

> Run a pass.  Then **check** the result against the input with a *decidable*
> certificate (`chk : List (JInstr 64) → Bool`).  Keep the pass output **only if
> the certificate passes**; otherwise keep the input unchanged.

Because the kept branch is gated by the certificate and the discarded branch is
the identity, the *composed* pipeline's soundness is **unconditional**: for every
block and every state, `runBlock s (composeValidated ps b) = runBlock s b`, with
**no** side hypothesis on `b` or on the passes — every kept step is
validated, and every rejected step is a no-op.  The untrusted optimizer
heuristic (the allocator, the forwarder, the scheduler) can be arbitrarily clever;
trust rests only on the small decidable `chk` and its soundness lemma.

## The validated-pass abstraction

A `ValidatedPass` packages
* `f`   — an arbitrary (untrusted) `List (JInstr 64) → List (JInstr 64)` rewrite;
* `chk` — a decidable per-block certificate `List (JInstr 64) → Bool`;
* `sem_sound` — `chk b = true → ∀ s, runBlock s (f b) = runBlock s b`
  (semantic translation validation: when the certificate fires, the rewrite is
  denotation-preserving on every state); and
* `ct_sound` — `chk b = true → allDirect b = true → allDirect (f b) = true`
  (constant-time preservation: when validated, the rewrite keeps the
  direct-addressing constant-time class).

`applyValidated p b := if p.chk b then p.f b else b` is then **unconditionally**
both denotation-preserving (`applyValidated_sound`) and CT-preserving
(`applyValidated_allDirect`) — the `if` makes both branches agree.  The composed
pipeline folds these with the same unconditional guarantees
(`composeValidated_sound`, `composeValidated_allDirect`).

## Which passes are wired with their certificate

| pass | certificate `chk` | kind |
|---|---|---|
| **store-to-load forwarding** | `allDirect b → allDirect (f b)`, decidably | semantics always sound (`storeToLoadForward_runBlock`), CT gated by a decidable implication check |
| **identity-mov drop** | `fun _ => true` | unconditional — both obligations hold on every block (`runBlock_dropIdMovs`, `allDirect_dropIdMovs`), so the gate never rejects |
| **redundant spill-reload elimination** | `fun _ => true` | unconditional — both obligations hold on every block (`dropReloads_runBlock`, `dropReloads_allDirect`), so the gate never rejects |
| **spill-slot reuse** | `decide (f b = b)` (fires only as a no-op) | conservative — CT is unconditional (`spillRewrite_reuse_allDirect`), but the semantic certificate is the per-cell `SpillValid` sandwich, so the rewrite is wrapped with the always-sound no-op gate |
| **graph-coloring register allocation** | `decide (f b = b)` (fires only as a no-op) | conservative — the allocator's whole-block soundness is a per-spill `SpillValid` sandwich, not an all-blocks `runBlock`-equality, so it is wrapped with the always-sound no-op gate pending the footprint-completeness upgrade |
| **mem2reg / DSE** | `decide (mem2reg prot b = storeToLoadForward b) ∧ allDirect implication` | content-carrying — fires on the sub-domain where the elimination stage is inert, where the pass reduces to store-to-load forwarding and `storeToLoadForward_runBlock` gives the full `runBlock`-equality; store elimination is outside the full-`runBlock` shape (`Mem2Reg`'s certificate there is `AgreeOn prot` only) |

The latency **scheduler** (`SchedulerPass.scheduleBlock`) is *not* in this
pipeline: it operates on the `LowCT`/`BBStmt` IR (`RustExec` semantics), not on
`List (JInstr 64)`/`runBlock`, so it does not fit the `ValidatedPass` shape at all
— it is a distinct-IR pass with its own (already-proved) `scheduleBlock_denote_eq`.

The reading: the **composition framework + its unconditional soundness** is the
deliverable.  It is *populated* with five content-carrying passes (store-to-load
forwarding, the identity-mov drop, redundant spill-reload elimination, MUL→MULX
fusion, and mem2reg on its forwarding-reducible sub-domain, each with a
certificate that fires beyond the identity) and two passes — the graph-coloring
allocator and spill-slot reuse — still behind the conservative-but-sound no-op
gate.  As
such a pass acquires a *decidable* whole-block `runBlock`-equality certificate (the
allocator's `SpillWellFormed` predicate threading `spillReload_sandwich_runBlock`
into a whole-block `spillReloadBlock_runBlock`), its `chk` is strengthened in place
and the composed theorems pick it up with **no** reproof.

## Integration point

In the driver `Com.toLprogPhysAbi` / `compileComToElf`, the block-level optimizer
hook calls `X86ComPipeline.optimizeX86Block`
(`= applyX86Pipeline defaultX86Pipeline`, i.e. forwarding, the identity-mov drop,
reload elimination, and the MUL→MULX fusion).  Substituting
`composeValidated defaultValidatedPipeline` for that call runs the graph-coloring RA,
mem2reg and spill-slot reuse passes by default, each gated by its certificate — semantics and constant-time
preserved unconditionally by `composeValidated_sound` /
`composeValidated_allDirect`.  No proof obligation is pushed to the driver.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.Optimizer.StoreToLoadForward (storeToLoadForward storeToLoadForward_runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFlagLiveness
  (fuseMulxGuarded fuseMulxGuarded_runBlock fuseMulxGuarded_allDirect)
open CatCrypt.Crypto.Optimizer.GraphColoringCoalesce
  (dropIdMovs runBlock_dropIdMovs allDirect_dropIdMovs)
open CatCrypt.Crypto.Optimizer.RedundantReloadElim
  (dropReloads defaultSpillBases dropReloads_runBlock dropReloads_allDirect)
open CatCrypt.Crypto.Optimizer.SpillSlotReuse (reuseSlots spillRewrite_reuse_allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT (spillRewrite)

-- `JInstr w` equality is decidable (every field is a `String`/`Int`/`Nat`/`JOperand`,
-- each with `DecidableEq`).  This lets the conservative `decide (f b = b)` no-op
-- certificate be a `Bool`.
deriving instance DecidableEq for JInstr

/-! ## §0  Agreement modulo a dead cell-set

The footprint-relative certificate a rewrite carries: the outputs agree on every
register, every flag, and every memory cell outside a fixed finite set `D` of dead
spill/scratch cells. The empty dead set is full `JState` equality
(`agreeExcept_nil_iff`), so a pass with `dead = []` recovers the full-state
certificate. -/

/-- `agreeExcept D s t`: the states have equal register files, equal flags, and
    equal memory at every cell `(base, off)` not in the dead set `D`. -/
def agreeExcept (D : List (String × Int)) (s t : JState 64) : Prop :=
  s.regs = t.regs ∧ s.flags = t.flags ∧ ∀ b o, (b, o) ∉ D → s.mem b o = t.mem b o

@[refl] theorem agreeExcept_refl (D : List (String × Int)) (s : JState 64) :
    agreeExcept D s s :=
  ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem agreeExcept_trans {D : List (String × Int)} {s t u : JState 64}
    (h₁ : agreeExcept D s t) (h₂ : agreeExcept D t u) : agreeExcept D s u :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
    fun b o hbo => (h₁.2.2 b o hbo).trans (h₂.2.2 b o hbo)⟩

/-- Weakening by a larger dead set: agreement outside `D` implies agreement outside
    any superset `D'`. -/
theorem agreeExcept_mono {D D' : List (String × Int)} {s t : JState 64}
    (hsub : D ⊆ D') (h : agreeExcept D s t) : agreeExcept D' s t :=
  ⟨h.1, h.2.1, fun b o hbo => h.2.2 b o (fun hd => hbo (hsub hd))⟩

/-- The empty dead set is full `JState` equality. -/
theorem agreeExcept_nil_iff (s t : JState 64) : agreeExcept [] s t ↔ s = t := by
  constructor
  · rintro ⟨hr, hf, hm⟩
    obtain ⟨sr, sf, sm⟩ := s
    obtain ⟨tr, tf, tm⟩ := t
    simp only at hr hf hm
    subst hr; subst hf
    congr 1
    funext b o
    exact hm b o (by simp)
  · rintro rfl
    exact agreeExcept_refl [] s

/-! ## §1  The validated-pass abstraction (the CompCert-style gate) -/

/-- A **translation-validated** owned-x86 optimizer pass: an *untrusted* block
    rewrite `f` together with a **decidable** per-block certificate `chk` and the
    two soundness lemmas the certificate underwrites — semantic preservation
    (`runBlock`-equality on every state) and constant-time preservation
    (`allDirect`).  Both are predicated on `chk b = true`; the guarded application
    `applyValidated` then upgrades them to *unconditional* facts. -/
structure ValidatedPass where
  /-- The untrusted block rewrite (the optimizer heuristic). -/
  f : List (JInstr 64) → List (JInstr 64)
  /-- The decidable per-block translation-validation certificate. -/
  chk : List (JInstr 64) → Bool
  /-- The dead spill/scratch cells the rewrite is permitted to disturb on a given
      input block. A pass whose rewrite preserves the whole state sets this to `[]`
      (`agreeExcept []` is full `JState` equality). -/
  dead : List (JInstr 64) → List (String × Int)
  /-- Footprint-relative semantic translation validation: when the certificate
      fires, the rewrite lands in a `runBlock` final state that agrees with the
      input's on every register, every flag, and every memory cell outside the dead
      set `dead b`, on **every** start state. With `dead b = []` this is full
      `runBlock`-state equality. -/
  sem_sound : ∀ (b : List (JInstr 64)), chk b = true →
    ∀ (s : JState 64), agreeExcept (dead b) (runBlock s (f b)) (runBlock s b)
  /-- Constant-time preservation: when the certificate fires, the rewrite keeps the
      direct-addressing constant-time class (`allDirect`). -/
  ct_sound : ∀ (b : List (JInstr 64)), chk b = true →
    allDirect b = true → allDirect (f b) = true

/-- **The guarded application of a validated pass.**  Run the rewrite only if its
    certificate passes; otherwise keep the input unchanged.  This is the
    translation-validation gate — the kept branch is certified, the rejected branch
    is the identity. -/
def applyValidated (p : ValidatedPass) (b : List (JInstr 64)) : List (JInstr 64) :=
  if p.chk b then p.f b else b

/-- **Footprint-relative soundness of the gate.**  For *every* block and state, the
    gated rewrite lands in a `runBlock` final state that agrees with the input's
    modulo the dead set `dead b` — no side hypothesis.  If the certificate fired,
    `sem_sound` closes it; if not, the output *is* the input (`agreeExcept_refl`). -/
theorem applyValidated_sound_fp (p : ValidatedPass) (b : List (JInstr 64))
    (s : JState 64) :
    agreeExcept (p.dead b) (runBlock s (applyValidated p b)) (runBlock s b) := by
  unfold applyValidated
  split
  · case isTrue h => exact p.sem_sound b h s
  · case isFalse _ => exact agreeExcept_refl _ _

/-- **Full-state soundness of the gate on a pass with an empty dead set.**  When
    `dead b = []` the footprint certificate is full `runBlock`-state equality. -/
theorem applyValidated_sound (p : ValidatedPass) (b : List (JInstr 64))
    (hdead : p.dead b = []) (s : JState 64) :
    runBlock s (applyValidated p b) = runBlock s b := by
  have h := applyValidated_sound_fp p b s
  rw [hdead] at h
  exact (agreeExcept_nil_iff _ _).mp h

/-- **Unconditional constant-time preservation of the gate.**  If the input is in
    the direct-addressing constant-time class, so is the gated output — no side
    hypothesis.  If the certificate fired, `ct_sound` closes it; if not, the output
    *is* the input. -/
theorem applyValidated_allDirect (p : ValidatedPass) (b : List (JInstr 64))
    (h : allDirect b = true) : allDirect (applyValidated p b) = true := by
  unfold applyValidated
  split
  · case isTrue hc => exact p.ct_sound b hc h
  · case isFalse _ => exact h

/-! ## §2  The composed pipeline (a left-fold of gated passes) -/

/-- **The composed validated pipeline.**  Apply a list of validated passes
    left-to-right, each through its translation-validation gate. -/
def composeValidated (ps : List ValidatedPass) (b : List (JInstr 64)) :
    List (JInstr 64) :=
  ps.foldl (fun acc p => applyValidated p acc) b

@[simp] theorem composeValidated_nil (b : List (JInstr 64)) :
    composeValidated [] b = b := rfl

@[simp] theorem composeValidated_cons (p : ValidatedPass) (ps : List ValidatedPass)
    (b : List (JInstr 64)) :
    composeValidated (p :: ps) b = composeValidated ps (applyValidated p b) := rfl

/-- **The composed pipeline's accumulated dead set.**  The union (as an append) of
    each stage's dead set, threaded through the block as it is rewritten. Every stage
    at `dead := fun _ => []` accumulates to `[]`. -/
def composedDead : List ValidatedPass → List (JInstr 64) → List (String × Int)
  | [], _ => []
  | p :: ps, b => p.dead b ++ composedDead ps (applyValidated p b)

/-- **Footprint-relative soundness of the composed pipeline.**  For *every* list of
    validated passes, every block, and every state, the pipeline-optimized block
    lands in a `runBlock` final state that agrees with the input's modulo the
    accumulated dead set `composedDead ps b`.  No side hypothesis: every kept step
    is validated, every rejected step is a no-op.  Induction on the pass list,
    chaining `applyValidated_sound_fp` through `agreeExcept_trans` under the
    weakening `agreeExcept_mono`. -/
theorem composeValidated_sound_fp (ps : List ValidatedPass) :
    ∀ (b : List (JInstr 64)) (s : JState 64),
      agreeExcept (composedDead ps b) (runBlock s (composeValidated ps b)) (runBlock s b) := by
  induction ps with
  | nil => intro b s; exact agreeExcept_refl _ _
  | cons p ps ih =>
    intro b s
    rw [composeValidated_cons]
    show agreeExcept (p.dead b ++ composedDead ps (applyValidated p b))
      (runBlock s (composeValidated ps (applyValidated p b))) (runBlock s b)
    refine agreeExcept_trans
      (agreeExcept_mono (List.subset_append_right _ _) (ih (applyValidated p b) s))
      (agreeExcept_mono (List.subset_append_left _ _) (applyValidated_sound_fp p b s))

/-- The accumulated dead set is `[]` when every pass in the list has an empty dead
    set on every block. -/
theorem composedDead_eq_nil (ps : List ValidatedPass)
    (h : ∀ p ∈ ps, ∀ x, p.dead x = []) : ∀ b, composedDead ps b = [] := by
  induction ps with
  | nil => intro b; rfl
  | cons p ps ih =>
    intro b
    show p.dead b ++ composedDead ps (applyValidated p b) = []
    rw [h p (List.mem_cons_self) b,
        ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) (applyValidated p b)]
    rfl

/-- **Full-state soundness of the composed pipeline when the accumulated dead set is
    empty.**  When `composedDead ps b = []`, the footprint certificate is full
    `runBlock`-state equality — the shape every stage-`dead := []` pipeline recovers,
    with no side hypothesis at the call site (the equality is `rfl`). -/
theorem composeValidated_sound (ps : List ValidatedPass) (b : List (JInstr 64))
    (hdead : composedDead ps b = []) (s : JState 64) :
    runBlock s (composeValidated ps b) = runBlock s b := by
  have h := composeValidated_sound_fp ps b s
  rw [hdead] at h
  exact (agreeExcept_nil_iff _ _).mp h

/-- **Unconditional constant-time preservation of the composed pipeline.**  If the
    input is in the direct-addressing constant-time class, so is the
    pipeline-optimized block.  Induction on the pass list, chaining
    `applyValidated_allDirect`. -/
theorem composeValidated_allDirect (ps : List ValidatedPass) :
    ∀ (b : List (JInstr 64)), allDirect b = true →
      allDirect (composeValidated ps b) = true := by
  induction ps with
  | nil => intro b h; exact h
  | cons p ps ih =>
    intro b h
    rw [composeValidated_cons]
    exact ih (applyValidated p b) (applyValidated_allDirect p b h)

/-- **Dialect/`Com`-level composed form.**  Through
    `X86Dialect.lowerBlock_denote_closed`, the lowered `Com` of the
    pipeline-optimized block denotes exactly the lowered `Com` of the input on
    every state — denotation preservation against the validated x86 model. -/
theorem composeValidated_lowering (ps : List ValidatedPass)
    (b : List (JInstr 64)) (s : JState 64) (hdead : composedDead ps b = []) :
    (lowerBlock (Γ := []) (composeValidated ps b)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) b).denote (.cons s .nil) := by
  rw [lowerBlock_denote_closed (composeValidated ps b) s, lowerBlock_denote_closed b s]
  exact composeValidated_sound ps b hdead s

/-! ## §3  Wrapping the real owned-x86 passes as validated passes -/

/-! ### §3.1  Store-to-load forwarding — the validated pass

Forwarding's semantic certificate is *unconditional* (`storeToLoadForward_runBlock`
holds on every block and state), so its `sem_sound` ignores `chk`.  Its constant-
time certificate is the **decidable implication** `allDirect b → allDirect (f b)`:
when `allDirect b` is false the implication is vacuous (the block is not in the CT
class so there is nothing to preserve); when `allDirect b` is true the certificate
fires iff the forwarded block is still all-direct.  This is a content-
carrying certificate: the `chk` decides exactly the CT-preservation obligation. -/

/-- The decidable constant-time certificate for store-to-load forwarding:
    `allDirect b → allDirect (storeToLoadForward b)`, checked by `decide`. -/
def stlfCT (b : List (JInstr 64)) : Bool :=
  decide (allDirect b = true → allDirect (storeToLoadForward b) = true)

/-- **Store-to-load forwarding as a validated pass.**  The semantic certificate is
    unconditional (`storeToLoadForward_runBlock`); the CT certificate `stlfCT`
    decides the `allDirect`-preservation implication. -/
def storeToLoadForwardValidated : ValidatedPass where
  f := storeToLoadForward
  chk := stlfCT
  dead := fun _ => []
  sem_sound := fun b _ s => (agreeExcept_nil_iff _ _).mpr (storeToLoadForward_runBlock b s)
  ct_sound := fun _b hc hd => (of_decide_eq_true hc) hd

/-! ### §3.1a  Identity-mov drop — the eliminator for forwarding's self-moves

`StoreToLoadForward.forwardStep` rewrites `loadMem d base off` into
`mov d (.reg r)` including when `r = d`, so a reload of a just-spilled register
leaves the self-move `mov d (.reg d)` in the block.
`GraphColoringCoalesce.dropIdMovs` deletes every such self-move.  Both of its
obligations are unconditional theorems — `runBlock_dropIdMovs` (a self-move
writes a register the value it already holds) and `allDirect_dropIdMovs` (the
output is a sub-list of the input) — so its certificate is `fun _ => true`: the
pass fires on every block, with nothing to decide. -/

/-- **Identity-mov drop as a validated pass.**  Both certificates are
    unconditional, so the gate always fires: semantics by `runBlock_dropIdMovs`,
    constant time by `allDirect_dropIdMovs`. -/
def dropIdMovsValidated : ValidatedPass where
  f := dropIdMovs
  chk := fun _ => true
  dead := fun _ => []
  sem_sound := fun b _ s => (agreeExcept_nil_iff _ _).mpr (runBlock_dropIdMovs b s)
  ct_sound := fun b _ hd => allDirect_dropIdMovs b hd

/-! ### §3.1b  Redundant spill-reload elimination — the eliminator for the reloads
the self-move residue hides

`RedundantReloadElim.dropReloads` deletes the reload of an adjacent store/reload
pair against the same frame cell and register.  Store-to-load forwarding already
rewrites such a reload to a self-move wherever its held environment survives from
the store to the reload; it does not survive a write to the held register, and the
self-move forwarding emits *is* such a write.  Once `dropIdMovs` removes that
self-move the store and its reload are adjacent, and this pass deletes the reload.
Both obligations are unconditional — `dropReloads_runBlock` (the reload writes the
register the value the store just read out of it) and `dropReloads_allDirect` (the
output is a sub-list of the input) — so the certificate is `fun _ => true`. -/

/-- **Redundant spill-reload elimination as a validated pass.**  Both certificates
    are unconditional, so the gate always fires: semantics by
    `dropReloads_runBlock`, constant time by `dropReloads_allDirect`. -/
def dropReloadsValidated (bases : List String) : ValidatedPass where
  f := dropReloads bases
  chk := fun _ => true
  dead := fun _ => []
  sem_sound := fun b _ s => (agreeExcept_nil_iff _ _).mpr (dropReloads_runBlock bases b s)
  ct_sound := fun b _ hd => dropReloads_allDirect bases b hd

/-! ### §3.1c  Flag-liveness-guarded MUL→MULX fusion — a content-validated pass

`JInstrFlagLiveness.fuseMulxGuarded` coalesces a low `imul` / widening `mulx` pair
into the single `mulx` exactly where the dropped `imul`'s flags are dead (its
internal backward flag-liveness scan) and the fusion's freshness holds.  Its
`runBlock`-equality (`fuseMulxGuarded_runBlock`) is therefore *unconditional*, so
`sem_sound` ignores `chk`; the `chk` decides the constant-time obligation
`allDirect b → allDirect (fuseMulxGuarded b)`, discharged by
`fuseMulxGuarded_allDirect`.  Unlike the no-op-gated wrappers below, this pass
fires on every block (the fusion decision is made inside the rewrite). -/

/-- The decidable constant-time certificate for the guarded MUL→MULX fusion:
    `allDirect b → allDirect (fuseMulxGuarded b)`, checked by `decide`. -/
def fuseMulxCT (b : List (JInstr 64)) : Bool :=
  decide (allDirect b = true → allDirect (fuseMulxGuarded b) = true)

/-- **Flag-liveness-guarded MUL→MULX fusion as a validated pass.**  The semantic
    certificate is unconditional (`fuseMulxGuarded_runBlock`); the CT certificate
    `fuseMulxCT` decides the `allDirect`-preservation implication (always true by
    `fuseMulxGuarded_allDirect`). -/
def fuseMulxValidated : ValidatedPass where
  f := fuseMulxGuarded
  chk := fuseMulxCT
  dead := fun _ => []
  sem_sound := fun b _ s => (agreeExcept_nil_iff _ _).mpr (fuseMulxGuarded_runBlock b s)
  ct_sound := fun _b hc hd => (of_decide_eq_true hc) hd

/-! ### §3.2  Certificates for the stronger passes

The graph-coloring register allocator and mem2reg do *not* carry an unconditional
all-blocks `runBlock`-equality (their proved certificates are a `SpillValid`
sandwich and `AgreeOn prot` respectively — see the module docstring).  Two shapes
are used here.  For a pass with no proved side condition that reaches full
`runBlock`-equality, we fall back on the **always-sound no-op gate**
`decide (f b = b)`: the pass fires only on blocks it leaves unchanged, where
soundness and CT preservation are trivial.  The graph-coloring allocator sits here,
pending the whole-block `spillReloadBlock` `runBlock`-equality theorem.  mem2reg
instead carries a content-carrying certificate that decides its full-state
side condition (§3.3): the pass reduces to store-to-load forwarding, whose
`runBlock`-equality is unconditional. -/

/-- The conservative no-op certificate: fire only when the rewrite is the identity
    on this block.  Always sound (`f b = b ⇒ runBlock s (f b) = runBlock s b` and
    `allDirect (f b) = allDirect b`). -/
def noOpCert (f : List (JInstr 64) → List (JInstr 64)) (b : List (JInstr 64)) : Bool :=
  decide (f b = b)

/-- **Wrap any rewrite behind the conservative no-op gate as a validated pass.**
    The certificate fires only where `f b = b`, so both soundness obligations are
    discharged by rewriting with that equality.  This is the always-available
    fallback for a pass without a proved unconditional whole-block certificate. -/
def conservativeValidated (f : List (JInstr 64) → List (JInstr 64)) : ValidatedPass where
  f := f
  chk := noOpCert f
  dead := fun _ => []
  sem_sound := fun b hc s => (agreeExcept_nil_iff _ _).mpr (by
    rw [show f b = b from of_decide_eq_true hc])
  ct_sound := fun b hc hd => by
    rw [show f b = b from of_decide_eq_true hc]; exact hd

/-- **Graph-coloring register allocation as a (conservatively-gated) validated
    pass**.  The allocator emits a `name ↦ Slot` decision list materialized
    by `SpillingRegAlloc.spillReloadBlock`; its proved soundness is the per-spill
    `SpillValid` sandwich (`GraphColoringRegAlloc.graphColor_spillReload_sound`),
    not an all-blocks `runBlock`-equality, so it is wrapped behind the no-op gate
    pending the footprint-completeness upgrade. -/
def graphColorRAValidated (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String) : ValidatedPass :=
  conservativeValidated (fun b =>
    CatCrypt.Crypto.Optimizer.SpillingRegAlloc.spillReloadBlock
      (CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc.graphColorAlloc pinned frameBase b)
      spillBase b)

/-! ### §3.3  mem2reg gated by its full-state side condition

`Mem2Reg.mem2reg prot = dse prot ∘ storeToLoadForward`.  The forwarding stage is
unconditionally `runBlock`-preserving (`storeToLoadForward_runBlock`); the
elimination stage `dse` preserves only the protected footprint (`AgreeOn prot`),
and drops the value at an eliminated cell, so full-state `runBlock`-equality holds
exactly when `dse` is inert on the forwarded block.  That condition is decidable
(`mem2regDseInert`), and on it the pass equals `storeToLoadForward` and inherits its
full `runBlock`-equality — a content-carrying certificate that fires beyond the
identity. -/

/-- The decidable side condition under which `Mem2Reg.mem2reg` preserves the **full**
    `runBlock` state: its dead-store-elimination stage removes nothing, so the pass
    reduces to store-to-load forwarding on this block
    (`mem2reg prot b = storeToLoadForward b`).  Whenever this holds the pass output is
    `runBlock`-equal to the input by `storeToLoadForward_runBlock`, which is
    unconditional.  This is the transform's side condition — it fires on any
    block whose forwarding is active but whose forwarded form has no dead store to
    eliminate, so the pass is not restricted to the identity. -/
def mem2regDseInert (prot : List (String × Int)) (b : List (JInstr 64)) : Bool :=
  decide (CatCrypt.Crypto.Optimizer.Mem2Reg.mem2reg prot b = storeToLoadForward b)

/-- The decidable constant-time side condition for the forwarding-reducible mem2reg:
    `allDirect b → allDirect (storeToLoadForward b)`, checked by `decide`. -/
def mem2regCT (b : List (JInstr 64)) : Bool :=
  decide (allDirect b = true → allDirect (storeToLoadForward b) = true)

/-- **mem2reg / dead-store elimination as a validated pass**.
    `Mem2Reg.mem2reg`'s whole-block certificate is `AgreeOn prot` (agreement on the
    protected footprint only), which is strictly weaker than the full-state
    `runBlock`-equality this abstraction requires: when the pass eliminates a store,
    the final memory differs at the dropped cell.  The certificate `chk`
    therefore fires exactly on the sub-domain where the elimination stage is inert
    (`mem2regDseInert`), where the pass reduces to store-to-load forwarding and
    `storeToLoadForward_runBlock` supplies the full `runBlock`-equality, gated in CT
    by the decidable `allDirect`-preservation implication `mem2regCT`.  The pass fires
    (is non-identity) on any such block whose forwarding is active. -/
def mem2regValidated (prot : List (String × Int)) : ValidatedPass where
  f := CatCrypt.Crypto.Optimizer.Mem2Reg.mem2reg prot
  chk := fun b => mem2regDseInert prot b && mem2regCT b
  dead := fun _ => []
  sem_sound := fun b hc s => (agreeExcept_nil_iff _ _).mpr (by
    rw [Bool.and_eq_true] at hc
    have heq : CatCrypt.Crypto.Optimizer.Mem2Reg.mem2reg prot b = storeToLoadForward b :=
      of_decide_eq_true hc.1
    rw [heq]; exact storeToLoadForward_runBlock b s)
  ct_sound := fun b hc hd => by
    rw [Bool.and_eq_true] at hc
    have heq : CatCrypt.Crypto.Optimizer.Mem2Reg.mem2reg prot b = storeToLoadForward b :=
      of_decide_eq_true hc.1
    rw [heq]; exact (of_decide_eq_true hc.2) hd

/-! ### §3.4  Spill-slot reuse behind the no-op gate

`SpillSlotReuse.reuseSlots` packs the spilled names of a block onto shared frame
offsets by greedy left-edge interval coloring, and the spill rewrite consumes the
packed map exactly as it consumes the distinct-cell one.  Its constant-time
obligation is discharged **unconditionally** by
`SpillSlotReuse.spillRewrite_reuse_allDirect`: a shared offset is still a
compile-time constant, so every inserted reload and store is still a
constant-displacement `loadMem`/`storeMem`.  Its semantic certificate is the
per-cell `SpillValid` sandwich `SpillSlotReuse.singleReuse_noClobber_runBlock`, the
same shape the graph-coloring allocator carries and not an all-blocks
`runBlock`-equality, so the rewrite enters through the conservative no-op gate
(§3.2) — the pass fires only where it leaves the block unchanged, which is exactly
where the allocator spills nothing. -/

/-- The block rewrite of the reuse pass: allocate with the graph-coloring allocator,
    repack the spilled names onto shared frame offsets, and materialize the packed
    map through the spill rewrite. -/
def reuseSpillRewrite (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String) (b : List (JInstr 64)) : List (JInstr 64) :=
  spillRewrite id spillBase
    (reuseSlots
      (CatCrypt.Crypto.Optimizer.SpillingRegAlloc.spillSlotOf
        (CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc.graphColorAlloc pinned frameBase b))
      frameBase
      (CatCrypt.Crypto.Optimizer.SpillingRegAlloc.liveRanges b))
    b

/-- **Spill-slot reuse as a (conservatively-gated) validated pass.**  Constant time
    is unconditional (`spillRewrite_reuse_allDirect`); the semantic certificate is the
    per-cell `SpillValid` sandwich, so the rewrite is gated by `noOpCert`. -/
def spillSlotReuseValidated
    (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String) : ValidatedPass where
  f := reuseSpillRewrite pinned frameBase spillBase
  chk := noOpCert (reuseSpillRewrite pinned frameBase spillBase)
  dead := fun _ => []
  sem_sound := fun b hc s => (agreeExcept_nil_iff _ _).mpr (by
    rw [show reuseSpillRewrite pinned frameBase spillBase b = b from of_decide_eq_true hc])
  ct_sound := fun b _ hd =>
    spillRewrite_reuse_allDirect id spillBase
      (CatCrypt.Crypto.Optimizer.SpillingRegAlloc.spillSlotOf
        (CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc.graphColorAlloc pinned frameBase b))
      frameBase
      (CatCrypt.Crypto.Optimizer.SpillingRegAlloc.liveRanges b) b hd

/-! ## §4  The candidate default validated pipeline -/

/-- **The candidate default validated pipeline.**  Store-to-load forwarding, the
    identity-mov drop that eliminates the self-moves forwarding produces, redundant
    spill-reload elimination, the flag-liveness-guarded MUL→MULX fusion, and mem2reg
    (each with a certificate that fires beyond the identity) followed by the
    graph-coloring register allocator and spill-slot reuse (both behind the
    conservative no-op gate, pending a whole-block `runBlock`-equality theorem).

    The order is the one each stage's input demands.  The self-move drop sits
    immediately after forwarding because that is what creates the self-moves.
    Reload elimination sits after the drop because a reload whose forwarding was
    blocked by a self-move on the reloaded register only becomes adjacent to its
    store once that self-move is gone.  Both deleting stages precede the fusion,
    which matches an `imul`/`mulx` pair only at adjacent positions.  The two
    allocator-side rewrites come last, on the block the peepholes have already
    shrunk: they read live ranges, and a shorter block has shorter ones.

    Every pass is gated by its decidable certificate, so `composeValidated` over
    this list is unconditionally semantics- and CT-preserving — the property that
    lets these passes become the *default*.  The `prot`/`pinned`/frame parameters
    are the per-driver placement choices supplied at the integration site. -/
def defaultValidatedPipeline
    (prot : List (String × Int))
    (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String) : List ValidatedPass :=
  [ storeToLoadForwardValidated,
    dropIdMovsValidated,
    dropReloadsValidated defaultSpillBases,
    fuseMulxValidated,
    mem2regValidated prot,
    graphColorRAValidated pinned frameBase spillBase,
    spillSlotReuseValidated pinned frameBase spillBase ]

/-- **The default validated pipeline is unconditionally semantics-preserving.**
    An instance of `composeValidated_sound` — every owned-emit kernel can route its
    block through this pipeline and recover its `runBlock` semantics unchanged by
    this one theorem, with the stronger passes enabled. -/
theorem defaultValidatedPipeline_sound
    (prot : List (String × Int))
    (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String)
    (b : List (JInstr 64)) (s : JState 64) :
    runBlock s (composeValidated (defaultValidatedPipeline prot pinned frameBase spillBase) b)
      = runBlock s b :=
  composeValidated_sound _ b rfl s

/-- **The default validated pipeline preserves the constant-time class.**  An
    instance of `composeValidated_allDirect`. -/
theorem defaultValidatedPipeline_allDirect
    (prot : List (String × Int))
    (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String)
    (b : List (JInstr 64)) (h : allDirect b = true) :
    allDirect (composeValidated (defaultValidatedPipeline prot pinned frameBase spillBase) b)
      = true :=
  composeValidated_allDirect _ b h

/-! ## §5  Worked demonstration on a real kernel: `fe25519_mul`

We instantiate the composed-pipeline soundness on the Curve25519 field-multiply
block (`Fe25519MulKernel.feMulBlock`).  The composed
validated pipeline lands in the same `runBlock` final state as the hand kernel on
every machine state, and preserves the `allDirect` constant-time class. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (feMulBlock)

/-- A concrete instantiation of the default validated pipeline's placement
    parameters for the demonstration (no protected footprint, no pinned registers,
    frame base `0`, spill base `%rbp`). -/
def demoPipeline : List ValidatedPass :=
  defaultValidatedPipeline [] [] 0 "%rbp"

/-- **The composed validated pipeline on `fe25519_mul` = the hand kernel, on every
    state.**  An instance of `composeValidated_sound` — the demonstration that the
    composition framework preserves semantics on a real owned-emit kernel with the
    stronger passes wired in. -/
theorem demo_runBlock (s : JState 64) :
    runBlock s (composeValidated demoPipeline feMulBlock) = runBlock s feMulBlock :=
  composeValidated_sound demoPipeline feMulBlock rfl s

/-- **The composed validated pipeline preserves `fe25519_mul`'s `Com`
    denotation.**  An instance of `composeValidated_lowering`. -/
theorem demo_lowering (s : JState 64) :
    (lowerBlock (Γ := []) (composeValidated demoPipeline feMulBlock)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) feMulBlock).denote (.cons s .nil) :=
  composeValidated_lowering demoPipeline feMulBlock s rfl

/-! ## §6  Passes as first-class named entities: a registered pass pipeline (D5c)

§1–§5 treat a pipeline as an anonymous `List ValidatedPass` built by hand at each
call site.  This section promotes passes to **first-class named entities**: each
`ValidatedPass` is paired with a stable `name` (and a short human-readable
`descr`) in a **registry**, and a pipeline is assembled by *naming* the passes to
run (`pipelineByName ["store-to-load-forward", …]`) rather than by reconstructing
the list literal.  The packaging is purely additive — the registry resolves to the
*same* `ValidatedPass` values, so `composeValidated (pipelineByName names)` is an
instance of the §2 fold and **every §2 soundness theorem applies verbatim**, with
no reproof.  The named form makes pipelines configuration-driven (a name list is
serialisable / overridable per driver) while the trust story is unchanged: it
still rests only on each pass's decidable `chk` and the `composeValidated_*`
theorems. -/

/-- A **registered** validated pass: a `ValidatedPass` (the gate + its two
    soundness certificates) promoted to a first-class named entity by a stable
    `name` and a short human-readable `descr`.  Registration adds *only* metadata —
    `toValidatedPass` recovers the underlying pass unchanged, so the §2 fold and its
    soundness theorems apply to the resolved passes verbatim. -/
structure RegisteredPass extends ValidatedPass where
  /-- The stable lookup key for this pass (used by `pipelineByName`). -/
  name : String
  /-- A short human-readable description of what the pass does. -/
  descr : String

/-- The default placement parameters that `graphColorRAValidated` / `mem2regValidated`
    are partially applied with for registration.  These are the per-driver placement
    choices; the registry pins the demonstration values (no protected footprint, no
    pinned registers, frame base `0`, spill base `%rbp`) so that registered passes
    are nullary-resolvable by name.  A driver that needs different placement builds
    its `RegisteredPass` list directly from the §3 constructors. -/
def registryPlacement : (List (String × Int)) ×
    CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc × Int × String :=
  ([], [], 0, "%rbp")

/-- **The pass registry.**  Each of the §3 owned-x86 passes promoted to a first-class
    named entity.  The names are the stable lookup keys consumed by `pipelineByName`;
    the registry pins the demonstration placement parameters (`registryPlacement`) so
    each pass is resolvable by name alone. -/
def passRegistry : List RegisteredPass :=
  [ { toValidatedPass := storeToLoadForwardValidated
      name := "store-to-load-forward"
      descr := "store-to-load forwarding; CT gated by a decidable allDirect-preservation implication" },
    { toValidatedPass := dropIdMovsValidated
      name := "drop-id-movs"
      descr := "deletion of the self-moves store-to-load forwarding leaves behind; semantics and CT both unconditional" },
    { toValidatedPass := dropReloadsValidated defaultSpillBases
      name := "drop-reloads"
      descr := "deletion of the reload of an adjacent store/reload pair against a frame cell; semantics and CT both unconditional" },
    { toValidatedPass := fuseMulxValidated
      name := "fuse-mulx"
      descr := "flag-liveness-guarded MUL→MULX fusion; semantics unconditional, CT gated by a decidable allDirect-preservation implication" },
    { toValidatedPass := mem2regValidated registryPlacement.1
      name := "mem2reg"
      descr := "mem2reg / dead-store elimination; fires on the forwarding-reducible sub-domain via storeToLoadForward_runBlock, CT gated by a decidable allDirect-preservation implication" },
    { toValidatedPass :=
        graphColorRAValidated registryPlacement.2.1 registryPlacement.2.2.1 registryPlacement.2.2.2
      name := "graph-color-ra"
      descr := "graph-coloring register allocation; no-op-gated pending SpillValid footprint-completeness" },
    { toValidatedPass :=
        spillSlotReuseValidated registryPlacement.2.1 registryPlacement.2.2.1 registryPlacement.2.2.2
      name := "spill-slot-reuse"
      descr := "spill-slot reuse (P6); CT unconditional, no-op-gated pending a whole-block runBlock-equality for the packed spill rewrite" } ]

/-- **Registry lookup.**  Resolve a pass name to its underlying `ValidatedPass`
    (dropping the `name`/`descr` metadata), or `none` if no pass is registered under
    that name. -/
def registryLookup (nm : String) : Option ValidatedPass :=
  (passRegistry.find? (fun rp => rp.name == nm)).map RegisteredPass.toValidatedPass

/-- **Build a pipeline from a name list.**  Resolve each name through the registry,
    dropping unknown names.  The result is an ordinary `List ValidatedPass`, so
    `composeValidated (pipelineByName names)` is an instance of the §2 fold. -/
def pipelineByName (names : List String) : List ValidatedPass :=
  names.filterMap registryLookup

/-- Every registered pass has an empty dead set on every block. -/
theorem passRegistry_dead_nil (rp : RegisteredPass) (h : rp ∈ passRegistry) :
    ∀ x, rp.toValidatedPass.dead x = [] := by
  simp only [passRegistry, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> intro x <;> rfl

/-- A name-resolved pass has an empty dead set on every block. -/
theorem registryLookup_dead_nil {nm : String} {p : ValidatedPass}
    (h : registryLookup nm = some p) : ∀ x, p.dead x = [] := by
  unfold registryLookup at h
  obtain ⟨rp, hfind, hrp⟩ := Option.map_eq_some_iff.mp h
  rw [← hrp]
  exact passRegistry_dead_nil rp (List.mem_of_find?_eq_some hfind)

/-- A named pipeline accumulates to an empty dead set: every resolved pass has an
    empty dead set, so `composedDead_eq_nil` applies. -/
theorem composedDead_pipelineByName (names : List String) (b : List (JInstr 64)) :
    composedDead (pipelineByName names) b = [] := by
  refine composedDead_eq_nil _ (fun p hp x => ?_) b
  rw [pipelineByName, List.mem_filterMap] at hp
  obtain ⟨nm, _, hnm⟩ := hp
  exact registryLookup_dead_nil hnm x

/-- **A named pipeline is unconditionally semantics-preserving.**  A thin corollary
    of `composeValidated_sound` applied to the resolved list — the existing soundness
    theorem carries over to the named form with no reproof. -/
theorem pipelineByName_sound (names : List String) (b : List (JInstr 64)) (s : JState 64) :
    runBlock s (composeValidated (pipelineByName names) b) = runBlock s b :=
  composeValidated_sound (pipelineByName names) b (composedDead_pipelineByName names b) s

/-- **A named pipeline preserves the constant-time class.**  A thin corollary of
    `composeValidated_allDirect` applied to the resolved list. -/
theorem pipelineByName_allDirect (names : List String) (b : List (JInstr 64))
    (h : allDirect b = true) :
    allDirect (composeValidated (pipelineByName names) b) = true :=
  composeValidated_allDirect (pipelineByName names) b h

/-- **A named pipeline preserves the `Com` denotation.**  A thin corollary of
    `composeValidated_lowering`. -/
theorem pipelineByName_lowering (names : List String) (b : List (JInstr 64)) (s : JState 64) :
    (lowerBlock (Γ := []) (composeValidated (pipelineByName names) b)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) b).denote (.cons s .nil) :=
  composeValidated_lowering (pipelineByName names) b s (composedDead_pipelineByName names b)

/-- **The registry round-trips the default pipeline.**  Resolving the pass names in
    the documented order reproduces exactly `defaultValidatedPipeline` at the
    registry's pinned placement (`registryPlacement`) — the named form and the
    hand-built §4 list are definitionally the same pipeline, so registration loses
    nothing. -/
theorem pipelineByName_defaultValidatedPipeline :
    pipelineByName
      ["store-to-load-forward", "drop-id-movs", "drop-reloads", "fuse-mulx", "mem2reg",
       "graph-color-ra", "spill-slot-reuse"]
      = defaultValidatedPipeline
          registryPlacement.1 registryPlacement.2.1 registryPlacement.2.2.1 registryPlacement.2.2.2 :=
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
