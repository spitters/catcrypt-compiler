/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFlagLiveness
public import CatCrypt.Crypto.Optimizer.StoreToLoadForward
public import CatCrypt.Crypto.Optimizer.Mem2Reg
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc
public import CatCrypt.Crypto.Optimizer.GraphColoringCoalesce
public import CatCrypt.Crypto.Optimizer.RedundantReloadElim

/-!
# The composed owned x86-`Com` optimizer driver (#555 core)

The owned x86 backend has several verified `List (JInstr 64) → List (JInstr 64)`
passes, each with its own translation-validation theorem.  This module is the
single `optimize : List (JInstr 64) → List (JInstr 64)` that chains them behind
**one** composed denotation-equality theorem — the `x86Dialect` analogue of the
LowCT / `JForProg` driver `Optimizer.Pipeline.optPipelineJ`.

Every owned-emit kernel routes its block through `optimizeX86Block` and gets its
`runBlock`/lowered-`Com` semantics back unchanged, plus its constant-time class
preserved, by three theorem calls (`optimizeX86Block_runBlock` /
`optimizeX86Block_lowering` / `optimizeX86Block_allDirect`), instead of
re-deriving the per-pass wiring.

## Which passes are in the unconditional composed core

A pass may enter the core only if it carries **both**

* an **unconditional, all-blocks, all-states full `runBlock`-equality**
  `∀ blk s, runBlock s (pass blk) = runBlock s blk` — the shape that chains
  transitively with no side hypothesis; and
* an **unconditional constant-time-class preservation**
  `∀ blk, allDirect blk = true → allDirect (pass blk) = true`.

Both are structure fields of `X86Pass`, so the requirement is enforced at
construction: a pass with no CT theorem cannot be wrapped.  The owned x86 passes
with both shapes are:

| pass | transform | `runBlock`-eq theorem | `allDirect` theorem |
|---|---|---|---|
| **store-to-load forward (#372/#412)** | `StoreToLoadForward.storeToLoadForward` | `storeToLoadForward_runBlock` | `storeToLoadForward_allDirect` (§1) |
| **identity-mov drop** | `GraphColoringCoalesce.dropIdMovs` | `runBlock_dropIdMovs` | `allDirect_dropIdMovs` |
| **redundant spill-reload elimination** | `RedundantReloadElim.dropReloads` | `dropReloads_runBlock` | `dropReloads_allDirect` |
| **flag-liveness-guarded MUL→MULX fusion** | `JInstrFlagLiveness.fuseMulxGuarded` | `fuseMulxGuarded_runBlock` | `fuseMulxGuarded_allDirect` |
| identity | `id` | `rfl` | `id` (base case) |

### Why identity-mov drop belongs next to forwarding

`StoreToLoadForward.forwardStep` is length-preserving: it rewrites
`loadMem d base off` into `mov d (.reg r)` even when `r = d`, which is the
self-move `mov d (.reg d)`.  Forwarding therefore leaves one dead self-move in
the block per reload of a just-spilled register, and `dropIdMovs` is the
eliminator for exactly those.  Running it after forwarding also restores
adjacency of the `imul`/`mulx` pairs the fusion pass matches on, which an
interposed self-move would hide.

### Why reload elimination belongs after the identity-mov drop

Forwarding subsumes reload elimination wherever its held environment survives
from the store to the reload: the reload is rewritten to a self-move and the
drop deletes it.  The held environment does not survive a write to the held
register, and the self-move forwarding itself emits *is* such a write.  A block
storing one register to two cells and reloading both illustrates it: the first
reload becomes `mov r (.reg r)`, which kills the binding for the second cell, so
the second reload stays a `loadMem` and forwarding cannot remove it.  Once
`dropIdMovs` deletes the intervening self-move, that store and reload are
adjacent and `dropReloads` recognizes the pair.  Placing the elimination before
the drop finds nothing extra; placing it after finds exactly the reloads the
forwarder's own residue hid.

### Passes that need side-conditions (gated — *not* in the unconditional core)

These have real, proved translation-validation theorems, but **not** of the
unconditional full-equality shape, so they cannot be dropped into the
transitive chain without threading a hypothesis:

* **mem2reg / dead-store elimination (#445, `Mem2Reg.mem2reg_runBlock_agree`)** —
  the certificate is `AgreeOn prot` (agreement on a *protected footprint*), not
  full-state equality.  A whole-program full equality holds only when the
  promoted/dead cells are outside the observable footprint; that is a per-kernel
  obligation, so this pass is gated behind a `prot` precondition.
* **randomized register allocation (#386, `RandomizedRegAlloc.regalloc_runBlock_sound`)** —
  the certificate is a `StateRel ρ` *simulation* under `Function.Injective ρ`
  (and it acts on a *renamed* input state `renameState σ s`), not an identity on
  the same state.  It needs the injectivity/acceptance side-conditions, so it is
  gated.
* **randomized schedule search (#385, `RandomizedScheduleSearch`)** — the
  all-states `runBlock`-equality is proved **per concrete block** (e.g.
  `hoisted_runBlock_eq_input`, and the `feMulBlock_legal_swaps = 8` legality
  count), reusing `legalSwap` disjoint-footprint reasoning; there is no single
  `∀ blk, runBlock s (searchBest … blk) = runBlock s blk` lemma to fold in
  generically (the search picks a winner whose equality is discharged for that
  winner).  Gated on a per-block legality certificate.

* **move coalescing (`GraphColoringCoalesce.coalesce`)** — its certificate is a
  `StateRel (subst d s)` *simulation* under an injectivity side-condition
  (`coalesceStep_runBlock_rel`), i.e. the coalesced run agrees with the original
  after renaming the merged register, not on the same state.  It has an
  unconditional CT theorem (`coalesce_allDirect`) but no unconditional
  `runBlock`-equality, so it stays out of the core.

On a frame-resident / register-resident straight-line kernel the
**unconditional** part of the generic pipeline is forwarding plus the two
shrinking peepholes; the renaming/scheduling levers carry side obligations that
are discharged per kernel.  The reusable *unconditional* driver and the hooks
(`X86Pass`) for callers to extend it are defined below.

## What is proved here

* `optimizeX86Block_runBlock : ∀ blk s, runBlock s (optimizeX86Block blk) =
  runBlock s blk` — the single composed translation-validation certificate every
  owned-emit kernel can call.
* `optimizeX86Block_allDirect` — the composed constant-time-class certificate.
* `optimizeX86Block_lowering` — the dialect/`Com`-level form, via
  `X86Dialect.lowerBlock_denote_closed`.
* `optimizeFeMulBlock_*` — the #555 pilot's bespoke `storeToLoadForward feMulBlock`
  wiring (and its denotation equality) collapses to a **single
  `optimizeX86Block feMulBlock` call**, demonstrating the driver on a real kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (IsDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFlagLiveness
  (fuseMulxGuarded fuseMulxGuarded_runBlock fuseMulxGuarded_allDirect)
open CatCrypt.Crypto.Optimizer.StoreToLoadForward
  (Held forwardStep forwardAux forwardAux_cons storeToLoadForward
   storeToLoadForward_runBlock)
open CatCrypt.Crypto.Optimizer.GraphColoringCoalesce
  (dropIdMovs runBlock_dropIdMovs allDirect_dropIdMovs)
open CatCrypt.Crypto.Optimizer.RedundantReloadElim
  (dropReloads defaultSpillBases dropReloads_runBlock dropReloads_allDirect)
open CatCrypt.Crypto.Optimizer.Mem2Reg
  (mem2reg mem2reg_runBlock_agree AgreeOn)

/-! ## §1  Constant-time-class preservation for store-to-load forwarding

The forwarding scan's only rewrite replaces `loadMem d base off` by
`mov d (.reg r)`; both are direct-addressing instructions, and every other
instruction passes through unchanged.  So the pass keeps every instruction in the
`IsDirect` class, hence keeps `allDirect`. -/

/-- `allDirect` on a cons cell splits into the head's directness and the tail's. -/
theorem allDirect_cons (i : JInstr 64) (is : List (JInstr 64)) :
    allDirect (i :: is) = true ↔ IsDirect i ∧ allDirect is = true := by
  simp [allDirect]

/-- One forwarding step keeps its instruction in the direct-addressing class: the
    rewritten form is either the input instruction or a register move. -/
theorem forwardStep_isDirect (h : Held) {i : JInstr 64} (hd : IsDirect i) :
    IsDirect (forwardStep h i).1 := by
  cases i with
  | loadMem d base off =>
    cases hf : h.find base off with
    | none => simpa [forwardStep, hf] using hd
    | some r => simp only [forwardStep, hf]; split <;> trivial
  | storeMem base off src => cases src <;> exact hd
  | _ => exact hd

/-- The forwarding scan preserves the constant-time class from any held env. -/
theorem forwardAux_allDirect : ∀ (h : Held) (blk : List (JInstr 64)),
    allDirect blk = true → allDirect (forwardAux h blk) = true := by
  intro h blk
  induction blk generalizing h with
  | nil => intro _; rfl
  | cons i is ih =>
    intro hd
    obtain ⟨hi, his⟩ := (allDirect_cons i is).mp hd
    rw [forwardAux_cons]
    exact (allDirect_cons _ _).mpr ⟨forwardStep_isDirect h hi, ih _ his⟩

/-- **Store-to-load forwarding preserves the constant-time class.**  The rewrite
    `loadMem → mov` swaps one direct-addressing instruction for another. -/
theorem storeToLoadForward_allDirect (blk : List (JInstr 64))
    (hd : allDirect blk = true) : allDirect (storeToLoadForward blk) = true :=
  forwardAux_allDirect [] blk hd

/-! ## §2  The unconditional owned-x86 pass record

An `X86Pass` is a `List (JInstr 64) → List (JInstr 64)` rewrite packaged with its
**unconditional all-blocks/all-states** `runBlock`-equality certificate and its
**unconditional** constant-time-class preservation certificate.  This is the
`x86Dialect` analogue of `Optimizer.Pipeline.OptimizerPass`, but phrased on the
owned `JInstr 64` block IR and its `runBlock` machine-state denotation (the
validated `JasminModel`).  Only passes whose translation-validation theorems have
these side-condition-free shapes may be wrapped here; gated passes (mem2reg, RA,
schedule search — see the module docstring) carry their hypotheses separately. -/

/-- An unconditional owned-x86 optimizer pass: a block rewrite together with its
    all-states `runBlock`-preservation theorem and its `allDirect`-preservation
    theorem. -/
structure X86Pass where
  /-- The block rewrite. -/
  run : List (JInstr 64) → List (JInstr 64)
  /-- Translation-validation: the rewrite preserves the `runBlock` final state on
      *every* block and *every* starting state. -/
  runBlock_eq : ∀ (blk : List (JInstr 64)) (s : JState 64),
    runBlock s (run blk) = runBlock s blk
  /-- Constant-time preservation: the rewrite keeps the direct-addressing class on
      *every* block. -/
  allDirect_pres : ∀ (blk : List (JInstr 64)),
    allDirect blk = true → allDirect (run blk) = true

/-- The identity pass (base case for empty pipelines). -/
def idPass : X86Pass where
  run := id
  runBlock_eq := fun _ _ => rfl
  allDirect_pres := fun _ h => h

/-- **Store-to-load forwarding as an `X86Pass`** (#372/#412).  Semantics by
    `storeToLoadForward_runBlock`, constant time by `storeToLoadForward_allDirect`. -/
def storeToLoadForwardPass : X86Pass where
  run := storeToLoadForward
  runBlock_eq := fun blk s => storeToLoadForward_runBlock blk s
  allDirect_pres := storeToLoadForward_allDirect

/-- **Identity-mov drop as an `X86Pass`.**  Deleting every `mov r (.reg r)` is a
    `runBlock` no-op (`runBlock_dropIdMovs`) and leaves a sub-list of the input, so
    it keeps the direct-addressing class (`allDirect_dropIdMovs`).  This is the
    eliminator for the self-moves store-to-load forwarding produces when a reload
    targets the register that already holds the cell. -/
def dropIdMovsPass : X86Pass where
  run := dropIdMovs
  runBlock_eq := fun blk s => runBlock_dropIdMovs blk s
  allDirect_pres := allDirect_dropIdMovs

/-- **Redundant spill-reload elimination as an `X86Pass`.**  Deleting the reload of
    an adjacent store/reload pair against the same frame cell and register is a
    `runBlock` no-op (`dropReloads_runBlock`) and leaves a sub-list of the input, so
    it keeps the direct-addressing class (`dropReloads_allDirect`).  It catches the
    reloads whose store/reload adjacency is only exposed once the self-moves
    forwarding leaves behind are deleted. -/
def dropReloadsPass : X86Pass where
  run := dropReloads defaultSpillBases
  runBlock_eq := fun blk s => dropReloads_runBlock defaultSpillBases blk s
  allDirect_pres := dropReloads_allDirect defaultSpillBases

/-- **Flag-liveness-guarded MUL→MULX fusion as an `X86Pass`.**  The fusion fires
    only where the dropped low `imul`'s flags are dead, so its `runBlock`-equality
    is unconditional (`fuseMulxGuarded_runBlock`); it introduces no instruction, so
    it keeps the direct-addressing class (`fuseMulxGuarded_allDirect`). -/
def fuseMulxGuardedPass : X86Pass where
  run := fuseMulxGuarded
  runBlock_eq := fun blk s => fuseMulxGuarded_runBlock blk s
  allDirect_pres := fuseMulxGuarded_allDirect

/-! ## §3  Pipeline composition

A pipeline is a list of `X86Pass` applied left-to-right.  The composed
`runBlock`-equality and the composed `allDirect`-preservation chain the per-pass
certificates by induction on the list — the exact analogue of
`Optimizer.Pipeline.applyPipeline_denote_eq`. -/

/-- Apply a list of passes left-to-right to a block. -/
def applyX86Pipeline (passes : List X86Pass) (blk : List (JInstr 64)) :
    List (JInstr 64) :=
  passes.foldl (fun acc p => p.run acc) blk

@[simp] theorem applyX86Pipeline_nil (blk : List (JInstr 64)) :
    applyX86Pipeline [] blk = blk := rfl

@[simp] theorem applyX86Pipeline_cons (p : X86Pass) (ps : List X86Pass)
    (blk : List (JInstr 64)) :
    applyX86Pipeline (p :: ps) blk = applyX86Pipeline ps (p.run blk) := rfl

/-- **Composed translation validation for an arbitrary `X86Pass` pipeline.**  For
    every block and every state, running the pipeline-optimized block lands in the
    same `runBlock` final state as the original — the composed owned x86 optimizer
    adds no trust.  Chains each pass's `runBlock_eq` through the `foldl`. -/
theorem applyX86Pipeline_runBlock (passes : List X86Pass) :
    ∀ (blk : List (JInstr 64)) (s : JState 64),
      runBlock s (applyX86Pipeline passes blk) = runBlock s blk := by
  induction passes with
  | nil => intro blk s; rfl
  | cons p ps ih =>
    intro blk s
    rw [applyX86Pipeline_cons, ih (p.run blk) s, p.runBlock_eq blk s]

/-- **Composed constant-time-class preservation for an arbitrary `X86Pass`
    pipeline.**  A block in the direct-addressing class stays in it through the
    whole pipeline; chains each pass's `allDirect_pres` through the `foldl`. -/
theorem applyX86Pipeline_allDirect (passes : List X86Pass) :
    ∀ (blk : List (JInstr 64)), allDirect blk = true →
      allDirect (applyX86Pipeline passes blk) = true := by
  induction passes with
  | nil => intro blk h; exact h
  | cons p ps ih =>
    intro blk h
    rw [applyX86Pipeline_cons]
    exact ih (p.run blk) (p.allDirect_pres blk h)

/-- **Dialect/`Com`-level composed form.**  Through
    `X86Dialect.lowerBlock_denote_closed`, the lowered `Com` of the
    pipeline-optimized block denotes exactly the lowered `Com` of the original on
    every state — denotation preservation against the validated x86 model. -/
theorem applyX86Pipeline_lowering (passes : List X86Pass)
    (blk : List (JInstr 64)) (s : JState 64) :
    (lowerBlock (Γ := []) (applyX86Pipeline passes blk)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) blk).denote (.cons s .nil) := by
  rw [lowerBlock_denote_closed (applyX86Pipeline passes blk) s,
      lowerBlock_denote_closed blk s]
  exact applyX86Pipeline_runBlock passes blk s

/-! ## §4  The default owned-x86 pipeline (the reusable driver)

`defaultX86Pipeline` is the canonical unconditional pipeline every owned-emit
kernel routes through.  The order is forced by what each stage consumes and
produces:

1. **store-to-load forwarding** (#372/#412) recovers register-residence on
   frame-resident bodies and is the identity on already register-resident
   schoolbooks.  It is length-preserving, and it turns a reload of a
   just-spilled register into the self-move `mov d (.reg d)`.
2. **identity-mov drop** deletes those self-moves.  It must follow forwarding —
   before it, there are none to delete — and it is the stage that makes the
   pipeline shrink the block at all.
3. **redundant spill-reload elimination** deletes the reload of an adjacent
   store/reload pair.  It must follow the self-move drop: a reload whose
   forwarding was blocked by a self-move on the reloaded register only becomes
   adjacent to its store once that self-move is gone.  Before the drop it finds
   nothing the forwarder had not already rewritten.
4. **flag-liveness-guarded MUL→MULX fusion** matches an `imul`/`mulx` pair at
   *adjacent* positions, so it must follow both deleting stages: an interposed
   self-move or reload hides the pair from the matcher.

The fusion introduces no moves, so no second drop stage is needed after it.  As
more owned x86 passes acquire the unconditional `runBlock`-equality *and*
`allDirect`-preservation shapes they are appended here and the composed theorems
below pick them up with no further proof.  The mem2reg / spilling-RA passes are
packaged in §4.5 as *gated* passes carrying their real side-conditioned
certificates; they fold into this pipeline via `X86GatedPass.toX86Pass` once a
caller discharges the gate, so they are not in the unconditional default core. -/

/-- The default owned-x86 optimizer pipeline (unconditional core). -/
def defaultX86Pipeline : List X86Pass :=
  [storeToLoadForwardPass, dropIdMovsPass, dropReloadsPass, fuseMulxGuardedPass]

/-- **The reusable owned-x86 `Com→Com` optimizer driver.**  Route an owned-emit
    block through the default unconditional pipeline.  This is the single entry
    point that replaces per-kernel hand-wiring of the individual passes. -/
def optimizeX86Block (blk : List (JInstr 64)) : List (JInstr 64) :=
  applyX86Pipeline defaultX86Pipeline blk

/-- **The composed driver translation-validation theorem (#555 core).**  For every
    block and every state, the optimized block has the same `runBlock` final state
    as the input.  This is the `x86Dialect` analogue of
    `Optimizer.Pipeline.optPipelineJ_denote`: every owned-emit kernel calls *this*
    one theorem to certify the optimizer preserved its semantics. -/
theorem optimizeX86Block_runBlock (blk : List (JInstr 64)) (s : JState 64) :
    runBlock s (optimizeX86Block blk) = runBlock s blk :=
  applyX86Pipeline_runBlock defaultX86Pipeline blk s

/-- **The composed driver constant-time certificate.**  A block in the
    direct-addressing constant-time class stays in it through the whole default
    pipeline, so an owned-emit kernel that discharged `allDirect` on its input
    keeps `allDirect_constant_time` on the optimized output. -/
theorem optimizeX86Block_allDirect (blk : List (JInstr 64))
    (h : allDirect blk = true) : allDirect (optimizeX86Block blk) = true :=
  applyX86Pipeline_allDirect defaultX86Pipeline blk h

/-- **Dialect/`Com`-level composed driver theorem.**  The lowered `Com` of the
    optimized block denotes exactly the lowered `Com` of the input on every
    state. -/
theorem optimizeX86Block_lowering (blk : List (JInstr 64)) (s : JState 64) :
    (lowerBlock (Γ := []) (optimizeX86Block blk)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) blk).denote (.cons s .nil) :=
  applyX86Pipeline_lowering defaultX86Pipeline blk s

/-! ## §4.5  Gated passes: mem2reg / spilling RA wrapped with their *real* certificates

The mem2reg (`Mem2Reg`) and spilling-register-allocation (`SpillingRegAlloc`)
passes are now build-fixed for the `loadMemIdx`/`storeMemIdx` SIB constructors
(commit `fba8d4a8d`), so they are available to wire in here.  But — exactly as the
module docstring's gated-pass table records — neither carries the *unconditional*
all-blocks/all-states full `runBlock`-equality that `X86Pass.runBlock_eq`
requires:

* `mem2reg prot` removes the now-dead scratch stores after forwarding, so its
  final state differs from the input's precisely on those eliminated cells.  Its
  proved translation-validation certificate (`mem2reg_runBlock_agree`) is
  `AgreeOn prot` — agreement on the register file and the *protected* footprint —
  not full-state equality.  Full equality holds only when the eliminated footprint
  is unobservable (a per-kernel `prot`-completeness obligation).
* `spillReloadBlock` interleaves spill-stores and reload-loads; its proved core
  (`SpillingRegAlloc.spillReload_sandwich_runBlock`) is a *single-spill* sandwich
  carrying the `SpillValid` cell-binding invariant `hmid`.  There is no whole-block
  `∀ blk s, runBlock s (spillReloadBlock … blk) = runBlock s blk` lemma — the §6
  multi-spill distinct-cell invariants are still open — so it cannot even be wrapped
  as a *gated whole-block* pass yet without proving those first.

Rather than fake an unconditional certificate, we package mem2reg as a
**gated pass**: a rewrite carrying a per-block/state precondition together with the
`AgreeOn`-form certificate it proves.  A combinator
(`X86GatedPass.toX86Pass`) then lifts *any* gated pass into the unconditional
`X86Pass` chain — and hence into `defaultX86Pipeline` / `applyX86Pipeline_runBlock`
with no reproof — **once the caller discharges the upgrade from the gated
certificate to full `runBlock`-equality** (for mem2reg, the footprint-completeness
proof).  This keeps `defaultX86Pipeline` and the two driver theorems above
unchanged (their proofs are preserved verbatim) while making the fixed passes
first-class, certified citizens of the driver. -/

/-- A **gated** owned-x86 optimizer pass: a block rewrite together with a per-block,
    per-state precondition `pre` and the translation-validation theorem the pass
    actually proves — `runBlock`-equality *under* `pre`.  This is the home for
    passes (mem2reg, spilling RA) whose certificate carries a side hypothesis and so
    cannot populate the unconditional `X86Pass.runBlock_eq` directly. -/
structure X86GatedPass where
  /-- The block rewrite. -/
  run : List (JInstr 64) → List (JInstr 64)
  /-- The per-block/state precondition under which the rewrite is fully sound. -/
  pre : List (JInstr 64) → JState 64 → Prop
  /-- Translation-validation: under `pre blk s`, the rewrite preserves the
      `runBlock` final state. -/
  runBlock_eq_of : ∀ (blk : List (JInstr 64)) (s : JState 64),
    pre blk s → runBlock s (run blk) = runBlock s blk

/-- **Lift a gated pass into the unconditional `X86Pass` chain.**  Given a proof
    that the gate's precondition holds on *every* block and state, the gated
    certificate upgrades to the side-condition-free all-blocks `runBlock`-equality
    `X86Pass` requires; `hct` supplies the constant-time obligation the record's
    second field asks for.  The caller supplies `hpre` (e.g. mem2reg's
    footprint-completeness obligation); the result then folds into
    `defaultX86Pipeline` / `applyX86Pipeline_runBlock` with no further proof. -/
def X86GatedPass.toX86Pass (g : X86GatedPass)
    (hpre : ∀ (blk : List (JInstr 64)) (s : JState 64), g.pre blk s)
    (hct : ∀ blk : List (JInstr 64),
      allDirect blk = true → allDirect (g.run blk) = true) : X86Pass where
  run := g.run
  runBlock_eq := fun blk s => g.runBlock_eq_of blk s (hpre blk s)
  allDirect_pres := hct

/-- **mem2reg / scalar-replacement as a gated pass** (#445, build-fixed in
    `fba8d4a8d`).  The gate is exactly the proved footprint-agreement obligation:
    `mem2reg prot`'s output must equal the input's `runBlock` final state — which
    holds when the dead-store footprint dropped by DSE is unobservable for this
    block.  The TV field is discharged trivially because the precondition *is* the
    target equality; the real content is `mem2reg_runBlock_agree` (`AgreeOn prot`),
    which a caller turns into the precondition by proving footprint completeness.

    We phrase the gate as the final-state equality rather than re-exporting
    `AgreeOn` so that `toX86Pass` composes directly; the obligation a caller
    must discharge (`AgreeOn prot ⇒ equality`, i.e. that `prot` covers the whole
    observable footprint) is named in `mem2regGatedPass_agree`. -/
def mem2regGatedPass (prot : List (String × Int)) : X86GatedPass where
  run := mem2reg prot
  pre := fun blk s => runBlock s (mem2reg prot blk) = runBlock s blk
  runBlock_eq_of := fun _ _ h => h

/-- The side-condition-free certificate `mem2reg` carries: its output
    agrees with the input on the register file and every protected cell, on every
    state.  This is `Mem2Reg.mem2reg_runBlock_agree`, surfaced at the driver so a
    caller can see precisely what must be upgraded (`AgreeOn prot ⇒ equality`,
    via footprint completeness) to discharge `mem2regGatedPass`'s gate. -/
theorem mem2regGatedPass_agree (prot : List (String × Int))
    (blk : List (JInstr 64)) (s : JState 64) :
    AgreeOn prot (runBlock s ((mem2regGatedPass prot).run blk)) (runBlock s blk) :=
  mem2reg_runBlock_agree prot blk s

/-! ## §5  Demonstration on a real kernel: `fe25519_mul`

The #555 pilot (`Fe25519MulOptimized.lean`) wired `storeToLoadForward feMulBlock`
by hand and proved its `runBlock`/lowering equality directly from
`storeToLoadForward_runBlock`.  With the driver, that whole bespoke wiring
collapses to a **single `optimizeX86Block feMulBlock` call**, and the equality
theorems are instances of the composed driver theorems above.  This is the
intended usage every owned-emit kernel adopts. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (feMulBlock)

/-- The Curve25519 field-multiply block routed through the **driver** (one call,
    replacing the pilot's hand-wired `storeToLoadForward feMulBlock`). -/
def optimizeFeMulBlock : List (JInstr 64) := optimizeX86Block feMulBlock

/-- **Driver-optimized `fe25519_mul` = hand kernel, on every state.**  An instance
    of `optimizeX86Block_runBlock` — the pilot's bespoke `runBlock` certificate is
    now a one-liner through the composed driver. -/
theorem optimizeFeMulBlock_runBlock (s : JState 64) :
    runBlock s optimizeFeMulBlock = runBlock s feMulBlock :=
  optimizeX86Block_runBlock feMulBlock s

/-- **Driver-optimized `fe25519_mul` `Com`-denotation equality.**  An instance of
    `optimizeX86Block_lowering`. -/
theorem optimizeFeMulBlock_lowering (s : JState 64) :
    (lowerBlock (Γ := []) optimizeFeMulBlock).denote (.cons s .nil)
      = (lowerBlock (Γ := []) feMulBlock).denote (.cons s .nil) :=
  optimizeX86Block_lowering feMulBlock s

/-! ### Where the drop stage fires

`feMulBlock` is register-resident, so the whole pipeline is the identity on it.
The stage that shrinks a block is the self-move drop, and the shape that produces
a self-move is the reload of a just-spilled register: forwarding rewrites the
reload into `mov r (.reg r)`, and the drop deletes it. -/

/-- A spill of `%r15` followed by its reload — the shape forwarding turns into a
    self-move. -/
def spillReloadDemoBlock : List (JInstr 64) :=
  [ .storeMem "%rsp" 16 (.reg "%r15"),
    .loadMem "%r15" "%rsp" 16,
    .add "%r15" (.reg "%r14") ]

/-- Forwarding is length-preserving here: the reload becomes the self-move
    `mov %r15, %r15`. -/
theorem storeToLoadForward_spillReloadDemo :
    storeToLoadForward spillReloadDemoBlock
      = [ .storeMem "%rsp" 16 (.reg "%r15"),
          .mov "%r15" (.reg "%r15"),
          .add "%r15" (.reg "%r14") ] := rfl

/-- The driver deletes that self-move. -/
theorem optimizeX86Block_spillReloadDemo :
    optimizeX86Block spillReloadDemoBlock
      = [ .storeMem "%rsp" 16 (.reg "%r15"), .add "%r15" (.reg "%r14") ] := rfl

/-- The optimized demo block is strictly shorter than the input, while
    `optimizeX86Block_runBlock` keeps its `runBlock` semantics. -/
theorem optimizeX86Block_spillReloadDemo_shorter :
    (optimizeX86Block spillReloadDemoBlock).length < spillReloadDemoBlock.length := by
  decide

/-! ### Where the reload-elimination stage fires

One register spilled to two cells, both reloaded.  Forwarding rewrites the first
reload to `mov %r15, %r15`, which writes `%r15` and so kills the held binding for
the second cell; the second reload therefore survives forwarding as a `loadMem`.
The identity-mov drop removes the self-move, leaving the second store adjacent to
its reload, and the reload-elimination stage deletes it. -/

/-- A register stored to two frame cells and reloaded from both. -/
def twoCellReloadBlock : List (JInstr 64) :=
  [ .storeMem "%rsp" 8 (.reg "%r15"),
    .storeMem "%rsp" 0 (.reg "%r15"),
    .loadMem "%r15" "%rsp" 8,
    .loadMem "%r15" "%rsp" 0,
    .add "%r15" (.reg "%r14") ]

/-- Forwarding rewrites the first reload to a self-move and leaves the second
    reload in place: the self-move's write to `%r15` killed the binding for the
    cell it reads. -/
theorem storeToLoadForward_twoCellReload :
    storeToLoadForward twoCellReloadBlock
      = [ .storeMem "%rsp" 8 (.reg "%r15"),
          .storeMem "%rsp" 0 (.reg "%r15"),
          .mov "%r15" (.reg "%r15"),
          .loadMem "%r15" "%rsp" 0,
          .add "%r15" (.reg "%r14") ] := rfl

/-- The forwarding + self-move-drop prefix of the pipeline leaves four
    instructions; the reload-elimination stage takes it to three. -/
theorem optimizeX86Block_twoCellReload :
    optimizeX86Block twoCellReloadBlock
      = [ .storeMem "%rsp" 8 (.reg "%r15"),
          .storeMem "%rsp" 0 (.reg "%r15"),
          .add "%r15" (.reg "%r14") ] := rfl

/-- The stage deletes an instruction that forwarding and the self-move drop
    together leave behind: without it the pipeline output has four instructions. -/
theorem dropReloads_twoCellReload_fires :
    (dropIdMovs (storeToLoadForward twoCellReloadBlock)).length = 4 ∧
      (optimizeX86Block twoCellReloadBlock).length = 3 := by
  constructor <;> rfl

/-! ## §6  Remaining passes to fold in (the #555 generalisation work)

To grow the unconditional core, each gated pass needs its translation-validation
theorem re-phrased (or specialised) into the side-condition-free all-blocks
`runBlock`-equality shape `X86Pass` requires:

* **mem2reg / DSE (#445)** — currently `AgreeOn prot`; a full-state-equality
  corollary holds when the promoted/dead footprint is unobservable.  Wrapping it
  as a `gated` pass (carrying `prot` + a footprint-unobservability obligation) is
  the next step.
* **register allocation (#386)** — currently a `StateRel ρ` simulation under
  `Injective ρ`; folding it in requires an output-equality corollary (the
  identity renaming, or a renaming whose observable outputs coincide) plus the
  acceptance check.
* **schedule search (#385)** — currently per-block; folding it in requires a
  generic `searchBest`-output legality certificate (`legalSwap`-disjointness ⇒
  `runBlock`-equality for the chosen winner).
* **move coalescing (`GraphColoringCoalesce.coalesce`)** — currently a `StateRel`
  simulation under injectivity of `subst d s`; folding it in requires an
  output-equality corollary (the merged register's value read back under the
  substitution), on top of the already-proved `coalesce_allDirect`.

The bigger #555 lever the pilot identified is **instruction selection** (the
fused-quotient-estimate reduce): it is upstream of schedule/RA and is *not* a
`JInstr → JInstr` reorder/rename, so it does not fit the `X86Pass` shape at all
and needs a distinct (selection) pass with its own value-semantics certificate.
That unblocks the #568 perf bar. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
