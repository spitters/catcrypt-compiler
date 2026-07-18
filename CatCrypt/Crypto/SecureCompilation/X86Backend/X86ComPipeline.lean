/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
import CatCrypt.Crypto.Optimizer.StoreToLoadForward
import CatCrypt.Crypto.Optimizer.Mem2Reg
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# The composed owned x86-`Com` optimizer driver (#555 core)

The owned x86 backend has several verified `List (JInstr 64) → List (JInstr 64)`
passes, each with its own translation-validation theorem.  Until now they were
only ever invoked **individually** (see `Fe25519MulOptimized.lean`, the #555
pilot, which wires `storeToLoadForward` by hand).  There was no single
`optimize : List (JInstr 64) → List (JInstr 64)` chaining them with **one**
composed denotation-equality theorem — the `x86Dialect` analogue of the
LowCT / `JForProg` driver `Optimizer.Pipeline.optPipelineJ`.

This module is that driver.  Every owned-emit kernel can now route its block
through `optimizeX86Block` and get its `runBlock`/lowered-`Com` semantics back
unchanged by **one** theorem call (`optimizeX86Block_runBlock` /
`optimizeX86Block_lowering`), instead of re-deriving the per-pass wiring.

## Which passes are in the unconditional composed core

The driver composes only passes carrying an **unconditional, all-blocks,
all-states full `runBlock`-equality**

```
∀ blk s, runBlock s (pass blk) = runBlock s blk
```

— the shape that chains transitively with no side hypothesis.  As of #555 the
owned x86 passes with *that* shape are:

| pass | transform | all-states `runBlock`-eq theorem | in core? |
|---|---|---|---|
| **store-to-load forward (#372/#412)** | `StoreToLoadForward.storeToLoadForward` | `storeToLoadForward_runBlock` (all blocks, all states) | ✅ **yes** |
| identity | `id` | `rfl` | ✅ (base case) |

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

The honest reading mirrors the pilot's finding: on a frame-resident /
register-resident straight-line kernel the **unconditional** part of the generic
pipeline is store-to-load forwarding; the renaming/scheduling levers carry side
obligations that are discharged per kernel.  This file gives the reusable
*unconditional* driver and the hooks (`X86Pass`) for callers to extend it.

## What is proved here

* `optimizeX86Block_runBlock : ∀ blk s, runBlock s (optimizeX86Block blk) =
  runBlock s blk` — the single composed translation-validation certificate every
  owned-emit kernel can call.
* `optimizeX86Block_lowering` — the dialect/`Com`-level form, via
  `X86Dialect.lowerBlock_denote_closed`.
* `optimizeFeMulBlock_*` — the #555 pilot's bespoke `storeToLoadForward feMulBlock`
  wiring (and its denotation equality) collapses to a **single
  `optimizeX86Block feMulBlock` call**, demonstrating the driver on a real kernel.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.Optimizer.StoreToLoadForward
  (storeToLoadForward storeToLoadForward_runBlock)
open CatCrypt.Crypto.Optimizer.Mem2Reg
  (mem2reg mem2reg_runBlock_agree AgreeOn)

/-! ## §1  The unconditional owned-x86 pass record

An `X86Pass` is a `List (JInstr 64) → List (JInstr 64)` rewrite packaged with its
**unconditional all-blocks/all-states** `runBlock`-equality certificate.  This is
the `x86Dialect` analogue of `Optimizer.Pipeline.OptimizerPass`, but phrased on
the owned `JInstr 64` block IR and its `runBlock` machine-state denotation (the
validated `JasminModel`).  Only passes whose translation-validation theorem has
this side-condition-free shape may be wrapped here; gated passes (mem2reg, RA,
schedule search — see the module docstring) carry their hypotheses separately. -/

/-- An unconditional owned-x86 optimizer pass: a block rewrite together with its
    all-states `runBlock`-preservation theorem. -/
structure X86Pass where
  /-- The block rewrite. -/
  run : List (JInstr 64) → List (JInstr 64)
  /-- Translation-validation: the rewrite preserves the `runBlock` final state on
      *every* block and *every* starting state. -/
  runBlock_eq : ∀ (blk : List (JInstr 64)) (s : JState 64),
    runBlock s (run blk) = runBlock s blk

/-- The identity pass (base case for empty pipelines). -/
def idPass : X86Pass where
  run := id
  runBlock_eq := fun _ _ => rfl

/-- **Store-to-load forwarding as an `X86Pass`** (#372/#412).  The one owned x86
    transform whose translation-validation theorem is an unconditional all-blocks
    full `runBlock`-equality. -/
def storeToLoadForwardPass : X86Pass where
  run := storeToLoadForward
  runBlock_eq := fun blk s => storeToLoadForward_runBlock blk s

/-! ## §2  Pipeline composition

A pipeline is a list of `X86Pass` applied left-to-right.  The composed
`runBlock`-equality chains the per-pass certificates by induction on the list —
the exact analogue of `Optimizer.Pipeline.applyPipeline_denote_eq`. -/

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

/-! ## §3  The default owned-x86 pipeline (the reusable driver)

`defaultX86Pipeline` is the canonical unconditional pipeline every owned-emit
kernel routes through.  At the current owned-x86 pass coverage it is the single
unconditional pass — store-to-load forwarding (#372/#412) — which recovers
register-residence on frame-resident bodies and is the identity on already
register-resident schoolbooks.  As more owned x86 passes acquire the
unconditional all-blocks `runBlock`-equality shape they are appended here and the
composed theorem below picks them up with no further proof.  The now-build-fixed
mem2reg / spilling-RA passes (`fba8d4a8d`) are packaged in §3.5 as *gated* passes
carrying their real side-conditioned certificates; they fold into this pipeline
via `X86GatedPass.toX86Pass` once a caller discharges the gate, so they are not in
the unconditional default core. -/

/-- The default owned-x86 optimizer pipeline (unconditional core). -/
def defaultX86Pipeline : List X86Pass := [storeToLoadForwardPass]

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

/-- **Dialect/`Com`-level composed driver theorem.**  The lowered `Com` of the
    optimized block denotes exactly the lowered `Com` of the input on every
    state. -/
theorem optimizeX86Block_lowering (blk : List (JInstr 64)) (s : JState 64) :
    (lowerBlock (Γ := []) (optimizeX86Block blk)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) blk).denote (.cons s .nil) :=
  applyX86Pipeline_lowering defaultX86Pipeline blk s

/-! ## §3.5  Gated passes: mem2reg / spilling RA wrapped with their *real* certificates

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
genuine `AgreeOn`-form certificate it proves.  A combinator
(`X86GatedPass.toX86Pass`) then lifts *any* gated pass into the unconditional
`X86Pass` chain — and hence into `defaultX86Pipeline` / `applyX86Pipeline_runBlock`
with no reproof — **once the caller discharges the upgrade from the gated
certificate to full `runBlock`-equality** (for mem2reg, the footprint-completeness
proof).  This keeps `defaultX86Pipeline` and the two driver theorems above
unchanged (their proofs are preserved verbatim) while making the fixed passes
first-class, honestly-certified citizens of the driver. -/

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
    `X86Pass` requires.  The caller supplies `hpre` (e.g. mem2reg's
    footprint-completeness obligation); the result then folds into
    `defaultX86Pipeline` / `applyX86Pipeline_runBlock` with no further proof. -/
def X86GatedPass.toX86Pass (g : X86GatedPass)
    (hpre : ∀ (blk : List (JInstr 64)) (s : JState 64), g.pre blk s) : X86Pass where
  run := g.run
  runBlock_eq := fun blk s => g.runBlock_eq_of blk s (hpre blk s)

/-- **mem2reg / scalar-replacement as a gated pass** (#445, build-fixed in
    `fba8d4a8d`).  The gate is exactly the proved footprint-agreement obligation:
    `mem2reg prot`'s output must equal the input's `runBlock` final state — which
    holds when the dead-store footprint dropped by DSE is unobservable for this
    block.  The TV field is discharged trivially because the precondition *is* the
    target equality; the real content is `mem2reg_runBlock_agree` (`AgreeOn prot`),
    which a caller turns into the precondition by proving footprint completeness.

    We phrase the gate as the final-state equality rather than re-exporting
    `AgreeOn` so that `toX86Pass` composes directly; the honest obligation a caller
    must discharge (`AgreeOn prot ⇒ equality`, i.e. that `prot` covers the whole
    observable footprint) is named in `mem2regGatedPass_agree`. -/
def mem2regGatedPass (prot : List (String × Int)) : X86GatedPass where
  run := mem2reg prot
  pre := fun blk s => runBlock s (mem2reg prot blk) = runBlock s blk
  runBlock_eq_of := fun _ _ h => h

/-- The genuine, side-condition-free certificate `mem2reg` carries: its output
    agrees with the input on the register file and every protected cell, on every
    state.  This is `Mem2Reg.mem2reg_runBlock_agree`, surfaced at the driver so a
    caller can see precisely what must be upgraded (`AgreeOn prot ⇒ equality`,
    via footprint completeness) to discharge `mem2regGatedPass`'s gate. -/
theorem mem2regGatedPass_agree (prot : List (String × Int))
    (blk : List (JInstr 64)) (s : JState 64) :
    AgreeOn prot (runBlock s ((mem2regGatedPass prot).run blk)) (runBlock s blk) :=
  mem2reg_runBlock_agree prot blk s

/-! ## §4  Demonstration on a real kernel: `fe25519_mul`

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

/-! ## §5  Remaining passes to fold in (the #555 generalisation work)

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

The bigger #555 lever the pilot identified is **instruction selection** (the
fused-quotient-estimate reduce): it is upstream of schedule/RA and is *not* a
`JInstr → JInstr` reorder/rename, so it does not fit the `X86Pass` shape at all
and needs a distinct (selection) pass with its own value-semantics certificate.
That unblocks the #568 perf bar. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
