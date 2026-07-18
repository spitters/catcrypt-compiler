/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc
import CatCrypt.Crypto.Optimizer.Mem2Reg

/-!
# A translation-validated composed owned-x86 optimizer pipeline (P1)

`X86ComPipeline.lean` gives the *unconditional-core* driver: a pipeline of
`X86Pass`es, each of which carries a **global, all-blocks, all-states**
`runBlock`-equality theorem.  Today only **one** owned-x86 transform has that
side-condition-free shape — store-to-load forwarding — so the default
`defaultX86Pipeline = [storeToLoadForwardPass]` is a one-pass pipeline, and the
stronger passes (graph-coloring register allocation, mem2reg / dead-store
elimination, the latency scheduler) remain **per-kernel opt-ins**: each carries a
*side-conditioned* certificate (`AgreeOn`, a `SpillValid` sandwich, a per-block
legality proof) that does not chain transitively without threading a hypothesis.

This module is P1 from `owned-vs-jasminc-perf-review.md`: a **CompCert-style
verified-validator** pipeline that lets those stronger passes become the default
*safely*.  The design is the classic translation-validation gate:

> Run a pass.  Then **check** the result against the input with a *decidable*
> certificate (`chk : List (JInstr 64) → Bool`).  Keep the pass output **only if
> the certificate passes**; otherwise keep the input unchanged.

Because the kept branch is gated by the certificate and the discarded branch is
the identity, the *composed* pipeline's soundness is **unconditional**: for every
block and every state, `runBlock s (composeValidated ps b) = runBlock s b`, with
**no** side hypothesis on `b` or on the passes — every step that was kept was
validated, and every step that was rejected was a no-op.  The untrusted optimizer
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

## Which passes are wired with their genuine certificate

| pass | certificate `chk` | kind |
|---|---|---|
| **store-to-load forwarding** (#372/#412) | `allDirect b → allDirect (f b)`, decidably | **genuine** — semantics always sound (`storeToLoadForward_runBlock`), CT gated by a decidable implication check |
| **graph-coloring register allocation** (#414) | `decide (f b = b)` (fires only as a no-op) | conservative — the allocator's whole-block soundness is a per-spill `SpillValid` sandwich, not an all-blocks `runBlock`-equality, so it is wrapped with the always-sound no-op gate pending the footprint-completeness upgrade |
| **mem2reg / DSE** (#415) | `decide (f b = b)` (fires only as a no-op) | conservative — `Mem2Reg`'s certificate is `AgreeOn prot`, full equality only on an unobservable footprint; wrapped with the always-sound no-op gate |

The latency **scheduler** (`SchedulerPass.scheduleBlock`) is *not* in this
pipeline: it operates on the `LowCT`/`BBStmt` IR (`RustExec` semantics), not on
`List (JInstr 64)`/`runBlock`, so it does not fit the `ValidatedPass` shape at all
— it is a distinct-IR pass with its own (already-proved) `scheduleBlock_denote_eq`.

The honest reading: the **composition framework + its unconditional soundness** is
the deliverable; it is *populated* with one genuinely-validated pass (forwarding)
and two passes wrapped behind a conservative-but-sound no-op gate.  As each
stronger pass acquires a *decidable* whole-block `runBlock`-equality certificate
(e.g. the graph-coloring allocator's `noAlias`/`RenInjOn` checker upgraded to
full equality), its `chk` is strengthened in place and the composed theorems pick
it up with **no** reproof.

## Deferred integration point (the merge-time step)

In the driver `Com.toLprogPhysAbi` / `compileComToElf`, the block-level optimizer
hook currently calls `X86ComPipeline.optimizeX86Block`
(`= applyX86Pipeline defaultX86Pipeline`, i.e. store-to-load forwarding only).
The merge replaces that call with
`composeValidated defaultValidatedPipeline`, so the graph-coloring RA and mem2reg
passes run by default, each gated by its certificate — semantics and constant-time
preserved unconditionally by `composeValidated_sound` /
`composeValidated_allDirect`.  No proof obligation is pushed to the driver.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.Optimizer.StoreToLoadForward (storeToLoadForward storeToLoadForward_runBlock)

-- `JInstr w` equality is decidable (every field is a `String`/`Int`/`Nat`/`JOperand`,
-- each with `DecidableEq`).  This lets the conservative `decide (f b = b)` no-op
-- certificate be a genuine `Bool`.
deriving instance DecidableEq for JInstr

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
  /-- Semantic translation validation: when the certificate fires, the rewrite
      lands in the same `runBlock` final state on **every** start state. -/
  sem_sound : ∀ (b : List (JInstr 64)), chk b = true →
    ∀ (s : JState 64), runBlock s (f b) = runBlock s b
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

/-- **Unconditional semantic soundness of the gate.**  For *every* block and state,
    the gated rewrite lands in the same `runBlock` final state as the input — no
    side hypothesis.  If the certificate fired, `sem_sound` closes it; if not, the
    output *is* the input. -/
theorem applyValidated_sound (p : ValidatedPass) (b : List (JInstr 64))
    (s : JState 64) : runBlock s (applyValidated p b) = runBlock s b := by
  unfold applyValidated
  split
  · case isTrue h => exact p.sem_sound b h s
  · case isFalse _ => rfl

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

/-- **Unconditional semantic soundness of the composed pipeline.**  For *every*
    list of validated passes, every block, and every state, the pipeline-optimized
    block lands in the same `runBlock` final state as the input.  No side
    hypothesis: every kept step was validated, every rejected step was a no-op.
    Induction on the pass list, chaining `applyValidated_sound`. -/
theorem composeValidated_sound (ps : List ValidatedPass) :
    ∀ (b : List (JInstr 64)) (s : JState 64),
      runBlock s (composeValidated ps b) = runBlock s b := by
  induction ps with
  | nil => intro b s; rfl
  | cons p ps ih =>
    intro b s
    rw [composeValidated_cons, ih (applyValidated p b) s, applyValidated_sound p b s]

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
    (b : List (JInstr 64)) (s : JState 64) :
    (lowerBlock (Γ := []) (composeValidated ps b)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) b).denote (.cons s .nil) := by
  rw [lowerBlock_denote_closed (composeValidated ps b) s, lowerBlock_denote_closed b s]
  exact composeValidated_sound ps b s

/-! ## §3  Wrapping the real owned-x86 passes as validated passes -/

/-! ### §3.1  Store-to-load forwarding — the genuinely-validated pass

Forwarding's semantic certificate is *unconditional* (`storeToLoadForward_runBlock`
holds on every block and state), so its `sem_sound` ignores `chk`.  Its constant-
time certificate is the **decidable implication** `allDirect b → allDirect (f b)`:
when `allDirect b` is false the implication is vacuous (the block is not in the CT
class so there is nothing to preserve); when `allDirect b` is true the certificate
fires iff the forwarded block is still all-direct.  This is a genuine, content-
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
  sem_sound := fun b _ s => storeToLoadForward_runBlock b s
  ct_sound := fun _b hc hd => (of_decide_eq_true hc) hd

/-! ### §3.2  Conservative (no-op-gated) wrappers for the stronger passes

The graph-coloring register allocator and mem2reg do *not* carry an unconditional
all-blocks `runBlock`-equality (their proved certificates are a `SpillValid`
sandwich and `AgreeOn prot` respectively — see the module docstring).  Rather than
fake an unconditional certificate, we wrap them behind the **always-sound no-op
gate** `decide (f b = b)`: the pass fires only on blocks it leaves unchanged, where
soundness and CT preservation are trivial.  This keeps the composition framework
honest while reserving the slot for the genuine certificate (the allocator's
`noAlias`/`RenInjOn` checker upgraded to full equality) to drop in later. -/

/-- The conservative no-op certificate: fire only when the rewrite is the identity
    on this block.  Always sound (`f b = b ⇒ runBlock s (f b) = runBlock s b` and
    `allDirect (f b) = allDirect b`). -/
def noOpCert (f : List (JInstr 64) → List (JInstr 64)) (b : List (JInstr 64)) : Bool :=
  decide (f b = b)

/-- **Wrap any rewrite behind the conservative no-op gate as a validated pass.**
    The certificate fires only where `f b = b`, so both soundness obligations are
    discharged by rewriting with that equality.  This is the always-available
    fallback for a pass whose unconditional whole-block certificate is not yet
    proved. -/
def conservativeValidated (f : List (JInstr 64) → List (JInstr 64)) : ValidatedPass where
  f := f
  chk := noOpCert f
  sem_sound := fun b hc s => by
    rw [show f b = b from of_decide_eq_true hc]
  ct_sound := fun b hc hd => by
    rw [show f b = b from of_decide_eq_true hc]; exact hd

/-- **Graph-coloring register allocation as a (conservatively-gated) validated
    pass** (#414).  The allocator emits a `name ↦ Slot` decision list materialized
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

/-- **mem2reg / dead-store elimination as a (conservatively-gated) validated pass**
    (#415).  `Mem2Reg.mem2reg`'s certificate is `AgreeOn prot` (agreement on the
    protected footprint), with full `runBlock`-equality only when the eliminated
    footprint is unobservable — a per-kernel obligation.  Wrapped behind the no-op
    gate pending that footprint-completeness proof. -/
def mem2regValidated (prot : List (String × Int)) : ValidatedPass :=
  conservativeValidated (CatCrypt.Crypto.Optimizer.Mem2Reg.mem2reg prot)

/-! ## §4  The candidate default validated pipeline -/

/-- **The candidate default validated pipeline.**  Store-to-load forwarding (its
    genuine certificate) followed by mem2reg and the graph-coloring register
    allocator (each behind the conservative no-op gate).  Every pass is gated by
    its decidable certificate, so `composeValidated` over this list is
    unconditionally semantics- and CT-preserving — the property that lets these
    passes become the *default* (replacing the forwarding-only
    `X86ComPipeline.defaultX86Pipeline`).  The `prot`/`pinned`/frame parameters are
    the per-driver placement choices supplied at the integration site. -/
def defaultValidatedPipeline
    (prot : List (String × Int))
    (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String) : List ValidatedPass :=
  [ storeToLoadForwardValidated,
    mem2regValidated prot,
    graphColorRAValidated pinned frameBase spillBase ]

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
  composeValidated_sound _ b s

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
block (`Fe25519MulKernel.feMulBlock`, the #555 pilot kernel).  The composed
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
  composeValidated_sound demoPipeline feMulBlock s

/-- **The composed validated pipeline preserves `fe25519_mul`'s `Com`
    denotation.**  An instance of `composeValidated_lowering`. -/
theorem demo_lowering (s : JState 64) :
    (lowerBlock (Γ := []) (composeValidated demoPipeline feMulBlock)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) feMulBlock).denote (.cons s .nil) :=
  composeValidated_lowering demoPipeline feMulBlock s

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
      descr := "store-to-load forwarding (#372/#412); CT gated by a decidable allDirect-preservation implication" },
    { toValidatedPass := mem2regValidated registryPlacement.1
      name := "mem2reg"
      descr := "mem2reg / dead-store elimination (#415); no-op-gated pending AgreeOn footprint-completeness" },
    { toValidatedPass :=
        graphColorRAValidated registryPlacement.2.1 registryPlacement.2.2.1 registryPlacement.2.2.2
      name := "graph-color-ra"
      descr := "graph-coloring register allocation (#414); no-op-gated pending SpillValid footprint-completeness" } ]

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

/-- **A named pipeline is unconditionally semantics-preserving.**  A thin corollary
    of `composeValidated_sound` applied to the resolved list — the existing soundness
    theorem carries over to the named form with no reproof. -/
theorem pipelineByName_sound (names : List String) (b : List (JInstr 64)) (s : JState 64) :
    runBlock s (composeValidated (pipelineByName names) b) = runBlock s b :=
  composeValidated_sound (pipelineByName names) b s

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
  composeValidated_lowering (pipelineByName names) b s

/-- **The registry round-trips the default pipeline.**  Resolving the three pass
    names in the documented order reproduces exactly `defaultValidatedPipeline` at
    the registry's pinned placement (`registryPlacement`) — the named form and the
    hand-built §4 list are definitionally the same pipeline, so registration loses
    nothing. -/
theorem pipelineByName_defaultValidatedPipeline :
    pipelineByName ["store-to-load-forward", "mem2reg", "graph-color-ra"]
      = defaultValidatedPipeline
          registryPlacement.1 registryPlacement.2.1 registryPlacement.2.2.1 registryPlacement.2.2.2 :=
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
