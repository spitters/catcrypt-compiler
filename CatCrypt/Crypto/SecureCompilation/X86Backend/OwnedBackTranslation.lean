/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect

/-!
# The genuine non-identity back-translation for the register-allocation refinement

Robust-compilation (RrHP / robust-preservation) proofs construct a
**back-translation**: a map sending an adversarial *target* context/observation to
a *source* context/observation, so the source side simulates whatever the target
adversary could observe. For a stage that is a full **equivalence** the identity
back-translation suffices — that is the case for the owned `LowCT → JInstr`
*lowering*, documented in `OwnedCompileRobust` (the lowering preserves the full
`SPComp` denotation, so source and target are observationally *equal* and the
correct functional back-translation is the identity, with nothing to construct).

The audit's point (b) is that a **genuine, non-identity** back-translation is the
technique for stages that are **refinements** rather than equivalences. The
**register-allocation** stage is exactly such a stage: the source uses abstract
slot names (`v`), the target observes renamed/physical registers
(`ρalloc (ρmap v)`). The correspondence is a non-trivial renaming, so the
back-translation of a target register-observation is genuinely non-identity — its
content is the composition `ρalloc ∘ ρmap`.

This module constructs that back-translation and proves it correct, on top of the
per-slot value correspondence `ScalarCompileCorrect.scalarCompileAlloc_denote`,
which states that the *allocated* compiled block holds, **at the renamed register
`ρalloc (ρmap v)`**, exactly the source post-value of slot `v`.

## What is built

* `TargetObs α` / `SourceObs α` — a target observation reads the allocated
  machine's register file (`String → BitVec 64 → α`); a source observation reads
  a `RustState`.
* `backTranslate ρmap ρalloc obs` — the **non-identity** back-translation: it
  turns a target register-file observation into a source observation by building,
  from a `RustState`, the register-file view the target expects — reading source
  slot `v` through the renamed register `ρalloc (ρmap v)` (coerced via
  `BitVec.ofNat 64`). The non-identity content is the `ρalloc ∘ ρmap` composition.
* `backTranslateReg` — the single-register specialization: the back-translation of
  "read renamed register `ρalloc (ρmap v)`" is "read source slot `v`".
* `backTranslate_correct_reg` — **correctness, single live register.** The target
  observation (read renamed register `ρalloc (ρmap v)`) of the allocated final
  state equals the back-translated source observation of the source final state.
  Proved directly from `scalarCompileAlloc_denote`. This is the minimum faithful
  deliverable and it genuinely uses the non-identity renaming.
* `LiveSet` / `DependsOnLive` / `backTranslate_correct` — **correctness,
  finite live set.** For a target observation that *depends only on the live
  renamed registers* (factors through the restriction to `{ρalloc (ρmap v) | v ∈
  live}`), the target observation of the allocated final register file equals the
  back-translated source observation. The "depends only on live registers"
  hypothesis is stated as: `obs` agrees on any two register files that agree on
  the live renamed registers.
* `backTranslate_nonidentity` — a concrete witness that the back-translation is
  **not** the identity: with `ρmap = id` and `ρalloc = ("r_" ++ ·)`, the renamed
  register `ρalloc (ρmap "x") = "r_x" ≠ "x"`, so the target reads a register whose
  name differs from the source slot — the renaming is real.

## Relation to `OwnedCompileRobust` (the identity case)

The full owned chain is two stages:

1. **lowering** `LowCT → JInstr` — an *equivalence* (full `SPComp`-denotation
   preservation), so its functional back-translation is the **identity**
   (`OwnedCompileRobust`, the "On back-translation" section);
2. **register allocation** `JInstr → renamed JInstr` — a *refinement* (abstract
   slots become physical registers), whose back-translation is the **non-identity**
   `ρalloc ∘ ρmap` map constructed here.

Composed, they give the value-observation back-translation for the owned
`LowCT → allocated JInstr` pipeline.

## Scope notes

This back-translation covers the **value observation** of the
register-allocation refinement: an adversary reading the live allocated registers
learns exactly the source slot values, recovered through the non-identity
renaming. It is *not*, by itself, a complete robust-compilation back-translation
for an arbitrary un-owned backend stage — it does not back-translate leakage/timing
observations (that is the constant-time conjunct, carried separately in
`OwnedCompileRobust` / `RegAllocSpillCT`), nor control-flow contexts, nor stages
outside the owned straight-line scalar-arith fragment. It is the value-observation
back-translation for the one refinement stage (allocation) that is genuinely a
renaming, complementing the identity back-translation of the equivalence lowering.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedBackTranslation

open CatCrypt.Crypto.Jasmin.LowCT (RustState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect
open CatCrypt.Crypto.Optimizer.GenericRegAlloc (RenInjOn)
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc (renameBlock)
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped (StateRelOn blockNamesXsym)

/-! ## 1. Target and source observations -/

/-- A **target observation**: an adversarial context observing the allocated
    machine, modelled as a function of the allocated register file
    (`String → BitVec 64`, the result of `(runBlock …).get` at each register
    name). Parameterized over the result type `α`. -/
def TargetObs (α : Type) := (String → BitVec 64) → α

/-- A **source observation**: a context reading a source `RustState`. -/
def SourceObs (α : Type) := RustState → α

/-! ## 2. The back-translation (genuinely non-identity)

`backTranslate` sends a target register-observation to a source observation.
Given a source `RustState rs`, it reconstructs the register-file view the target
observation expects, reading each source slot `v` through the **renamed** register
`ρalloc (ρmap v)`. The reconstruction inverts the renaming: to supply the value at
a *physical register* `r`, it finds the source slot whose renamed register is `r`
and returns that slot's value. Where the renaming is injective on the live slots
(the `scalarCompileAlloc_denote` hypothesis), this is exactly the source value the
target sees. The non-identity content is the `ρalloc ∘ ρmap` composition. -/

/-- The register-file view a source `RustState` presents at a renamed register,
    *for a fixed slot `v`*: the value of source slot `v`, coerced to a 64-bit word.
    This is the per-slot kernel of the back-translation. -/
def slotView (rs : RustState) (v : String) : BitVec 64 :=
  BitVec.ofNat 64 (rs.rsScalar v)

open Classical in
/-- **The back-translation.** A target observation `obs` of the allocated register
    file becomes a source observation: from `rs`, build the register file that, at
    each renamed register `ρalloc (ρmap v)`, carries source slot `v`'s value
    (`slotView`), and read `obs` of it. The reconstruction
    `decode ρmap ρalloc rs : String → BitVec 64` reads physical register `r` by
    returning the value of the source slot `v` with `ρalloc (ρmap v) = r`
    (`0` if none / ambiguous — those registers are outside the live set the
    correctness theorem scopes to). The non-identity is the `ρalloc ∘ ρmap`
    renaming threaded into `decode`. -/
noncomputable def decode (ρmap : RegMap) (ρalloc : String → String)
    (rs : RustState) : String → BitVec 64 :=
  fun r =>
    if h : ∃ v, ρalloc (ρmap v) = r then slotView rs h.choose
    else 0

/-- **The back-translation of a target observation.** -/
noncomputable def backTranslate (ρmap : RegMap) (ρalloc : String → String)
    {α : Type} (obs : TargetObs α) : SourceObs α :=
  fun rs => obs (decode ρmap ρalloc rs)

/-! ## 3. The single-register read and its back-translation

The simplest faithful target observation is "read renamed register
`ρalloc (ρmap v)`". Its back-translation is "read source slot `v`" — the
non-identity renaming is what connects the two. -/

/-- The target observation "read renamed register `ρalloc (ρmap v)`". -/
def readReg (r : String) : TargetObs (BitVec 64) := fun rf => rf r

/-- The source observation "read source slot `v` (as a 64-bit word)". -/
def readSlot (v : String) : SourceObs (BitVec 64) := fun rs => slotView rs v

/-! ## 4. Correctness — single live register

The target observation (read renamed register `ρalloc (ρmap v)`) of the allocated
final state equals the back-translated source observation of the source final
state. Proved directly from `scalarCompileAlloc_denote`. -/

/-- **Back-translation correctness, single live register.**

    Under the hypotheses of `scalarCompileAlloc_denote` (register map injective on
    live slots, well-formed source, alias-free allocation, matched/related initial
    states, `v` a live slot), the target observation reading the renamed register
    `ρalloc (ρmap v)` of the *allocated final state*
    `runBlock s (renameBlock ρalloc (lowerSeq ρmap ps))` equals reading source slot
    `v` of the source final state `srcDenote ps rs`.

    This is the value-observation back-translation correctness for the register-
    allocation refinement, in the simplest faithful form: the register the target
    observes (`ρalloc (ρmap v)`, a *physical* name) carries exactly the source slot
    `v`'s value (an *abstract* name), connected by the non-identity renaming. -/
theorem backTranslate_correct_reg (ρmap : RegMap) (ρalloc : String → String)
    (hmapinj : Function.Injective ρmap) (ps : List ArithSrc)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (hallocinj : RenInjOn (blockNamesXsym (lowerSeq ρmap ps)) ρalloc)
    (rs : RustState) (js s : JState 64)
    (hmatch : StateMatch ρmap rs js)
    (hrel : StateRelOn (blockNamesXsym (lowerSeq ρmap ps)) ρalloc s js)
    (v : String) (hv : ρmap v ∈ blockNamesXsym (lowerSeq ρmap ps)) :
    readReg (ρalloc (ρmap v))
        (fun r => (runBlock s (renameBlock ρalloc (lowerSeq ρmap ps))).get r)
      = readSlot v (srcDenote ps rs) := by
  simp only [readReg, readSlot, slotView]
  exact scalarCompileAlloc_denote ρmap ρalloc hmapinj ps hwf hallocinj rs js s
    hmatch hrel v hv

/-! ## 5. Correctness — finite live set

We generalize to a target observation `obs` that **depends only on the live
renamed registers**. "Live" is a finite set `live : List String` of source slots
that the block mentions (each `ρmap v ∈ blockNamesXsym …`). The dependence
hypothesis `DependsOnLive`: `obs` agrees on any two register files that agree on
the renamed live registers `{ρalloc (ρmap v) | v ∈ live}`. Under this, the target
observation of the allocated register file equals the target observation of the
`decode`d source register file — i.e. the back-translation is correct. -/

/-- The set of renamed (physical) registers for a live source-slot list. -/
def renamedLive (ρmap : RegMap) (ρalloc : String → String)
    (live : List String) : List String :=
  live.map (fun v => ρalloc (ρmap v))

/-- **`obs` depends only on the live renamed registers.** `obs` returns the same
    result on any two register files that agree on every renamed live register
    `ρalloc (ρmap v)`, `v ∈ live`. This is the clean "factors through the
    restriction to live registers" hypothesis. -/
def DependsOnLive (ρmap : RegMap) (ρalloc : String → String)
    (live : List String) {α : Type} (obs : TargetObs α) : Prop :=
  ∀ rf₁ rf₂ : String → BitVec 64,
    (∀ v ∈ live, rf₁ (ρalloc (ρmap v)) = rf₂ (ρalloc (ρmap v))) →
    obs rf₁ = obs rf₂

/-- **Back-translation correctness, finite live set.**

    For a target observation `obs` that depends only on the live renamed registers
    (`DependsOnLive`), the target observation of the *allocated final register
    file* equals the back-translation of `obs` applied to the source final state.

    The proof: by `DependsOnLive`, it suffices to show the allocated register file
    and the `decode`d source register file agree on each renamed live register
    `ρalloc (ρmap v)`. On the allocated side that value is the source slot `v`'s
    value by `scalarCompileAlloc_denote`; on the `decode` side it is `slotView`
    of slot `v` — which (by injectivity of `ρalloc ∘ ρmap` on live slots) is also
    slot `v`'s value. -/
theorem backTranslate_correct (ρmap : RegMap) (ρalloc : String → String)
    (hmapinj : Function.Injective ρmap) (ps : List ArithSrc)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (hallocinj : RenInjOn (blockNamesXsym (lowerSeq ρmap ps)) ρalloc)
    (rs : RustState) (js s : JState 64)
    (hmatch : StateMatch ρmap rs js)
    (hrel : StateRelOn (blockNamesXsym (lowerSeq ρmap ps)) ρalloc s js)
    (live : List String)
    (hlive : ∀ v ∈ live, ρmap v ∈ blockNamesXsym (lowerSeq ρmap ps))
    (hallocfun : Function.Injective (fun v => ρalloc (ρmap v)))
    {α : Type} (obs : TargetObs α)
    (hdep : DependsOnLive ρmap ρalloc live obs) :
    obs (fun r => (runBlock s (renameBlock ρalloc (lowerSeq ρmap ps))).get r)
      = backTranslate ρmap ρalloc obs (srcDenote ps rs) := by
  unfold backTranslate
  apply hdep
  intro v hvmem
  -- allocated side: equals slot v's value
  have hval := scalarCompileAlloc_denote ρmap ρalloc hmapinj ps hwf hallocinj rs js s
    hmatch hrel v (hlive v hvmem)
  rw [hval]
  -- decode side: decode … (ρalloc (ρmap v)) = slotView (srcDenote ps rs) v
  show BitVec.ofNat 64 ((srcDenote ps rs).rsScalar v)
        = decode ρmap ρalloc (srcDenote ps rs) (ρalloc (ρmap v))
  unfold decode
  have hex : ∃ w, ρalloc (ρmap w) = ρalloc (ρmap v) := ⟨v, rfl⟩
  rw [dif_pos hex]
  -- the chosen witness equals v by injectivity of ρalloc ∘ ρmap
  have hchoose : hex.choose = v := hallocfun hex.choose_spec
  rw [slotView, hchoose]

/-! ## 6. The back-translation is genuinely non-identity

A concrete witness contrasting with the equivalence lowering's identity
back-translation: with `ρmap = id` and `ρalloc = ("r_" ++ ·)`, the renamed
register the target observes is `"r_x" ≠ "x"`. So the target reads a register
whose *name* differs from the source slot — the back-translation threads a real,
non-identity renaming, unlike the identity back-translation correct for the
equivalence lowering. -/

/-- **Non-identity witness.** For the concrete renaming `ρmap = id`,
    `ρalloc = ("r_" ++ ·)`, the renamed register `ρalloc (ρmap "x")` the target
    observes is `"r_x"`, which is **not** the source slot name `"x"`. The
    register-allocation back-translation therefore threads a genuinely non-identity
    map — in contrast with the identity back-translation correct for the
    equivalence lowering. -/
theorem backTranslate_nonidentity :
    let ρmap : RegMap := id
    let ρalloc : String → String := fun s => "r_" ++ s
    ρalloc (ρmap "x") ≠ "x" := by
  intro ρmap ρalloc
  decide

/-- The same witness phrased over the observation: the target observation reading
    the renamed register `ρalloc (ρmap "x") = "r_x"` reads a *different* register
    name than the source-slot read `"x"` would — witnessing that the
    register the value is observed at is not the source slot name. -/
theorem readReg_nonidentity :
    let ρmap : RegMap := id
    let ρalloc : String → String := fun s => "r_" ++ s
    (readReg (ρalloc (ρmap "x")) : TargetObs (BitVec 64))
      = readReg "r_x" ∧ ("r_x" ≠ "x") := by
  refine ⟨rfl, by decide⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedBackTranslation
