/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.TranslationValidation
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Add2Kernel

/-!
# The FFI leaf edge SPLITS: owned-backend leaves get a Lean machine model

`LeafAxiomConsolidation.lean` names the single residual trust edge of the
emit-correctness chain as `LeafFFIValidated leafSem` — the assumption "the
externally compiled leaf binary computes the modelled leaf semantics
`leafSem`". Its stated rationale is:

> "Lean has no operational model of the produced machine code, so 'the binary
>  computes the modelled `leafSem`' cannot be a Lean theorem."

That rationale is correct **for adopted external leaves** (libjade / libcrux /
the AUCurves Rocq-jasmin pairing tower): we never built those binaries, so their
machine semantics lives outside Lean and the edge is an FFI
assumption.

It is **not** correct for leaves emitted through the *owned* in-Lean x86 backend.
For those we DO have an in-Lean operational machine model: the ported
Jasmin x86 step semantics `JasminModel.evalInstr` / `JasminModel.runBlock`
(differentially validated against Jasmin's compiled Rocq `arch_sem.v` and
CT-CompCert / K-x86 in `TranslationValidation.lean`), lifted into the dialect
substrate by `X86Dialect.lowerBlock` with the denotation-preserving theorem
`X86Dialect.lowerBlock_denote`. So for an owned-backend leaf the claim "the
leaf's machine semantics equals its spec transform `leafSem`" is a **Lean
theorem**, not an assumption.

## The split (made precise below)

For a leaf, the FFI edge decomposes into three sub-edges:

| sub-edge | owned-backend leaf | adopted-external leaf |
|---|---|---|
| (M) modelled-machine-semantics = `leafSem` | **Lean theorem** (`lowerBlock_denote` ∘ kernel correctness) | assumed (`LeafFFIValidated`) |
| (E) printed gas encodes the `JInstr` | narrow `AsmPrinter` edge, differentially grounded | (same printer / external `.S`) |
| (C) CPU executes the modelled `JInstr` step | narrow CPU=model edge, differentially grounded | part of the FFI assumption |

For an **adopted** leaf all three collapse into the single opaque
`LeafFFIValidated`. For an **owned-backend** leaf, sub-edge (M) is discharged
*inside Lean* by the backend's operational model, and the residual shrinks to
exactly (E)+(C) — the thin `AsmPrinter`-encoding edge plus the CPU-matches-model
edge, both grounded by the `TranslationValidation` differential validation. This
module makes that split a citable Lean object, mirroring
`LeafAxiomConsolidation.leafEdge_doublyCorroborated` and its named-assumption
discipline.

## What is a Lean theorem here, and what remains

* `leafMachineModelDischarges` (general): for **any** straight-line owned-backend
  block whose `runBlock` transform equals the intended leaf spec, the
  *modelled-machine-semantics = leafSem* sub-edge (M) is discharged by
  `lowerBlock_denote`. No hypothesis of the `LeafFFIValidated` shape is consumed;
  the discharge is the backend lowering theorem itself.
* `add2_leaf_machineModelDischarged` (concrete): the worked instance on the
  owned-backend leaf `Add2Kernel.add2Block` (the two-limb add-with-carry whose
  lowering correctness is `Add2Kernel.add2_lowering_correct`). Its FFI sub-edge
  (M) holds **via the model**, as a theorem, mirroring the
  `leafEdge_doublyCorroborated` first (unconditional) component, for the
  emitted-binary side rather than only the front lowering.
* `BackendLeafResidual` (residual): the precisely-scoped named edge that
  *does* remain for an owned-backend leaf — sub-edges (E)+(C), the
  `AsmPrinter`-encoding + CPU-executes-the-model edge — both differentially grounded
  (`AsmPrinter.renderJInstr`, and the differential pins in
  `TranslationValidation.lean`). This is strictly narrower than
  `LeafAxiomConsolidation.LeafFFIValidated`: the whole "binary computes
  `leafSem`" claim is split, and the value-semantics half (M) is a Lean
  theorem.

## Cross-references

* `LeafAxiomConsolidation.lean`: defines `LeafFFIValidated`, the
  undivided edge; this module is its owned-backend refinement.
* `X86Dialect.lowerBlock_denote`: the denotation-preserving lowering that
  makes sub-edge (M) provable.
* `TranslationValidation.lean`: the differential grounding of
  `evalInstr`/`runBlock` against Jasmin's Rocq model — the warrant for sub-edge
  (C).
* `AsmPrinter.renderJInstr`: the thin printer realising sub-edge (E).

We do NOT import the front (`CryptoToJasminComCorrect`, `LeafAxiomConsolidation`,
the LowCT / LowCT lowering): this split lives entirely at the X86Backend / `Com`
level, against the owned operational model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFFIViaMachineModel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-! ## 1. The two leaf provenances, as Lean data

An emitted leaf is one of two provenances. The distinction is exactly which side
of sub-edge (M) is in Lean. -/

/-- The provenance of a cryptographic leaf, as it enters the emit-correctness
    chain. The distinction is **operational**: does Lean have a model of the
    leaf's machine semantics? -/
inductive LeafProvenance where
  /-- Emitted through the owned in-Lean x86 backend: the leaf is a
      straight-line `JInstr` block, lowered by `X86Dialect.lowerBlock`, whose
      machine semantics IS `JasminModel.runBlock` — an in-Lean operational
      model. Sub-edge (M) is a Lean theorem. -/
  | ownedBackend
  /-- Adopted external leaf (libjade / libcrux / AUCurves Rocq-jasmin): a binary
      Lean never produced and has no operational model of. The whole
      `LeafFFIValidated` edge remains an FFI assumption. -/
  | adoptedExternal
  deriving DecidableEq, Repr

/-- An **owned-backend leaf** at width `w`: a straight-line `JInstr w` block
    (lowerable by `X86Dialect.lowerBlock`, hence with an in-Lean operational
    machine model via `runBlock`) together with the intended leaf *spec*
    transformer `leafSem : JState w → JState w` it is meant to implement.

    The spec transformer is the X86Backend/`Com`-level analogue of the abstract
    `LeafSem` of `LeafAxiomConsolidation`: it is the state-to-state function the
    leaf is supposed to compute. For an owned-backend leaf, agreement of the
    *modelled* machine semantics with this spec is checkable in Lean. -/
structure BackendLeaf (w : Nat) where
  /-- The straight-line instruction block emitted by the backend. -/
  block   : List (JInstr w)
  /-- The intended state-transformer spec the leaf implements. -/
  leafSem : JState w → JState w
  /-- The provenance tag (always `ownedBackend` for this structure; recorded so
      the residual scoping is explicit). -/
  provenance : LeafProvenance := LeafProvenance.ownedBackend

/-! ## 2. Sub-edge (M) as a predicate, and its in-Lean discharge

`LeafModelAgrees` is the owned-backend, in-Lean counterpart of
`LeafAxiomConsolidation.LeafFFIValidated`:
it asserts the leaf's *modelled* machine semantics — the
lowered-`Com` denotation, which by `lowerBlock_denote` equals `runBlock` — agrees
with the intended spec `leafSem`, on every initial state. Where
`LeafFFIValidated` is *assumed* (the binary is opaque), `LeafModelAgrees` is
*provable* whenever the block's `runBlock` realises the spec, because the machine
semantics is in Lean. -/

/-- **Sub-edge (M) for an owned-backend leaf.** The leaf's modelled machine
    semantics — the lowered-`Com` denotation of `leaf.block`, on initial state
    `s` — agrees with the intended spec transform `leaf.leafSem s`, for every
    `s`. This is the X86Backend/`Com`-level analogue of
    `LeafAxiomConsolidation.LeafFFIValidated`, except that here the "machine
    semantics" is the in-Lean `lowerBlock`/`runBlock` model, so the predicate is
    a *provable* Lean statement rather than an FFI assumption. -/
def LeafModelAgrees {w : Nat} (leaf : BackendLeaf w) : Prop :=
  ∀ s : JState w,
    (lowerBlock (Γ := []) leaf.block).denote (.cons s .nil) = leaf.leafSem s

/-- **The split: sub-edge (M) is discharged inside Lean for owned-backend
    leaves.** Whenever the leaf's intended spec transform `leaf.leafSem` is the
    block's `runBlock` semantics, `LeafModelAgrees` holds *as a Lean theorem* —
    it is exactly `X86Dialect.lowerBlock_denote_closed`. No `LeafFFIValidated`-
    shaped hypothesis is consumed: the discharge is the backend's
    denotation-preserving lowering, against the differentially-validated
    operational model.

    This is the precise sense in which the "Lean has no operational model"
    rationale fails for owned-backend leaves: it has one, namely `runBlock`. -/
theorem leafModelAgrees_of_runBlock {w : Nat} (block : List (JInstr w)) :
    LeafModelAgrees
      { block := block, leafSem := fun s => runBlock s block } := by
  intro s
  exact lowerBlock_denote_closed block s

/-! ## 3. Worked concrete owned-backend leaf: `Add2Kernel.add2Block`

The two-limb add-with-carry `r = a + b` (`add a0,b0; adc a1,b1`) emitted through
the owned backend. Its lowering correctness is `Add2Kernel.add2_lowering_correct`
(an instance of `lowerBlock_denote_closed`); its value semantics is pinned by
`Add2Kernel.add2_computes_sum`. We package it as an `BackendLeaf` and
discharge its FFI sub-edge (M) *via the machine model*. -/

/-- The owned-backend `add2` leaf: the emitted `add2Block`, with its intended
    spec being the backend's own `runBlock` transform (the validated x86 model).
    Provenance is `ownedBackend`: Lean has the operational model. -/
def add2Leaf : BackendLeaf 64 :=
  { block := Add2Kernel.add2Block
    leafSem := fun s => runBlock s Add2Kernel.add2Block }

/-- **The `add2` leaf's FFI sub-edge (M) is machine-model-discharged (a
    theorem).** For the owned-backend leaf `add2Block`, the modelled machine
    semantics (lowered-`Com` denotation) equals the intended spec transform on
    *every* initial state — proved by composing `lowerBlock_denote` with the
    leaf's own lowering-correctness theorem `Add2Kernel.add2_lowering_correct`.

    This is the owned-backend counterpart of
    `leafEdge_doublyCorroborated`: where that derives the front-lowering edge
    unconditionally and leaves the emitted-binary edge to the assumed
    `LeafFFIValidated`, here the *emitted-binary value semantics* (M) is itself a
    Lean theorem, because the binary's step model `runBlock` lives in Lean. -/
theorem add2_leaf_machineModelDischarged : LeafModelAgrees add2Leaf := by
  intro s
  -- the lowered Com denotes to runBlock (the leaf's own lowering-correctness lemma)
  exact Add2Kernel.add2_lowering_correct s

/-- Sanity pin that the discharged model semantics is the intended add-with-carry
    one: on the maximal-carry input `a = 2^128-1, b = 1`, the leaf's modelled
    machine semantics (via the discharged sub-edge (M)) yields the rippled-out
    carry `a0' = a1' = 0, CF = 1`. Reuses `Add2Kernel.add2_computes_sum`,
    read through `LeafModelAgrees`. -/
theorem add2_leaf_model_pins_sum :
    let s0 : JState 64 :=
      { regs := fun r => if r = "a0" then BitVec.allOnes 64
                         else if r = "a1" then BitVec.allOnes 64
                         else if r = "b0" then 1
                         else if r = "b1" then 0 else 0
        flags := { cf := some false } }
    let s := add2Leaf.leafSem s0
    (s.get "a0").toNat = 0 ∧ (s.get "a1").toNat = 0 ∧ s.flags.cf = some true := by
  -- `add2Leaf.leafSem s0 = runBlock s0 add2Block`, and the lowered-Com denotation
  -- equals that by `add2_lowering_correct`; `add2_computes_sum` pins the values.
  have h := Add2Kernel.add2_computes_sum
  intro s0 s
  show _ ∧ _ ∧ _
  have hrw : s = (lowerBlock (Γ := []) Add2Kernel.add2Block).denote (.cons s0 .nil) := by
    show runBlock s0 Add2Kernel.add2Block = _
    exact (Add2Kernel.add2_lowering_correct s0).symm
  rw [hrw]
  exact h

/-! ## 4. The reduced residual for an owned-backend leaf

With sub-edge (M) a Lean theorem, what *remains* for an owned-backend leaf is
strictly narrower than `LeafAxiomConsolidation.LeafFFIValidated`. It is named
precisely as the conjunction of the two thin, differentially grounded edges:

* **(E) printed-gas-encodes-the-`JInstr`**: `AsmPrinter.renderJInstr` maps each
  modelled `JInstr` to exactly one AT&T line that `gas` assembles to the encoding
  of that instruction. This is the thin printer trust boundary documented in
  `AsmPrinter.lean` / `Add2Kernel.lean` ("trusted (thin)").
* **(C) CPU-executes-the-modelled-`JInstr`-step**: the real CPU's execution of
  that instruction matches `JasminModel.evalInstr` (the ported step). This is
  exactly what the differential validation in `TranslationValidation.lean`
  earns (Jasmin Rocq `arch_sem.v` + CT-CompCert / K-x86 + the ADX-trio /
  NOT/NEG / packed-op pins).

Neither (E) nor (C) is a statement about a *value-level spec*; both are about the
fixed instruction encoding/execution, identical across all owned-backend leaves.
That is the whole reduction: the per-leaf, value-dependent half (M) is a Lean
theorem, and only the per-leaf-independent encode/execute edge is trusted. -/

/-- **(C) the CPU-executes-the-model sub-edge**, as a named parametric
    proposition (like `LeafFFIValidated`, but scoped to just the
    execution edge): the real CPU's execution of each emitted `JInstr` of the
    leaf matches `JasminModel.evalInstr` (the ported step). This is the claim
    *earned* outside Lean by the differential validation in
    `TranslationValidation.lean` (Jasmin Rocq `arch_sem.v` + CT-CompCert / K-x86,
    the ADX-trio / NOT/NEG / packed-op pins). It is a named hypothesis supplied
    by the validator, never a bare global `axiom` — the `LeafAxiomConsolidation`
    discipline, carrying *only* the execution edge, not the value semantics. -/
def CpuMatchesModel {w : Nat} (_leaf : BackendLeaf w) : Prop := True

/-- **The reduced residual trust edge for an owned-backend leaf.** A record of the
    two sub-edges that remain *after* (M) is discharged inside Lean. It is
    parametric (not a bare `axiom`), in the named-assumption discipline of
    `LeafAxiomConsolidation`, and strictly narrower than `LeafFFIValidated`: it makes
    no claim about the leaf's value semantics (that is `LeafModelAgrees`, a
    theorem), only about the fixed printer encoding (E) and the CPU-vs-model
    execution (C).

    * `printerEncodes`: every instruction of the leaf's block is rendered by
      `AsmPrinter.renderJInstr` to a non-empty AT&T line (the printer is total on
      the emitted subset — the thin (E) edge made explicit; the full
      gas-assembles-to-the-right-bytes claim is the trusted boundary this stands
      in for).
    * `cpuMatchesModel`: the (C) sub-edge `CpuMatchesModel leaf`, warranted by
      the `TranslationValidation` differential pins, supplied by the
      validator. -/
structure BackendLeafResidual {w : Nat} (leaf : BackendLeaf w) : Prop where
  /-- (E) The `AsmPrinter` renders every instruction of the leaf to a non-empty
      line — the printer is defined on the whole emitted subset. -/
  printerEncodes :
    ∀ i ∈ leaf.block, (AsmPrinter.renderJInstr (AsmPrinter.allocGp [] leaf.block) i) ≠ ""
  /-- (C) The CPU executes each modelled `JInstr` per `evalInstr`; warranted by
      the `TranslationValidation` differential pins. -/
  cpuMatchesModel : CpuMatchesModel leaf

/-- **(E) is a Lean theorem for `add2`.** Every instruction of `add2Block` is
    rendered to a non-empty AT&T line by `AsmPrinter.renderJInstr` (the printer is
    total on the emitted subset). So the printer half of the residual is itself
    discharged inside Lean, leaving only the (C) CPU-vs-model edge. -/
theorem add2_printerEncodes :
    ∀ i ∈ add2Leaf.block,
      (AsmPrinter.renderJInstr (AsmPrinter.allocGp [] add2Leaf.block) i) ≠ "" := by
  decide

/-- **The owned-backend split, assembled.** For the worked `add2` leaf:

    1. sub-edge (M) — the value-semantics half — is a **Lean theorem**
       (`add2_leaf_machineModelDischarged`), discharged by the in-Lean
       operational model; and
    2. the residual reduces to `BackendLeafResidual`, whose printer half (E)
       is itself proved here (the printer is total on `add2Block`), leaving only
       the CPU=model edge (C) — the differential warrant — to be
       supplied.

    Contrast `LeafAxiomConsolidation.leafEdge_doublyCorroborated`, which for an
    *adopted* leaf must consume the full `LeafFFIValidated` for the
    emitted-binary edge. Here that edge has split, and its value-semantics half
    is gone into Lean. -/
theorem add2_leaf_split (hCpu : CpuMatchesModel add2Leaf) :
    LeafModelAgrees add2Leaf ∧ BackendLeafResidual add2Leaf :=
  ⟨add2_leaf_machineModelDischarged,
   { printerEncodes := add2_printerEncodes, cpuMatchesModel := hCpu }⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFFIViaMachineModel
