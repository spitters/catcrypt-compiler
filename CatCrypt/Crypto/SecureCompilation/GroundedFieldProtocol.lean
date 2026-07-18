/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer

/-!
# A fully-grounded field protocol — whole-pipeline emit-realization with ZERO
  assumed per-kernel hypotheses

`ProtocolEmitRealizes.ProtocolKernels.runRealizes` reduces a protocol's
*whole-pipeline* emit-realization to a `List.Forall₂` of *per-kernel*
realizations (`KernelRealizes decode spec leaf leafSpec`).  In every prior
instantiation those per-kernel realizations were **cited as hypotheses** —
"this leaf's emitted bytes decode to its spec", a fact a leaf-bytes KAT would
*assert*.  A KAT is a test vector, not a proof; a hypothesis is an axiom in
disguise.

This module is the capstone answering that gap.  Here **every per-kernel
realization is a theorem**, discharged by the *unconditional* concrete field
realizers `ConcreteSymFieldRealizer.fieldAdd_realizes_concrete` /
`fieldMul_realizes_concrete` — themselves proved (no hypotheses) from the
verified codec round-trip `decodeF_encodeF`.  The headline results
(`grounded_accumulate_realizes`, `grounded_horner_realizes`) therefore carry
**zero `KernelRealizes`/`KernelRealizes2` hypotheses**: a real multi-kernel
field pipeline whose whole emit-realization assumes *nothing* about its
kernels.

## What is grounded and what is not

* **Grounded (unconditional Lean theorem):** the per-kernel realizations.  Each
  `KernelRealizes (decodeF width) (· + c) leaf …` is derived *as a theorem* by
  plugging `xVal` and the encoded constant into the proved binary realizer
  `fieldAdd_realizes_concrete` and collapsing `decodeF (encodeF c) = c` via the
  proved round-trip `decodeF_encodeF`.  No KAT, no abstract section, no
  hypothesis.
* **The only residual (the machine-code obligation, NOT a per-kernel
  hypothesis):** that the *jasmin-emitted machine bytes* of the field-op kernel
  equal the realizer `LeafSpec` (`fieldAddLeafSpec`/`fieldMulLeafSpec`).  That
  equality — emitted assembly ≡ realizer — is the owned-machine-code route, a
  single global obligation, and is explicitly *not* one of the per-kernel
  realization hypotheses this file eliminates (and is *not* a KAT either).

## The two grounded pipelines

* **`grounded_accumulate_realizes` (Option A — unary chain).**  An `n`-step
  accumulate-by-a-constant chain: spec `(· + c) : ZMod q → ZMod q` applied `n`
  times, i.e. the unary `pipeN` of `n` copies of the add-by-`c` kernel.  Its
  per-kernel realizations are `n` copies of one proved theorem
  (`addByConst_realizes`), assembled into the `List.Forall₂` of
  `ProtocolKernels.realized` — so `runRealizes` delivers the whole pipeline with
  no hypotheses.
* **`grounded_horner_realizes` (Option B — binary, mul-then-add).**  One Horner
  step `x ↦ x * v + c` over the *binary* concrete kernels, proved directly by
  chaining `fieldMul_realizes_concrete` and `fieldAdd_realizes_concrete` (each a
  theorem) — again no per-kernel hypotheses.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedFieldProtocol

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer

/-! ## §1  Option A — a single binary kernel with one operand fixed to a constant

The unary `KernelRealizes` predicate invokes the leaf with **one** positional
`.TFp` argument; the field realizers are **binary** (two positional `.TFp`
arguments).  We bridge by a unary `LeafSpec` whose call, at the leaf, forwards
its single argument together with an *encoded constant* `encodeF width c` as the
second operand to the **proved** `fieldAddLeafSpec` realizer.  The resulting
unary realization is then a theorem: `fieldAdd_realizes_concrete` gives the
binary equation, and `decodeF_encodeF` collapses `decodeF width (encodeF width c)
= c`. -/

/-- The unary "add-by-constant `c`" call spec: at `leaf`, given a single `.TFp`
    operand, forward `(operand, encodeF width c)` to the proved binary
    `fieldAddLeafSpec` realizer; off-leaf return `oldDest`. -/
def addByConstCallSpec (q : ℕ) [NeZero q] (width : ℕ) (c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) : CallSpec :=
  fun fname dt _argTs oldDest args =>
    if fname = leaf then
      if hd : dt = TowerType.TFp then
        match args with
        | a :: _ =>
            hd ▸ (fieldAddLeafSpec q width leaf limbStore).call leaf .TFp
              [.TFp, .TFp] (hd ▸ oldDest) [a, ⟨.TFp, encodeF width c⟩]
        | _ => oldDest
      else oldDest
    else oldDest

/-- The unary "add-by-constant `c`" leaf spec, built atop the proved
    `fieldAddLeafSpec`. -/
def addByConstLeafSpec (q : ℕ) [NeZero q] (width : ℕ) (c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := addByConstCallSpec q width c leaf limbStore, limbStore := limbStore }

/-- **Per-kernel grounded realization (Option A) — a THEOREM, not a hypothesis.**
    The unary add-by-constant kernel realizes the unary spec `(· + c)`.  Proved
    by plugging the single operand and the *encoded constant* into the proved
    binary realizer `fieldAdd_realizes_concrete`, then collapsing
    `decodeF width (encodeF width c) = c` via the proved round-trip
    `decodeF_encodeF`.  No KAT, no assumed section, no `KernelRealizes`
    hypothesis. -/
theorem addByConst_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := q) width) (· + c) leaf
      (addByConstLeafSpec q width c leaf limbStore) := by
  intro xVal oldDest
  -- The unary call unfolds to the binary `fieldAddLeafSpec` call at
  -- `(xVal, encodeF width c)`.
  show decodeF width
      (addByConstCallSpec q width c leaf limbStore leaf .TFp [.TFp] oldDest
        [⟨.TFp, xVal⟩])
    = decodeF width xVal + c
  simp only [addByConstCallSpec, if_true, dif_pos]
  -- Now the LHS is `decodeF (fieldAddLeafSpec.call … [⟨.TFp,xVal⟩, ⟨.TFp, encodeF c⟩])`.
  have hbin := fieldAdd_realizes_concrete q width hw hq leaf limbStore
      xVal (encodeF width c) oldDest
  rw [hbin, decodeF_encodeF width hw hq]

/-- The `n`-fold accumulate-by-constant kernel list: `n` copies of the single
    add-by-`c` leaf. -/
def accumulateLeaves (leaf : String) (n : ℕ) : List String :=
  List.replicate n leaf

/-- The matching spec list: `n` copies of the unary spec `(· + c)`. -/
def accumulateSpecs (q : ℕ) [NeZero q] (c : ZMod q) (n : ℕ) :
    List (ZMod q → ZMod q) :=
  List.replicate n (· + c)

/-- The position-wise `Forall₂` of per-kernel realizations for the accumulate
    chain — `n` copies of the single proved `addByConst_realizes` theorem.  No
    hypothesis is assumed; each entry is discharged. -/
theorem accumulate_realized (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizes (decodeF (q := q) width) s l
        (addByConstLeafSpec q width c leaf limbStore))
      (accumulateLeaves leaf n) (accumulateSpecs q c n) := by
  unfold accumulateLeaves accumulateSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (addByConst_realizes q width hw hq c leaf limbStore) ih

/-- The bundled accumulate protocol: `n` add-by-`c` kernels, all per-kernel
    realizations discharged (no hypothesis). -/
def accumulateProtocol (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) (n : ℕ) :
    ProtocolKernels (ZMod q) (addByConstLeafSpec q width c leaf limbStore) where
  leaves := accumulateLeaves leaf n
  specs := accumulateSpecs q c n
  decode := decodeF width
  realized := accumulate_realized q width hw hq c leaf limbStore n

/-- **GROUNDED whole-pipeline emit-realization (Option A).**  The `n`-step
    accumulate-by-constant field pipeline's entire `pipeN` computation decodes to
    the composite of its per-kernel specs — with **ZERO `KernelRealizes`
    hypotheses**.  Every per-kernel realization is the proved
    `addByConst_realizes` (in turn `fieldAdd_realizes_concrete` + the codec
    round-trip), not a KAT.  The only residual is the machine-code obligation
    (emitted bytes = `addByConstLeafSpec`), which is the owned-route, NOT a
    per-kernel hypothesis. -/
theorem grounded_accumulate_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal .TFp) :
    decodeF width
        (pipeN (addByConstLeafSpec q width c leaf limbStore)
          (accumulateLeaves leaf n) oldDest xVal)
      = composeSpecs (accumulateSpecs q c n) (decodeF width xVal) :=
  (accumulateProtocol q width hw hq c leaf limbStore n).runRealizes oldDest xVal

/-! ## §2  Option B — a binary Horner step over the binary concrete kernels

A single Horner step `x ↦ x * v + c` chains the *binary* `fieldMulLeafSpec` (with
second operand the encoded coefficient `v`) into the *binary* `fieldAddLeafSpec`
(with second operand the encoded constant `c`).  We express the pipeline directly
as the chained value and prove its realization by applying the two proved binary
realizers — `fieldMul_realizes_concrete` then `fieldAdd_realizes_concrete` — and
collapsing the two encoded constants via `decodeF_encodeF`.  No `KernelRealizes2`
hypothesis is assumed. -/

/-- The value of one Horner step `x ↦ x * v + c`: apply the binary mul leaf to
    `(x, encodeF v)`, then the binary add leaf to `(that, encodeF c)`. -/
def hornerStepValue (q : ℕ) [NeZero q] (width : ℕ) (v c : ZMod q)
    (mulLeaf addLeaf : String) (limbStore : LimbStoreSpec)
    (oldDest xVal : RustVal .TFp) : RustVal .TFp :=
  (fieldAddLeafSpec q width addLeaf limbStore).call addLeaf .TFp [.TFp, .TFp]
    oldDest
    [ ⟨.TFp,
        (fieldMulLeafSpec q width mulLeaf limbStore).call mulLeaf .TFp
          [.TFp, .TFp] oldDest [⟨.TFp, xVal⟩, ⟨.TFp, encodeF width v⟩]⟩
    , ⟨.TFp, encodeF width c⟩ ]

/-- **GROUNDED Horner-step emit-realization (Option B).**  One Horner step
    `x ↦ x * v + c` over the *binary* concrete field kernels decodes to exactly
    `decodeF width xVal * v + c` — with **ZERO `KernelRealizes2` hypotheses**.
    Both per-kernel realizations are the proved `fieldMul_realizes_concrete` and
    `fieldAdd_realizes_concrete`; the encoded coefficient and constant collapse by
    the proved `decodeF_encodeF`.  The only residual is the machine-code
    obligation for the two leaves, NOT a per-kernel hypothesis. -/
theorem grounded_horner_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (v c : ZMod q)
    (mulLeaf addLeaf : String) (limbStore : LimbStoreSpec)
    (oldDest xVal : RustVal .TFp) :
    decodeF width
        (hornerStepValue q width v c mulLeaf addLeaf limbStore oldDest xVal)
      = decodeF width xVal * v + c := by
  unfold hornerStepValue
  -- Outer add leaf realizes `(· + ·)` on its two decoded operands.
  rw [fieldAdd_realizes_concrete q width hw hq addLeaf limbStore _
        (encodeF width c) oldDest]
  -- Inner mul leaf realizes `(· * ·)` on its two decoded operands.
  rw [fieldMul_realizes_concrete q width hw hq mulLeaf limbStore xVal
        (encodeF width v) oldDest]
  -- Collapse the two encoded constants via the proved round-trip.
  rw [decodeF_encodeF width hw hq, decodeF_encodeF width hw hq]

end CatCrypt.Crypto.SecureCompilation.GroundedFieldProtocol
