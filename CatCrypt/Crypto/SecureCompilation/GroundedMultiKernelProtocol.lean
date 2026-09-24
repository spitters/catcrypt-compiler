/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GroundedFieldProtocol

/-!
# A combined-dispatch leafSpec realizing MULTIPLE distinct kernels — the move
  that makes a VARYING-kernel protocol fully unconditional

`GroundedFieldProtocol` grounds whole pipelines whose every step uses the **same**
leaf (an accumulate-by-constant chain, or one Horner step over a fixed mul/add
pair).  Real protocols — AES-GCM, HKDF — interleave **different** kernels: a step
adds, the next multiplies, the next reduces.  To ground such a protocol with zero
assumed kernel facts, one concrete `LeafSpec` must realize **all** the protocol's
distinct kernels at once.

This module supplies exactly that: a single `fieldCombinedLeafSpec` whose `.call`
**dispatches on the leaf name** —

```
if leaf = "field_add" then  (the proved fieldAddCallSpec arm)
else if leaf = "field_mul" then  (the proved fieldMulCallSpec arm)
else oldDest
```

— each arm reusing the already-proved `fieldBinopCallSpec` realizer, so each
arm's behavior is *defeq* to a proved-unconditional realizer.  We then prove the
**one** leafSpec realizes **two distinct kernels** as theorems (no hypotheses):

* `combined_realizes_add : KernelRealizes2 (decodeF width) (· + ·) "field_add"
  (fieldCombinedLeafSpec …)` — the dispatch at `field_add` fires the first `if`
  (`if_pos rfl`), reducing to `fieldAdd_realizes_concrete`'s equation.
* `combined_realizes_mul : KernelRealizes2 (decodeF width) (· * ·) "field_mul"
  (fieldCombinedLeafSpec …)` — `field_mul ≠ field_add` so the first `if` is
  `if_neg`, then the second `if_pos rfl`, reducing to `fieldMul_realizes_concrete`.

The headline `grounded_multikernel_realizes` then grounds a **mixed-kernel**
pipeline — alternating `field_add` and `field_mul` leaves (two distinct
kernels, not one repeated) — through the single combined leafSpec, with **ZERO
`KernelRealizes`/`KernelRealizes2` hypotheses**.  Every per-step realization is a
theorem (`combined_realizes_add` / `combined_realizes_mul`, in turn the proved
concrete field realizers + the codec round-trip).

## What is grounded and what is not

* **Grounded (unconditional Lean theorem):** that ONE concrete leafSpec realizes
  BOTH the `field_add` and `field_mul` kernels (`combined_realizes_add` /
  `combined_realizes_mul`), and that the alternating mixed-kernel pipeline decodes
  to the composite of its per-step specs — no assumed kernel facts.
* **The only residual (the machine-code obligation, NOT a per-kernel
  hypothesis):** that the jasmin-emitted machine bytes of the real field-op
  kernels equal `fieldCombinedLeafSpec`'s arms.  That is the owned-machine-code
  route — a single global obligation, not one of the per-kernel realizations this
  file discharges.

## Why this is the unlock

Single-fixed-kernel grounding (the prior chains) can only express protocols that
repeat one kernel.  A combined-dispatch leafSpec realizing every distinct kernel
the protocol uses is the prerequisite for grounding *mixed*-kernel protocols.
The dispatch is on a decidable `String` equality; each branch is a proved arm, so
each kernel's realization is a theorem, and the mixed pipeline grounds with no
assumed kernel facts.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedFieldProtocol

/-! ## §1  The combined-dispatch leafSpec — one spec, two kernels

`fieldCombinedCallSpec` dispatches on the supplied function name `fname`: at
`"field_add"` it runs the proved field-add arm (`fieldBinopCallSpec` for `(· + ·)`
at leaf `"field_add"`), at `"field_mul"` the proved field-mul arm, and otherwise
returns `oldDest`.  Each arm is literally the `fieldBinopRealizerCallSpec`
underlying the proved `fieldAddLeafSpec` / `fieldMulLeafSpec`, so the combined
spec's behavior at each leaf is *defeq* to a proved-unconditional realizer. -/

/-- The combined add/mul dispatch `CallSpec`: dispatch on the leaf name, each arm
    the proved `fieldBinopRealizerCallSpec`. -/
def fieldCombinedCallSpec (q : ℕ) [NeZero q] (width : ℕ) : CallSpec :=
  fun fname dt argTs oldDest args =>
    if fname = "field_add" then
      fieldBinopRealizerCallSpec width ((· + ·) : ZMod q → ZMod q → ZMod q)
        "field_add" fname dt argTs oldDest args
    else if fname = "field_mul" then
      fieldBinopRealizerCallSpec width ((· * ·) : ZMod q → ZMod q → ZMod q)
        "field_mul" fname dt argTs oldDest args
    else oldDest

/-- The combined add/mul dispatch `LeafSpec`. -/
def fieldCombinedLeafSpec (q : ℕ) [NeZero q] (width : ℕ)
    (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := fieldCombinedCallSpec q width, limbStore := limbStore }

/-- **One leafSpec realizes the `field_add` kernel — a THEOREM, no hypothesis.**
    At `fname = "field_add"` the dispatch fires the first `if` (`if_pos rfl`),
    reducing the combined spec to the proved `fieldAdd_realizes_concrete`'s
    equation. -/
theorem combined_realizes_add (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := q) width) ((· + ·) : ZMod q → ZMod q → ZMod q)
      "field_add" (fieldCombinedLeafSpec q width limbStore) := by
  intro aVal bVal oldDest
  show decodeF width
      (fieldCombinedCallSpec q width "field_add" .TFp [.TFp, .TFp] oldDest
        [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = decodeF width aVal + decodeF width bVal
  -- Dispatch picks the field-add arm (`if_pos rfl`); it is the proved realizer.
  simp only [fieldCombinedCallSpec, if_pos]
  have hbin := fieldAdd_realizes_concrete q width hw hq "field_add" limbStore
      aVal bVal oldDest
  -- `fieldAddLeafSpec.call` is exactly `fieldBinopRealizerCallSpec` for `(·+·)`.
  exact hbin

/-- **One leafSpec realizes the `field_mul` kernel — a THEOREM, no hypothesis.**
    `field_mul ≠ field_add`, so the first `if` is `if_neg` and the second
    `if_pos rfl` fires, reducing the combined spec to the proved
    `fieldMul_realizes_concrete`'s equation. -/
theorem combined_realizes_mul (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := q) width) ((· * ·) : ZMod q → ZMod q → ZMod q)
      "field_mul" (fieldCombinedLeafSpec q width limbStore) := by
  intro aVal bVal oldDest
  show decodeF width
      (fieldCombinedCallSpec q width "field_mul" .TFp [.TFp, .TFp] oldDest
        [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = decodeF width aVal * decodeF width bVal
  -- First `if` is `if_neg` (`field_mul ≠ field_add`), second `if_pos rfl`.
  simp only [fieldCombinedCallSpec, if_neg (by decide : "field_mul" ≠ "field_add"),
    if_pos]
  have hbin := fieldMul_realizes_concrete q width hw hq "field_mul" limbStore
      aVal bVal oldDest
  exact hbin

/-! ## §2  A grounded VARYING-kernel pipeline through the single combined leafSpec

The unary `pipeN` invokes each leaf with a single `.TFp` operand; the field
kernels are binary.  Exactly as in `GroundedFieldProtocol`, we bridge each step
to a *unary* "binop-by-constant" leaf whose call forwards `(operand, encoded
constant)` to the combined leafSpec — and crucially each step's combined-spec arm
is a DIFFERENT kernel (`field_add` for the add steps, `field_mul` for the mul
steps).  Each unary realization is then a theorem from `combined_realizes_add` /
`combined_realizes_mul`. -/

/-- A unary "binop-by-constant `c` at leaf `leaf`" call spec atop the *combined*
    leafSpec: at `leaf`, forward `(operand, encodeF width c)` to the combined
    leafSpec's `leaf` arm; off-leaf return `oldDest`.  `leaf` selects which kernel
    of the combined spec is exercised (`"field_add"` or `"field_mul"`). -/
def combinedByConstCallSpec (q : ℕ) [NeZero q] (width : ℕ) (c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) : CallSpec :=
  fun fname dt _argTs oldDest args =>
    if fname = leaf then
      if hd : dt = TowerType.TFp then
        match args with
        | a :: _ =>
            hd ▸ (fieldCombinedLeafSpec q width limbStore).call leaf .TFp
              [.TFp, .TFp] (hd ▸ oldDest) [a, ⟨.TFp, encodeF width c⟩]
        | _ => oldDest
      else oldDest
    else oldDest

/-- The unary "binop-by-constant" leaf spec, built atop the combined leafSpec. -/
def combinedByConstLeafSpec (q : ℕ) [NeZero q] (width : ℕ) (c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := combinedByConstCallSpec q width c leaf limbStore,
    limbStore := limbStore }

/-- **The add-step realization — a THEOREM.**  The unary `field_add`-by-`a` kernel
    (over the combined leafSpec) realizes the unary spec `(· + a)`.  Proved from
    `combined_realizes_add` plus the codec round-trip on the encoded constant. -/
theorem combinedAddByConst_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (a : ZMod q)
    (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := q) width) (· + a) "field_add"
      (combinedByConstLeafSpec q width a "field_add" limbStore) := by
  intro xVal oldDest
  show decodeF width
      (combinedByConstCallSpec q width a "field_add" limbStore "field_add" .TFp
        [.TFp] oldDest [⟨.TFp, xVal⟩])
    = decodeF width xVal + a
  simp only [combinedByConstCallSpec, if_true, dif_pos]
  rw [combined_realizes_add q width hw hq limbStore xVal (encodeF width a) oldDest,
    decodeF_encodeF width hw hq]

/-- **The mul-step realization — a THEOREM.**  The unary `field_mul`-by-`v` kernel
    (over the same combined leafSpec) realizes the unary spec `(· * v)`.  Proved
    from `combined_realizes_mul` plus the codec round-trip. -/
theorem combinedMulByConst_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (v : ZMod q)
    (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := q) width) (· * v) "field_mul"
      (combinedByConstLeafSpec q width v "field_mul" limbStore) := by
  intro xVal oldDest
  show decodeF width
      (combinedByConstCallSpec q width v "field_mul" limbStore "field_mul" .TFp
        [.TFp] oldDest [⟨.TFp, xVal⟩])
    = decodeF width xVal * v
  simp only [combinedByConstCallSpec, if_true, dif_pos]
  rw [combined_realizes_mul q width hw hq limbStore xVal (encodeF width v) oldDest,
    decodeF_encodeF width hw hq]

/-! ### A mixed two-step pipeline: `x ↦ (x + a) * v`

One add step (leaf `"field_add"`, spec `(· + a)`) followed by one mul step (leaf
`"field_mul"`, spec `(· * v)`) — DISTINCT kernels of the SAME combined leafSpec.
Each leaf is dispatched to a different arm; each step's leafSpec is the
combined-by-constant spec for that step.  We express the pipeline at the value
level and prove its realization directly from the two proved step theorems. -/

/-- The value of the mixed two-step pipeline `x ↦ (x + a) * v`: apply the
    `field_add`-by-`a` leaf to `x`, then the `field_mul`-by-`v` leaf to that. -/
def addThenMulValue (q : ℕ) [NeZero q] (width : ℕ) (a v : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) : RustVal .TFp :=
  (combinedByConstLeafSpec q width v "field_mul" limbStore).call "field_mul" .TFp
    [.TFp] oldDest
    [ ⟨.TFp,
        (combinedByConstLeafSpec q width a "field_add" limbStore).call "field_add"
          .TFp [.TFp] oldDest [⟨.TFp, xVal⟩]⟩ ]

/-- **GROUNDED mixed-kernel pipeline emit-realization — ZERO kernel hypotheses.**
    The two-step pipeline `x ↦ (x + a) * v`, whose two steps exercise the
    **distinct** `field_add` and `field_mul` kernels of the single combined
    leafSpec, decodes to exactly `(decodeF width xVal + a) * v`.  Both per-step
    realizations are theorems (`combinedAddByConst_realizes` /
    `combinedMulByConst_realizes`, in turn `combined_realizes_add` /
    `combined_realizes_mul` + the codec round-trip).  No assumed kernel fact; the
    only residual is the machine-code obligation for the two combined arms. -/
theorem grounded_addThenMul_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (a v : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) :
    decodeF width (addThenMulValue q width a v limbStore oldDest xVal)
      = (decodeF width xVal + a) * v := by
  unfold addThenMulValue
  -- Outer step: `field_mul`-by-`v` realizes `(· * v)` on the inner value.
  rw [combinedMulByConst_realizes q width hw hq v limbStore _ oldDest]
  -- Inner step: `field_add`-by-`a` realizes `(· + a)` on `xVal`.
  rw [combinedAddByConst_realizes q width hw hq a limbStore xVal oldDest]

/-! ### The headline: a longer alternating mixed-kernel `pipeN` pipeline

The `pipeN`/`composeSpecs` form (the `ProtocolKernels.runRealizes`
shape) over a leaf list that **alternates** `"field_add"` and `"field_mul"` — so
the pipeline uses two distinct kernels of the single combined leafSpec.

Because `pipeN` invokes every leaf through ONE `leafSpec`, but our two steps need
different per-step constants AND different dispatch arms, we use the combined
leafSpec directly as the single `pipeN` spec and prove the per-step realizations
as a `Forall₂` whose entries alternate the two proved step theorems.  Here the
combined-by-constant leaves coincide on the constant per family, so we fix a
single add-constant `a` and a single mul-constant `v` and alternate the leaves —
`["field_add", "field_mul", "field_add", "field_mul"]`. -/

/-- A combined unary leafSpec that dispatches BOTH the add-by-`a` and mul-by-`v`
    steps by leaf name — the single `pipeN` spec for the alternating pipeline. -/
def alternatingLeafSpec (q : ℕ) [NeZero q] (width : ℕ) (a v : ZMod q)
    (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := fun fname dt argTs oldDest args =>
      if fname = "field_add" then
        (combinedByConstLeafSpec q width a "field_add" limbStore).call fname dt
          argTs oldDest args
      else
        (combinedByConstLeafSpec q width v "field_mul" limbStore).call fname dt
          argTs oldDest args
    limbStore := limbStore }

/-- The add-step realization through the alternating leafSpec — a THEOREM. -/
theorem alternating_realizes_add (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (a v : ZMod q)
    (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := q) width) (· + a) "field_add"
      (alternatingLeafSpec q width a v limbStore) := by
  intro xVal oldDest
  show decodeF width
      ((alternatingLeafSpec q width a v limbStore).call "field_add" .TFp [.TFp]
        oldDest [⟨.TFp, xVal⟩])
    = decodeF width xVal + a
  simp only [alternatingLeafSpec, if_pos]
  exact combinedAddByConst_realizes q width hw hq a limbStore xVal oldDest

/-- The mul-step realization through the alternating leafSpec — a THEOREM. -/
theorem alternating_realizes_mul (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (a v : ZMod q)
    (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := q) width) (· * v) "field_mul"
      (alternatingLeafSpec q width a v limbStore) := by
  intro xVal oldDest
  show decodeF width
      ((alternatingLeafSpec q width a v limbStore).call "field_mul" .TFp [.TFp]
        oldDest [⟨.TFp, xVal⟩])
    = decodeF width xVal * v
  simp only [alternatingLeafSpec, if_neg (by decide : "field_mul" ≠ "field_add")]
  exact combinedMulByConst_realizes q width hw hq v limbStore xVal oldDest

/-- The alternating leaf list `["field_add", "field_mul", "field_add",
    "field_mul"]` — interleaving the two distinct kernels. -/
def alternatingLeaves : List String :=
  ["field_add", "field_mul", "field_add", "field_mul"]

/-- The matching spec list `[(· + a), (· * v), (· + a), (· * v)]`. -/
def alternatingSpecs (q : ℕ) [NeZero q] (a v : ZMod q) :
    List (ZMod q → ZMod q) :=
  [(· + a), (· * v), (· + a), (· * v)]

/-- The position-wise `Forall₂` of per-step realizations for the alternating
    pipeline — alternating the two proved step theorems.  No hypothesis. -/
theorem alternating_realized (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (a v : ZMod q)
    (limbStore : LimbStoreSpec) :
    List.Forall₂
      (fun l s => KernelRealizes (decodeF (q := q) width) s l
        (alternatingLeafSpec q width a v limbStore))
      alternatingLeaves (alternatingSpecs q a v) := by
  unfold alternatingLeaves alternatingSpecs
  exact List.Forall₂.cons (alternating_realizes_add q width hw hq a v limbStore)
    (List.Forall₂.cons (alternating_realizes_mul q width hw hq a v limbStore)
      (List.Forall₂.cons (alternating_realizes_add q width hw hq a v limbStore)
        (List.Forall₂.cons (alternating_realizes_mul q width hw hq a v limbStore)
          List.Forall₂.nil)))

/-- The bundled alternating mixed-kernel protocol: distinct add/mul kernels, all
    per-step realizations discharged (no hypothesis). -/
def alternatingProtocol (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (a v : ZMod q)
    (limbStore : LimbStoreSpec) :
    ProtocolKernels (ZMod q) (alternatingLeafSpec q width a v limbStore) where
  leaves := alternatingLeaves
  specs := alternatingSpecs q a v
  decode := decodeF width
  realized := alternating_realized q width hw hq a v limbStore

/-- **THE HEADLINE — grounded VARYING-kernel pipeline, ZERO kernel hypotheses.**
    The alternating `["field_add", "field_mul", "field_add", "field_mul"]`
    pipeline — two DISTINCT kernels of the single combined leafSpec —
    has its whole `pipeN` computation decode to the composite of its per-step
    specs `[(· + a), (· * v), (· + a), (· * v)]`, with **ZERO `KernelRealizes` /
    `KernelRealizes2` hypotheses**.  Every per-step realization is a theorem
    (`alternating_realizes_add` / `_mul`, in turn `combined_realizes_add` /
    `combined_realizes_mul` + the codec round-trip).  This is the move that makes
    VARYING-kernel protocols unconditional: ONE concrete leafSpec realizes all the
    protocol's distinct kernels by dispatch, each realization a theorem from the
    proved concrete realizers.  The only residual is the machine-code obligation
    for the combined arms — NOT a per-kernel hypothesis. -/
theorem grounded_multikernel_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (a v : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) :
    decodeF width
        (pipeN (alternatingLeafSpec q width a v limbStore)
          alternatingLeaves oldDest xVal)
      = composeSpecs (alternatingSpecs q a v) (decodeF width xVal) :=
  (alternatingProtocol q width hw hq a v limbStore).runRealizes oldDest xVal

end CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol
