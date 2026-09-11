/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GroundedFieldProtocol

/-!
# Fully-grounded AES-mode and field protocol realizations — ZERO assumed kernel
  hypotheses

`ProtocolEmitRealizes.ProtocolKernels.runRealizes` reduces a protocol's
*whole-pipeline* emit-realization to a `List.Forall₂` of *per-kernel*
realizations (`KernelRealizes decode spec leaf leafSpec`).  Companion module
`GroundedFieldProtocol.lean` discharged that `Forall₂` from the proved field
realizers, with **zero** assumed `KernelRealizes` hypotheses.

This module does the same for **AES-mode** chains and for a **multi-step field
pipeline**.  AES's `State` (16 bytes) and a single `ZMod q` element both fit the
48-byte `RustVal .TFp` carrier, so the *existing* `.TFp`-based `pipeN` /
`ProtocolKernels` machinery applies directly — no carrier generalization is
needed.

These protocols **assume nothing about their kernels**: every per-kernel
realization is a *theorem*, discharged from the proved concrete realizers
(`aes_realizes_concrete`, `fieldAdd_realizes_concrete`,
`fieldMul_realizes_concrete`) together with the verified codec round-trips
(`decodeA_encodeA`, `decodeF_encodeF`).  The headline theorems therefore carry
**no `KernelRealizes`/`KernelRealizes2` hypothesis**.  The only residual is the
*owned-machine-code obligation* — that the jasmin-emitted bytes of the AES /
field-op kernels equal these realizer `LeafSpec`s — which is a single global
obligation, NOT a per-kernel hypothesis and NOT a KAT.

## The grounded pipelines

* **`grounded_aes_ecb_realizes` (AES-ECB chain).**  An `n`-block ECB chain under
  a fixed key: spec `aes128_encrypt key : State → State` applied `n` times, i.e.
  the unary `pipeN` of `n` copies of the AES leaf.  Its per-kernel realizations
  are `n` copies of the proved `aes_realizes_concrete`, assembled into the
  `List.Forall₂` of `ProtocolKernels.realized`; `runRealizes` then delivers the
  whole chain with no hypotheses.
* **`grounded_poly_eval_realizes` (multi-step field Horner / polynomial eval).**
  A full Horner chain of length `n` over the *unary* add-by-`c`-and-fixed-coeff
  steps: `n` copies of one proved Horner-by-constants step, assembled into a
  `ProtocolKernels` and run by `runRealizes` — a genuine multi-step field
  pipeline, unconditional.
* **`grounded_inner_product_step_realizes` (field multiply-accumulate).**  One
  multiply-accumulate `x ↦ x + a * b` over the binary concrete kernels, proved
  by chaining `fieldMul_realizes_concrete` then `fieldAdd_realizes_concrete`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedAesFieldProtocols

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedFieldProtocol
open CatCrypt.Crypto.Primitives.AES128

/-! ## §1  AES-ECB — an `n`-block chain under a fixed key

ECB mode under a fixed `key` is the pipeline `aes128_encrypt key` applied `n`
times to a running `State`.  Since `aes128_encrypt key : State → State` is a
unary `σ → σ` kernel (the key is fixed, no varying positional parameter), the
unary `pipeN` machinery applies directly: the kernel list is `n` copies of the
single AES leaf, and the spec list is `n` copies of `aes128_encrypt key`. -/

/-- The `n`-block AES-ECB kernel list: `n` copies of the single AES leaf. -/
def aesEcbLeaves (leaf : String) (n : ℕ) : List String :=
  List.replicate n leaf

/-- The matching spec list: `n` copies of `aes128_encrypt key`. -/
def aesEcbSpecs (key : Key128) (n : ℕ) : List (State → State) :=
  List.replicate n (aes128_encrypt key)

/-- The position-wise `Forall₂` of per-kernel realizations for the AES-ECB
    chain — `n` copies of the proved `aes_realizes_concrete` theorem.  No
    hypothesis is assumed; each entry is discharged. -/
theorem aesEcb_realized (key : Key128) (leaf : String)
    (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizes decodeA s l (aesLeafSpec key leaf limbStore))
      (aesEcbLeaves leaf n) (aesEcbSpecs key n) := by
  unfold aesEcbLeaves aesEcbSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons (aes_realizes_concrete key leaf limbStore) ih

/-- The bundled AES-ECB protocol: `n` AES blocks under a fixed key, all
    per-kernel realizations discharged (no hypothesis). -/
def aesEcbProtocol (key : Key128) (leaf : String)
    (limbStore : LimbStoreSpec) (n : ℕ) :
    ProtocolKernels State (aesLeafSpec key leaf limbStore) where
  leaves := aesEcbLeaves leaf n
  specs := aesEcbSpecs key n
  decode := decodeA
  realized := aesEcb_realized key leaf limbStore n

/-- **GROUNDED whole-pipeline emit-realization (AES-ECB).**  The `n`-block
    AES-ECB chain's entire `pipeN` computation decodes to the composite of its
    per-block specs — with **ZERO `KernelRealizes` hypotheses**.  Every
    per-kernel realization is the proved `aes_realizes_concrete` (in turn the AES
    round-trip `decodeA_encodeA`), not a KAT.  The only residual is the
    machine-code obligation (emitted bytes = `aesLeafSpec`), which is the
    owned-route, NOT a per-kernel hypothesis. -/
theorem grounded_aes_ecb_realizes (key : Key128) (leaf : String)
    (limbStore : LimbStoreSpec) (n : ℕ) (oldDest xVal : RustVal .TFp) :
    decodeA (pipeN (aesLeafSpec key leaf limbStore) (aesEcbLeaves leaf n)
        oldDest xVal)
      = composeSpecs (aesEcbSpecs key n) (decodeA xVal) :=
  (aesEcbProtocol key leaf limbStore n).runRealizes oldDest xVal

/-! ## §2  Multi-step field polynomial evaluation — a full Horner chain

`GroundedFieldProtocol.grounded_horner_realizes` discharges a *single* Horner
step `x ↦ x * v + c`.  A full Horner / polynomial-evaluation pipeline iterates
that step.  To compose it through the *unary* `pipeN` (one output feeds one
input), we fix the coefficient `v` and constant `c` per step, giving a unary
kernel `hornerByConst : x ↦ x * v + c`, realized as a theorem.  The `n`-fold
chain is then `n` copies of that one step, run by `ProtocolKernels.runRealizes`
with no hypotheses. -/

/-- The unary "Horner-by-constants `v, c`" call spec: at `leaf`, given a single
    `.TFp` operand `a`, first multiply by the *encoded coefficient* `encodeF v`
    via the proved `fieldMulLeafSpec` realizer, then add the *encoded constant*
    `encodeF c` via the proved `fieldAddLeafSpec` realizer; off-leaf return
    `oldDest`. -/
def hornerByConstCallSpec (q : ℕ) [NeZero q] (width : ℕ) (v c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) : CallSpec :=
  fun fname dt _argTs oldDest args =>
    if fname = leaf then
      if hd : dt = TowerType.TFp then
        match args with
        | a :: _ =>
            hd ▸ (fieldAddLeafSpec q width leaf limbStore).call leaf .TFp
              [.TFp, .TFp] (hd ▸ oldDest)
              [ ⟨.TFp,
                  (fieldMulLeafSpec q width leaf limbStore).call leaf .TFp
                    [.TFp, .TFp] (hd ▸ oldDest) [a, ⟨.TFp, encodeF width v⟩]⟩
              , ⟨.TFp, encodeF width c⟩ ]
        | _ => oldDest
      else oldDest
    else oldDest

/-- The unary "Horner-by-constants `v, c`" leaf spec, built atop the proved
    `fieldMulLeafSpec` and `fieldAddLeafSpec`. -/
def hornerByConstLeafSpec (q : ℕ) [NeZero q] (width : ℕ) (v c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := hornerByConstCallSpec q width v c leaf limbStore,
    limbStore := limbStore }

/-- **Per-kernel grounded realization (Horner step) — a THEOREM, not a
    hypothesis.**  The unary Horner-by-constants kernel realizes the unary spec
    `x ↦ x * v + c`.  Proved by plugging the single operand and the *encoded*
    coefficient/constant into the proved binary realizers
    `fieldMul_realizes_concrete` then `fieldAdd_realizes_concrete`, collapsing
    `decodeF (encodeF v) = v` and `decodeF (encodeF c) = c` via the proved
    round-trip `decodeF_encodeF`.  No KAT, no `KernelRealizes` hypothesis. -/
theorem hornerByConst_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (v c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := q) width) (fun x => x * v + c) leaf
      (hornerByConstLeafSpec q width v c leaf limbStore) := by
  intro xVal oldDest
  show decodeF width
      (hornerByConstCallSpec q width v c leaf limbStore leaf .TFp [.TFp] oldDest
        [⟨.TFp, xVal⟩])
    = decodeF width xVal * v + c
  simp only [hornerByConstCallSpec, if_true, dif_pos]
  -- Outer add leaf realizes `(· + ·)` on its two decoded operands.
  rw [fieldAdd_realizes_concrete q width hw hq leaf limbStore _
        (encodeF width c) oldDest]
  -- Inner mul leaf realizes `(· * ·)` on its two decoded operands.
  rw [fieldMul_realizes_concrete q width hw hq leaf limbStore xVal
        (encodeF width v) oldDest]
  -- Collapse the two encoded constants via the proved round-trip.
  rw [decodeF_encodeF width hw hq, decodeF_encodeF width hw hq]

/-- The `n`-step Horner kernel list: `n` copies of the single Horner leaf. -/
def hornerLeaves (leaf : String) (n : ℕ) : List String :=
  List.replicate n leaf

/-- The matching spec list: `n` copies of the unary spec `x ↦ x * v + c`. -/
def hornerSpecs (q : ℕ) [NeZero q] (v c : ZMod q) (n : ℕ) :
    List (ZMod q → ZMod q) :=
  List.replicate n (fun x => x * v + c)

/-- The position-wise `Forall₂` of per-kernel realizations for the Horner chain
    — `n` copies of the proved `hornerByConst_realizes` theorem.  No hypothesis
    is assumed; each entry is discharged. -/
theorem horner_realized (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (v c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizes (decodeF (q := q) width) s l
        (hornerByConstLeafSpec q width v c leaf limbStore))
      (hornerLeaves leaf n) (hornerSpecs q v c n) := by
  unfold hornerLeaves hornerSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (hornerByConst_realizes q width hw hq v c leaf limbStore) ih

/-- The bundled Horner / polynomial-eval protocol: `n` Horner-by-constants
    kernels, all per-kernel realizations discharged (no hypothesis). -/
def hornerProtocol (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (v c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) (n : ℕ) :
    ProtocolKernels (ZMod q) (hornerByConstLeafSpec q width v c leaf limbStore) where
  leaves := hornerLeaves leaf n
  specs := hornerSpecs q v c n
  decode := decodeF width
  realized := horner_realized q width hw hq v c leaf limbStore n

/-- **GROUNDED whole-pipeline emit-realization (multi-step Horner / polynomial
    evaluation).**  The `n`-step Horner field pipeline's entire `pipeN`
    computation decodes to the composite of its per-step specs — with **ZERO
    `KernelRealizes` hypotheses**.  Every per-kernel realization is the proved
    `hornerByConst_realizes` (in turn `fieldMul_realizes_concrete` +
    `fieldAdd_realizes_concrete` + the codec round-trip), not a KAT.  The only
    residual is the machine-code obligation (emitted bytes =
    `hornerByConstLeafSpec`), the owned-route, NOT a per-kernel hypothesis. -/
theorem grounded_poly_eval_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (v c : ZMod q)
    (leaf : String) (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal .TFp) :
    decodeF width
        (pipeN (hornerByConstLeafSpec q width v c leaf limbStore)
          (hornerLeaves leaf n) oldDest xVal)
      = composeSpecs (hornerSpecs q v c n) (decodeF width xVal) :=
  (hornerProtocol q width hw hq v c leaf limbStore n).runRealizes oldDest xVal

/-! ## §3  Field multiply-accumulate (inner-product step)

One inner-product step `x ↦ x + a * b` over the *binary* concrete field kernels:
chain `fieldMulLeafSpec` (on the encoded `a, b`) into `fieldAddLeafSpec` (with
the running accumulator `x`).  Proved directly from the two binary realizers, no
`KernelRealizes2` hypothesis. -/

/-- The value of one multiply-accumulate step `x ↦ x + a * b`: apply the binary
    mul leaf to `(encodeF a, encodeF b)`, then the binary add leaf to
    `(x, that)`. -/
def innerProductStepValue (q : ℕ) [NeZero q] (width : ℕ) (a b : ZMod q)
    (mulLeaf addLeaf : String) (limbStore : LimbStoreSpec)
    (oldDest xVal : RustVal .TFp) : RustVal .TFp :=
  (fieldAddLeafSpec q width addLeaf limbStore).call addLeaf .TFp [.TFp, .TFp]
    oldDest
    [ ⟨.TFp, xVal⟩
    , ⟨.TFp,
        (fieldMulLeafSpec q width mulLeaf limbStore).call mulLeaf .TFp
          [.TFp, .TFp] oldDest
          [⟨.TFp, encodeF width a⟩, ⟨.TFp, encodeF width b⟩]⟩ ]

/-- **GROUNDED multiply-accumulate emit-realization (inner-product step).**  One
    step `x ↦ x + a * b` over the *binary* concrete field kernels decodes to
    exactly `decodeF width xVal + a * b` — with **ZERO `KernelRealizes2`
    hypotheses**.  Both per-kernel realizations are the proved
    `fieldMul_realizes_concrete` and `fieldAdd_realizes_concrete`; the encoded
    `a, b` collapse by the proved `decodeF_encodeF`.  The only residual is the
    machine-code obligation for the two leaves, NOT a per-kernel hypothesis. -/
theorem grounded_inner_product_step_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (a b : ZMod q)
    (mulLeaf addLeaf : String) (limbStore : LimbStoreSpec)
    (oldDest xVal : RustVal .TFp) :
    decodeF width
        (innerProductStepValue q width a b mulLeaf addLeaf limbStore oldDest xVal)
      = decodeF width xVal + a * b := by
  unfold innerProductStepValue
  -- Outer add leaf realizes `(· + ·)` on its two decoded operands.
  rw [fieldAdd_realizes_concrete q width hw hq addLeaf limbStore xVal _ oldDest]
  -- Inner mul leaf realizes `(· * ·)` on its two decoded operands.
  rw [fieldMul_realizes_concrete q width hw hq mulLeaf limbStore
        (encodeF width a) (encodeF width b) oldDest]
  -- Collapse the two encoded constants via the proved round-trip.
  rw [decodeF_encodeF width hw hq, decodeF_encodeF width hw hq]

end CatCrypt.Crypto.SecureCompilation.GroundedAesFieldProtocols
