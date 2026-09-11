/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol

/-!
# A grounded Schnorr / EdDSA signature SCALAR-ARITHMETIC core — ZERO assumed
  kernel hypotheses

A discrete-log signature's response equation (`s = r + c·x` for Schnorr, `s = r +
e·a` for EdDSA) is, over the scalar field, a single field multiply followed by a
single field add: `x ↦ c·x + r` (multiply the running scalar by the challenge
`c`, add the nonce `r`).  The EC verification check `s·G == R + c·P` reduces — on
honest signatures — to exactly this scalar identity over the scalar field, so the
*field-arithmetic* part of the response is the genuine groundable core.

`SignatureProtocolKernels` instantiates Schnorr / EdDSA / ECDSA / FROST over the
generic `ProtocolKernels` template, but each per-kernel realization is taken as a
**hypothesis** (the kernel's leaf-bytes KAT).  This module grounds the
Schnorr / EdDSA scalar-field combine **unconditionally**: every per-op
realization is a *theorem* (the proved concrete field realizers
`combined_realizes_mul` / `combined_realizes_add`, reached through the single
combined-dispatch leafSpec), so the headline carries **ZERO `KernelRealizes` /
`KernelRealizes2` hypotheses** — only the codec fit `width ≤ 48`, `q < 2^(8·width)`.

This reuses the *same* combined-dispatch move as the Horner / poly-eval
grounding (`GroundedMultiKernelProtocol`): ONE concrete `LeafSpec` realizes both
the `field_mul` and `field_add` kernels by dispatching on the leaf name, each arm
a proved-unconditional realizer.

## What is grounded and what is NOT

* **Grounded (unconditional Lean theorem):** the Schnorr / EdDSA scalar response
  combine `x ↦ c·x + r` — one `field_mul` step (by the challenge `c`) then one
  `field_add` step (by the nonce `r`), genuinely DISTINCT kernels of the single
  combined leafSpec — decodes to exactly `(decodeF width xVal) · c + r`, with no
  assumed kernel fact.  Both per-op realizations are theorems.  A batch /
  multi-scalar version (`n` chained combine steps, the batch-verification shape)
  is grounded the same way via `pipeN`.

* **The hash-to-challenge step** (`c = hash(R ‖ M)`) is a *separate* carrier and
  is the proved `ConcreteHashRealizer.sha256_realizes_concrete` (over `.TBytes
  32`) — unconditional, but on the byte-state carrier, not the scalar field.  We
  keep the scalar-field combine as the headline and note the hash as a proved but
  separate row.

* **The EC point operations** (`s·G`, `c·P`, the point add `R + c·P`) are NOT
  field-arithmetic: they are elliptic-curve group operations with no concrete
  field realizer.  They are the **honest residual** of this grounding — only the
  scalar-field response equation is grounded here, which is the genuine
  groundable part of the verification arithmetic.

* **The only machine-code residual (NOT a per-kernel hypothesis):** that the
  jasmin-emitted bytes of the real `scalar_mul` / `scalar_add` kernels equal the
  combined leafSpec's arms — the owned-machine-code route, a single global
  obligation, not one of the per-op realizations this file discharges.

## References
* RFC 8032 (EdDSA / Ed25519), the Schnorr Σ-protocol signature.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedSignatureCore

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol

/-! ## §1  The Schnorr / EdDSA scalar response combine `x ↦ c·x + r`

The response `s = r + c·x` is — over the scalar field — a `field_mul` by the
challenge `c` followed by a `field_add` by the nonce `r`.  We dispatch both
through the single `alternatingLeafSpec a v` of `GroundedMultiKernelProtocol`,
whose `"field_mul"` arm is mul-by-`v` and whose `"field_add"` arm is add-by-`a`.
Setting `v := c` (the challenge) and `a := r` (the nonce) makes the two
combined-by-constant arms exactly the Schnorr response's two scalar steps. -/

/-- The Schnorr scalar-multiply kernel leaf (`c·x`). -/
def schnorrMulLeaf : String := "field_mul"

/-- The Schnorr scalar-add kernel leaf (`r + c·x`). -/
def schnorrAddLeaf : String := "field_add"

/-- The single combined-dispatch leafSpec for the Schnorr response: one concrete
    `LeafSpec` whose `"field_mul"` arm is mul-by-the-challenge-`c` and whose
    `"field_add"` arm is add-by-the-nonce-`r`.  Reuses
    `GroundedMultiKernelProtocol.alternatingLeafSpec` with add-constant `r` and
    mul-constant `c`. -/
def schnorrResponseLeafSpec (q : ℕ) [NeZero q] (width : ℕ) (c r : ZMod q)
    (limbStore : LimbStoreSpec) : LeafSpec :=
  alternatingLeafSpec q width r c limbStore

/-- **The mul-step realization — a THEOREM (no kernel hypothesis).**  Through the
    combined Schnorr leafSpec, the `"field_mul"` leaf realizes the unary spec
    `(· * c)` (multiply the running scalar by the challenge).  Proved from
    `GroundedMultiKernelProtocol.alternating_realizes_mul`, in turn the proved
    `combined_realizes_mul` + the codec round-trip. -/
theorem schnorrResponse_realizes_mul (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := q) width) (· * c) schnorrMulLeaf
      (schnorrResponseLeafSpec q width c r limbStore) :=
  alternating_realizes_mul q width hw hq r c limbStore

/-- **The add-step realization — a THEOREM (no kernel hypothesis).**  Through the
    same combined leafSpec, the `"field_add"` leaf realizes the unary spec
    `(· + r)` (add the nonce).  Proved from
    `GroundedMultiKernelProtocol.alternating_realizes_add`, in turn the proved
    `combined_realizes_add` + the codec round-trip. -/
theorem schnorrResponse_realizes_add (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeF (q := q) width) (· + r) schnorrAddLeaf
      (schnorrResponseLeafSpec q width c r limbStore) :=
  alternating_realizes_add q width hw hq r c limbStore

/-! ### The headline: the grounded two-step response `x ↦ c·x + r`

The Schnorr / EdDSA response equation over the scalar field — `field_mul` by `c`
then `field_add` by `r` — assembled through the single combined leafSpec.  We
use the genuine `pipeN` / `composeSpecs` form (the `ProtocolKernels.runRealizes`
shape), with the per-step realization bundle discharged by the two proved
theorems above (no hypothesis). -/

/-- The Schnorr-response leaf list `["field_mul", "field_add"]` — multiply by the
    challenge, then add the nonce. -/
def schnorrResponseLeaves : List String :=
  [schnorrMulLeaf, schnorrAddLeaf]

/-- The matching spec list `[(· * c), (· + r)]` — the two scalar steps of the
    response `s = r + c·x`. -/
def schnorrResponseSpecs (q : ℕ) [NeZero q] (c r : ZMod q) :
    List (ZMod q → ZMod q) :=
  [(· * c), (· + r)]

/-- The position-wise `Forall₂` of per-step realizations for the Schnorr response
    — the two proved step theorems.  No hypothesis. -/
theorem schnorrResponse_realized (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) :
    List.Forall₂
      (fun l s => KernelRealizes (decodeF (q := q) width) s l
        (schnorrResponseLeafSpec q width c r limbStore))
      schnorrResponseLeaves (schnorrResponseSpecs q c r) := by
  unfold schnorrResponseLeaves schnorrResponseSpecs
  exact List.Forall₂.cons
    (schnorrResponse_realizes_mul q width hw hq c r limbStore)
    (List.Forall₂.cons
      (schnorrResponse_realizes_add q width hw hq c r limbStore)
      List.Forall₂.nil)

/-- The bundled grounded Schnorr-response protocol: the two distinct scalar
    kernels of the single combined leafSpec, all per-step realizations discharged
    (no hypothesis). -/
def schnorrResponseProtocol (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) :
    ProtocolKernels (ZMod q) (schnorrResponseLeafSpec q width c r limbStore) where
  leaves := schnorrResponseLeaves
  specs := schnorrResponseSpecs q c r
  decode := decodeF width
  realized := schnorrResponse_realized q width hw hq c r limbStore

/-- **THE HEADLINE — grounded Schnorr / EdDSA scalar response, ZERO kernel
    hypotheses.**  The response equation `s = r + c·x` over the scalar field —
    `field_mul` by the challenge `c` then `field_add` by the nonce `r`, two
    DISTINCT kernels of the single combined leafSpec — has its whole `pipeN`
    computation decode to the composite of its per-step specs `[(· * c), (· +
    r)]`, i.e. to `(decodeF width xVal) · c + r`, with **ZERO `KernelRealizes` /
    `KernelRealizes2` hypotheses** (only the codec fit `width ≤ 48`, `q <
    2^(8·width)`).  Every per-op realization is a theorem
    (`schnorrResponse_realizes_mul` / `_add`, in turn `combined_realizes_mul` /
    `combined_realizes_add` + the codec round-trip).

    This is the genuine groundable part of the verification arithmetic: the
    EC point operations (`s·G`, `R + c·P`) are NOT field-arithmetic and have no
    concrete field realizer — they are the honest residual.  The only machine-code
    residual is the owned-emit obligation for the two combined arms — NOT a
    per-kernel hypothesis. -/
theorem grounded_schnorr_response_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) :
    decodeF width
        (pipeN (schnorrResponseLeafSpec q width c r limbStore)
          schnorrResponseLeaves oldDest xVal)
      = composeSpecs (schnorrResponseSpecs q c r) (decodeF width xVal) :=
  (schnorrResponseProtocol q width hw hq c r limbStore).runRealizes oldDest xVal

/-- The grounded response stated as a plain scalar identity: the whole emitted
    response pipeline decodes to `(decodeF width xVal) * c + r`.  A `composeSpecs`
    unfolding of `grounded_schnorr_response_realizes`; still ZERO kernel
    hypotheses. -/
theorem grounded_schnorr_response_eq (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) :
    decodeF width
        (pipeN (schnorrResponseLeafSpec q width c r limbStore)
          schnorrResponseLeaves oldDest xVal)
      = decodeF width xVal * c + r := by
  rw [grounded_schnorr_response_realizes q width hw hq c r limbStore oldDest xVal]
  simp [schnorrResponseSpecs, composeSpecs]

/-! ## §2  Batch verification: a chain of `n` response combines — grounded

Batch / multi-scalar verification runs the *same* scalar combine `x ↦ c·x + r`
across many signatures.  Modelled as the `pipeN`-chain of `n` copies of the
response leaf-pair, it grounds the same way: each per-step realization is one of
the two proved theorems, so the whole batch carries ZERO kernel hypotheses. -/

/-- The `n`-fold batch response leaf list: `n` copies of `["field_mul",
    "field_add"]`. -/
def batchResponseLeaves (n : ℕ) : List String :=
  (List.replicate n schnorrResponseLeaves).flatten

/-- The matching `n`-fold batch spec list: `n` copies of `[(· * c), (· + r)]`. -/
def batchResponseSpecs (q : ℕ) [NeZero q] (c r : ZMod q) (n : ℕ) :
    List (ZMod q → ZMod q) :=
  (List.replicate n (schnorrResponseSpecs q c r)).flatten

/-- The position-wise `Forall₂` of per-step realizations for the `n`-fold batch
    — `n` copies of the two proved step theorems.  No hypothesis. -/
theorem batchResponse_realized (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizes (decodeF (q := q) width) s l
        (schnorrResponseLeafSpec q width c r limbStore))
      (batchResponseLeaves n) (batchResponseSpecs q c r n) := by
  unfold batchResponseLeaves batchResponseSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ,
        List.flatten_cons, List.flatten_cons]
      refine List.rel_append ?_ ?_ <;>
        [exact schnorrResponse_realized q width hw hq c r limbStore; exact ih]

/-- The bundled grounded `n`-fold batch response protocol — every per-step
    realization discharged, no hypothesis. -/
def batchResponseProtocol (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) (n : ℕ) :
    ProtocolKernels (ZMod q) (schnorrResponseLeafSpec q width c r limbStore) where
  leaves := batchResponseLeaves n
  specs := batchResponseSpecs q c r n
  decode := decodeF width
  realized := batchResponse_realized q width hw hq c r limbStore n

/-- **GROUNDED batch-verification response — ZERO kernel hypotheses.**  An
    `n`-fold batch of the Schnorr / EdDSA scalar response combine `x ↦ c·x + r`
    (the multi-scalar / batch-verification shape) has its whole `pipeN`
    computation decode to the composite of its per-step specs, with **ZERO
    `KernelRealizes` hypotheses** (only the codec fit).  Every per-op realization
    is one of the two proved step theorems; the composition is the generic
    `runRealizes`.  The EC point operations remain the honest non-field residual;
    the only machine-code residual is the combined arms' owned-emit obligation. -/
theorem grounded_schnorr_batch_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (c r : ZMod q)
    (limbStore : LimbStoreSpec) (n : ℕ) (oldDest xVal : RustVal .TFp) :
    decodeF width
        (pipeN (schnorrResponseLeafSpec q width c r limbStore)
          (batchResponseLeaves n) oldDest xVal)
      = composeSpecs (batchResponseSpecs q c r n) (decodeF width xVal) :=
  (batchResponseProtocol q width hw hq c r limbStore n).runRealizes oldDest xVal

end CatCrypt.Crypto.SecureCompilation.GroundedSignatureCore
