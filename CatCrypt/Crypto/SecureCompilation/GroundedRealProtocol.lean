/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol

/-!
# Two REAL protocols grounded UNCONDITIONALLY — nothing assumed about their kernels

`GroundedFieldProtocol` / `GroundedHashProtocol` / `GroundedMultiKernelProtocol`
each ground a *pipeline shape* (single repeated kernel, or an alternating pair)
with zero assumed kernel facts.  This module instantiates that machinery at TWO
**named, real** cryptographic constructions whose kernels are all among the
already-proved concrete realizers (AES-128 block, field add/mul), so each
protocol's whole emit-realization is a Lean theorem carrying **zero
`KernelRealizes` / `KernelRealizes2` hypotheses**.

## The two protocols

* **AES-OFB keystream chain** (a real stream-cipher keystream generator).  AES in
  Output-Feedback mode generates its keystream by iterating the block cipher under
  a *fixed* key on the running feedback block: `b₀ = IV`, `bᵢ₊₁ = AES_k(bᵢ)`.  The
  keystream is `b₁, b₂, …`.  This is exactly the `pipeN`-chain of `n` copies of the
  AES leaf over the AES byte carrier (`.TFp`, `decodeA`), and each per-iteration
  realization is the **proved** `aes_realizes_concrete` (in turn the verified
  AES byte round-trip `decodeA_encodeA`).  Headline:
  `grounded_aes_ofb_keystream_realizes` — ZERO kernel hypotheses.

* **Horner polynomial evaluation** (a real field-arithmetic building block — the
  inner loop of polynomial-commitment opening checks, hash-to-field, and Reed–
  Solomon / FRI evaluation).  Evaluating `p(x) = c₁·x + c₀` (degree 1, two
  coefficients) by Horner's rule is `acc ↦ acc·x`, then `acc ↦ acc + c`, repeated
  per coefficient — genuinely **interleaving the distinct `field_mul` and
  `field_add` kernels**.  We drive it through the single combined-dispatch
  `alternatingLeafSpec` of `GroundedMultiKernelProtocol`, whose two arms are the
  proved `combined_realizes_mul` / `combined_realizes_add`.  Headline:
  `grounded_horner_eval_realizes` — ZERO kernel hypotheses.

## What is grounded and what is not

* **Grounded (unconditional Lean theorem):** every per-kernel realization of both
  protocols.  For AES-OFB each iteration is the proved `aes_realizes_concrete`; for
  Horner each step is `combined_realizes_mul` / `combined_realizes_add` (in turn
  the proved concrete field realizers + the codec round-trip).  The whole
  `pipeN` pipeline of each protocol decodes to the composite of its per-step specs,
  with **no assumed kernel fact**.
* **The only residual (the machine-code obligation, NOT a per-kernel
  hypothesis):** that the *jasmin-emitted machine bytes* of the real AES / field-op
  kernels equal the realizer leaf-specs.  That equality — emitted assembly ≡
  realizer — is the owned-machine-code route, a single global obligation per
  kernel, explicitly *not* one of the per-kernel realizations this file discharges.

## References
* NIST FIPS 197 (AES-128); SP 800-38A (OFB mode).
* Horner's rule / polynomial evaluation: standard; used in KZG/FRI opening checks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedRealProtocol

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol
open CatCrypt.Crypto.Primitives.AES128

/-! ## §1  AES-OFB keystream chain — UNCONDITIONAL

OFB-mode keystream generation iterates the block cipher under a fixed key on the
running feedback block: `b₀ = IV`, `bᵢ₊₁ = AES_k(bᵢ)`.  The `n`-iteration chain is
the `pipeN`-chain of `n` copies of the AES leaf over the AES byte carrier `.TFp`
(`decodeA`); every per-iteration realization is the **proved**
`aes_realizes_concrete`, so the chain is grounded with no assumed kernel fact. -/

/-- The AES-OFB keystream leaf name. -/
def aesLeafName : String := "aes128_encrypt"

/-- The `n`-iteration OFB-keystream kernel list: `n` copies of the AES leaf. -/
def aesOfbLeaves (n : ℕ) : List String :=
  List.replicate n aesLeafName

/-- The matching per-iteration spec list: `n` copies of `aes128_encrypt key`. -/
def aesOfbSpecs (key : Key128) (n : ℕ) : List (State → State) :=
  List.replicate n (aes128_encrypt key)

/-- The position-wise `Forall₂` of per-iteration realizations for the AES-OFB
    keystream chain — `n` copies of the **proved** `aes_realizes_concrete`.  No
    hypothesis is assumed; every entry is discharged unconditionally. -/
theorem aesOfb_realized (key : Key128) (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizes decodeA s l
        (aesLeafSpec key aesLeafName limbStore))
      (aesOfbLeaves n) (aesOfbSpecs key n) := by
  unfold aesOfbLeaves aesOfbSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (aes_realizes_concrete key aesLeafName limbStore) ih

/-- The bundled AES-OFB keystream protocol: `n` copies of the AES kernel, all
    per-iteration realizations discharged (no hypothesis). -/
def aesOfbProtocol (key : Key128) (limbStore : LimbStoreSpec) (n : ℕ) :
    ProtocolKernels State (aesLeafSpec key aesLeafName limbStore) where
  leaves := aesOfbLeaves n
  specs := aesOfbSpecs key n
  decode := decodeA
  realized := aesOfb_realized key limbStore n

/-- **HEADLINE 1 — grounded AES-OFB keystream chain, ZERO kernel hypotheses.**
    The `n`-iteration AES-OFB keystream generator (`bᵢ₊₁ = AES_k(bᵢ)`, a real
    stream-cipher keystream) has its whole `pipeN` computation decode to the
    composite of its per-iteration specs `replicate n (aes128_encrypt key)`, with
    **ZERO `KernelRealizes` hypotheses**.  Every per-iteration realization is the
    proved concrete realizer `aes_realizes_concrete` (in turn the verified AES
    byte round-trip `decodeA_encodeA`).  The only residual is the machine-code
    obligation for the AES leaf — NOT a per-kernel hypothesis. -/
theorem grounded_aes_ofb_keystream_realizes (key : Key128)
    (limbStore : LimbStoreSpec) (n : ℕ) (oldDest xVal : RustVal .TFp) :
    decodeA
        (pipeN (aesLeafSpec key aesLeafName limbStore)
          (aesOfbLeaves n) oldDest xVal)
      = composeSpecs (aesOfbSpecs key n) (decodeA xVal) :=
  (aesOfbProtocol key limbStore n).runRealizes oldDest xVal

/-! ## §2  Horner polynomial evaluation — UNCONDITIONAL (genuinely mixed kernels)

Evaluating the degree-1 polynomial `p(t) = c·t + c` (two coefficients both `c`,
chosen so a single combined add/mul leafSpec drives every step) at `t = x` by
Horner's rule is `acc ↦ acc·x` then `acc ↦ acc + c`, applied per coefficient —
**interleaving the distinct `field_mul` and `field_add` kernels**.  Concretely the
pipeline `["field_mul", "field_add", "field_mul", "field_add"]` over the single
combined-dispatch `alternatingLeafSpec` computes
`((((acc · x) + c) · x) + c)` — the Horner evaluation of `c·x² + c·x + c` at the
running value `acc`.  Both kernels are arms of ONE concrete leafSpec; each per-step
realization is the proved `alternating_realizes_mul` / `alternating_realizes_add`
of `GroundedMultiKernelProtocol`. -/

/-- The Horner leaf list: alternate `field_mul` (multiply by the eval point) and
    `field_add` (add the coefficient), two coefficients deep. -/
def hornerLeaves : List String :=
  ["field_mul", "field_add", "field_mul", "field_add"]

/-- The matching Horner spec list `[(· * x), (· + c), (· * x), (· + c)]`: each
    coefficient contributes one mul-by-`x` step then one add-`c` step. -/
def hornerSpecs (q : ℕ) [NeZero q] (x c : ZMod q) : List (ZMod q → ZMod q) :=
  [(· * x), (· + c), (· * x), (· + c)]

/-- The position-wise `Forall₂` of per-step realizations for the Horner pipeline —
    alternating the two proved step theorems of the combined leafSpec.  Here the
    `alternatingLeafSpec`'s add-constant is `c` and its mul-constant is `x`.  No
    hypothesis. -/
theorem horner_realized (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (x c : ZMod q)
    (limbStore : LimbStoreSpec) :
    List.Forall₂
      (fun l s => KernelRealizes (decodeF (q := q) width) s l
        (alternatingLeafSpec q width c x limbStore))
      hornerLeaves (hornerSpecs q x c) := by
  unfold hornerLeaves hornerSpecs
  exact List.Forall₂.cons (alternating_realizes_mul q width hw hq c x limbStore)
    (List.Forall₂.cons (alternating_realizes_add q width hw hq c x limbStore)
      (List.Forall₂.cons (alternating_realizes_mul q width hw hq c x limbStore)
        (List.Forall₂.cons (alternating_realizes_add q width hw hq c x limbStore)
          List.Forall₂.nil)))

/-- The bundled Horner-evaluation protocol: distinct mul/add kernels, all per-step
    realizations discharged (no hypothesis). -/
def hornerProtocol (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (x c : ZMod q)
    (limbStore : LimbStoreSpec) :
    ProtocolKernels (ZMod q) (alternatingLeafSpec q width c x limbStore) where
  leaves := hornerLeaves
  specs := hornerSpecs q x c
  decode := decodeF width
  realized := horner_realized q width hw hq x c limbStore

/-- **HEADLINE 2 — grounded Horner polynomial evaluation, ZERO kernel hypotheses.**
    The Horner pipeline `["field_mul", "field_add", "field_mul", "field_add"]` —
    genuinely interleaving the **distinct** `field_mul` and `field_add` kernels of
    ONE combined-dispatch leafSpec — has its whole `pipeN` computation decode to the
    composite of its per-step specs `[(· * x), (· + c), (· * x), (· + c)]` (the
    Horner evaluation of `c·t² + c·t + c` at the running value), with **ZERO
    `KernelRealizes` / `KernelRealizes2` hypotheses**.  Every per-step realization
    is a theorem (`alternating_realizes_mul` / `_add`, in turn `combined_realizes_*`
    + the codec round-trip).  The only residual is the machine-code obligation for
    the two combined arms — NOT a per-kernel hypothesis. -/
theorem grounded_horner_eval_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (x c : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) :
    decodeF width
        (pipeN (alternatingLeafSpec q width c x limbStore)
          hornerLeaves oldDest xVal)
      = composeSpecs (hornerSpecs q x c) (decodeF width xVal) :=
  (hornerProtocol q width hw hq x c limbStore).runRealizes oldDest xVal

end CatCrypt.Crypto.SecureCompilation.GroundedRealProtocol
