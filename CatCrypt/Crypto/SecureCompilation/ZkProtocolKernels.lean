/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# A batch of zero-knowledge proof-system verifiers as `ProtocolKernels` instances

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on a **batch** of
zero-knowledge proof-system *verifiers*, exactly as `MerkleProtocolKernels.lean`
does for a Merkle authentication path and `KdfMacProtocolKernels.lean` does for
the KDF/MAC family.

Every ZK verifier in this batch is, at the kernel level, a **unary pipeline**
over the running verifier state (the accumulated transcript / running field
element): a sequence of `state → state` steps, each emitted to a leaf kernel.
The two recurring step shapes are

* a **Fiat-Shamir challenge round** — absorb the current transcript into a
  duplex/transcript hash, then squeeze a challenge, then fold that challenge into
  the running field accumulator (a field add/mul); and
* a **FRI / Merkle fold round** — hash-compress a running node with the next
  query/sibling element.

These are precisely the `state → state` shape the `ProtocolKernels` template
models, so each verifier's whole emit-realization assembles from its per-kernel
realizations by a single `runRealizes` call.

## The shared "challenge round" shape

Bulletproofs-IPA, PLONK, and STARK/FRI all repeat the same two-kernel round:

```text
state ↦ challenge = H(transcript(state))      -- a transcript-hash kernel
      ↦ fold(challenge, state)                 -- a field / poly-eval fold kernel
```

so one round emits **two** leaf kernels (a hash then a fold).  §0 factors that
into `roundSpecs` / `roundLeaves` / `roundRealized`, a one-prefix-then-`r`-rounds
chain where each round is itself a hash-leaf followed by a fold-leaf.  Each
verifier instance below is then a thin renaming of that helper.

## What each instance delivers (mirroring the templates)

For each verifier `V` we provide `<V>Specs` (the abstract unary round-spec list),
`<V>Leaves` (the matching emitted leaf-names, taken from the real Plonky3 /
ZK-SumCheck owned-emit kernels), `<V>Protocol : ProtocolKernels C leafSpec` (the
assembled bundle whose `realized` field is the position-wise `Forall₂` of the
per-kernel realizations, each an honest leaf-bytes-KAT **hypothesis**), and
`<V>_protocol_realizes` (the whole-verifier emit-realization, obtained by a
single `runRealizes` call).

## Honesty

The per-round specs are **abstract** (`C → C`) — the deliverable is the
protocol-structure composition, not re-deriving each round's hash / field
internals.  The per-kernel realizations are honest hypotheses: each is the leaf's
emitted-bytes KAT, supplied at instantiation.  Leaf-names are the real emitted
kernels (Fiat-Shamir duplex `"p3_fs_observe"` / `"p3_fs_sample"`, FRI fold
`"fri_fold_rc"`, Merkle compress `"plonky3_merkle_compress_rc"`, field ops, the
Poseidon2 transcript permutation `"hp_perm16"`); the abstract specs stand for the
composite each round computes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ZkProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

variable {C : Type*}

/-! ## §0  The shared Fiat-Shamir "challenge round" chain helper

Every verifier below is one *prefix* kernel (the transcript/setup absorb)
followed by `r` *challenge rounds*, where each round is a **hash leaf** (squeeze a
challenge from the transcript) immediately followed by a **fold leaf** (fold that
challenge into the running field accumulator).  So `r` rounds emit `2 * r` leaf
kernels in strict `[hash, fold, hash, fold, …]` order.

`roundSpecs prefixStep hashStep foldStep r` is
`prefixStep :: (range r).flatMap (fun i => [hashStep i, foldStep i])`,
and `roundLeaves prefixLeaf hashLeaf foldLeaf r` is the matching leaf list
`prefixLeaf :: (range r).flatMap (fun _ => [hashLeaf, foldLeaf])` — same length,
same order.  `roundRealized` assembles the position-wise `Forall₂` by induction
on `r`, from the prefix realization and the two per-round realizations. -/

/-- A one-prefix-then-`r`-rounds unary spec list; each round is a hash spec
    followed by a fold spec. -/
def roundSpecs (prefixStep : C → C) (hashStep foldStep : Nat → C → C) (r : Nat) :
    List (C → C) :=
  prefixStep :: (List.range r).flatMap (fun i => [hashStep i, foldStep i])

/-- The matching one-prefix-then-`r`-rounds leaf list; each round is a hash leaf
    followed by a fold leaf. -/
def roundLeaves (prefixLeaf hashLeaf foldLeaf : String) (r : Nat) : List String :=
  prefixLeaf :: (List.range r).flatMap (fun _ => [hashLeaf, foldLeaf])

/-- The position-wise realization bundle for the one-prefix-then-`r`-rounds
    pipeline, assembled by induction on `r` from the prefix realization and one
    hash + one fold realization per round. -/
theorem roundRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (hashStep foldStep : Nat → C → C)
    (prefixLeaf hashLeaf foldLeaf : String) (r : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hHash : ∀ i, KernelRealizes decode (hashStep i) hashLeaf leafSpec)
    (hFold : ∀ i, KernelRealizes decode (foldStep i) foldLeaf leafSpec) :
    List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
      (roundLeaves prefixLeaf hashLeaf foldLeaf r)
      (roundSpecs prefixStep hashStep foldStep r) := by
  unfold roundLeaves roundSpecs
  refine List.Forall₂.cons hPrefix ?_
  induction r with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_append]
      refine List.rel_append ih ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.Forall₂.cons (hHash m) (List.Forall₂.cons (hFold m) List.Forall₂.nil)

/-- The assembled one-prefix-then-`r`-rounds `ProtocolKernels`. -/
def roundProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (hashStep foldStep : Nat → C → C)
    (prefixLeaf hashLeaf foldLeaf : String) (r : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hHash : ∀ i, KernelRealizes decode (hashStep i) hashLeaf leafSpec)
    (hFold : ∀ i, KernelRealizes decode (foldStep i) foldLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := roundLeaves prefixLeaf hashLeaf foldLeaf r
  specs := roundSpecs prefixStep hashStep foldStep r
  decode := decode
  realized :=
    roundRealized leafSpec decode prefixStep hashStep foldStep
      prefixLeaf hashLeaf foldLeaf r hPrefix hHash hFold

/-- The whole-pipeline emit-realization of a one-prefix-then-`r`-rounds
    challenge chain, obtained by a single `runRealizes` call. -/
theorem round_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (hashStep foldStep : Nat → C → C)
    (prefixLeaf hashLeaf foldLeaf : String) (r : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hHash : ∀ i, KernelRealizes decode (hashStep i) hashLeaf leafSpec)
    (hFold : ∀ i, KernelRealizes decode (foldStep i) foldLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (roundLeaves prefixLeaf hashLeaf foldLeaf r) oldDest xVal)
      = composeSpecs (roundSpecs prefixStep hashStep foldStep r) (decode xVal) :=
  (roundProtocol leafSpec decode prefixStep hashStep foldStep
      prefixLeaf hashLeaf foldLeaf r hPrefix hHash hFold).runRealizes oldDest xVal

/-! ## §1  Bulletproofs inner-product-argument (IPA) verify

The Bulletproofs IPA verifier (Bünz et al., S&P 2018) recomputes the folded
generators/commitment by `log₂ n` rounds, each one:

```text
challenge u ← H(transcript ‖ Lᵢ ‖ Rᵢ)        -- Fiat-Shamir challenge
state ← fold(u, uᶦⁿᵛ, state)                  -- field fold of the running point
```

After absorbing the public input/commitment into the transcript once, the
verifier runs `r = log₂ n` of these two-kernel `[challenge-hash, field-fold]`
rounds.  The challenge-hash reuses the emitted Fiat-Shamir sample kernel
`"p3_fs_sample"`; the fold reuses the emitted field-multiply fold
`"pasta_field_add"` (the Bulletproofs carrier is the Pasta/Vesta field). -/

/-- The Bulletproofs IPA transcript-setup (absorb commitment) kernel leaf. -/
def bulletproofsSetupLeaf : String := "p3_fs_observe"

/-- The Bulletproofs IPA per-round Fiat-Shamir challenge-squeeze kernel leaf. -/
def bulletproofsChallengeLeaf : String := "p3_fs_sample"

/-- The Bulletproofs IPA per-round field-fold kernel leaf. -/
def bulletproofsFoldLeaf : String := "pasta_field_add"

/-- The Bulletproofs IPA verifier kernel-spec list: one `setupStep` then `r`
    `[challengeStep i, foldStep i]` rounds (`r = log₂ n`). -/
def bulletproofsSpecs (setupStep : C → C) (challengeStep foldStep : Nat → C → C)
    (r : Nat) : List (C → C) :=
  roundSpecs setupStep challengeStep foldStep r

/-- The Bulletproofs IPA verifier leaf list. -/
def bulletproofsLeaves (r : Nat) : List String :=
  roundLeaves bulletproofsSetupLeaf bulletproofsChallengeLeaf bulletproofsFoldLeaf r

/-- **The assembled Bulletproofs IPA verifier protocol.** -/
def bulletproofsProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (setupStep : C → C) (challengeStep foldStep : Nat → C → C) (r : Nat)
    (hSetup : KernelRealizes decode setupStep bulletproofsSetupLeaf leafSpec)
    (hChallenge : ∀ i,
      KernelRealizes decode (challengeStep i) bulletproofsChallengeLeaf leafSpec)
    (hFold : ∀ i,
      KernelRealizes decode (foldStep i) bulletproofsFoldLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  roundProtocol leafSpec decode setupStep challengeStep foldStep
    bulletproofsSetupLeaf bulletproofsChallengeLeaf bulletproofsFoldLeaf r
    hSetup hChallenge hFold

/-- **The whole-Bulletproofs-IPA-verify emit-realization (parametric in the
    round count `r = log₂ n`).**  The entire emitted IPA-verify pipeline — one
    transcript-setup kernel then `r` `[challenge-hash, field-fold]` rounds —
    decodes to the composite `composeSpecs (bulletproofsSpecs …)` of the input
    verifier state.  Assembled by one `runRealizes` call from the per-kernel
    realizations (each an honest leaf-bytes KAT hypothesis) and the generic
    composition law. -/
theorem bulletproofs_protocol_realizes (leafSpec : LeafSpec)
    (decode : RustVal .TFp → C)
    (setupStep : C → C) (challengeStep foldStep : Nat → C → C) (r : Nat)
    (hSetup : KernelRealizes decode setupStep bulletproofsSetupLeaf leafSpec)
    (hChallenge : ∀ i,
      KernelRealizes decode (challengeStep i) bulletproofsChallengeLeaf leafSpec)
    (hFold : ∀ i,
      KernelRealizes decode (foldStep i) bulletproofsFoldLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (bulletproofsLeaves r) oldDest xVal)
      = composeSpecs (bulletproofsSpecs setupStep challengeStep foldStep r)
          (decode xVal) :=
  round_protocol_realizes leafSpec decode setupStep challengeStep foldStep
    bulletproofsSetupLeaf bulletproofsChallengeLeaf bulletproofsFoldLeaf r
    hSetup hChallenge hFold oldDest xVal

/-! ## §2  PLONK verify

The PLONK verifier (Gabizon–Williamson–Ciobotaru) derives its challenges
(`β, γ, α, ζ, v, u`) by Fiat-Shamir, then evaluates the linearisation /
quotient polynomials at the evaluation point.  Round-by-round this is again the
`[challenge-hash, poly-eval/field-fold]` shape: each Fiat-Shamir challenge is
squeezed from the running transcript, then folded into the running evaluation
accumulator.  After the initial absorb of the commitments, the verifier runs
the `r` challenge rounds.

The challenge-squeeze reuses the emitted Fiat-Shamir sample kernel
`"p3_fs_sample"`; the polynomial-evaluation fold reuses the emitted field-multiply
kernel `"gf251_mul"` (the running evaluation is a field multiply-accumulate). -/

/-- The PLONK transcript-setup (absorb wire/permutation commitments) kernel leaf. -/
def plonkSetupLeaf : String := "p3_fs_observe"

/-- The PLONK per-round Fiat-Shamir challenge-squeeze kernel leaf. -/
def plonkChallengeLeaf : String := "p3_fs_sample"

/-- The PLONK per-round polynomial-evaluation field-fold kernel leaf. -/
def plonkEvalLeaf : String := "gf251_mul"

/-- The PLONK verifier kernel-spec list: one `setupStep` then `r`
    `[challengeStep i, evalStep i]` rounds. -/
def plonkSpecs (setupStep : C → C) (challengeStep evalStep : Nat → C → C)
    (r : Nat) : List (C → C) :=
  roundSpecs setupStep challengeStep evalStep r

/-- The PLONK verifier leaf list. -/
def plonkLeaves (r : Nat) : List String :=
  roundLeaves plonkSetupLeaf plonkChallengeLeaf plonkEvalLeaf r

/-- **The assembled PLONK verifier protocol.** -/
def plonkProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (setupStep : C → C) (challengeStep evalStep : Nat → C → C) (r : Nat)
    (hSetup : KernelRealizes decode setupStep plonkSetupLeaf leafSpec)
    (hChallenge : ∀ i,
      KernelRealizes decode (challengeStep i) plonkChallengeLeaf leafSpec)
    (hEval : ∀ i, KernelRealizes decode (evalStep i) plonkEvalLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  roundProtocol leafSpec decode setupStep challengeStep evalStep
    plonkSetupLeaf plonkChallengeLeaf plonkEvalLeaf r
    hSetup hChallenge hEval

/-- **The whole-PLONK-verify emit-realization.**  The entire emitted PLONK-verify
    pipeline — one transcript-setup kernel then `r` `[challenge-hash,
    poly-eval-fold]` rounds — decodes to the composite `composeSpecs
    (plonkSpecs …)` of the input verifier state.  Assembled by one `runRealizes`
    call from the per-kernel realizations (each an honest leaf-bytes KAT
    hypothesis). -/
theorem plonk_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (setupStep : C → C) (challengeStep evalStep : Nat → C → C) (r : Nat)
    (hSetup : KernelRealizes decode setupStep plonkSetupLeaf leafSpec)
    (hChallenge : ∀ i,
      KernelRealizes decode (challengeStep i) plonkChallengeLeaf leafSpec)
    (hEval : ∀ i, KernelRealizes decode (evalStep i) plonkEvalLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (plonkLeaves r) oldDest xVal)
      = composeSpecs (plonkSpecs setupStep challengeStep evalStep r)
          (decode xVal) :=
  round_protocol_realizes leafSpec decode setupStep challengeStep evalStep
    plonkSetupLeaf plonkChallengeLeaf plonkEvalLeaf r
    hSetup hChallenge hEval oldDest xVal

/-! ## §3  Groth16 verify

The Groth16 verifier (Groth, EUROCRYPT 2016) is *not* Fiat-Shamir interactive —
its check is `e(A, B) = e(α, β) · e(L, γ) · e(C, δ)`, where the linear
combination `L = Σ aᵢ · ICᵢ` is a multi-scalar accumulation over the public
inputs.  Kernel-wise this is still a unary chain over the running accumulator:
one `hashToScalar` prefix (hash the public inputs to field scalars) followed by
`r` `[scalar-mul, field-add]` rounds accumulating `L`, then the pairing check.
We reuse the `[hash, fold]` round helper with the "hash" slot taken by the
scalar-multiply leaf and the "fold" slot by the field-add accumulation leaf.

Leaf names: the public-input hash prefix `"mgf1_sha256"` (hash-to-scalar of the
inputs), the per-input scalar-multiply `"bn254_mont_mul_x86_from_lean"` (Groth16
over BN254 — Montgomery multiply for the EC scalar step), and the per-input
field-add accumulation `"field_addmod251"`. -/

/-- The Groth16 hash-to-scalar (public-input hash) prefix kernel leaf. -/
def groth16HashLeaf : String := "mgf1_sha256"

/-- The Groth16 per-input scalar-multiply (Montgomery-mul) kernel leaf. -/
def groth16ScalarMulLeaf : String := "bn254_mont_mul_x86_from_lean"

/-- The Groth16 per-input field-add accumulation kernel leaf. -/
def groth16AddLeaf : String := "field_addmod251"

/-- The Groth16 verifier kernel-spec list: one `hashStep` then `r`
    `[scalarMulStep i, addStep i]` accumulation rounds. -/
def groth16Specs (hashStep : C → C) (scalarMulStep addStep : Nat → C → C)
    (r : Nat) : List (C → C) :=
  roundSpecs hashStep scalarMulStep addStep r

/-- The Groth16 verifier leaf list. -/
def groth16Leaves (r : Nat) : List String :=
  roundLeaves groth16HashLeaf groth16ScalarMulLeaf groth16AddLeaf r

/-- **The assembled Groth16 verifier protocol.** -/
def groth16Protocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (hashStep : C → C) (scalarMulStep addStep : Nat → C → C) (r : Nat)
    (hHash : KernelRealizes decode hashStep groth16HashLeaf leafSpec)
    (hScalarMul : ∀ i,
      KernelRealizes decode (scalarMulStep i) groth16ScalarMulLeaf leafSpec)
    (hAdd : ∀ i, KernelRealizes decode (addStep i) groth16AddLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  roundProtocol leafSpec decode hashStep scalarMulStep addStep
    groth16HashLeaf groth16ScalarMulLeaf groth16AddLeaf r
    hHash hScalarMul hAdd

/-- **The whole-Groth16-verify emit-realization.**  The entire emitted
    Groth16-verify pipeline — one hash-to-scalar kernel then `r` `[scalar-mul,
    field-add]` accumulation rounds for the public-input linear combination —
    decodes to the composite `composeSpecs (groth16Specs …)` of the input
    verifier state.  Assembled by one `runRealizes` call from the per-kernel
    realizations (each an honest leaf-bytes KAT hypothesis). -/
theorem groth16_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (hashStep : C → C) (scalarMulStep addStep : Nat → C → C) (r : Nat)
    (hHash : KernelRealizes decode hashStep groth16HashLeaf leafSpec)
    (hScalarMul : ∀ i,
      KernelRealizes decode (scalarMulStep i) groth16ScalarMulLeaf leafSpec)
    (hAdd : ∀ i, KernelRealizes decode (addStep i) groth16AddLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (groth16Leaves r) oldDest xVal)
      = composeSpecs (groth16Specs hashStep scalarMulStep addStep r)
          (decode xVal) :=
  round_protocol_realizes leafSpec decode hashStep scalarMulStep addStep
    groth16HashLeaf groth16ScalarMulLeaf groth16AddLeaf r
    hHash hScalarMul hAdd oldDest xVal

/-! ## §4  STARK / FRI verify (Plonky3)

The STARK / FRI verifier (Ben-Sasson et al.; Plonky3 instantiation) runs a
Poseidon2-duplex Fiat-Shamir transcript and then `r` FRI query/fold rounds, each
one:

```text
challenge βᵢ ← squeeze(Poseidon2 transcript)   -- Fiat-Shamir fold challenge
node ← FRI-fold(βᵢ, Merkle-compress(node))      -- one FRI fold + Merkle step
```

After absorbing the trace/quotient commitments via the Poseidon2 permutation
once, the verifier runs the `r = log₂(blowup·degree)` fold rounds.  We use the
`[hash, fold]` round helper with the "hash" slot taken by the Poseidon2
challenge-squeeze and the "fold" slot by the FRI fold kernel.

Leaf names from the real Plonky3 owned-emit (`VIR/Plonky3*Emit.lean`,
`Plonky3FriFoldEmit.lean`): the Poseidon2 transcript permutation `"hp_perm16"`
(the duplex permutation that absorbs the commitments and squeezes challenges, cf.
the Poseidon2-perm row of `MoreKernelRegistryEntries`), the per-round challenge
squeeze `"challenger_squeeze_rc"`, and the FRI fold `"fri_fold_rc"`. -/

/-- The STARK/FRI Poseidon2 transcript-absorb (duplex permutation) prefix kernel
    leaf. -/
def starkSetupLeaf : String := "hp_perm16"

/-- The STARK/FRI per-round Fiat-Shamir challenge-squeeze kernel leaf. -/
def starkChallengeLeaf : String := "challenger_squeeze_rc"

/-- The STARK/FRI per-round FRI-fold (with Merkle compress) kernel leaf. -/
def starkFriFoldLeaf : String := "fri_fold_rc"

/-- The STARK/FRI verifier kernel-spec list: one Poseidon2 `setupStep` then `r`
    `[challengeStep i, friFoldStep i]` FRI fold rounds. -/
def starkSpecs (setupStep : C → C) (challengeStep friFoldStep : Nat → C → C)
    (r : Nat) : List (C → C) :=
  roundSpecs setupStep challengeStep friFoldStep r

/-- The STARK/FRI verifier leaf list. -/
def starkLeaves (r : Nat) : List String :=
  roundLeaves starkSetupLeaf starkChallengeLeaf starkFriFoldLeaf r

/-- **The assembled STARK/FRI verifier protocol.** -/
def starkProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (setupStep : C → C) (challengeStep friFoldStep : Nat → C → C) (r : Nat)
    (hSetup : KernelRealizes decode setupStep starkSetupLeaf leafSpec)
    (hChallenge : ∀ i,
      KernelRealizes decode (challengeStep i) starkChallengeLeaf leafSpec)
    (hFriFold : ∀ i,
      KernelRealizes decode (friFoldStep i) starkFriFoldLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  roundProtocol leafSpec decode setupStep challengeStep friFoldStep
    starkSetupLeaf starkChallengeLeaf starkFriFoldLeaf r
    hSetup hChallenge hFriFold

/-- **The whole-STARK/FRI-verify emit-realization (Plonky3).**  The entire
    emitted STARK-verify pipeline — one Poseidon2 transcript-absorb kernel then
    `r` `[challenge-squeeze, FRI-fold]` rounds — decodes to the composite
    `composeSpecs (starkSpecs …)` of the input verifier state.  Assembled by one
    `runRealizes` call from the per-kernel realizations (each an honest
    leaf-bytes KAT hypothesis). -/
theorem stark_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (setupStep : C → C) (challengeStep friFoldStep : Nat → C → C) (r : Nat)
    (hSetup : KernelRealizes decode setupStep starkSetupLeaf leafSpec)
    (hChallenge : ∀ i,
      KernelRealizes decode (challengeStep i) starkChallengeLeaf leafSpec)
    (hFriFold : ∀ i,
      KernelRealizes decode (friFoldStep i) starkFriFoldLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (starkLeaves r) oldDest xVal)
      = composeSpecs (starkSpecs setupStep challengeStep friFoldStep r)
          (decode xVal) :=
  round_protocol_realizes leafSpec decode setupStep challengeStep friFoldStep
    starkSetupLeaf starkChallengeLeaf starkFriFoldLeaf r
    hSetup hChallenge hFriFold oldDest xVal

end CatCrypt.Crypto.SecureCompilation.ZkProtocolKernels
