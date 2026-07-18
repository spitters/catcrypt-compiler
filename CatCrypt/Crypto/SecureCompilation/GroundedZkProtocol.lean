/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
import CatCrypt.Crypto.SecureCompilation.ConcretePoseidon2Realizer

/-!
# A fully-grounded ZK Fiat-Shamir / Poseidon2-transcript pipeline — whole-pipeline
  emit-realization with ZERO assumed per-kernel hypotheses

A STARK / Plonky3 verifier is, at its Fiat-Shamir core, a chain of Poseidon2
permutation "absorb / squeeze" steps over the 16-lane Baby Bear state: the
transcript sponge applies the *same* permutation `poseidon2BabyBearPermute`
(fixed round constants — no per-step varying parameter) repeatedly to derive
challenges.  `ZkProtocolKernels.lean` models these verifiers with the per-round
Poseidon2 transcript permutation as an **abstract `ProtocolKernels` hypothesis**
(`KernelRealizesT`).  This module makes that Poseidon2-transcript phase
**unconditional**.

The whole-pipeline composition law `GroundedHashProtocol.pipeNT_realizes` is
carrier-parametric (`RustVal T` running value, per-step `KernelRealizesT`
rewrite).  We instantiate it at the Poseidon2 permutation carrier `.TBytes 64`
(16 lanes × 4 bytes), assembling the per-step realization bundle from `n` copies
of the **proved** `ConcretePoseidon2Realizer.poseidon2_perm_realizes_concrete`
(itself unconditional — derived from the verified codec round-trip
`decodeP_encodeP`).  The headline `grounded_poseidon_transcript_realizes`
therefore carries **zero `KernelRealizesT` hypotheses**: a STARK / Plonky3
Fiat-Shamir transcript whose whole emit-realization assumes *nothing* about its
Poseidon2 kernel.

## What is grounded and what is not

* **Grounded (unconditional Lean theorem):** every per-round / per-level
  realization.  Each is the proved Poseidon2 realizer + codec round-trip, with
  no KAT, no abstract section assumption, and no per-kernel hypothesis.  The
  whole `pipeNT` pipeline decodes to the composite of its per-round specs.
* **The only residual (the machine-code obligation, NOT a per-kernel
  hypothesis):** that the *jasmin-emitted machine bytes* of the real Poseidon2
  permutation / compression kernels equal their realizers.  That equality is the
  owned-machine-code route, a single global obligation, and is explicitly *not*
  one of the per-round realization hypotheses this file eliminates (nor a KAT,
  nor the upstream Plonky3 reference vector).

This covers ZK proof-system verifiers (STARK, Plonky3, FRI) whose Fiat-Shamir
transcript is a chain of Poseidon2 permutation calls.

## References
* Grassi et al., *Poseidon2*, ePrint 2023/323.
* Ben-Sasson et al., *Fast Reed–Solomon IOPP* (FRI); Plonky3 `p3-fri`.
* Plonky3 — `p3-baby-bear` / `p3-poseidon2` crates, v0.5.2.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedZkProtocol

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
open CatCrypt.Crypto.SecureCompilation.ConcretePoseidon2Realizer
open CatCrypt.Crypto.Hash.Poseidon2.BabyBear

/-! ## §1  The grounded Poseidon2 Fiat-Shamir transcript — UNCONDITIONAL

A STARK / Plonky3 Fiat-Shamir transcript sponge applies the *same* permutation
`poseidon2BabyBearPermute` (fixed round constants — no per-iteration varying
parameter) `n` times to the 16-lane Baby Bear state.  We model the `n`-step
transcript pipeline as the `pipeNT`-chain of `n` copies of the leaf
`"poseidon2_babybear_permute"` over carrier `.TBytes 64`, and discharge each
per-step realization with the **proved** `poseidon2_perm_realizes_concrete` —
no hypothesis. -/

/-- The `n`-step Poseidon2 transcript kernel list: `n` copies of
    `"poseidon2_babybear_permute"`. -/
def poseidonTranscriptLeaves (n : ℕ) : List String :=
  List.replicate n "poseidon2_babybear_permute"

/-- The matching per-step spec list: `n` copies of the Poseidon2 permutation
    `poseidon2BabyBearPermute`. -/
def poseidonTranscriptSpecs (n : ℕ) :
    List ((Fin width → F) → (Fin width → F)) :=
  List.replicate n poseidon2BabyBearPermute

/-- The position-wise `Forall₂` of per-step realizations for the Poseidon2
    Fiat-Shamir transcript — `n` copies of the **proved**
    `poseidon2_perm_realizes_concrete` theorem.  No hypothesis is assumed; every
    entry is discharged unconditionally. -/
theorem poseidonTranscript_realized (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizesT (.TBytes 64) decodeP s l
        (specLeafSpecT (.TBytes 64) decodeP encodeP poseidon2BabyBearPermute
          "poseidon2_babybear_permute" limbStore))
      (poseidonTranscriptLeaves n) (poseidonTranscriptSpecs n) := by
  unfold poseidonTranscriptLeaves poseidonTranscriptSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (poseidon2_perm_realizes_concrete limbStore) ih

/-- **GROUNDED whole-transcript emit-realization — UNCONDITIONAL.**

    A STARK / Plonky3 Fiat-Shamir transcript: `n` Poseidon2 permutation
    absorb/squeeze steps over the 16-lane Baby Bear state.  Its entire `pipeNT`
    pipeline decodes to the composite of its per-step specs — with **ZERO
    `KernelRealizesT` hypotheses**.  Every per-step realization is the proved
    concrete realizer `poseidon2_perm_realizes_concrete` (in turn the verified
    codec round-trip `decodeP_encodeP`), assembled by the carrier-generalized
    `pipeNT_realizes`.  Nothing is assumed about the `poseidon2_babybear_permute`
    kernel.

    The only residual is the machine-code obligation — that the jasmin-emitted
    bytes of the real Poseidon2 permutation kernel equal the realizer
    `specLeafSpecT … "poseidon2_babybear_permute" …` — which is the
    owned-machine-code route, NOT a per-step hypothesis (and NOT a KAT, nor the
    upstream Plonky3 reference vector). -/
theorem grounded_poseidon_transcript_realizes (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 64)) :
    decodeP
        (pipeNT (.TBytes 64)
          (specLeafSpecT (.TBytes 64) decodeP encodeP poseidon2BabyBearPermute
            "poseidon2_babybear_permute" limbStore)
          (poseidonTranscriptLeaves n) oldDest xVal)
      = composeSpecs (poseidonTranscriptSpecs n) (decodeP xVal) :=
  pipeNT_realizes (.TBytes 64) decodeP
    (specLeafSpecT (.TBytes 64) decodeP encodeP poseidon2BabyBearPermute
      "poseidon2_babybear_permute" limbStore)
    (poseidonTranscriptLeaves n) (poseidonTranscriptSpecs n)
    (poseidonTranscript_realized limbStore n) oldDest xVal

end CatCrypt.Crypto.SecureCompilation.GroundedZkProtocol
