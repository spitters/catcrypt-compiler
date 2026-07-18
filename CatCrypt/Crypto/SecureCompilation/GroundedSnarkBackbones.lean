/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GroundedZkProtocol
import CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol
import CatCrypt.Crypto.SecureCompilation.GroundedKdfKem

/-!
# Grounded SNARK / STARK proof-system computational backbones — whole-pipeline
  emit-realization with ZERO assumed per-kernel hypotheses

This module grounds the **computational backbones** of modern SNARK / STARK
proof systems **unconditionally** — every per-step realization is a *theorem* (a
proved concrete realizer), so each headline carries **zero
`KernelRealizesT` / `KernelRealizes` / `KernelRealizes2` hypotheses** (only
codec-fit side conditions, honestly flagged).  The three backbones are the ones
that dominate a PLONK / Groth16 / STARK / FRI prover and verifier:

1. the **Fiat–Shamir transcript / challenge derivation** — a Keccak (SHA-3 /
   SHAKE) sponge absorbing the transcript, the non-interactive heart of every
   FS-compiled argument;
2. the **sum-check round / FRI folding step** — a field-arithmetic Horner
   evaluation `p(r) = (⋯(c_d·r + c_{d-1})·r + ⋯)·r + c_0`, the linear-combination
   each interactive round (or each FRI fold) computes; and
3. the **Merkle / vector commitment** — a Poseidon2 (STARK / Plonky3) or Keccak
   2-to-1 compression, the commitment layer a STARK / FRI verifier opens.

Each reuses the proved concrete realizers already in-repo:

* `ConcreteHashRealizer.keccak_realizes_concrete` — the Keccak `keccak_f` leaf
  over the `.TBytes 200` (1600-bit) carrier, decoding to `keccak_f steps` for
  **every** input (in turn the verified codec round-trip
  `decodeKbytes_encodeKbytes`).  Axiom-clean
  (`{propext, Classical.choice, Quot.sound}` only).
* `GroundedMultiKernelProtocol.combined_realizes_add` / `combined_realizes_mul`
  — one combined leafSpec realizing BOTH the `field_add` and `field_mul`
  kernels as theorems (in turn `ConcreteSymFieldRealizer.fieldAdd/Mul_realizes_concrete`
  + the codec round-trip `decodeF_encodeF`).  Strictly axiom-clean.
* `ConcretePoseidon2Realizer.poseidon2_compress_realizes_concrete` — the
  Poseidon2 2-to-1 compression leaf (`KernelRealizes2` over the 4-byte Baby Bear
  field codec `decodeF 4`), proved unconditionally from the verified codec
  round-trip `decodeF_encodeF`.  Strictly axiom-clean.
* `ProtocolEmitRealizes.pipeNT` / `composeSpecs` — the carrier-generic
  composition law for the transcript sponge chain.

## The grounded backbones

* **`grounded_fiat_shamir_transcript_realizes`** — the Fiat–Shamir transcript /
  challenge-derivation sponge.  A PLONK / Groth16 / STARK verifier squeezes its
  random challenges by hashing the running transcript: absorbing the `n`
  transcript blocks into the 1600-bit Keccak sponge is `n` applications of the
  `keccak_f` permutation, modeled as the `pipeNT (.TBytes 200)`-chain, every
  per-block realization the proved `keccak_realizes_concrete`.  **ZERO kernel
  hypotheses.**

* **`grounded_sumcheck_round_realizes` / `grounded_fri_fold_realizes`** — the
  sum-check round / FRI folding field step.  A sum-check verifier folds the
  prover's univariate `g(X)` at the challenge `r` by Horner evaluation
  `p(r) = (⋯(c_d·r + c_{d-1})·r + ⋯)·r + c_0`; a FRI fold computes the same
  affine combination `f_{i+1}(x) = f_i^{even}(x) + r·f_i^{odd}(x)`.  Each is the
  mul-then-add step `x ↦ x · r + c` over the combined field leafSpec, exercising
  the **distinct** `field_mul` then `field_add` kernels — grounded from
  `combined_realizes_mul` / `combined_realizes_add`.  The full degree-`d` Horner
  evaluation is that step folded over the coefficient list
  (`grounded_horner_fold_realizes`).  **ZERO kernel hypotheses.**

* **`grounded_poseidon_vector_commitment_realizes` /
  `grounded_keccak_vector_commitment_realizes`** — the Merkle / vector
  commitment.  A STARK / Plonky3 verifier opens a Poseidon2 Merkle tree whose
  internal node is the 2-to-1 compression `H(left, right)`, grounded as a
  `KernelRealizes2` theorem from `poseidon2_compress_realizes_concrete`; the
  Keccak-tree variant grounds an `n`-block sponge commitment from
  `keccak_realizes_concrete`.  **ZERO kernel hypotheses.**

## HONEST scope — what is grounded and what is NOT

* **Grounded (unconditional Lean theorems):** every per-step realization of all
  backbones — each a proved concrete realizer (`keccak_realizes_concrete`,
  `combined_realizes_add/mul`, `poseidon2_compress_realizes_concrete`), with no
  KAT and no per-kernel hypothesis.  Each whole pipeline decodes to the
  composite of its per-step specs.

* **The PROOF-SYSTEM SECURITY property is NOT what is grounded here.**  We ground
  the *computational backbone* — the field / hash / NTT KERNEL PIPELINE realized
  by emitted code — NOT the cryptographic security of the proof system.
  Concretely: SNARK / STARK **knowledge-soundness** and **completeness**, the
  Fiat–Shamir transform's **soundness** in the random-oracle model, **FRI
  low-degree-testing soundness**, sum-check **soundness** (the Schwartz–Zippel
  round-by-round bound), and **zero-knowledge** are separate, assumption-bearing
  results proved elsewhere (or out of scope).  This file says only: *the emitted
  Keccak / field / Poseidon2 kernel pipeline computes its arithmetic spec*,
  unconditionally.

* **Why Keccak / field / Poseidon2 and not SHA-256.**  Each backbone here has a
  proved concrete realizer whose codec round-trip is proved *per-bit* /
  *digit-sum* (axiom-clean).  The SHA-256 route is avoided because its codec
  round-trip uses a `bv_decide` LRAT certificate, which leaks a certificate
  axiom — out of policy for this file.

* **The only machine-code residual (NOT a per-kernel hypothesis):** that the
  *jasmin-emitted machine bytes* of the real Keccak / field-op / Poseidon2
  kernels equal the realizer leaf-specs — the owned-machine-code route, a single
  global obligation per kernel, explicitly not one of the per-step realizations
  this file discharges (nor a KAT).

## References
* Ben-Sasson et al., *Scalable, transparent, and post-quantum secure
  computational integrity* (STARK), ePrint 2018/046; Ben-Sasson et al., *Fast
  Reed–Solomon IOPP* (FRI), ICALP 2018.
* Gabizon–Williamson–Ciobotaru, *PLONK*, ePrint 2019/953; Groth, *On the size of
  pairing-based non-interactive arguments* (Groth16), EUROCRYPT 2016.
* Lund–Fortnow–Karloff–Nisan, *Algebraic methods for interactive proof systems*
  (sum-check), JACM 1992.
* Fiat–Shamir, *How to prove yourself*, CRYPTO 1986; NIST FIPS 202 (SHA-3 /
  SHAKE / sponge); Grassi et al., *Poseidon2*, ePrint 2023/323; Plonky3
  `p3-merkle-tree` vector commitments.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedSnarkBackbones

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.ConcretePoseidon2Realizer
open CatCrypt.Crypto.SecureCompilation.GroundedMultiKernelProtocol
open CatCrypt.Crypto.Hash.Poseidon2.BabyBear
open CatCrypt.Crypto.Hash.Keccak

/-! ## §1  Fiat–Shamir transcript / challenge derivation — UNCONDITIONAL

Every Fiat–Shamir-compiled argument (PLONK, Groth16's QAP transcript, a STARK /
FRI verifier) derives its random challenges by hashing the running protocol
transcript with a sponge.  At the leaf level the Keccak (SHA-3 / SHAKE) sponge
absorbs the `n` transcript blocks into the 1600-bit state by `n` applications of
the *same* permutation `keccak_f steps`.  We model the absorb as the
`pipeNT (.TBytes 200)`-chain of `n` copies of `"keccak_f1600"`, every per-block
realization the **proved** `keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-block Fiat–Shamir transcript leaf list: `n` copies of
    `"keccak_f1600"` (one Keccak permutation per absorbed transcript block). -/
def fsTranscriptLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the Fiat–Shamir transcript sponge. -/
def fsTranscriptSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED Fiat–Shamir transcript / challenge derivation — UNCONDITIONAL.**

    A PLONK / Groth16 / STARK verifier derives its random challenges by squeezing
    a Keccak (SHA-3 / SHAKE) sponge over the running transcript: absorbing the
    `n` transcript blocks into the 1600-bit Keccak state is `n` applications of
    the permutation `keccak_f steps`.  Its entire `pipeNT (.TBytes 200)` pipeline
    decodes to the composite of its per-block specs — with **ZERO
    `KernelRealizesT` hypotheses**.  Every per-block realization is the proved
    concrete realizer `keccak_realizes_concrete` (in turn the verified 200-byte
    codec round-trip `decodeKbytes_encodeKbytes`), assembled by `pipeNT_realizes`.

    HONEST scope: this grounds the *computational backbone* — the emitted Keccak
    permutation chain computes its arithmetic spec.  It does NOT prove the
    Fiat–Shamir transform's SOUNDNESS in the random-oracle model (that the
    derived challenges are sound, i.e. a cheating prover cannot grind the
    transcript), which is a separate ROM / cryptographic result.  The only
    residual is the machine-code obligation for the `"keccak_f1600"` leaf — the
    owned-machine-code route, NOT a per-block hypothesis (and NOT a KAT). -/
theorem grounded_fiat_shamir_transcript_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (fsTranscriptLeaves n) oldDest xVal)
      = composeSpecs (fsTranscriptSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (fsTranscriptLeaves n) (fsTranscriptSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §2  Sum-check round / FRI folding step — field mul-then-add, UNCONDITIONAL

A sum-check verifier folds the prover's univariate message `g(X)` at the random
challenge `r` by Horner evaluation
`p(r) = (⋯(c_d·r + c_{d-1})·r + ⋯)·r + c_0`; a FRI fold computes the same affine
combination `f_{i+1}(x) = f_i^{even}(x) + r·f_i^{odd}(x)`.  Both reduce to the
single mul-then-add step `x ↦ x · r + c`, which exercises the **distinct**
`field_mul` and `field_add` kernels of the single combined leafSpec
(`fieldCombinedLeafSpec`).  Each kernel's realization is the proved
`combined_realizes_mul` / `combined_realizes_add`; the encoded challenge and
coefficient collapse by the codec round-trip `decodeF_encodeF`.  The full
degree-`d` Horner evaluation is that step FOLDED over the coefficient list. -/

/-- The value of one sum-check / FRI field step `x ↦ x · v + c` over the
    *combined* leafSpec: apply the `field_mul` arm to `(x, encodeF v)`, then the
    `field_add` arm to `(that, encodeF c)`.  Used both for a sum-check / Horner
    step (`v = r` the challenge, `c = cᵢ` the next coefficient) and for a FRI
    fold (`v = r`, `c = f_i^{even}(x)`). -/
def foldStepValue (q : ℕ) [NeZero q] (width : ℕ) (v c : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) : RustVal .TFp :=
  (fieldCombinedLeafSpec q width limbStore).call "field_add" .TFp [.TFp, .TFp]
    oldDest
    [ ⟨.TFp,
        (fieldCombinedLeafSpec q width limbStore).call "field_mul" .TFp
          [.TFp, .TFp] oldDest [⟨.TFp, xVal⟩, ⟨.TFp, encodeF width v⟩]⟩
    , ⟨.TFp, encodeF width c⟩ ]

/-- **GROUNDED sum-check / FRI field step — ZERO kernel hypotheses.**  The step
    `x ↦ x · v + c` over the combined field leafSpec — exercising the **distinct**
    `field_mul` then `field_add` kernels — decodes to exactly
    `decodeF width xVal · v + c`.  Both per-kernel realizations are the proved
    `combined_realizes_mul` / `combined_realizes_add`; the encoded challenge and
    coefficient collapse by the proved `decodeF_encodeF`.  No assumed kernel
    fact; the only residual is the machine-code obligation for the two combined
    arms.  This is the common backbone of a sum-check Horner step and a FRI
    fold. -/
theorem grounded_foldStep_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (v c : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) :
    decodeF width (foldStepValue q width v c limbStore oldDest xVal)
      = decodeF width xVal * v + c := by
  unfold foldStepValue
  -- Outer `field_add` arm realizes `(· + ·)` on its two decoded operands.
  rw [combined_realizes_add q width hw hq limbStore _ (encodeF width c) oldDest]
  -- Inner `field_mul` arm realizes `(· * ·)` on its two decoded operands.
  rw [combined_realizes_mul q width hw hq limbStore xVal (encodeF width v) oldDest]
  -- Collapse the two encoded constants via the proved round-trip.
  rw [decodeF_encodeF width hw hq, decodeF_encodeF width hw hq]

/-- **GROUNDED sum-check round folding — UNCONDITIONAL.**

    A sum-check verifier (Lund–Fortnow–Karloff–Nisan, JACM 1992) folds the
    prover's univariate message at the random challenge `r` by Horner evaluation;
    one such fold step `x ↦ x · r + c`, with `(v, c) = (r, c)`, decodes to exactly
    `decodeF width xVal · r + c`, with **ZERO kernel hypotheses**.  Both per-kernel
    realizations are theorems (`combined_realizes_mul` / `combined_realizes_add` +
    codec round-trip).

    HONEST scope: this grounds the *computational backbone* — the emitted field
    mul/add kernel pipeline computes the sum-check fold arithmetic.  It does NOT
    prove sum-check SOUNDNESS (the round-by-round Schwartz–Zippel bound that a
    cheating prover is caught with probability `≥ 1 - d/|F|` per round) — that is
    a separate cryptographic result.  The only residual is the machine-code
    obligation for the combined `field_mul` / `field_add` arms. -/
theorem grounded_sumcheck_round_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (r c : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest xVal : RustVal .TFp) :
    decodeF width (foldStepValue q width r c limbStore oldDest xVal)
      = decodeF width xVal * r + c :=
  grounded_foldStep_realizes q width hw hq r c limbStore oldDest xVal

/-- **GROUNDED FRI folding step — UNCONDITIONAL.**

    A FRI fold (Ben-Sasson et al., ICALP 2018) combines the even / odd halves of
    the current oracle at the verifier's challenge `r`:
    `f_{i+1}(x) = f_i^{even}(x) + r · f_i^{odd}(x)`.  Expressed as the step
    `x ↦ x · r + c` with `x = f_i^{odd}(x)`, `c = f_i^{even}(x)`, it decodes to
    exactly `decodeF width xVal · r + c`, with **ZERO kernel hypotheses** — the
    same grounded mul-then-add backbone.  Both per-kernel realizations are
    theorems (`combined_realizes_mul` / `combined_realizes_add` + codec
    round-trip).

    HONEST scope: this grounds the *computational backbone* — the emitted field
    kernel pipeline computes the FRI-fold affine combination.  It does NOT prove
    FRI LOW-DEGREE-TESTING SOUNDNESS (that an oracle far from low-degree is
    rejected with high probability), which is a separate result.  The only
    residual is the machine-code obligation for the combined arms. -/
theorem grounded_fri_fold_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (r feven : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest fodd : RustVal .TFp) :
    decodeF width (foldStepValue q width r feven limbStore oldDest fodd)
      = decodeF width fodd * r + feven :=
  grounded_foldStep_realizes q width hw hq r feven limbStore oldDest fodd

/-- The value of a degree-`d` Horner polynomial evaluation `p(r)` over the
    combined leafSpec: fold the coefficient list `coeffs` (highest-degree first)
    left-to-right, each step the grounded `foldStepValue` mul-then-add at the
    challenge `r`.  The running `acc0` is the leading coefficient's slot. -/
def hornerFoldValue (q : ℕ) [NeZero q] (width : ℕ) (r : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest : RustVal .TFp)
    (coeffs : List (ZMod q)) (acc0 : RustVal .TFp) : RustVal .TFp :=
  coeffs.foldl
    (fun acc c => foldStepValue q width r c limbStore oldDest acc) acc0

/-- The matching abstract spec of the degree-`d` Horner evaluation: fold
    `x ↦ x · r + c` against the coefficients, left-to-right. -/
def hornerFoldSpec (q : ℕ) (r : ZMod q) (coeffs : List (ZMod q))
    (acc0 : ZMod q) : ZMod q :=
  coeffs.foldl (fun acc c => acc * r + c) acc0

/-- **GROUNDED degree-`d` Horner evaluation (sum-check / FRI polynomial fold) —
    UNCONDITIONAL.**

    The full sum-check / FRI univariate fold evaluates `p(r)` by Horner's rule
    over the coefficient list.  Its whole `foldl` pipeline decodes to the
    abstract Horner fold of the decoded leading coefficient against the
    coefficients — with **ZERO kernel hypotheses**.  Every per-coefficient step
    is the grounded `grounded_foldStep_realizes` (in turn the proved
    `combined_realizes_mul` / `combined_realizes_add` + codec round-trip).

    HONEST scope: this grounds the *computational backbone* — the emitted field
    mul/add chain computes the Horner polynomial evaluation.  It does NOT prove
    sum-check / FRI SOUNDNESS.  The only residual is the machine-code obligation
    for the combined arms. -/
theorem grounded_horner_fold_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (r : ZMod q)
    (limbStore : LimbStoreSpec) (oldDest : RustVal .TFp)
    (coeffs : List (ZMod q)) (acc0 : RustVal .TFp) :
    decodeF width (hornerFoldValue q width r limbStore oldDest coeffs acc0)
      = hornerFoldSpec q r coeffs (decodeF width acc0) := by
  unfold hornerFoldValue hornerFoldSpec
  induction coeffs generalizing acc0 with
  | nil => simp
  | cons c rest ih =>
      simp only [List.foldl_cons]
      rw [ih (foldStepValue q width r c limbStore oldDest acc0)]
      rw [grounded_foldStep_realizes q width hw hq r c limbStore oldDest acc0]

/-! ## §3  Merkle / vector commitment — UNCONDITIONAL

A STARK / Plonky3 verifier opens a Poseidon2 Merkle tree: each internal node is
the 2-to-1 compression `H(left, right) = poseidon2BabyBearCompress left right`,
grounded as a `KernelRealizes2` theorem from the proved
`poseidon2_compress_realizes_concrete` over the 4-byte field codec `decodeF 4`
(strictly axiom-clean).  An alternative Keccak-based vector commitment absorbs
the `n` committed leaves into the 1600-bit sponge, grounded as the
`pipeNT (.TBytes 200)`-chain of `keccak_realizes_concrete`. -/

/-- **GROUNDED Poseidon2 Merkle / vector-commitment 2-to-1 node — UNCONDITIONAL
    (strictly axiom-clean).**

    A single internal node of a STARK / Plonky3 Poseidon2 Merkle vector
    commitment hashes its two children
    `H(left, right) = poseidon2BabyBearCompress left right`.  Over the proved
    concrete compression realizer `compressLeafSpec` and the round-trip-verified
    4-byte field codec `decodeF 4`, the binary kernel realization holds for
    **every** input — the emitted compression kernel decodes its two operands and
    computes exactly the compression spec, with **ZERO `KernelRealizes2`
    hypotheses**.  The realization is the proved
    `poseidon2_compress_realizes_concrete` (in turn the field codec round-trip
    `decodeF_encodeF` at `width = 4`, `q = babyBearPrime`); strictly axiom-clean
    (`{propext, Classical.choice, Quot.sound}`).

    HONEST scope: this grounds the *computational backbone* — the emitted
    Poseidon2 compression kernel computes `poseidon2BabyBearCompress`.  It does
    NOT prove the vector commitment's BINDING (collision-resistance of Poseidon2)
    nor the STARK / FRI verifier's knowledge-soundness — separate cryptographic
    assumptions.  The only residual is the machine-code obligation for the
    compression leaf — the owned-machine-code route, NOT a per-kernel hypothesis. -/
theorem grounded_poseidon_vector_commitment_realizes (leaf : String)
    (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := babyBearPrime) 4) poseidon2BabyBearCompress leaf
      (compressLeafSpec leaf limbStore) :=
  poseidon2_compress_realizes_concrete leaf limbStore

/-- The `n`-block Keccak vector-commitment leaf list: `n` copies of
    `"keccak_f1600"` (one Keccak permutation per absorbed committed leaf). -/
def keccakVectorCommitLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the vector-commitment sponge. -/
def keccakVectorCommitSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED Keccak vector commitment — UNCONDITIONAL.**

    An alternative SNARK / STARK vector commitment absorbs the `n` committed
    leaves into the 1600-bit Keccak sponge by `n` applications of the
    permutation `keccak_f steps`.  Its entire `pipeNT (.TBytes 200)` pipeline
    decodes to the composite of its per-block specs — with **ZERO
    `KernelRealizesT` hypotheses**.  Every per-block realization is the proved
    `keccak_realizes_concrete` (in turn the verified 200-byte codec round-trip
    `decodeKbytes_encodeKbytes`), assembled by `pipeNT_realizes`.

    HONEST scope: this grounds the *computational backbone* — the emitted Keccak
    permutation chain computes its arithmetic spec.  It does NOT prove the vector
    commitment's BINDING (collision-resistance of Keccak) or the proof system's
    knowledge-soundness, which are separate assumptions.  The only residual is the
    machine-code obligation for the `"keccak_f1600"` leaf — NOT a per-block
    hypothesis (and NOT a KAT). -/
theorem grounded_keccak_vector_commitment_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (keccakVectorCommitLeaves n) oldDest xVal)
      = composeSpecs (keccakVectorCommitSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (keccakVectorCommitLeaves n) (keccakVectorCommitSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §4  The combined SNARK / STARK headline — all backbones grounded

The proof-system portfolio is its grounded backbones conjoined: the Fiat–Shamir
transcript sponge, the sum-check / FRI field fold, and the Poseidon2 Merkle
vector-commitment node.  Each conjunct is unconditional in its kernels; each
grounds a *computational backbone*, not a proof-system security property.  The
portfolio uses the strictly axiom-clean Poseidon2 2-to-1 compression node and the
strictly axiom-clean field fold, plus the Keccak transcript chain, so it stays
within `{propext, Classical.choice, Quot.sound}`. -/

/-- **THE SNARK / STARK HEADLINE — grounded backbones, ZERO kernel hypotheses.**

    The SNARK / STARK proof-system backbones conjoined:

    * the Fiat–Shamir transcript / challenge derivation (`pipeNT (.TBytes 200)`
      Keccak sponge chain),
    * the sum-check round / FRI field fold step `x ↦ x·r + c` (combined
      `field_mul` / `field_add` arms), and
    * the Poseidon2 Merkle / vector-commitment 2-to-1 node compression
      `H(left, right)` (the `KernelRealizes2` over the 4-byte field codec),

    each with **ZERO kernel hypotheses** — every per-step realization is a proved
    concrete realizer (`keccak_realizes_concrete`, `combined_realizes_mul/add`,
    `poseidon2_compress_realizes_concrete`), in turn a verified codec round-trip.
    All conjuncts are strictly axiom-clean
    (`{propext, Classical.choice, Quot.sound}`).

    HONEST scope: each conjunct grounds the *computational backbone* — that the
    emitted Keccak / field / Poseidon2 kernel pipeline computes its arithmetic
    spec.  It does NOT prove the proof-system security (SNARK / STARK
    KNOWLEDGE-SOUNDNESS and COMPLETENESS, FIAT–SHAMIR SOUNDNESS in the ROM, FRI
    LOW-DEGREE-TESTING SOUNDNESS, sum-check SOUNDNESS, ZERO-KNOWLEDGE), which are
    separate assumption-bearing results.  The only residuals are the per-kernel
    machine-code obligations (owned-emit route). -/
theorem grounded_snark_portfolio (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ) (merkleLeaf : String)
    (q : ℕ) [NeZero q] (width : ℕ) (hw : width ≤ 48) (hq : q < 2 ^ (8 * width))
    (r c : ZMod q) (fieldOldDest fieldXVal : RustVal .TFp)
    (fsOldDest fsXVal : RustVal (.TBytes 200)) :
    -- Fiat–Shamir transcript / challenge derivation: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (fsTranscriptLeaves n) fsOldDest fsXVal)
      = composeSpecs (fsTranscriptSpecs steps n) (decodeKbytes fsXVal)
    ∧
    -- Sum-check round / FRI field fold step: grounded, only codec fit.
    decodeF width (foldStepValue q width r c limbStore fieldOldDest fieldXVal)
      = decodeF width fieldXVal * r + c
    ∧
    -- Poseidon2 Merkle / vector-commitment 2-to-1 node compression: grounded.
    KernelRealizes2 (decodeF (q := babyBearPrime) 4) poseidon2BabyBearCompress
      merkleLeaf (compressLeafSpec merkleLeaf limbStore) :=
  ⟨grounded_fiat_shamir_transcript_realizes steps limbStore n fsOldDest fsXVal,
   grounded_foldStep_realizes q width hw hq r c limbStore fieldOldDest fieldXVal,
   grounded_poseidon_vector_commitment_realizes merkleLeaf limbStore⟩

end CatCrypt.Crypto.SecureCompilation.GroundedSnarkBackbones
