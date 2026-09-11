/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
public import CatCrypt.Crypto.SecureCompilation.ConcreteEcScalarRealizer

/-!
# Grounded SIGNATURE / TRANSPORT backbones — whole-pipeline emit-realization with
  ZERO assumed per-kernel hypotheses

This module grounds the computational backbones of three real signature /
transport constructions **unconditionally** — every per-step realization is a
*theorem* (a proved concrete realizer), so each headline carries **zero
`KernelRealizesT` / `KernelRealizes` hypotheses** (only codec-fit side
conditions, honestly flagged).  It reuses the carrier-driven groundings already
proved in-repo:

* `GroundedHashProtocol.keccakSponge_realized` + `pipeNT_realizes` — the
  carrier-`.TBytes 200` (1600-bit) Keccak sponge chain, every per-iteration
  realization the **proved** `ConcreteHashRealizer.keccak_realizes_concrete`
  (whose codec round-trip `decodeKbytes_encodeKbytes` is proved per-bit,
  *axiom-clean*: `{propext, Classical.choice, Quot.sound}` only).
* `ConcreteEcScalarRealizer.mul121665_realizes_concrete` + the `ProtocolKernels`
  template — the Curve25519 base-field doubling-constant multiply over
  `ZMod (2^255 − 19)`, codec a theorem (`decodeF_encodeF`), axiom-clean.

## The grounded backbones

* **`grounded_slh_treehash_realizes`** — the hash-based-signature TREEHASH /
  Merkle authentication-path backbone of SLH-DSA / SPHINCS⁺ (FIPS 205) in its
  SHAKE / Keccak instantiation: a Merkle tree's node hashes and the
  authentication-path verification are a chain of the *same* Keccak permutation
  on the 1600-bit sponge state, one `keccak_f steps` per absorbed/squeezed
  block.  Modeled as the `pipeNT (.TBytes 200)`-chain of `n` copies of
  `"keccak_f1600"`; every per-block realization is the proved
  `keccak_realizes_concrete`.  **ZERO `KernelRealizesT` hypotheses.**

* **`grounded_mldsa_fiatshamir_realizes`** — the Fiat–Shamir CHALLENGE-HASH of an
  ML-DSA / Dilithium signature (FIPS 204): the challenge `c̃ = H(μ ‖ w₁)` and the
  message representative `μ = H(tr ‖ M)` are SHAKE-256 sponge squeezes — `n`
  applications of `keccak_f steps` to the 1600-bit state.  Modeled as the same
  `pipeNT (.TBytes 200)` Keccak chain; every per-block realization is the proved
  `keccak_realizes_concrete`.  **ZERO `KernelRealizesT` hypotheses.**

* **`grounded_x25519_ladder_dbl_realizes`** — the X25519 Montgomery-ladder
  base-field DOUBLING-CONSTANT chain (RFC 7748 §5): each ladder doubling `xDBL`
  multiplies a running base-field coordinate by `a24 = (A−2)/4 = 121665` over
  `Fp = ZMod (2^255 − 19)`.  The `n`-step chain of this *unary* field multiply is
  modeled as the `pipeN`-chain of `n` copies of `mul121665`; every per-step
  realization is the proved `mul121665_realizes_concrete`.  **ZERO
  `KernelRealizes` hypotheses** (only the codec fit `width ≤ 48`,
  `p25519 < 2^(8·width)`).  The ladder's binary coordinate ops (field
  `add`/`sub`/`mul`) are exposed as separately-proved rows (`ConcreteEcScalarRealizer`),
  not chained here.

## HONEST scope — what is grounded and what is NOT

* **Grounded (unconditional Lean theorems):** every per-step realization of all
  three backbones — each a proved concrete realizer (`keccak_realizes_concrete`
  for the two hash backbones; `mul121665_realizes_concrete` for the ladder
  multiply), with no KAT and no per-kernel hypothesis.  Each whole pipeline
  decodes to the composite of its per-step specs.

* **Why Keccak / SHAKE and not SHA-256.**  SLH-DSA and ML-DSA each have a
  SHAKE-256 (Keccak-permutation) instantiation that is the actual NIST primitive
  (FIPS 205/204), and the Keccak codec round-trip is proved per-bit with no
  `bv_decide` certificate axiom — so grounding on Keccak keeps every theorem
  axiom-clean (`{propext, Classical.choice, Quot.sound}`).  The SHA-256
  Merkle–Damgård instantiation is **dropped here**: its codec round-trip
  `decodeSbytes_encodeSbytes` is proved by a `bv_decide` LRAT certificate, which
  introduces a certificate axiom — out of policy for this file.

* **The abstract elliptic-curve group law is NOT grounded.**  Only the
  base-field arithmetic sub-step (`mul121665`) of the ladder is grounded — the EC
  group operation / point addition has no concrete field realizer and is the
  honest residual, exactly as in `ConcreteEcScalarRealizer`.  Likewise the
  lattice arithmetic of ML-DSA (NTT, sampling, rejection) and the WOTS⁺ /
  FORS chaining *parameters* of SLH-DSA beyond the bare Keccak permutation are
  out of scope — only the hash/sponge and field-multiply backbones are grounded.

* **The only machine-code residual (NOT a per-kernel hypothesis):** that the
  *jasmin-emitted machine bytes* of the real `keccak_f1600` / `mul121665` kernels
  equal the realizer leaf-specs — the owned-machine-code route, a single global
  obligation per kernel, explicitly not one of the per-step realizations this
  file discharges (nor a KAT).

## References
* NIST FIPS 205 (SLH-DSA / SPHINCS⁺); FIPS 204 (ML-DSA / Dilithium); FIPS 202
  (SHA-3 / SHAKE / Keccak sponge).
* RFC 7748 §5 (X25519 Montgomery ladder); D. J. Bernstein, "Curve25519", PKC 2006
  (`a24 = (A−2)/4 = 121665`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedSigTransport

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.ConcreteEcScalarRealizer
open CatCrypt.Crypto.Hash.Keccak

/-! ## §1  SLH-DSA / SPHINCS⁺ TREEHASH / authentication-path backbone — UNCONDITIONAL

A hash-based signature (SLH-DSA, FIPS 205; SPHINCS⁺) verifies by recomputing a
Merkle tree's node hashes up an authentication path and the WOTS⁺ / FORS hash
chains.  In the SHAKE / Keccak instantiation every node hash and chain step is
one application of the *same* permutation `keccak_f steps` to the 1600-bit sponge
state.  The `n`-block treehash / auth-path run is therefore the
`pipeNT (.TBytes 200)`-chain of `n` copies of the leaf `"keccak_f1600"`, every
per-block realization discharged by the **proved** `keccak_realizes_concrete` —
no hypothesis. -/

/-- The `n`-block SLH-DSA treehash / authentication-path leaf list: `n` copies of
    `"keccak_f1600"` (one Keccak permutation per node-hash / chain block). -/
def slhTreehashLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the SLH-DSA Merkle/chain sponge. -/
def slhTreehashSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED SLH-DSA / SPHINCS⁺ treehash / auth-path backbone — UNCONDITIONAL.**

    The hash-based-signature Merkle authentication-path verification of SLH-DSA
    (FIPS 205) in its SHAKE / Keccak instantiation: recomputing node hashes and
    WOTS⁺ / FORS chain steps up the tree is `n` applications of the permutation
    `keccak_f steps` to the 1600-bit sponge state.  Its entire
    `pipeNT (.TBytes 200)` pipeline decodes to the composite of its per-block
    specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-block
    realization is the proved concrete realizer `keccak_realizes_concrete` (in
    turn the verified 200-byte codec round-trip `decodeKbytes_encodeKbytes`),
    assembled by the carrier-generalized `pipeNT_realizes`.

    Honest scope: this grounds the **Keccak-permutation hash backbone** of the
    treehash / auth-path.  The structural tweak / FORS-index / WOTS⁺-checksum
    bookkeeping around the bare permutation is NOT modeled, and the SHA-256
    instantiation of SLH-DSA is dropped (its codec uses a `bv_decide` certificate
    axiom).  The only machine-code residual is the owned-emit obligation for the
    `"keccak_f1600"` leaf — NOT a per-block hypothesis (and NOT a KAT). -/
theorem grounded_slh_treehash_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (slhTreehashLeaves n) oldDest xVal)
      = composeSpecs (slhTreehashSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (slhTreehashLeaves n) (slhTreehashSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §2  ML-DSA / Dilithium Fiat–Shamir challenge-hash — UNCONDITIONAL

An ML-DSA signature (FIPS 204) derives its Fiat–Shamir challenge by SHAKE-256
hashing: the message representative `μ = H(tr ‖ M)` and the challenge seed
`c̃ = H(μ ‖ w₁)` are sponge squeezes, each output / absorb block costing one
application of the permutation `keccak_f steps` to the 1600-bit state.  The
`n`-block challenge-hash transcript is the `pipeNT (.TBytes 200)`-chain of `n`
copies of `"keccak_f1600"`, every per-block realization discharged by the
**proved** `keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-block ML-DSA Fiat–Shamir challenge-hash leaf list: `n` copies of
    `"keccak_f1600"` (one Keccak permutation per absorbed/squeezed block). -/
def mldsaFiatShamirLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of the permutation
    `keccak_f steps` driving the SHAKE-256 challenge-hash sponge. -/
def mldsaFiatShamirSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED ML-DSA / Dilithium Fiat–Shamir challenge-hash — UNCONDITIONAL.**

    The Fiat–Shamir transcript of an ML-DSA signature (FIPS 204): the message
    representative `μ = H(tr ‖ M)` and the challenge seed `c̃ = H(μ ‖ w₁)` are
    SHAKE-256 sponge squeezes — `n` applications of the permutation
    `keccak_f steps` to the 1600-bit state.  Its entire `pipeNT (.TBytes 200)`
    pipeline decodes to the composite of its per-block specs — with **ZERO
    `KernelRealizesT` hypotheses**.  Every per-block realization is the proved
    concrete realizer `keccak_realizes_concrete` (in turn the verified 200-byte
    codec round-trip `decodeKbytes_encodeKbytes`), assembled by `pipeNT_realizes`.

    Honest scope: this grounds the **SHAKE-256 / Keccak-permutation hash
    backbone** of the Fiat–Shamir challenge.  The lattice arithmetic of ML-DSA
    (NTT, `w₁` decomposition, `SampleInBall`, rejection sampling) is NOT modeled —
    only the hash transcript.  The only machine-code residual is the owned-emit
    obligation for the `"keccak_f1600"` leaf — NOT a per-block hypothesis (and NOT
    a KAT). -/
theorem grounded_mldsa_fiatshamir_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (mldsaFiatShamirLeaves n) oldDest xVal)
      = composeSpecs (mldsaFiatShamirSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (mldsaFiatShamirLeaves n) (mldsaFiatShamirSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §3  X25519 Montgomery-ladder doubling-constant chain — UNCONDITIONAL

The X25519 ladder (RFC 7748 §5) computes an x-only scalar multiply by iterating a
field-arithmetic step over `Fp = ZMod (2^255 − 19)`.  Its doubling step `xDBL`
contains the distinctive scalar multiply by `a24 = (A−2)/4 = 121665` — a *unary*
base-field op, `x ↦ x · 121665`.  The `n`-step chain of this doubling multiply is
the `pipeN`-chain of `n` copies of the leaf `"mul121665"`, every per-step
realization discharged by the **proved** `mul121665_realizes_concrete` — no
hypothesis (only the codec fit). -/

/-- The X25519 doubling-constant kernel leaf (`x ↦ x · 121665`). -/
def x25519DblLeaf : String := "mul121665"

/-- The `n`-step X25519 ladder doubling-constant leaf list: `n` copies of
    `"mul121665"` (one doubling-constant multiply per ladder step). -/
def x25519LadderDblLeaves (n : ℕ) : List String :=
  List.replicate n x25519DblLeaf

/-- The matching per-step spec list: `n` copies of the unary base-field op
    `mul121665` (`x ↦ x · 121665` over `ZMod p25519`). -/
def x25519LadderDblSpecs (n : ℕ) : List (ZMod p25519 → ZMod p25519) :=
  List.replicate n mul121665

/-- The position-wise `Forall₂` of per-step realizations for the X25519
    doubling-constant chain — `n` copies of the **proved**
    `mul121665_realizes_concrete`.  No hypothesis is assumed; every entry is
    discharged unconditionally (only the codec-fit side conditions thread). -/
theorem x25519LadderDbl_realized (width : ℕ) (hw : width ≤ 48)
    (hq : p25519 < 2 ^ (8 * width)) (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizes (decodeF (q := p25519) width) s l
        (mul121665LeafSpec width x25519DblLeaf limbStore))
      (x25519LadderDblLeaves n) (x25519LadderDblSpecs n) := by
  unfold x25519LadderDblLeaves x25519LadderDblSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (mul121665_realizes_concrete width hw hq x25519DblLeaf limbStore) ih

/-- The bundled grounded X25519 doubling-constant chain protocol — every per-step
    realization discharged, no hypothesis. -/
def x25519LadderDblProtocol (width : ℕ) (hw : width ≤ 48)
    (hq : p25519 < 2 ^ (8 * width)) (limbStore : LimbStoreSpec) (n : ℕ) :
    ProtocolKernels (ZMod p25519) (mul121665LeafSpec width x25519DblLeaf limbStore) where
  leaves := x25519LadderDblLeaves n
  specs := x25519LadderDblSpecs n
  decode := decodeF width
  realized := x25519LadderDbl_realized width hw hq limbStore n

/-- **GROUNDED X25519 ladder doubling-constant chain — UNCONDITIONAL.**

    The X25519 Montgomery ladder's base-field doubling-constant multiply (RFC 7748
    §5; Bernstein 2006): each ladder doubling `xDBL` multiplies a base-field
    coordinate by `a24 = (A−2)/4 = 121665` over `Fp = ZMod (2^255 − 19)`.  The
    `n`-step chain of this *unary* multiply has its whole `pipeN` computation
    decode to the composite of its per-step specs — `n` copies of `mul121665` —
    with **ZERO `KernelRealizes` hypotheses** (only the codec fit `width ≤ 48`,
    `p25519 < 2^(8·width)`).  Every per-step realization is the proved
    `mul121665_realizes_concrete` (in turn the field codec round-trip
    `decodeF_encodeF`); the composition is the generic `runRealizes`.

    Honest scope: this grounds the **base-field arithmetic** doubling-constant of
    the ladder.  The abstract elliptic-curve group law / point addition is NOT
    field arithmetic and has no concrete field realizer — it is the honest
    residual, exactly as in `ConcreteEcScalarRealizer`.  The ladder's binary
    coordinate ops (field `add`/`sub`/`mul`) are separately proved
    (`ConcreteEcScalarRealizer.fieldAdd/Sub/Mul25519_realizes_concrete`), not
    chained here (they are `KernelRealizes2`, not the unary `pipeN` shape).  The
    only machine-code residual is the owned-emit obligation for the `"mul121665"`
    leaf — NOT a per-step hypothesis. -/
theorem grounded_x25519_ladder_dbl_realizes (width : ℕ) (hw : width ≤ 48)
    (hq : p25519 < 2 ^ (8 * width)) (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal .TFp) :
    decodeF width
        (pipeN (mul121665LeafSpec width x25519DblLeaf limbStore)
          (x25519LadderDblLeaves n) oldDest xVal)
      = composeSpecs (x25519LadderDblSpecs n) (decodeF width xVal) :=
  (x25519LadderDblProtocol width hw hq limbStore n).runRealizes oldDest xVal

/-! ## §4  The combined SIGNATURE / TRANSPORT headline — all three backbones grounded

The signature / transport portfolio is its three grounded backbones conjoined:
the SLH-DSA treehash sponge, the ML-DSA Fiat–Shamir challenge-hash sponge (both
over the 1600-bit Keccak carrier `.TBytes 200`), and the X25519 ladder
doubling-constant chain (over the base-field carrier `.TFp`).  Each conjunct is
unconditional in its kernels. -/

/-- **THE SIGNATURE / TRANSPORT HEADLINE — three grounded backbones, ZERO kernel
    hypotheses.**

    The three signature / transport backbones conjoined:

    * the SLH-DSA / SPHINCS⁺ treehash / auth-path Keccak sponge,
    * the ML-DSA / Dilithium Fiat–Shamir SHAKE-256 challenge-hash, and
    * the X25519 Montgomery-ladder doubling-constant field chain,

    each with **ZERO kernel hypotheses** — every per-step realization is a proved
    concrete realizer (`keccak_realizes_concrete` for the two hash backbones,
    `mul121665_realizes_concrete` for the ladder multiply), in turn a verified
    codec round-trip.  All three are axiom-clean
    (`{propext, Classical.choice, Quot.sound}`).

    Honest scope: only the hash/sponge backbones (Keccak) and the base-field
    doubling-constant (`mul121665`) are grounded.  The abstract EC group law, the
    ML-DSA lattice arithmetic, and the SLH-DSA structural bookkeeping are NOT
    grounded; the SHA-256 instantiations are dropped (certificate axiom).  The
    only residuals are the per-kernel machine-code obligations (owned-emit
    route). -/
theorem grounded_sig_transport_portfolio (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (slhOldDest slhXVal mldsaOldDest mldsaXVal : RustVal (.TBytes 200))
    (width : ℕ) (hw : width ≤ 48) (hq : p25519 < 2 ^ (8 * width))
    (x25519OldDest x25519XVal : RustVal .TFp) :
    -- SLH-DSA treehash / auth-path Keccak sponge: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (slhTreehashLeaves n) slhOldDest slhXVal)
      = composeSpecs (slhTreehashSpecs steps n) (decodeKbytes slhXVal)
    ∧
    -- ML-DSA Fiat–Shamir SHAKE-256 challenge-hash: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (mldsaFiatShamirLeaves n) mldsaOldDest mldsaXVal)
      = composeSpecs (mldsaFiatShamirSpecs steps n) (decodeKbytes mldsaXVal)
    ∧
    -- X25519 ladder doubling-constant field chain: grounded, only codec fit.
    decodeF width
        (pipeN (mul121665LeafSpec width x25519DblLeaf limbStore)
          (x25519LadderDblLeaves n) x25519OldDest x25519XVal)
      = composeSpecs (x25519LadderDblSpecs n) (decodeF width x25519XVal) :=
  ⟨grounded_slh_treehash_realizes steps limbStore n slhOldDest slhXVal,
   grounded_mldsa_fiatshamir_realizes steps limbStore n mldsaOldDest mldsaXVal,
   grounded_x25519_ladder_dbl_realizes width hw hq limbStore n
     x25519OldDest x25519XVal⟩

end CatCrypt.Crypto.SecureCompilation.GroundedSigTransport
