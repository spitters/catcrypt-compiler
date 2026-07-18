/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer

/-!
# A fully-grounded HASH-sponge protocol — whole-pipeline emit-realization with
  ZERO assumed per-kernel hypotheses, over the carrier-generalized composition

`ProtocolEmitRealizes.pipeN` / `pipeN_realizes` thread the running pipeline value
through the `.TFp` carrier (each leaf-call uses the `.TFp` argument type).  That
suffices for field protocols (`GroundedFieldProtocol`) but is **too small** for a
hash sponge: a Keccak-f[1600] permutation operates on a 1600-bit state, and no
faithful `decode ∘ encode = id` codec can live on the 384-bit `.TFp` carrier
(pigeonhole — exactly the carrier-size point `ConcreteHashRealizer` makes).

This module does two things:

* **Generalizes the composition off `.TFp`.**  `pipeNT` / `pipeNT_realizes` are
  the carrier-parametric analogues of `pipeN` / `pipeN_realizes`: the running
  value is a `RustVal T` for an arbitrary carrier TowerType `T`, each leaf-call
  uses argument type `T`, and the per-step rewrite is the carrier-parametric
  `ConcreteHashRealizer.KernelRealizesT` equation.  The proof mirrors
  `pipeN_realizes`'s induction on the `List.Forall₂` witness.

* **Builds an UNCONDITIONAL grounded Keccak sponge.**  A Keccak sponge / SHAKE
  squeeze is `n` iterations of the *same* permutation `keccak_f steps` over
  `σ = KeccakState`, carrier `.TBytes 200` (1600 bits).  We assemble the
  `pipeNT`-chain of `n` copies of `"keccak_f1600"` and supply its per-step
  realization bundle from `n` copies of the **proved** `keccak_realizes_concrete`
  (itself unconditional — derived from the verified codec round-trip
  `decodeKbytes_encodeKbytes`).  The headline `grounded_keccak_sponge_realizes`
  therefore carries **zero `KernelRealizesT` hypotheses**: a Keccak-based
  sponge / PRG protocol whose whole emit-realization assumes *nothing* about its
  `keccak_f` kernel.

## What is grounded and what is not

* **Grounded (unconditional Lean theorem):** every per-iteration realization.
  Each is the proved `keccak_realizes_concrete`, with no KAT, no abstract section
  assumption, and no per-kernel hypothesis.  The whole `pipeNT` pipeline decodes
  to the composite `composeSpecs (replicate n (keccak_f steps))` of the
  per-iteration specs.
* **The only residual (the machine-code obligation, NOT a per-kernel
  hypothesis):** that the *jasmin-emitted machine bytes* of the real Keccak-f
  kernel equal the realizer `specLeafSpecT … "keccak_f1600" …`.  That equality —
  emitted assembly ≡ realizer — is the owned-machine-code route, a single global
  obligation, and is explicitly *not* one of the per-iteration realization
  hypotheses this file eliminates (nor a KAT).

## References
* NIST FIPS 202 (Keccak / SHA-3 sponge), FIPS 180-4 (SHA-256)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.Hash.Keccak
open CatCrypt.Crypto.Primitives.SHA256

/-! ## §1  The carrier-parametric n-kernel pipeline

`pipeNT T leafSpec [k₁, …, kₘ] oldDest xVal` folds the kernel list left-to-right,
threading the running `RustVal T` (rather than `RustVal .TFp`) through each
leaf-call, whose sole positional argument has type `T`.  It is the exact
`pipeN` shape with `.TFp` replaced by the carrier parameter `T`. -/

/-- The value produced by chaining a *list* of kernels left-to-right over an
    arbitrary carrier TowerType `T`. -/
def pipeNT (T : TowerType) (leafSpec : LeafSpec) (leaves : List String)
    (oldDest xVal : RustVal T) : RustVal T :=
  leaves.foldl
    (fun acc leaf => leafSpec.call leaf T [T] oldDest [⟨T, acc⟩])
    xVal

/-- **The carrier-parametric n-kernel composition law.**  If each leaf in
    `leaves` realizes the corresponding spec in `specs` (position-wise, via
    `List.Forall₂` of `KernelRealizesT T decode …`), then the `pipeNT` pipeline
    realizes the composite spec `composeSpecs specs`.

    This is `ProtocolEmitRealizes.pipeN_realizes` generalized off the fixed
    `.TFp` carrier: the per-step rewrite is the `KernelRealizesT` equation
    `decode (leafSpec.call leaf T [T] oldDest [⟨T, x⟩]) = spec (decode x)`.
    Proof by induction on the `Forall₂` witness, mirroring `pipeN_realizes`. -/
theorem pipeNT_realizes {C : Type*} (T : TowerType) (decode : RustVal T → C)
    (leafSpec : LeafSpec) :
    ∀ (leaves : List String) (specs : List (C → C)),
      List.Forall₂ (fun leaf spec => KernelRealizesT T decode spec leaf leafSpec)
        leaves specs →
      ∀ (oldDest xVal : RustVal T),
        decode (pipeNT T leafSpec leaves oldDest xVal)
          = composeSpecs specs (decode xVal) := by
  intro leaves specs h
  induction h with
  | nil =>
      intro oldDest xVal
      simp [pipeNT, composeSpecs]
  | @cons leaf spec restL restS hhead _htail ih =>
      intro oldDest xVal
      -- Peel the first leaf-call off both pipeline and spec-fold.
      have hstep : decode (leafSpec.call leaf T [T] oldDest [⟨T, xVal⟩])
          = spec (decode xVal) := hhead xVal oldDest
      -- `pipeNT` of the cons is `pipeNT` of the tail started from the new value.
      have hpipe : pipeNT T leafSpec (leaf :: restL) oldDest xVal
          = pipeNT T leafSpec restL oldDest
              (leafSpec.call leaf T [T] oldDest [⟨T, xVal⟩]) := by
        simp [pipeNT, List.foldl_cons]
      -- `composeSpecs` of the cons applies the head spec first, then the tail.
      have hcomp : ∀ (g : C → C) (ss : List (C → C)) (c : C),
          ss.foldl (fun acc f => f ∘ acc) g c
            = ss.foldl (fun acc f => f ∘ acc) id (g c) := by
        intro g ss
        induction ss generalizing g with
        | nil => intro c; rfl
        | cons s ss' ihs =>
            intro c
            simp only [List.foldl_cons]
            rw [ihs (s ∘ g), ihs (s ∘ id)]
            simp
      rw [hpipe, ih oldDest
        (leafSpec.call leaf T [T] oldDest [⟨T, xVal⟩]), hstep]
      -- Goal: composeSpecs restS (spec (decode xVal))
      --     = composeSpecs (spec :: restS) (decode xVal)
      simp only [composeSpecs, List.foldl_cons]
      rw [hcomp (spec ∘ id) restS (decode xVal)]
      simp

/-! ## §2  The grounded Keccak sponge — UNCONDITIONAL

A Keccak sponge / SHAKE squeeze applies the *same* permutation `keccak_f steps`
(fixed step mappings — no per-iteration varying parameter) `n` times to the
1600-bit state.  We model the `n`-iteration pipeline as the `pipeNT`-chain of `n`
copies of the leaf `"keccak_f1600"` over carrier `.TBytes 200`, and discharge
each per-iteration realization with the **proved** `keccak_realizes_concrete` —
no hypothesis. -/

/-- The `n`-iteration Keccak-sponge kernel list: `n` copies of `"keccak_f1600"`. -/
def keccakSpongeLeaves (n : ℕ) : List String :=
  List.replicate n "keccak_f1600"

/-- The matching per-iteration spec list: `n` copies of the permutation
    `keccak_f steps`. -/
def keccakSpongeSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  List.replicate n (keccak_f steps)

/-- The position-wise `Forall₂` of per-iteration realizations for the Keccak
    sponge — `n` copies of the **proved** `keccak_realizes_concrete` theorem.
    No hypothesis is assumed; every entry is discharged unconditionally. -/
theorem keccakSponge_realized (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizesT (.TBytes 200) decodeKbytes s l
        (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
          "keccak_f1600" limbStore))
      (keccakSpongeLeaves n) (keccakSpongeSpecs steps n) := by
  unfold keccakSpongeLeaves keccakSpongeSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (keccak_realizes_concrete steps limbStore) ih

/-- **GROUNDED whole-sponge emit-realization — UNCONDITIONAL.**

    A Keccak-based sponge / PRG protocol: `n` iterations of the permutation
    `keccak_f steps` over the 1600-bit state.  Its entire `pipeNT` pipeline
    decodes to the composite of its per-iteration specs — with **ZERO
    `KernelRealizesT` hypotheses**.  Every per-iteration realization is the
    proved concrete realizer `keccak_realizes_concrete` (in turn the verified
    codec round-trip `decodeKbytes_encodeKbytes`), assembled by the
    carrier-generalized `pipeNT_realizes`.  Nothing is assumed about the
    `keccak_f` kernel.

    The only residual is the machine-code obligation — that the jasmin-emitted
    bytes of the real Keccak-f kernel equal the realizer `specLeafSpecT …
    "keccak_f1600" …` — which is the owned-machine-code route, NOT a per-iteration
    hypothesis (and NOT a KAT). -/
theorem grounded_keccak_sponge_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (keccakSpongeLeaves n) oldDest xVal)
      = composeSpecs (keccakSpongeSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (keccakSpongeLeaves n) (keccakSpongeSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §3  The grounded SHA-256 chain — UNCONDITIONAL (the analogous instance)

A Merkle–Damgård / chained SHA-256 compression run applies the *same* one-block
compression `fun s => compress s block` `n` times, over carrier `.TBytes 32`
(256 bits).  Same skeleton as the Keccak sponge, with the proved
`sha256_realizes_concrete` discharging each per-iteration realization. -/

/-- The `n`-iteration SHA-256 chain kernel list: `n` copies of `"sha256_compress"`. -/
def sha256ChainLeaves (n : ℕ) : List String :=
  List.replicate n "sha256_compress"

/-- The matching per-iteration spec list: `n` copies of the one-block compression
    `fun s => compress s block`. -/
def sha256ChainSpecs (block : Fin 64 → UInt8) (n : ℕ) :
    List (State256 → State256) :=
  List.replicate n (fun s => compress s block)

/-- The position-wise `Forall₂` of per-iteration realizations for the SHA-256
    chain — `n` copies of the proved `sha256_realizes_concrete`.  No hypothesis. -/
theorem sha256Chain_realized (block : Fin 64 → UInt8)
    (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizesT (.TBytes 32) decodeSbytes s l
        (specLeafSpecT (.TBytes 32) decodeSbytes encodeSbytes
          (fun s => compress s block) "sha256_compress" limbStore))
      (sha256ChainLeaves n) (sha256ChainSpecs block n) := by
  unfold sha256ChainLeaves sha256ChainSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (sha256_realizes_concrete block limbStore) ih

/-- **GROUNDED whole-chain emit-realization (SHA-256) — UNCONDITIONAL.**  An
    `n`-block chained SHA-256 compression run's entire `pipeNT` pipeline decodes
    to the composite of its per-iteration specs — with **ZERO `KernelRealizesT`
    hypotheses**.  Every per-iteration realization is the proved
    `sha256_realizes_concrete`; the composition is the carrier-generalized
    `pipeNT_realizes`.  The only residual is the machine-code obligation for the
    `"sha256_compress"` leaf, NOT a per-iteration hypothesis. -/
theorem grounded_sha256_chain_realizes (block : Fin 64 → UInt8)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 32)) :
    decodeSbytes
        (pipeNT (.TBytes 32)
          (specLeafSpecT (.TBytes 32) decodeSbytes encodeSbytes
            (fun s => compress s block) "sha256_compress" limbStore)
          (sha256ChainLeaves n) oldDest xVal)
      = composeSpecs (sha256ChainSpecs block n) (decodeSbytes xVal) :=
  pipeNT_realizes (.TBytes 32) decodeSbytes
    (specLeafSpecT (.TBytes 32) decodeSbytes encodeSbytes
      (fun s => compress s block) "sha256_compress" limbStore)
    (sha256ChainLeaves n) (sha256ChainSpecs block n)
    (sha256Chain_realized block limbStore n) oldDest xVal

end CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
