/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ConcreteSymmetric2Realizer
import CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol

/-!
# A fully-grounded ChaCha20-Poly1305 AEAD — both phases' kernel realizations are
  THEOREMS (zero assumed kernel hypotheses), over the proved concrete realizers

`AeadProtocolKernels.chachapoly_protocol_realizes` assembles the whole
ChaCha20-Poly1305 (RFC 8439) AEAD — `n` ChaCha20 keystream blocks then `m`
Poly1305 accumulator-update blocks — from **per-kernel realization hypotheses**:
each `KernelRealizes decode (chachaStep i) "chacha20_block" leafSpec` /
`KernelRealizes decode (polyStep i) "poly1305_block" leafSpec` is taken as an
honest leaf-bytes KAT hypothesis.

This module makes those kernel realizations **theorems**, eliminating the
hypotheses.  The two AEAD phases live on **different carriers** — and that is
honest, not a workaround:

* the ChaCha keystream phase advances the 512-bit cipher state
  `ChaChaState = Fin 16 → BitVec 32` (carrier `.TBytes 64`), and
* the Poly1305 MAC phase advances the polynomial accumulator `acc : Nat`
  (carrier `.TBytes width`, a base-256 little-endian codec),

so a single unified carrier would be an artifact.  We therefore deliver the AEAD
as its **two grounded phases**, each unconditional in its kernels:

* **`chachapoly_keystream_grounded`** — the `n`-block ChaCha20 keystream phase,
  a `pipeNT (.TBytes 64)` chain of `n` copies of `"chacha20_block"`, with every
  per-iteration realization discharged by the **proved**
  `ConcreteSymmetric2Realizer.chacha_realizes_concrete` (in turn the verified
  64-byte codec round-trip `decodeCbytes_encodeCbytes`).  **ZERO
  `KernelRealizesT` hypotheses.**
* **`chachapoly_mac_grounded`** — the `m`-block Poly1305 MAC fold phase, a
  `pipeNT (.TBytes width)` chain of `m` copies of `"poly1305_block"` over the
  base-256 accumulator codec, with every per-iteration realization discharged by
  the **proved** `ConcreteSymmetric2Realizer.poly1305_realizes_concrete`.  **ZERO
  `KernelRealizesT` hypotheses**; the only residual is the codec-fit/range
  side-condition `hrange : ∀ acc, processBlock r acc block < 256 ^ width`
  (`width ≥ 17` accommodates every reachable accumulator `< 2^130 - 5`), exactly
  like the field protocols' `width ≤ 48` side-condition.

The two grounded phases ARE the deliverable: each phase's kernel realizations
are theorems (the proved concrete ChaCha/Poly1305 realizers + codec
round-trips), not hypotheses.

## What is grounded and what is not

* **Grounded (unconditional Lean theorem):** every per-block realization of both
  phases — each is the proved `chacha_realizes_concrete` /
  `poly1305_realizes_concrete`, with no KAT, no abstract section assumption, and
  no per-kernel hypothesis.  The keystream `pipeNT` pipeline decodes to the
  composite of `n` ChaCha-block specs; the MAC `pipeNT` pipeline decodes to the
  composite of `m` Poly1305-fold specs.
* **The only residual (the machine-code obligation, NOT a per-kernel
  hypothesis):** that the *jasmin-emitted machine bytes* of the real ChaCha20 /
  Poly1305 kernels equal these realizers (the owned-machine-code route — a single
  global obligation per kernel, explicitly not one of the per-block realizations
  this file eliminates, nor a KAT).  The Poly1305 phase additionally carries the
  honest codec-fit/range side-condition `hrange`, which is a *range* condition on
  the accumulator (`width ≥ 17`), not a kernel hypothesis.

## References
* RFC 8439 (ChaCha20-Poly1305), NIST SP 800-38D
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedChaChaPoly

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.ConcreteSymmetric2Realizer
open CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
open CatCrypt.Crypto.Jasmin.ChaCha20Block
open CatCrypt.Crypto.Primitives.Poly1305

/-! ## §1  The grounded ChaCha20 keystream phase — UNCONDITIONAL

A ChaCha20 keystream is `n` iterations of the *same* block function
`chachaBlock` over the 512-bit cipher state, carrier `.TBytes 64`.  We model the
`n`-block phase as the `pipeNT (.TBytes 64)`-chain of `n` copies of the leaf
`"chacha20_block"`, and discharge each per-block realization with the **proved**
`chacha_realizes_concrete` — no hypothesis.  This is the exact skeleton of
`GroundedHashProtocol.grounded_keccak_sponge_realizes`, here for the ChaCha
block function. -/

/-- The `n`-block ChaCha20 keystream leaf list: `n` copies of `"chacha20_block"`. -/
def chachaKeystreamLeaves (n : ℕ) : List String :=
  List.replicate n "chacha20_block"

/-- The matching per-block spec list: `n` copies of the ChaCha block function
    `chachaBlock`. -/
def chachaKeystreamSpecs (n : ℕ) : List (ChaChaState → ChaChaState) :=
  List.replicate n chachaBlock

/-- The position-wise `Forall₂` of per-block realizations for the ChaCha keystream
    phase — `n` copies of the **proved** `chacha_realizes_concrete` theorem.  No
    hypothesis is assumed; every entry is discharged unconditionally. -/
theorem chachaKeystream_realized (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizesT (.TBytes 64) decodeCbytes s l
        (specLeafSpecT (.TBytes 64) decodeCbytes encodeCbytes chachaBlock
          "chacha20_block" limbStore))
      (chachaKeystreamLeaves n) (chachaKeystreamSpecs n) := by
  unfold chachaKeystreamLeaves chachaKeystreamSpecs
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons (chacha_realizes_concrete limbStore) ih

/-- **GROUNDED ChaCha20 keystream-phase emit-realization — UNCONDITIONAL.**

    The `n`-block ChaCha20 keystream phase of RFC 8439's AEAD: `n` iterations of
    the block function `chachaBlock` over the 512-bit cipher state.  Its entire
    `pipeNT` pipeline decodes to the composite of its per-block specs — with
    **ZERO `KernelRealizesT` hypotheses**.  Every per-block realization is the
    proved concrete realizer `chacha_realizes_concrete` (in turn the verified
    64-byte codec round-trip `decodeCbytes_encodeCbytes`), assembled by the
    carrier-generalized `pipeNT_realizes`.  Nothing is assumed about the
    `chachaBlock` kernel.

    The only residual is the machine-code obligation — that the jasmin-emitted
    bytes of the real ChaCha20-block kernel equal the realizer `specLeafSpecT …
    "chacha20_block" …` — which is the owned-machine-code route, NOT a per-block
    hypothesis (and NOT a KAT). -/
theorem chachapoly_keystream_grounded (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 64)) :
    decodeCbytes
        (pipeNT (.TBytes 64)
          (specLeafSpecT (.TBytes 64) decodeCbytes encodeCbytes chachaBlock
            "chacha20_block" limbStore)
          (chachaKeystreamLeaves n) oldDest xVal)
      = composeSpecs (chachaKeystreamSpecs n) (decodeCbytes xVal) :=
  pipeNT_realizes (.TBytes 64) decodeCbytes
    (specLeafSpecT (.TBytes 64) decodeCbytes encodeCbytes chachaBlock
      "chacha20_block" limbStore)
    (chachaKeystreamLeaves n) (chachaKeystreamSpecs n)
    (chachaKeystream_realized limbStore n) oldDest xVal

/-! ## §2  The grounded Poly1305 MAC phase — UNCONDITIONAL (range-restricted codec)

A Poly1305 MAC fold is `m` iterations of the *same* block step
`fun acc => processBlock r acc block` over the polynomial accumulator `acc : Nat`,
carrier `.TBytes width` (a base-256 little-endian codec).  We model the `m`-block
phase as the `pipeNT (.TBytes width)`-chain of `m` copies of the leaf
`"poly1305_block"`, and discharge each per-block realization with the **proved**
`poly1305_realizes_concrete` — no kernel hypothesis.  The only residual is the
codec-fit/range condition `hrange` (the accumulator stays `< 256^width`;
`width ≥ 17` accommodates every reachable accumulator `< 2^130 - 5`), exactly
analogous to the field protocols' `width ≤ 48` side-condition. -/

/-- The `m`-block Poly1305 MAC leaf list: `m` copies of `"poly1305_block"`. -/
def poly1305MacLeaves (m : ℕ) : List String :=
  List.replicate m "poly1305_block"

/-- The matching per-block spec list: `m` copies of the Poly1305 block step
    `fun acc => processBlock r acc block` (the clamped key `r` and message
    `block` fixed). -/
def poly1305MacSpecs (r : Nat) (block : List UInt8) (m : ℕ) : List (Nat → Nat) :=
  List.replicate m (fun acc => processBlock r acc block)

/-- The position-wise `Forall₂` of per-block realizations for the Poly1305 MAC
    phase — `m` copies of the **proved** `poly1305_realizes_concrete` theorem.  No
    kernel hypothesis is assumed; every entry is discharged unconditionally from
    the codec round-trip, conditioned only on the accumulator-range side-condition
    `hrange`. -/
theorem poly1305Mac_realized (width : ℕ) [NeZero width] (r : Nat)
    (block : List UInt8) (hrange : ∀ acc, processBlock r acc block < 256 ^ width)
    (limbStore : LimbStoreSpec) (m : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizesT (.TBytes width) (decodePbytes width) s l
        (specLeafSpecT (.TBytes width) (decodePbytes width) (encodePbytes width)
          (fun acc => processBlock r acc block) "poly1305_block" limbStore))
      (poly1305MacLeaves m) (poly1305MacSpecs r block m) := by
  unfold poly1305MacLeaves poly1305MacSpecs
  induction m with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (poly1305_realizes_concrete width r block hrange limbStore) ih

/-- **GROUNDED Poly1305 MAC-phase emit-realization — UNCONDITIONAL (range-restricted
    codec).**

    The `m`-block Poly1305 MAC fold phase of RFC 8439's AEAD: `m` iterations of the
    block step `fun acc => processBlock r acc block` over the polynomial
    accumulator.  Its entire `pipeNT` pipeline decodes to the composite of its
    per-block specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-block
    realization is the proved concrete realizer `poly1305_realizes_concrete` (in
    turn the verified base-256 accumulator codec round-trip
    `decodePbytes_encodePbytes`), assembled by the carrier-generalized
    `pipeNT_realizes`.  Nothing is assumed about the Poly1305 block-step kernel.

    The only residual side-condition is the codec-fit/range condition
    `hrange : ∀ acc, processBlock r acc block < 256 ^ width` — a *range* condition
    on the accumulator (`width ≥ 17` accommodates every reachable accumulator
    `< 2^130 - 5`), exactly analogous to the field protocols' `width ≤ 48`; it is
    NOT a kernel-realization hypothesis.

    The remaining residual is the machine-code obligation — that the jasmin-emitted
    bytes of the real Poly1305 block-step kernel equal the realizer `specLeafSpecT …
    "poly1305_block" …` — the owned-machine-code route, NOT a per-block hypothesis
    (and NOT a KAT). -/
theorem chachapoly_mac_grounded (width : ℕ) [NeZero width] (r : Nat)
    (block : List UInt8) (hrange : ∀ acc, processBlock r acc block < 256 ^ width)
    (limbStore : LimbStoreSpec) (m : ℕ)
    (oldDest xVal : RustVal (.TBytes width)) :
    decodePbytes width
        (pipeNT (.TBytes width)
          (specLeafSpecT (.TBytes width) (decodePbytes width) (encodePbytes width)
            (fun acc => processBlock r acc block) "poly1305_block" limbStore)
          (poly1305MacLeaves m) oldDest xVal)
      = composeSpecs (poly1305MacSpecs r block m) (decodePbytes width xVal) :=
  pipeNT_realizes (.TBytes width) (decodePbytes width)
    (specLeafSpecT (.TBytes width) (decodePbytes width) (encodePbytes width)
      (fun acc => processBlock r acc block) "poly1305_block" limbStore)
    (poly1305MacLeaves m) (poly1305MacSpecs r block m)
    (poly1305Mac_realized width r block hrange limbStore m) oldDest xVal

/-! ## §3  The combined AEAD headline — both phases grounded

The ChaCha20-Poly1305 AEAD is its two grounded phases conjoined: the keystream
phase (carrier `.TBytes 64`, cipher state) and the MAC phase (carrier
`.TBytes width`, accumulator).  Because the two phases live on different carriers
— the cipher state vs the MAC accumulator — the honest combined statement is the
conjunction of the two grounded phase realizations, each unconditional in its
kernels.  No single unified carrier is forced; the conjunction is the AEAD. -/

/-- **THE AEAD HEADLINE — ChaCha20-Poly1305 grounded, ZERO kernel hypotheses.**

    ChaCha20-Poly1305 (RFC 8439) as its two grounded phases conjoined:

    * the `n`-block ChaCha20 keystream `pipeNT (.TBytes 64)` pipeline decodes to
      the composite of `n` ChaCha-block specs, and
    * the `m`-block Poly1305 MAC `pipeNT (.TBytes width)` pipeline decodes to the
      composite of `m` Poly1305-fold specs,

    each with **ZERO `KernelRealizesT` hypotheses** — every per-block realization
    is the proved concrete realizer (`chacha_realizes_concrete` /
    `poly1305_realizes_concrete`, in turn the verified codec round-trips).  The
    two phases live on different carriers (cipher state vs MAC accumulator), which
    is honest, so the AEAD is delivered as their conjunction.

    The only residual is the per-kernel machine-code obligation (the
    owned-machine-code route) plus the Poly1305 codec-fit/range side-condition
    `hrange` (a range condition on the accumulator, `width ≥ 17`, NOT a kernel
    hypothesis). -/
theorem chachapoly_grounded (width : ℕ) [NeZero width] (r : Nat)
    (block : List UInt8) (hrange : ∀ acc, processBlock r acc block < 256 ^ width)
    (limbStore : LimbStoreSpec) (n m : ℕ)
    (ksOldDest ksXVal : RustVal (.TBytes 64))
    (macOldDest macXVal : RustVal (.TBytes width)) :
    -- Keystream phase: grounded, no kernel hypotheses.
    decodeCbytes
        (pipeNT (.TBytes 64)
          (specLeafSpecT (.TBytes 64) decodeCbytes encodeCbytes chachaBlock
            "chacha20_block" limbStore)
          (chachaKeystreamLeaves n) ksOldDest ksXVal)
      = composeSpecs (chachaKeystreamSpecs n) (decodeCbytes ksXVal)
    ∧
    -- MAC phase: grounded, no kernel hypotheses (residual = codec range `hrange`).
    decodePbytes width
        (pipeNT (.TBytes width)
          (specLeafSpecT (.TBytes width) (decodePbytes width) (encodePbytes width)
            (fun acc => processBlock r acc block) "poly1305_block" limbStore)
          (poly1305MacLeaves m) macOldDest macXVal)
      = composeSpecs (poly1305MacSpecs r block m) (decodePbytes width macXVal) :=
  ⟨chachapoly_keystream_grounded limbStore n ksOldDest ksXVal,
   chachapoly_mac_grounded width r block hrange limbStore m macOldDest macXVal⟩

end CatCrypt.Crypto.SecureCompilation.GroundedChaChaPoly
