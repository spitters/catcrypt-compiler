/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# A BATCH of AEAD protocols as axis-6 `ProtocolKernels` instantiations

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on a **batch of real
AEAD constructions**: ChaCha20-Poly1305 (RFC 8439), AES-GCM, AES-SIV
(RFC 5297), and AEGIS-128L.

Every one of these AEADs is structurally a **cipher pipeline followed by a MAC
fold** — a sequence of `state → state` steps over the running keying/MAC state,
exactly the *unary* pipeline the `ProtocolKernels` template models:

* **ChaCha20-Poly1305**: `n` ChaCha20 keystream blocks, then `m` Poly1305
  accumulator-update blocks.
* **AES-GCM**: `n` AES counter-mode blocks (`GCTR`), then `m` GHASH fold steps.
* **AES-SIV**: `n` S2V/CMAC fold steps over the AD/plaintext vector, then `m`
  AES counter-mode blocks.
* **AEGIS-128L**: `n` `state_update` absorb steps, then `m` `state_update`
  encrypt/squeeze steps (the AEGIS state machine is one update primitive used in
  two phases).

Each phase's per-block step is a unary kernel over the AEAD's state carrier, so
the whole encrypt-then-authenticate pipeline is the unary `pipeN` the template
threads.  Unlike the per-primitive registry rows
(`AesKernelRegistryEntry`, `SymmetricKernelRegistryEntry`), which register *one*
cipher/MAC kernel each, this file assembles a *whole AEAD protocol's* emit
realization from its cipher + MAC kernel rows by the generic template.

## What each AEAD delivers

For protocol `P` (one of the four above):

* `<P>Specs` — the kernel pipeline as a list of unary specs over a carrier `C`:
  the cipher round specs followed by the MAC fold specs.  These are **abstract**
  opaque `C → C` round functions; the deliverable is the protocol-structure
  composition, not re-deriving the AEAD's cipher/MAC internals.
* `<P>Leaves` — the matching emitted leaf-names, taken from the real AEAD
  extractions (`CatCrypt/Crypto/{ChaCha20Poly1305,AESGCM,AESSIV,AEGIS}/`): the
  whole-AEAD chain leaf and the per-phase block/step leaves.
* `<P>Protocol` — the assembled `ProtocolKernels C leafSpec`, whose `realized`
  field is the position-wise `List.Forall₂` of the per-kernel realizations, each
  taken as a **hypothesis** — exactly how a protocol cites each cipher/MAC
  kernel's leaf-bytes KAT at instantiation.
* `<P>_protocol_realizes` — the whole-AEAD emit-realization,
  `decode (pipeN <P>Leaves …) = composeSpecs <P>Specs (decode x)`, obtained by a
  single `runRealizes` call from nothing but the per-kernel realizations and the
  generic composition law.

## The point (axis-6 on a batch of real protocols)

These AEADs' *whole* emit-realizations are assembled from their cipher + MAC
kernel rows by the generic template — per-protocol emit is: list the kernels,
cite each kernel's realization (the leaf-bytes KAT, an honest hypothesis here),
and apply `runRealizes`.  No per-protocol proof skeleton: the
encrypt-then-authenticate structure fits the unary `ProtocolKernels` template
exactly, so the protocol-level composition assembles for free.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeadProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

variable {C : Type*}

/-! ## §0  A shared two-phase pipeline assembler

Every AEAD here is a two-phase pipeline: `n` copies of a *cipher* leaf realizing
the cipher round specs, then `m` copies of a *MAC* leaf realizing the MAC fold
specs.  We factor the leaf list / spec list / realization bundle once and reuse
it for all four protocols; only the leaf-names and abstract round specs differ.

The realization bundle is assembled by induction over each phase from the
per-block realization hypotheses (each indexed by block position), exactly the
`List.Forall₂.cons`/`nil` assembly the template's `realized` field demands. -/

/-- The leaf list of a two-phase AEAD: `n` cipher-leaf copies then `m` MAC-leaf
    copies. -/
def twoPhaseLeaves (cipherLeaf macLeaf : String) (n m : Nat) : List String :=
  List.replicate n cipherLeaf ++ List.replicate m macLeaf

/-- The spec list of a two-phase AEAD: `n` cipher round specs
    (`cipherStep 0, …, cipherStep (n-1)`) then `m` MAC fold specs
    (`macStep 0, …, macStep (m-1)`).  Pipeline order is AEAD order: encrypt
    first, then authenticate. -/
def twoPhaseSpecs (cipherStep macStep : Nat → C → C) (n m : Nat) : List (C → C) :=
  (List.range n).map (fun i => cipherStep i)
    ++ (List.range m).map (fun i => macStep i)

/-- A single phase's realization bundle: `replicate k leaf` realizes
    `(range k).map (step ·)`, assembled by induction on `k` from the per-block
    realization hypotheses. -/
theorem phaseRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (step : Nat → C → C) (leaf : String) (k : Nat)
    (hStep : ∀ i, KernelRealizes decode (step i) leaf leafSpec) :
    List.Forall₂
      (fun l s => KernelRealizes decode s l leafSpec)
      (List.replicate k leaf) ((List.range k).map (fun i => step i)) := by
  induction k with
  | zero => exact List.Forall₂.nil
  | succ j ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.replicate_succ']
      exact List.rel_append ih (List.Forall₂.cons (hStep j) List.Forall₂.nil)

/-- The two-phase realization bundle: the cipher phase concatenated with the MAC
    phase, each assembled by `phaseRealized`. -/
theorem twoPhaseRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (cipherStep macStep : Nat → C → C) (cipherLeaf macLeaf : String) (n m : Nat)
    (hCipher : ∀ i, KernelRealizes decode (cipherStep i) cipherLeaf leafSpec)
    (hMac : ∀ i, KernelRealizes decode (macStep i) macLeaf leafSpec) :
    List.Forall₂
      (fun l s => KernelRealizes decode s l leafSpec)
      (twoPhaseLeaves cipherLeaf macLeaf n m)
      (twoPhaseSpecs cipherStep macStep n m) := by
  unfold twoPhaseLeaves twoPhaseSpecs
  exact List.rel_append
    (phaseRealized leafSpec decode cipherStep cipherLeaf n hCipher)
    (phaseRealized leafSpec decode macStep macLeaf m hMac)

/-- The assembled two-phase `ProtocolKernels`: cipher then MAC leaves, their
    abstract round specs, the decoder, and the per-kernel realizations assembled
    into the position-wise `Forall₂` via `twoPhaseRealized`. -/
def twoPhaseProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (cipherStep macStep : Nat → C → C) (cipherLeaf macLeaf : String) (n m : Nat)
    (hCipher : ∀ i, KernelRealizes decode (cipherStep i) cipherLeaf leafSpec)
    (hMac : ∀ i, KernelRealizes decode (macStep i) macLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := twoPhaseLeaves cipherLeaf macLeaf n m
  specs := twoPhaseSpecs cipherStep macStep n m
  decode := decode
  realized :=
    twoPhaseRealized leafSpec decode cipherStep macStep cipherLeaf macLeaf n m
      hCipher hMac

/-- The whole two-phase AEAD emit-realization: the full cipher-then-MAC `pipeN`
    pipeline decodes to the composite of the cipher + MAC specs.  A single
    `runRealizes` call on the assembled protocol. -/
theorem twoPhase_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (cipherStep macStep : Nat → C → C) (cipherLeaf macLeaf : String) (n m : Nat)
    (hCipher : ∀ i, KernelRealizes decode (cipherStep i) cipherLeaf leafSpec)
    (hMac : ∀ i, KernelRealizes decode (macStep i) macLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (twoPhaseLeaves cipherLeaf macLeaf n m) oldDest xVal)
      = composeSpecs (twoPhaseSpecs cipherStep macStep n m) (decode xVal) :=
  (twoPhaseProtocol leafSpec decode cipherStep macStep cipherLeaf macLeaf n m
    hCipher hMac).runRealizes oldDest xVal

/-! ## §1  ChaCha20-Poly1305 (RFC 8439)

The IETF AEAD: `n` ChaCha20 keystream blocks (RFC 8439 §2.3) feeding the
running state, then `m` Poly1305 accumulator-update blocks (RFC 8439 §2.5) over
the ciphertext.  The emitted leaves are the scalar ChaCha20 block kernel
(`SymmetricKernelRegistryEntry`'s `chachaBlock` row) and the Poly1305 per-block
update kernel (`processBlock` row).  The whole AEAD is the cipher phase then the
MAC phase — `twoPhase` instantiated at these two leaves. -/

/-- The emitted leaf-name of the ChaCha20 block kernel (RFC 8439 §2.3,
    `SymmetricKernelRegistryEntry`'s scalar `chachaBlock` row). -/
def chachaBlockLeaf : String := "chacha20_block"

/-- The emitted leaf-name of the Poly1305 per-block update kernel
    (RFC 8439 §2.5, `SymmetricKernelRegistryEntry`'s `processBlock` row). -/
def poly1305BlockLeaf : String := "poly1305_block"

/-- The ChaCha20-Poly1305 emitted leaf list: `n` ChaCha20 block leaves then `m`
    Poly1305 block leaves. -/
def chachapolyLeaves (n m : Nat) : List String :=
  twoPhaseLeaves chachaBlockLeaf poly1305BlockLeaf n m

/-- The ChaCha20-Poly1305 kernel-spec list: `n` ChaCha20 keystream-block round
    specs then `m` Poly1305 fold specs. -/
def chachapolySpecs (chachaStep polyStep : Nat → C → C) (n m : Nat) : List (C → C) :=
  twoPhaseSpecs chachaStep polyStep n m

/-- **The assembled ChaCha20-Poly1305 protocol.**  The cipher = `n` ChaCha20
    blocks, the MAC = `m` Poly1305 blocks, their abstract round specs, the
    decoder, and the per-kernel realizations (each an honest leaf-bytes KAT
    hypothesis) assembled by `twoPhaseRealized`. -/
def chachapolyProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (chachaStep polyStep : Nat → C → C) (n m : Nat)
    (hChacha : ∀ i, KernelRealizes decode (chachaStep i) chachaBlockLeaf leafSpec)
    (hPoly : ∀ i, KernelRealizes decode (polyStep i) poly1305BlockLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  twoPhaseProtocol leafSpec decode chachaStep polyStep chachaBlockLeaf
    poly1305BlockLeaf n m hChacha hPoly

/-- **The whole ChaCha20-Poly1305 emit-realization (axis-6).**  The full
    `n`-block ChaCha20 keystream then `m`-block Poly1305 fold `pipeN` pipeline,
    read through `decode`, computes the composite `composeSpecs chachapolySpecs`
    of the input.  A single `runRealizes` call from the per-kernel realizations
    and the generic composition law. -/
theorem chachapoly_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (chachaStep polyStep : Nat → C → C) (n m : Nat)
    (hChacha : ∀ i, KernelRealizes decode (chachaStep i) chachaBlockLeaf leafSpec)
    (hPoly : ∀ i, KernelRealizes decode (polyStep i) poly1305BlockLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (chachapolyLeaves n m) oldDest xVal)
      = composeSpecs (chachapolySpecs chachaStep polyStep n m) (decode xVal) :=
  (chachapolyProtocol leafSpec decode chachaStep polyStep n m hChacha hPoly).runRealizes
    oldDest xVal

/-! ## §2  AES-GCM

`n` AES counter-mode blocks (`GCTR`: AES-128 of the counter, XORed into the
state) then `m` GHASH fold steps (the `GF(2^128)` MAC, one `state ↦ (state ⊕
block) · H` per block).  The emitted leaves are the AES-CTR block kernel and the
GHASH step kernel (cf. `CatCrypt/Crypto/AESGCM/SurfaceDeps.lean`'s `gctrBlock`
and `ghashStep`).  No GHASH-specific registry row exists, so the GHASH fold spec
is an abstract `C → C` step (an honest opaque model of one GHASH multiply-add). -/

/-- The emitted leaf-name of the AES-GCM counter-mode block kernel
    (`gctrBlock`, cf. `AESGCM/SurfaceDeps.lean`). -/
def gctrBlockLeaf : String := "aesgcm_gctr_block"

/-- The emitted leaf-name of the AES-GCM GHASH fold-step kernel (`ghashStep`,
    cf. `AESGCM/SurfaceDeps.lean`).  No GHASH registry row exists; its fold spec
    is an abstract `C → C` step. -/
def ghashStepLeaf : String := "aesgcm_ghash_step"

/-- The AES-GCM emitted leaf list: `n` GCTR block leaves then `m` GHASH step
    leaves. -/
def aesgcmLeaves (n m : Nat) : List String :=
  twoPhaseLeaves gctrBlockLeaf ghashStepLeaf n m

/-- The AES-GCM kernel-spec list: `n` AES counter-block round specs then `m`
    GHASH fold specs (abstract). -/
def aesgcmSpecs (ctrStep ghashStep : Nat → C → C) (n m : Nat) : List (C → C) :=
  twoPhaseSpecs ctrStep ghashStep n m

/-- **The assembled AES-GCM protocol.**  The cipher = `n` AES counter blocks,
    the MAC = `m` GHASH fold steps, their abstract round specs, the decoder, and
    the per-kernel realizations assembled by `twoPhaseRealized`. -/
def aesgcmProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (ctrStep ghashStep : Nat → C → C) (n m : Nat)
    (hCtr : ∀ i, KernelRealizes decode (ctrStep i) gctrBlockLeaf leafSpec)
    (hGhash : ∀ i, KernelRealizes decode (ghashStep i) ghashStepLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  twoPhaseProtocol leafSpec decode ctrStep ghashStep gctrBlockLeaf
    ghashStepLeaf n m hCtr hGhash

/-- **The whole AES-GCM emit-realization (axis-6).**  The full `n`-block AES
    counter-mode then `m`-step GHASH fold `pipeN` pipeline, read through
    `decode`, computes the composite `composeSpecs aesgcmSpecs` of the input.  A
    single `runRealizes` call from the per-kernel realizations and the generic
    composition law. -/
theorem aesgcm_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (ctrStep ghashStep : Nat → C → C) (n m : Nat)
    (hCtr : ∀ i, KernelRealizes decode (ctrStep i) gctrBlockLeaf leafSpec)
    (hGhash : ∀ i, KernelRealizes decode (ghashStep i) ghashStepLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (aesgcmLeaves n m) oldDest xVal)
      = composeSpecs (aesgcmSpecs ctrStep ghashStep n m) (decode xVal) :=
  (aesgcmProtocol leafSpec decode ctrStep ghashStep n m hCtr hGhash).runRealizes
    oldDest xVal

/-! ## §3  AES-SIV (RFC 5297)

The misuse-resistant SIV mode runs **authenticate-then-encrypt** in the encrypt
direction: `n` S2V/CMAC fold steps over the AD/plaintext vector produce the
synthetic IV, then `m` AES counter-mode blocks encrypt under it.  The emitted
leaves are the S2V fold-step kernel (`s2vStep`/`cmac`, cf.
`AESSIV/AesSivVerified.lean` and `AESSIV/SurfaceDeps.lean`) and the AES-CTR
block kernel.  Here the "cipher phase" of the template is the S2V fold and the
"MAC phase" the CTR blocks — the template is order-agnostic (two unary phases),
so it models SIV's authenticate-first order directly. -/

/-- The emitted leaf-name of the AES-SIV S2V/CMAC fold-step kernel
    (`s2vStep`, cf. `AESSIV/AesSivVerified.lean`). -/
def s2vStepLeaf : String := "aessiv_s2v_step"

/-- The emitted leaf-name of the AES-SIV counter-mode block kernel
    (`aesCtrEncrypt`, cf. `AESSIV/SurfaceDeps.lean`). -/
def sivCtrBlockLeaf : String := "aessiv_ctr_block"

/-- The AES-SIV emitted leaf list: `n` S2V fold-step leaves then `m` CTR block
    leaves (authenticate-then-encrypt). -/
def aessivLeaves (n m : Nat) : List String :=
  twoPhaseLeaves s2vStepLeaf sivCtrBlockLeaf n m

/-- The AES-SIV kernel-spec list: `n` S2V fold-step specs then `m` AES
    counter-block specs. -/
def aessivSpecs (s2vStep ctrStep : Nat → C → C) (n m : Nat) : List (C → C) :=
  twoPhaseSpecs s2vStep ctrStep n m

/-- **The assembled AES-SIV protocol.**  Phase 1 = `n` S2V/CMAC fold steps,
    phase 2 = `m` AES counter blocks, their abstract round specs, the decoder,
    and the per-kernel realizations assembled by `twoPhaseRealized`. -/
def aessivProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (s2vStep ctrStep : Nat → C → C) (n m : Nat)
    (hS2v : ∀ i, KernelRealizes decode (s2vStep i) s2vStepLeaf leafSpec)
    (hCtr : ∀ i, KernelRealizes decode (ctrStep i) sivCtrBlockLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  twoPhaseProtocol leafSpec decode s2vStep ctrStep s2vStepLeaf
    sivCtrBlockLeaf n m hS2v hCtr

/-- **The whole AES-SIV emit-realization (axis-6).**  The full `n`-step S2V
    fold then `m`-block AES counter-mode `pipeN` pipeline, read through
    `decode`, computes the composite `composeSpecs aessivSpecs` of the input.  A
    single `runRealizes` call from the per-kernel realizations and the generic
    composition law. -/
theorem aessiv_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (s2vStep ctrStep : Nat → C → C) (n m : Nat)
    (hS2v : ∀ i, KernelRealizes decode (s2vStep i) s2vStepLeaf leafSpec)
    (hCtr : ∀ i, KernelRealizes decode (ctrStep i) sivCtrBlockLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (aessivLeaves n m) oldDest xVal)
      = composeSpecs (aessivSpecs s2vStep ctrStep n m) (decode xVal) :=
  (aessivProtocol leafSpec decode s2vStep ctrStep n m hS2v hCtr).runRealizes
    oldDest xVal

/-! ## §4  AEGIS-128L

AEGIS-128L is an AES-round-based AEAD whose entire computation is a chain of
`state_update` steps (cf. `AEGIS/Extraction/Aegis_haxpipe.lean`): `n` absorb
steps over the AD, then `m` encrypt/finalize steps over the message.  Both
phases use the *same* `state_update` primitive (it is one emitted kernel applied
in two phases), so the two leaf-names coincide — the `twoPhase` assembler still
applies (the leaf list is `n + m` copies of the one update leaf), and the
distinct per-phase specs capture the different absorb-vs-encrypt block data. -/

/-- The emitted leaf-name of the AEGIS-128L `state_update` kernel (the single
    AEGIS state-machine update primitive, cf.
    `AEGIS/Extraction/Aegis_haxpipe.lean`). -/
def aegisUpdateLeaf : String := "aegis_state_update"

/-- The AEGIS-128L emitted leaf list: `n` absorb-phase update leaves then `m`
    encrypt-phase update leaves — both the same `state_update` kernel. -/
def aegisLeaves (n m : Nat) : List String :=
  twoPhaseLeaves aegisUpdateLeaf aegisUpdateLeaf n m

/-- The AEGIS-128L kernel-spec list: `n` absorb-step specs then `m`
    encrypt-step specs (distinct per-block data, same update primitive). -/
def aegisSpecs (absorbStep encStep : Nat → C → C) (n m : Nat) : List (C → C) :=
  twoPhaseSpecs absorbStep encStep n m

/-- **The assembled AEGIS-128L protocol.**  Phase 1 = `n` absorb updates,
    phase 2 = `m` encrypt updates, their abstract round specs, the decoder, and
    the per-kernel realizations assembled by `twoPhaseRealized`. -/
def aegisProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (absorbStep encStep : Nat → C → C) (n m : Nat)
    (hAbsorb : ∀ i, KernelRealizes decode (absorbStep i) aegisUpdateLeaf leafSpec)
    (hEnc : ∀ i, KernelRealizes decode (encStep i) aegisUpdateLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  twoPhaseProtocol leafSpec decode absorbStep encStep aegisUpdateLeaf
    aegisUpdateLeaf n m hAbsorb hEnc

/-- **The whole AEGIS-128L emit-realization (axis-6).**  The full `n`-step
    absorb then `m`-step encrypt `state_update` chain `pipeN` pipeline, read
    through `decode`, computes the composite `composeSpecs aegisSpecs` of the
    input.  A single `runRealizes` call from the per-kernel realizations and the
    generic composition law. -/
theorem aegis_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (absorbStep encStep : Nat → C → C) (n m : Nat)
    (hAbsorb : ∀ i, KernelRealizes decode (absorbStep i) aegisUpdateLeaf leafSpec)
    (hEnc : ∀ i, KernelRealizes decode (encStep i) aegisUpdateLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (aegisLeaves n m) oldDest xVal)
      = composeSpecs (aegisSpecs absorbStep encStep n m) (decode xVal) :=
  (aegisProtocol leafSpec decode absorbStep encStep n m hAbsorb hEnc).runRealizes
    oldDest xVal

end CatCrypt.Crypto.SecureCompilation.AeadProtocolKernels
