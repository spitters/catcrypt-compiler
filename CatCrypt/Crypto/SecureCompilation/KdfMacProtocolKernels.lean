/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# A batch of KDF / MAC / DRBG protocols as axis-6 `ProtocolKernels` instances

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on a **batch** of real
NIST KDF / MAC / DRBG protocols, exactly as `HkdfProtocolKernels.lean` does for
HKDF (RFC 5869).  Each of these protocols is structurally a **unary kernel
chain** — a sequence of `state → state` steps over the running keying / sponge
material — which is precisely the shape the `ProtocolKernels` template models.

The protocols covered:

* **HMAC-DRBG** (NIST SP 800-90A §10.1.2): a chain of HMAC `Update`/`Generate`
  steps over the `(Key, V)` working state.  `Generate` emits one output block per
  HMAC application, so the pipeline is one `instantiate`/`update` step followed by
  `n` `generate-block` HMAC rounds — parametric in the output-block count `n`,
  just like HKDF-Expand.
* **KBKDF** (NIST SP 800-108 counter mode): a chain of PRF (= HMAC) evaluations
  `K(i) = PRF(K_IN, [i] ‖ Label ‖ 0x00 ‖ Context ‖ [L])`, one emitted PRF block
  per counter value — a pure `n`-block HMAC chain.
* **KMAC** (NIST SP 800-185): cSHAKE-based, i.e. a Keccak-f[1600] sponge chain —
  one `cSHAKE` initialisation/absorb of the customisation+key prefix, then `n`
  Keccak-f permutation rounds over the running sponge state.
* **TLS 1.3 HKDF-Expand-Label / key schedule** (RFC 8446 §7.1): the TLS key
  schedule is a chain of `HKDF-Expand-Label` / `Derive-Secret` steps, each one
  an HMAC application over the running secret — a clean unary chain of `n`
  expand-label kernels following the initial extract.

## What each instance delivers (mirroring HKDF)

For each protocol `P` we provide:

* `<P>Specs` — the kernel pipeline as a list of **abstract, unary** `C → C`
  round specs (one prefix step plus `n` repeated block steps).  These are opaque
  models of each round; the deliverable is the protocol-structure composition,
  not re-deriving each round's HMAC / Keccak internals.
* `<P>Leaves` — the matching emitted leaf-names, taken from the real
  extraction (`CatCrypt/Crypto/{HMACDRBG,KBKDF,KMAC,…}`), e.g.
  `"hmac_drbg_update"`, `"hmac_sha256"`, `"keccak_f1600"`.
* `<P>Protocol : ProtocolKernels C leafSpec` — the assembled bundle, whose
  `realized` field is the position-wise `List.Forall₂` of the per-kernel
  realizations, **each taken as a hypothesis** (the kernel's leaf-bytes KAT).
* `<P>_protocol_realizes` — the whole-protocol emit-realization,
  `decode (pipeN <P>Leaves …) = composeSpecs <P>Specs (decode x)`, obtained by a
  single `runRealizes` call from nothing but the per-kernel realizations and the
  generic composition law.

## The point (axis-6 on a batch of real protocols)

Each of these RFC / NIST protocols has its *whole* emit-realization assembled
from its kernel rows by `runRealizes`, with no per-protocol proof skeleton: the
KDF/MAC/DRBG kernel-chain structure fits the unary `ProtocolKernels` template
exactly.  The per-kernel realizations are honest hypotheses (each is the
kernel's leaf-bytes KAT); the contribution is that the protocol-level
composition assembles for free from them.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.KdfMacProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

variable {C : Type*}

/-! ## §0  A shared chain helper

Every protocol below has the same shape as HKDF: one *prefix* kernel followed by
`n` copies of a *block* kernel.  We factor that shape into a single helper so each
protocol instance is a thin renaming.

`chainSpecs prefixStep blockStep n` is `prefixStep :: (range n).map blockStep`
and `chainLeaves prefixLeaf blockLeaf n` is `prefixLeaf :: replicate n blockLeaf`
— same length, same order.  `chainRealized` then assembles the position-wise
`Forall₂` by induction on `n` from the prefix realization and one block
realization per block (verbatim the `HkdfProtocolKernels.hkdfRealized` proof). -/

/-- A one-prefix-then-`n`-blocks unary spec list. -/
def chainSpecs (prefixStep : C → C) (blockStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  prefixStep :: (List.range n).map (fun i => blockStep i)

/-- The matching one-prefix-then-`n`-blocks leaf list. -/
def chainLeaves (prefixLeaf blockLeaf : String) (n : Nat) : List String :=
  prefixLeaf :: List.replicate n blockLeaf

/-- The position-wise realization bundle for the one-prefix-then-`n`-blocks
    pipeline, assembled by induction on `n` from the prefix realization and one
    block realization per block. -/
theorem chainRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (blockStep : Nat → C → C)
    (prefixLeaf blockLeaf : String) (n : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec) :
    List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
      (chainLeaves prefixLeaf blockLeaf n)
      (chainSpecs prefixStep blockStep n) := by
  unfold chainLeaves chainSpecs
  refine List.Forall₂.cons hPrefix ?_
  induction n with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.replicate_succ']
      exact List.rel_append ih (List.Forall₂.cons (hBlock m) List.Forall₂.nil)

/-- The assembled one-prefix-then-`n`-blocks `ProtocolKernels`. -/
def chainProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (blockStep : Nat → C → C)
    (prefixLeaf blockLeaf : String) (n : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := chainLeaves prefixLeaf blockLeaf n
  specs := chainSpecs prefixStep blockStep n
  decode := decode
  realized :=
    chainRealized leafSpec decode prefixStep blockStep prefixLeaf blockLeaf n
      hPrefix hBlock

/-- The whole-pipeline emit-realization of a one-prefix-then-`n`-blocks chain,
    obtained by a single `runRealizes` call. -/
theorem chain_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prefixStep : C → C) (blockStep : Nat → C → C)
    (prefixLeaf blockLeaf : String) (n : Nat)
    (hPrefix : KernelRealizes decode prefixStep prefixLeaf leafSpec)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (chainLeaves prefixLeaf blockLeaf n) oldDest xVal)
      = composeSpecs (chainSpecs prefixStep blockStep n) (decode xVal) :=
  (chainProtocol leafSpec decode prefixStep blockStep prefixLeaf blockLeaf n
      hPrefix hBlock).runRealizes oldDest xVal

/-! ## §1  HMAC-DRBG (NIST SP 800-90A §10.1.2)

HMAC-DRBG keeps a working state `(Key, V)`.  `Instantiate`/`Update` runs one HMAC
application to seed the state; `Generate` then runs a *chain* of HMAC
applications `V ← HMAC(Key, V)`, emitting one output block per application.  This
is HMAC-of-the-running-state, i.e. a unary chain: one `update`-step prefix
followed by `n` `generate`-block HMAC rounds.

Leaf names from the real extraction (`CatCrypt/Crypto/HMACDRBG/`):
`"hmac_drbg_update"` (the update/instantiate kernel) and `"hmac_sha256"` (each
HMAC generate block reuses the emitted SHA-256 HMAC kernel — cf. the
`HmacKernelRegistryEntry` row). -/

/-- The HMAC-DRBG `Update`/`Instantiate` kernel leaf. -/
def hmacDrbgUpdateLeaf : String := "hmac_drbg_update"

/-- The HMAC-DRBG `Generate`-block HMAC kernel leaf (SHA-256 HMAC). -/
def hmacDrbgGenerateLeaf : String := "hmac_sha256"

/-- The HMAC-DRBG kernel-spec list: one `updateStep` then `n` `generateStep i`
    HMAC blocks. -/
def hmacDrbgSpecs (updateStep : C → C) (generateStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs updateStep generateStep n

/-- The HMAC-DRBG leaf list: the update leaf then `n` copies of the generate
    HMAC leaf. -/
def hmacDrbgLeaves (n : Nat) : List String :=
  chainLeaves hmacDrbgUpdateLeaf hmacDrbgGenerateLeaf n

/-- **The assembled HMAC-DRBG protocol.** -/
def hmacDrbgProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (updateStep : C → C) (generateStep : Nat → C → C) (n : Nat)
    (hUpdate : KernelRealizes decode updateStep hmacDrbgUpdateLeaf leafSpec)
    (hGenerate : ∀ i,
      KernelRealizes decode (generateStep i) hmacDrbgGenerateLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  chainProtocol leafSpec decode updateStep generateStep
    hmacDrbgUpdateLeaf hmacDrbgGenerateLeaf n hUpdate hGenerate

/-- **The whole-HMAC-DRBG emit-realization (axis-6 on a real protocol).**  The
    entire emitted DRBG chain — one update kernel then `n` HMAC generate blocks —
    decodes to the composite `composeSpecs (hmacDrbgSpecs …)` of the input.
    Assembled by one `runRealizes` call from the per-kernel realizations
    (each an honest leaf-bytes KAT hypothesis) and the generic composition law. -/
theorem hmacdrbg_protocol_realizes (leafSpec : LeafSpec)
    (decode : RustVal .TFp → C)
    (updateStep : C → C) (generateStep : Nat → C → C) (n : Nat)
    (hUpdate : KernelRealizes decode updateStep hmacDrbgUpdateLeaf leafSpec)
    (hGenerate : ∀ i,
      KernelRealizes decode (generateStep i) hmacDrbgGenerateLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (hmacDrbgLeaves n) oldDest xVal)
      = composeSpecs (hmacDrbgSpecs updateStep generateStep n) (decode xVal) :=
  chain_protocol_realizes leafSpec decode updateStep generateStep
    hmacDrbgUpdateLeaf hmacDrbgGenerateLeaf n hUpdate hGenerate oldDest xVal

/-! ## §2  KBKDF — counter mode (NIST SP 800-108)

The SP 800-108 counter-mode KDF derives keying material as a chain of PRF
(= HMAC) evaluations
`K(i) = PRF(K_IN, [i]₂ ‖ Label ‖ 0x00 ‖ Context ‖ [L]₂)`, one PRF block per
counter value `i = 1, …, n`.  Each block reuses the emitted HMAC kernel.  We
model this as a `prepareKey` prefix (the `hmac_prepare_key` precomputation, cf.
`CatCrypt/Crypto/KBKDF/`) followed by `n` `prfBlock i` HMAC rounds.

Leaf names from the real extraction (`CatCrypt/Crypto/KBKDF/`):
`"hmac_prepare_key"` and `"hmac_sha256"`. -/

/-- The KBKDF key-preparation kernel leaf. -/
def kbkdfPrepareLeaf : String := "hmac_prepare_key"

/-- The KBKDF per-counter PRF (HMAC) block kernel leaf. -/
def kbkdfPrfLeaf : String := "hmac_sha256"

/-- The KBKDF kernel-spec list: one `prepareStep` then `n` `prfStep i` HMAC
    blocks. -/
def kbkdfSpecs (prepareStep : C → C) (prfStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs prepareStep prfStep n

/-- The KBKDF leaf list: the prepare leaf then `n` copies of the PRF HMAC leaf. -/
def kbkdfLeaves (n : Nat) : List String :=
  chainLeaves kbkdfPrepareLeaf kbkdfPrfLeaf n

/-- **The assembled KBKDF protocol.** -/
def kbkdfProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prepareStep : C → C) (prfStep : Nat → C → C) (n : Nat)
    (hPrepare : KernelRealizes decode prepareStep kbkdfPrepareLeaf leafSpec)
    (hPrf : ∀ i, KernelRealizes decode (prfStep i) kbkdfPrfLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  chainProtocol leafSpec decode prepareStep prfStep
    kbkdfPrepareLeaf kbkdfPrfLeaf n hPrepare hPrf

/-- **The whole-KBKDF emit-realization (axis-6 on a real protocol).**  The entire
    emitted counter-mode chain — one key-prepare kernel then `n` PRF HMAC blocks —
    decodes to the composite `composeSpecs (kbkdfSpecs …)` of the input.
    Assembled by one `runRealizes` call from the per-kernel realizations. -/
theorem kbkdf_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (prepareStep : C → C) (prfStep : Nat → C → C) (n : Nat)
    (hPrepare : KernelRealizes decode prepareStep kbkdfPrepareLeaf leafSpec)
    (hPrf : ∀ i, KernelRealizes decode (prfStep i) kbkdfPrfLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (kbkdfLeaves n) oldDest xVal)
      = composeSpecs (kbkdfSpecs prepareStep prfStep n) (decode xVal) :=
  chain_protocol_realizes leafSpec decode prepareStep prfStep
    kbkdfPrepareLeaf kbkdfPrfLeaf n hPrepare hPrf oldDest xVal

/-! ## §3  KMAC (NIST SP 800-185)

KMAC is a cSHAKE-based MAC: cSHAKE in turn is the Keccak sponge with a
customisation/function-name prefix absorbed first.  The computation is therefore
a Keccak-f[1600] **sponge chain**: one `cSHAKE`-init/absorb of the encoded
`(function-name, customisation, key)` prefix, then `n` Keccak-f permutation
rounds over the running sponge state (one per absorbed/squeezed block).

Leaf names: the cSHAKE prefix-absorb kernel `"cshake_absorb"` (the bytepad /
`encode_string` framing from `CatCrypt/Crypto/KMAC/`) and the Keccak-f
permutation `"keccak_f1600"` (the FIPS-202 permutation row, cf. the
`HashKernelRegistryEntry` `keccak_f`-spec). -/

/-- The KMAC cSHAKE prefix-absorb kernel leaf. -/
def kmacAbsorbLeaf : String := "cshake_absorb"

/-- The KMAC Keccak-f[1600] permutation round kernel leaf. -/
def kmacKeccakLeaf : String := "keccak_f1600"

/-- The KMAC kernel-spec list: one `absorbStep` then `n` `keccakStep i`
    permutation rounds. -/
def kmacSpecs (absorbStep : C → C) (keccakStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs absorbStep keccakStep n

/-- The KMAC leaf list: the cSHAKE-absorb leaf then `n` copies of the Keccak-f
    permutation leaf. -/
def kmacLeaves (n : Nat) : List String :=
  chainLeaves kmacAbsorbLeaf kmacKeccakLeaf n

/-- **The assembled KMAC protocol.** -/
def kmacProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (absorbStep : C → C) (keccakStep : Nat → C → C) (n : Nat)
    (hAbsorb : KernelRealizes decode absorbStep kmacAbsorbLeaf leafSpec)
    (hKeccak : ∀ i, KernelRealizes decode (keccakStep i) kmacKeccakLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  chainProtocol leafSpec decode absorbStep keccakStep
    kmacAbsorbLeaf kmacKeccakLeaf n hAbsorb hKeccak

/-- **The whole-KMAC emit-realization (axis-6 on a real protocol).**  The entire
    emitted cSHAKE sponge chain — one prefix-absorb kernel then `n` Keccak-f
    permutation rounds — decodes to the composite `composeSpecs (kmacSpecs …)` of
    the input.  Assembled by one `runRealizes` call from the per-kernel
    realizations (each an honest leaf-bytes KAT hypothesis). -/
theorem kmac_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (absorbStep : C → C) (keccakStep : Nat → C → C) (n : Nat)
    (hAbsorb : KernelRealizes decode absorbStep kmacAbsorbLeaf leafSpec)
    (hKeccak : ∀ i, KernelRealizes decode (keccakStep i) kmacKeccakLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (kmacLeaves n) oldDest xVal)
      = composeSpecs (kmacSpecs absorbStep keccakStep n) (decode xVal) :=
  chain_protocol_realizes leafSpec decode absorbStep keccakStep
    kmacAbsorbLeaf kmacKeccakLeaf n hAbsorb hKeccak oldDest xVal

/-! ## §4  TLS 1.3 key schedule — HKDF-Expand-Label chain (RFC 8446 §7.1)

The TLS 1.3 key schedule (RFC 8446 §7.1) is a chain of `Derive-Secret` /
`HKDF-Expand-Label` steps over the running secret: each `Derive-Secret`/
`HKDF-Expand-Label` is one HMAC application, and the schedule threads each
derived secret into the next derivation.  After the initial `HKDF-Extract`, the
schedule is a unary chain of `n` `HKDF-Expand-Label` steps.

Leaf names from the HKDF/TLS extraction (`CatCrypt/Crypto/HKDF/`, reused by the
TLS key schedule): the extract leaf `"hkdf_sha256_extract"` and the
expand-label leaf `"hkdf_expand_label"`. -/

/-- The TLS 1.3 key-schedule `HKDF-Extract` kernel leaf. -/
def tls13ExtractLeaf : String := "hkdf_sha256_extract"

/-- The TLS 1.3 `HKDF-Expand-Label` / `Derive-Secret` kernel leaf. -/
def tls13ExpandLabelLeaf : String := "hkdf_expand_label"

/-- The TLS 1.3 key-schedule kernel-spec list: one `extractStep` then `n`
    `expandLabelStep i` HMAC derivations. -/
def tls13Specs (extractStep : C → C) (expandLabelStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs extractStep expandLabelStep n

/-- The TLS 1.3 key-schedule leaf list: the extract leaf then `n` copies of the
    expand-label leaf. -/
def tls13Leaves (n : Nat) : List String :=
  chainLeaves tls13ExtractLeaf tls13ExpandLabelLeaf n

/-- **The assembled TLS 1.3 key-schedule protocol.** -/
def tls13Protocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (extractStep : C → C) (expandLabelStep : Nat → C → C) (n : Nat)
    (hExtract : KernelRealizes decode extractStep tls13ExtractLeaf leafSpec)
    (hExpandLabel : ∀ i,
      KernelRealizes decode (expandLabelStep i) tls13ExpandLabelLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  chainProtocol leafSpec decode extractStep expandLabelStep
    tls13ExtractLeaf tls13ExpandLabelLeaf n hExtract hExpandLabel

/-- **The whole-TLS-1.3-key-schedule emit-realization (axis-6 on a real
    protocol).**  The entire emitted key-schedule chain — one extract kernel then
    `n` HKDF-Expand-Label derivations — decodes to the composite
    `composeSpecs (tls13Specs …)` of the input secret.  Assembled by one
    `runRealizes` call from the per-kernel realizations. -/
theorem tls13_keyschedule_protocol_realizes (leafSpec : LeafSpec)
    (decode : RustVal .TFp → C)
    (extractStep : C → C) (expandLabelStep : Nat → C → C) (n : Nat)
    (hExtract : KernelRealizes decode extractStep tls13ExtractLeaf leafSpec)
    (hExpandLabel : ∀ i,
      KernelRealizes decode (expandLabelStep i) tls13ExpandLabelLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (tls13Leaves n) oldDest xVal)
      = composeSpecs (tls13Specs extractStep expandLabelStep n) (decode xVal) :=
  chain_protocol_realizes leafSpec decode extractStep expandLabelStep
    tls13ExtractLeaf tls13ExpandLabelLeaf n hExtract hExpandLabel oldDest xVal

end CatCrypt.Crypto.SecureCompilation.KdfMacProtocolKernels
